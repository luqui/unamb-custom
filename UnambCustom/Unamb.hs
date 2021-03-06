----------------------------------------
-- |
-- Module    : UnambCustom.Unamb
-- License   : BSD3
--
-- Maintainer  : Luke Palmer <lrpalmer@gmail.com>
-- Stability   : experimental
-- Portability : GHC only
--
-- Functional concurrency with unambiguous choice.  The primary
-- export of this module is the @unamb@ function, which has the
-- following semantics:
--
-- > unamb x   _|_ = x
-- > unamb _|_ x   = x
-- > unamb x   x   = x
--
-- This function is only well-defined when the arguments are
-- constrained to be either equal or @_|_@.  Using it in other
-- capacities will break purity.
--
-- In particular, it is always safe to use on the @()@ type.
--
-- This is a reimplementation of the @unamb@ package by Conal
-- Elliott.  This package implements a custom thread scheduler,
-- whose purpose is to make feasabile \"dense\" uses of 
-- @unamb@ such as:
--
-- > foldr1 unamb [ if x == 100 then 100 else undefined | x <- [0..] ] 
----------------------------------------

module UnambCustom.Unamb 
    ( race, unamb, rebootScheduler )
where

import Prelude hiding (catch)
import Control.Concurrent
import Data.IORef
import qualified Data.Map as Map
import System.IO.Unsafe (unsafePerformIO)
import Control.Exception
import Data.Unique
import Control.Monad.Writer

{- FOR DEBUGGING: 

{-# NOINLINE monChan #-}
monChan :: Chan (String, Monitor)
monChan = unsafePerformIO $ newChan

data Monitor = Take | Taken | Put | Putted

monThread n = do
    (fname,c) <- readChan monChan
    putStr $ fname ++ ": " ++ replicate (2*n) ' '
    case c of
        Take   -> putStrLn "  take"   >> monThread (n+1)
        Taken  -> putStrLn "taken"    >> monThread (n-1)
        Put    -> putStrLn "  put"    >> monThread (n+1)
        Putted -> putStrLn "putted"   >> monThread (n-1)
    
{-
takeMVar' s v = do
    writeChan monChan (s, Take)
    r <- takeMVar v
    writeChan monChan (s, Taken)
    return r

putMVar' s v x = do
    writeChan monChan (s, Put)
    putMVar v x
    writeChan monChan (s, Putted)
-}

END DEBUGGING -}

{-# INLINE takeMVar' #-}
takeMVar' = const takeMVar
{-# INLINE putMVar' #-}
putMVar' = const putMVar

-- Keeps track of the state of an active managed thread.
data LiveEntry = LiveEntry {
    aliveVar :: IORef Bool,
    -- we use this instead of Set for smoother interaction with the other various maps
    subthreads :: IORef (Map.Map ThreadId ()),
    parentEntry :: Maybe LiveEntry
}

-- A record in the queue of threads to spark
data ForkRecord = ForkRecord {
    frParent :: ThreadId,   
    frEntry :: LiveEntry,
    frAction :: IO ()
}

type LiveMap = Map.Map ThreadId LiveEntry
type ForkQueue = Chan ForkRecord

data Scheduler = Scheduler {
    liveMap :: MVar (LiveMap),
    forkQueue :: ForkQueue
}

makeScheduler :: IO Scheduler
makeScheduler = do
    livemap <- newMVar Map.empty
    forkqueue <- newChan
    let sched = Scheduler livemap forkqueue
    forkIO $ schedDaemon sched
    return sched

newLiveEntry :: Maybe LiveEntry -> IO LiveEntry
newLiveEntry parent = do
    var <- newIORef True
    subs <- newIORef Map.empty
    return $ LiveEntry var subs parent

newMThreadWithParent :: Scheduler -> Maybe LiveEntry -> IO () -> IO ()
newMThreadWithParent sched parententry thr = block $ do
    parentid <- myThreadId
    entry <- newLiveEntry parententry
    writeChan (forkQueue sched) $ ForkRecord {
        frParent = parentid,
        frEntry = entry,
        frAction = thr }
    
newMThread :: Scheduler -> IO () -> IO ()
newMThread sched thr = block $ do
    parentid <- myThreadId
    livemap <- takeMVar' "newMThread " (liveMap sched)
    parententry <- return $! Map.lookup parentid livemap
    newMThreadWithParent sched parententry thr
    putMVar' "newMThread " (liveMap sched) livemap

endMThread :: Scheduler -> ThreadId -> IO ()
endMThread sched threadid = block $ do
    livemap <- takeMVar' "endMThread " (liveMap sched)
    death <- execWriterT $ go livemap threadid
    putMVar' "endMThread " (liveMap sched) $ 
        Map.delete threadid (livemap `Map.difference` death)
    mapM_ killThread (Map.keys death)
    where
    go livemap threadid = do
        case Map.lookup threadid livemap of
            Nothing -> return ()
            Just entry -> do
                case parentEntry entry of
                    Nothing -> return ()
                    Just p -> liftIO $ safeModifyIORef (subthreads p) (Map.delete threadid)
                subs <- liftIO . readIORef $ subthreads entry
                tell subs
                liftIO $ writeIORef (aliveVar entry) False
                forM_ (Map.keys subs) $ go livemap

killMThread :: Scheduler -> ThreadId -> IO ()
killMThread sched threadid = do
    endMThread sched threadid
    killThread threadid

schedDaemon :: Scheduler -> IO ()
schedDaemon sched = forever . block $ do
    record <- readChan (forkQueue sched)
    livemap <- takeMVar' "schedDaemon" (liveMap sched)

    case parentEntry (frEntry record) of
        -- unmanaged parent
        Nothing -> do   
            childid <- forkIO $ 
                frAction record `finally` (endMThread sched =<< myThreadId)
            putMVar' "schedDaemon" (liveMap sched) (Map.insert childid (frEntry record) livemap)
        -- managed parent
        Just entry -> do
            alive <- readIORef (aliveVar entry)
            case alive of
                -- dead parent, die of grief
                False -> putMVar' "schedDaemon" (liveMap sched) livemap
                -- live parent, fork and add to parent's list of children
                True -> do
                    childid <- forkIO $ do
                        frAction record
                        endMThread sched =<< myThreadId
                    safeModifyIORef (subthreads entry) (Map.insert childid ())
                    putMVar' "schedDaemon" (liveMap sched) (Map.insert childid (frEntry record) livemap)

rebootSched :: Scheduler -> IO ()
rebootSched sched = block $ do
    livemap <- takeMVar (liveMap sched)
    mapM_ killThread (Map.keys livemap)
    putMVar (liveMap sched) Map.empty
    
{-# NOINLINE theScheduler #-}
theScheduler = unsafePerformIO makeScheduler

raceOn :: Scheduler -> IO a -> IO a -> IO a
raceOn sched ioa iob = do
    -- bootstrap with a single thread if it is not already managed
    livemap <- readMVar (liveMap sched)
    mythread <- myThreadId
    case Map.lookup mythread livemap of
        Nothing -> do
            var <- newEmptyMVar
            newMThreadWithParent sched Nothing $ do
                unsafeRaceOn sched ioa iob >>= putMVar var
            takeMVar var
        Just _ -> unsafeRaceOn sched ioa iob

unsafeRaceOn :: Scheduler -> IO a -> IO a -> IO a
unsafeRaceOn sched ioa iob = do
    var <- newEmptyMVar
    let writer a = a >>= putMVar var
    newMThread sched $ ignoreExceptions (writer ioa)
    newMThread sched $ ignoreExceptions (writer iob)
    takeMVar var
    where
    ignoreExceptions io = io `catch` (\e -> let _ = (e::SomeException) in return ())

-- | Race two actions against each other, returning the value
-- of the first one to finish.
race :: IO a -> IO a -> IO a
race = raceOn theScheduler

-- | Unambiguous choice.  Calling @unamb x y@ has a proof obligation
-- that if @x \/= _|_@ and @y \/= _|_@ then @x = y@.  If this is satisfied,
-- returns the more defined of the two.
--
-- @unamb@ will treat any exception raised as @_|_@.
unamb :: a -> a -> a
unamb a b = unsafePerformIO $ race (return $! a) (return $! b)

-- | Kill all active threads managed by the custom scheduler.
-- Useful for debugging in interactive sessions, but not 
-- recommended otherwise (it will cause all running @unamb@s
-- to block forever).
rebootScheduler :: IO ()
rebootScheduler = rebootSched theScheduler


safeModifyIORef :: IORef a -> (a -> a) -> IO ()
safeModifyIORef r f = atomicModifyIORef r (\x -> (f x, ()))
