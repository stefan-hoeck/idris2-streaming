module Data.MVar

import Data.IORef
import System.Concurrency

export
withMutex : Mutex -> IO a -> IO a
withMutex m io = do
  mutexAcquire m
  res <- io
  mutexRelease m
  pure res

export
record MVar a where
  constructor MkMVar
  ref : IORef a
  mu  : Mutex

export
newMVar : a -> IO (MVar a)
newMVar va = [| MkMVar (newIORef va) makeMutex |]

export
readMVar : MVar a -> IO a
readMVar (MkMVar ref mu) = withMutex mu $ readIORef ref

export
writeMVar : MVar a -> a -> IO ()
writeMVar (MkMVar ref mu) va = withMutex mu $ writeIORef ref va

export
modifyMVar : MVar a -> (a -> a) -> IO ()
modifyMVar (MkMVar ref mu) f = withMutex mu $ modifyIORef ref f

export
modifyAndGetMVar : MVar a -> (a -> a) -> IO a
modifyAndGetMVar (MkMVar ref mu) f = withMutex mu $ do
  va <- f <$> readIORef ref
  writeIORef ref va
  pure va

export
withMVar : MVar a -> (IORef a -> IO b) -> IO b
withMVar (MkMVar ref mu) f = withMutex mu (f ref)
