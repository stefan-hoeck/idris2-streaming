||| Utilities to convert `Stream`s, `Colist`s, and `List`s to
||| `InputStream`s, and collect stream data in a `List`.
module System.IO.Stream.List

import Data.Colist
import Data.DPair
import Data.Fuel
import Data.IORef
import Data.Iterable
import Data.List
import Data.MVar
import Data.Nat
import System.IO.Stream.Core

%default total

||| Transforms a list into an 'InputStream' that produces no side effects.
export
fromList : List a -> IO (InputStream a)
fromList as = do
  ref <- newIORef as

  let next : IO (Maybe a)
      next = do
        h :: t <- readIORef ref | Nil => pure Nothing
        writeIORef ref t
        pure $ Just h

  makeInputStream next

||| `listOutputStream` returns an `OutputStream` which stores values fed into
||| it and an action which flushes all stored values to a `List`.
||| 
||| The flush action resets the store.
||| 
||| Note that this function /will/ buffer any input sent to it on the heap.
||| If you feed output streams with a reasonable amount of
||| `Fuel` (by invoking `connectWith` for instance), this will
||| not be an issue. If you use one of the partial functions
||| like `connect` to feed an output stream, all bets are of
||| and this might consume arbitrary amounts of memory.
export
listOutputStream : IO (OutputStream c, IO (List c))
listOutputStream = do
    r <- newMVar (the (List c) Nil)

    let go : Maybe a -> IO ()

        flush : IO (List c)
        flush = withMVar r $ \ref => do
                  cs <- readIORef ref
                  writeIORef ref Nil
                  pure (reverse cs)

    c <- makeOutputStream go
    pure (c, flush)

||| Given an IO action that requires an 'OutputStream', creates one and
||| captures all the output the action sends to it as a list.
export
outputToList : (OutputStream a -> IO b) -> IO (List a)
outputToList f = do
  (os, getList) <- listOutputStream
  _ <- f os
  getList

export
toList : Fuel -> InputStream a -> IO (List a)
toList f = outputToList . connectWith f

||| Transforms a `Colist` into an 'InputStream' that produces no side effects.
export
fromColist : Colist a -> IO (InputStream a)
fromColist as = do
  ref <- newIORef as

  let next : IO (Maybe a)
      next = do
        h :: t <- readIORef ref | Nil => pure Nothing
        writeIORef ref t
        pure $ Just h

  makeInputStream next

||| Transforms a `Stream` into an 'InputStream' that produces no side effects.
export
fromStream : Stream a -> IO (InputStream a)
fromStream as = do
  ref <- newIORef as

  let next : IO (Maybe a)
      next = do
        h :: t <- readIORef ref
        writeIORef ref t
        pure $ Just h

  makeInputStream next

||| Feeds a list to an 'OutputStream'. Does /not/ write an end-of-stream to
||| the stream.
export
writeList : List a -> OutputStream a -> IO ()
writeList xs os = forM_ (writeTo os . Just) xs

public export
Nel : Type -> Type
Nel a = Subset (List a) NonEmpty

reverseToNel : List a -> Maybe (Nel a)
reverseToNel xs = case reverse xs of
  Nil        => Nothing
  l@(_ :: _) => Just $ Element l IsNonEmpty

||| Splits an input stream into non-empty chunks of at most size `n`.
export
chunkList :  (n : Nat)
          -> {auto 0 prf : IsSucc n}
          -> InputStream a
          -> IO (InputStream $ Nel a)
chunkList n input = do
  ref <- newIORef False -- whether input is exhausted

  let go : (n : Nat) -> List a -> IO (Step Smaller n (List a) (Maybe $ Nel a))
      go 0     as = pure . Done $ reverseToNel as
      go (S k) as = do
        Just va <- read input
          | Nothing => writeIORef ref True $> Done (reverseToNel as)
        pure $ Cont k (reflexive {rel = LTE}) (va :: as)

  makeInputStream $ do
    False <- readIORef ref | True => pure Nothing
    trSized go n Nil
