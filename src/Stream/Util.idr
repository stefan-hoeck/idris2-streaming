||| `Source` and `Sink` utilities and combinators
module Stream.Util

import Control.MonadRec
import Data.ByteString
import Data.Colist
import Stream.Driver
import Stream.Result
import Stream.Source

--------------------------------------------------------------------------------
--          Pure Sources
--------------------------------------------------------------------------------

export
fromList : List a -> Source err a ()
fromList xs = ST xs $ \case (h :: t) => Value (t,h)
                            Nil      => Done ()

export
fromStream : Stream a -> Source err a res
fromStream xs = ST xs $ \(h :: t) => Value (t,h)

export
fromColist : Colist a -> Source err a ()
fromColist xs = ST xs $ \case (h :: t) => Value (t,h)
                              Nil      => Done ()

||| Emits the given value `n` times.
export
replicate : (n : Nat) -> a -> Source err a ()
replicate n va = ST n $ \case S k => Value (k,va)
                              0   => Done ()

||| Emits the given value eternally
export
repeat : a -> Source err a res
repeat = ST () . const . Value . ((),)

||| Generates the sequence (ini, f ini, f $ f ini, ...)
export
iterate : (fun : a -> a) -> (ini : a) -> Source err a res
iterate f ini = ST ini $ \va => Value (f va, va)

export
unfold : (s -> (s,a)) -> s -> Source err a res
unfold f ini = ST ini (Value . f)

--------------------------------------------------------------------------------
--          Source Transformers
--------------------------------------------------------------------------------

||| Stateful `Source` transformer. This is used to accumulate a
||| (finite!) number of values emitted by a `Source` on each evaluation step,
||| limit the number of values a source produces, or interleave the
||| values emitted by two different source.
|||
||| This function is *very* general and can be used to implement
||| all kinds of source transformers. If you don't want to accumulate
||| or drop values, consider using `transformRes` instead.
export
transformST :  (fun :  (state, Source e v r)
                    -> IO (Result e2 ((state,Source e v r), v2) r2))
            -> (ini :  state)
            -> (src :  Source e v r)
            -> Source e2 v2 r2
transformST fun ini src = STIO (ini,src) fun (release . snd)

||| Stateless `Source` transformer.
export
transform :  (fun :  Source e v r -> IO (Result e2 (Source e v r, v2) r2))
          -> (src :  Source e v r)
          -> Source e2 v2 r2
transform fun = transformST go () 
  where go : ((), Source e v r) -> IO (Result e2 (((),Source e v r), v2) r2)
        go (_,src) = do
          Value (src2,vv2) <- fun src
            | Done  res => pure (Done res)
            | Error err => pure (Error err)
          pure $ Value (((),src2),vv2)

export
transformRes :  (onVal : state -> v -> IO (Result e2 (state, v2) r2))
             -> (onErr : state -> e -> IO e2)
             -> (onRes : state -> r -> IO r2)
             -> (ini :  state)
             -> (src :  Source e v r)
             -> Source e2 v2 r2
transformRes onVal onErr onRes = transformST $ \(st,src) => do
  Value (vv, src2) <- step src
    | Done  res => Done  <$> onRes st res
    | Error err => Error <$> onErr st err

  Value (st2,vv2) <- onVal st vv
    | Done res  => release src2 $> Done res
    | Error err => release src2 $> Error err
  pure $ Value ((st2, src2),vv2)

||| Emit the first `n` values from the given `Source`.
export
take : (n : Nat) -> Source err val res -> Source err val ()
take = transformRes go (\_,e => pure e) (\_,_ => pure ())
  where go : Nat -> val -> IO (Result err (Nat,val) ())
        go (S k) x = pure $ Value (k,x)
        go 0     _ = pure $ Done ()

||| Emit values until `p` returns `False`.
export
takeWhile : (p : val -> Bool) -> Source err val res -> Source err val ()
takeWhile p = transformRes go (\_,e => pure e) (\_,_ => pure ()) ()
  where go : () -> val -> IO (Result err ((),val) ())
        go _ x = pure $ if p x then Value ((),x) else Done ()

||| Group emitted values in chunks of size `n`.
||| The final list might be shorter than `n` elements.
export
chunks : Nat -> Source err val res -> Source err (List val) res
chunks n = transform go
  where stp :  (n : Nat)
            -> (Source err val res, List val)
            -> IO $ Step Smaller n
                      (Source err val res, List val)
                      (Result err (Source err val res, List val) res)
        stp 0     (src,vs) = pure . Done $ Value (src, reverse vs)
        stp (S k) (src,vs) = do
          Value (v,src2) <- step src
            | Error err => pure . Done $ Error err
            | Done  res => case vs of
                Nil => pure . Done $ Done res
                _   => pure . Done $ Value (Pure res, reverse vs)
          pure $ Cont k (reflexive {rel = LTE}) (src2, v::vs)

        go :  Source err val res
           -> IO (Result err (Source err val res, List val) res)
        go src = trSized stp n (src,Nil)

export
lines :  (maxNrOfChunks  : Nat)
      -> (chunksExceeded : err)
      -> Source err ByteString res
      -> Source err ByteString res
lines n ce = transformST go empty
  where stp :  (n : Nat)
            -> (Source err val res, List ByteString)
            -> IO $ Step Smaller n
                      (Source err val res, List ByteString)
                      (Result err ((ByteString,Source err val res), ByteString) res)

        go :  (ByteString, Source err val res)
           -> IO (Result err ((ByteString,Source err val res), ByteString) res)
        go (bs,src) = trSized stp n (src,[bs])
