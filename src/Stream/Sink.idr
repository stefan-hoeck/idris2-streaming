module Stream.Sink

public export
record Sink (a : Type) where
  constructor MkSink
  sink : a -> IO ()

export
filter : (a -> Bool) -> Sink a -> Sink a
filter f (MkSink sink) = MkSink $ \va => when (f va) (sink va)
