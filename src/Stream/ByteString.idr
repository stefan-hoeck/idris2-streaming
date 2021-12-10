module Stream.ByteString

import Data.ByteString
import Stream.Internal
import Stream.Util

export
break :  (Bits8 -> Bool)
      -> Stream (Of ByteString) m r
      -> Stream (Of ByteString) m (Stream (Of ByteString) m r)
break p = go empty
  where go :  ByteString
           -> Stream (Of ByteString) m r
           -> Stream (Of ByteString) m (Stream (Of ByteString) m r)
        go pre str = case toView str of
          BindF (MkOf bs) f =>
            let (x,y) = break p $ pre <+> bs
             in if null y
                   then pure () >>= \_ => go x (f bs)
                   else yield x $> (yield y >>= \_ => f bs)

          BindP x         f => pure x >>= \v => go pre (f v)
          BindM x         f => lift x >>= \v => go pre (f v)
          VF (MkOf bs)      =>
            let (x,y) = break p $ pre <+> bs
             in yield x $> (yield y >>= \_ => f bs)
          VP x              => pure (pure x)
          VM x              => pure (lift x)

