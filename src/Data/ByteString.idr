||| Immutable strings of raw bytes.
module Data.ByteString

import Data.Buffer
import Data.So
import System.File
import System.File.Support

%default total

--------------------------------------------------------------------------------
--          FFI
--------------------------------------------------------------------------------

||| Immutable wrapper around `Buffer`.
export
record Buf where
  constructor MkBuf
  buf : Buffer

%foreign "scheme:blodwen-buffer-getbyte"
         "RefC:getBufferByte"
         "node:lambda:(buf,offset)=>buf.readUInt8(offset)"
prim__getBits8 : Buffer -> (offset : Bits32) -> Bits8

%foreign "scheme:blodwen-new-buffer"
         "RefC:newBuffer"
         "node:lambda:s=>Buffer.alloc(s)"
prim__newBuffer : Bits32 -> PrimIO Buffer

%foreign "scheme:blodwen-buffer-setbyte"
         "RefC:setBufferByte"
         "node:lambda:(buf,offset,value)=>buf.writeUInt8(value, offset)"
prim__setBits8 : Buffer -> (offset : Bits32) -> (val : Bits8) -> PrimIO Int

%foreign support "idris2_readBufferData"
         "node:lambda:(f,b,l,m) => require('fs').readSync(f.fd,b,l,m)"
prim__readBufferData :  FilePtr
                     -> Buffer
                     -> (offset : Bits32)
                     -> (maxbytes : Bits32) -> PrimIO Int

--------------------------------------------------------------------------------
--          API
--------------------------------------------------------------------------------

public export
record ByteString where
  constructor MkBS
  buf    : Buf
  offset : Bits32
  length : Bits32

export
toList : ByteString -> List Bits8
toList (MkBS (MkBuf buf) o l) = go Nil l
  where go : List Bits8 -> Bits32 -> List Bits8
        go bs 0 = bs
        go bs n = 
          let ix = assert_smaller n (n-1)
           in go (prim__getBits8 buf (o + ix) :: bs) ix

export
empty : ByteString
empty = MkBS (MkBuf . unsafePerformIO . primIO $ prim__newBuffer 0) 0 0

export
fromList : List Bits8 -> ByteString
fromList ns = 
  let len = cast {to = Bits32} $ length ns
   in MkBS (MkBuf . unsafePerformIO $ go' len) 0 len
  where go : List Bits8 -> Bits32 -> Buffer -> PrimIO Buffer
        go []        _  buf w = MkIORes buf w
        go (b :: bs) ix buf w =
          case prim__setBits8 buf ix b w of
            -- this is a hack: Without this (completely useless) pattern
            -- match, the call to `prim__setBits8` is erased and ignored
            MkIORes 0 w2 => go bs (ix+1) buf w2
            MkIORes _ w2 => go bs (ix+1) buf w2

        go' : Bits32 -> IO Buffer
        go' l = do
          buf <- fromPrim $ prim__newBuffer l
          fromPrim $ go ns 0 buf

export
Show ByteString where
  showPrec p bs = showCon p "fromList" $ showArg (toList bs)

export
getBits8 : Bits32 -> ByteString -> Maybe Bits8
getBits8 x (MkBS (MkBuf bf) o l) =
  if x < l then Just $ prim__getBits8 bf (o + x) else Nothing

export
bits8 :  (ix : Bits32)
      -> (bs : ByteString)
      -> {auto 0 _ : So (ix < bs.length)}
      -> Bits8
bits8 x (MkBS (MkBuf bf) o l) = prim__getBits8 bf (o + x)

--------------------------------------------------------------------------------
--          Reading and Writing from and to Files
--------------------------------------------------------------------------------

export
readChunk : HasIO io => Bits32 -> File -> io (Either FileError ByteString)
readChunk max (FHandle h) = do
  Just buf <- newBuffer (cast max) | Nothing => pure (Left FileReadError)
  read     <- primIO (prim__readBufferData h buf 0 max)
  if read >= 0
     then pure (Right $ MkBS (MkBuf buf) 0 (cast read))
     else pure (Left FileReadError)

export
write : HasIO io => File -> ByteString -> io (Either FileError ())
write h (MkBS (MkBuf buf) o l) = writeBufferData h buf (cast o) (cast l)

--------------------------------------------------------------------------------
--          Utilities (Lots of stuff still missing)
--------------------------------------------------------------------------------

export
splitAt : Bits32 -> ByteString -> (ByteString,ByteString)
splitAt n (MkBS buf offset l) =
  if n >= l
     then (MkBS buf offset l, empty)
     else (MkBS buf offset n, MkBS buf (offset + n) (l - n))

export
break : Bits8 -> ByteString -> (ByteString,ByteString)
break b bs@(MkBS bf o l) = go 0
  where go : Bits32 -> (ByteString,ByteString)
        go n = if n < l
                  then if prim__getBits8 bf.buf (o + n) == b
                          then (MkBS bf o n, MkBS bf (o + n) (l - n))
                          else go (assert_smaller n (n+1))
                  else (bs,empty)
