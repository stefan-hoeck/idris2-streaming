||| Immutable strings of raw bytes.
module Data.ByteString

import Data.Buffer
import Data.So

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

-- 
-- -- Get the length of a string in bytes, rather than characters
-- export
-- %foreign "scheme:blodwen-stringbytelen"
--          "C:strlen, libc 6"
-- stringByteLength : String -> Int
-- 
-- %foreign "scheme:blodwen-buffer-setstring"
--          "RefC:setBufferString"
--          "node:lambda:(buf,offset,value)=>buf.write(value, offset,buf.length - offset, 'utf-8')"
-- prim__setString : Buffer -> (offset : Int) -> (val : String) -> PrimIO ()
-- 
-- export %inline
-- setString : HasIO io => Buffer -> (offset : Int) -> (val : String) -> io ()
-- setString buf offset val
--     = primIO (prim__setString buf offset val)
-- 
-- %foreign "scheme:blodwen-buffer-getstring"
--          "RefC:getBufferString"
--          "node:lambda:(buf,offset,len)=>buf.slice(offset, offset+len).toString('utf-8')"
-- prim__getString : Buffer -> (offset : Int) -> (len : Int) -> PrimIO String
-- 
-- export %inline
-- getString : HasIO io => Buffer -> (offset : Int) -> (len : Int) -> io String
-- getString buf offset len
--     = primIO (prim__getString buf offset len)
-- 
-- 
-- %foreign "scheme:blodwen-buffer-copydata"
--          "RefC:copyBuffer"
--          "node:lambda:(b1,o1,length,b2,o2)=>b1.copy(b2,o2,o1,o1+length)"
-- prim__copyData : (src : Buffer) -> (srcOffset, len : Int) ->
--                  (dst : Buffer) -> (dstOffset : Int) -> PrimIO ()
-- 
-- export
-- copyData : HasIO io => Buffer -> (srcOffset, len : Int) ->
--            (dst : Buffer) -> (dstOffset : Int) -> io ()
-- copyData src start len dest offset
--     = primIO (prim__copyData src start len dest offset)
-- 
-- export
-- resizeBuffer : HasIO io => Buffer -> Int -> io (Maybe Buffer)
-- resizeBuffer old newsize
--     = do Just buf <- newBuffer newsize
--               | Nothing => pure Nothing
--          -- If the new buffer is smaller than the old one, just copy what
--          -- fits
--          oldsize <- rawSize old
--          let len = if newsize < oldsize then newsize else oldsize
--          copyData old 0 len buf 0
--          pure (Just buf)
-- 
-- ||| Create a buffer containing the concatenated content from a
-- ||| list of buffers.
-- export
-- concatBuffers : HasIO io => List Buffer -> io (Maybe Buffer)
-- concatBuffers xs
--     = do let sizes = map prim__bufferSize xs
--          let (totalSize, revCumulative) = foldl scanSize (0,[]) sizes
--          let cumulative = reverse revCumulative
--          Just buf <- newBuffer totalSize
--               | Nothing => pure Nothing
--          traverse_ (\(b, size, watermark) => copyData b 0 size buf watermark) (zip3 xs sizes cumulative)
--          pure (Just buf)
--     where
--         scanSize : (Int, List Int) -> Int -> (Int, List Int)
--         scanSize (s, cs) x  = (s+x, s::cs)
-- 
-- ||| Split a buffer into two at a position.
-- export
-- splitBuffer : HasIO io => Buffer -> Int -> io (Maybe (Buffer, Buffer))
-- splitBuffer buf pos = do size <- rawSize buf
--                          if pos > 0 && pos < size
--                              then do Just first <- newBuffer pos
--                                         | Nothing => pure Nothing
--                                      Just second <- newBuffer (size - pos)
--                                         | Nothing => pure Nothing
--                                      copyData buf 0 pos first 0
--                                      copyData buf pos (size-pos) second 0
--                                      pure $ Just (first, second)
--                              else pure Nothing
