module Data.ByteString.Internal

import Data.Buffer

%default total

--------------------------------------------------------------------------------
--          FFI
--------------------------------------------------------------------------------

%foreign "scheme:blodwen-buffer-getbyte"
         "RefC:getBufferByte"
         "node:lambda:(buf,offset)=>buf.readUInt8(offset)"
prim__getBits8 : Buffer -> (offset : Bits32) -> Bits8

%foreign "scheme:blodwen-new-buffer"
         "RefC:newBuffer"
         "node:lambda:s=>Buffer.alloc(s)"
prim__newBuffer : Bits32 -> Buffer

%foreign "scheme:blodwen-buffer-size"
         "RefC:getBufferSize"
         "node:lambda:b => b.length"
prim__bufferSize : Buffer -> Bits32

%foreign "scheme:blodwen-buffer-setbyte"
         "RefC:setBufferByte"
         "node:lambda:(buf,offset,value)=>buf.writeUInt8(value, offset)"
prim__setBits8 : Buffer -> (offset : Bits32) -> (val : Bits8) -> PrimIO Int

--------------------------------------------------------------------------------
--          ByteString
--------------------------------------------------------------------------------

||| Internally represented by a `Data.Buffer` together
||| with its length and offset.
|||
||| The internal buffer is treated as being immutable,
||| so operations modifying a `ByteString` will create
||| and write to a new `Buffer`.
export
record ByteString where
  constructor BS
  buf    : Buffer
  offset : Bits32
  len    : Bits32

--------------------------------------------------------------------------------
--          Unsafe Operations
--------------------------------------------------------------------------------

||| Wraps a `Buffer` in a `ByteString` *without making a copy*.
||| Use this for efficient reading of data from a file or other resource
||| into a `ByteString`, but make sure to not reuse the
||| `Buffer` in question elsewhere.
export %inline
unsafeFromBuffer : Buffer -> ByteString
unsafeFromBuffer b = BS b 0 $ prim__bufferSize b

||| Reads the value of a `ByteString` at the given position
||| *without checking the bounds*.
export %inline
unsafeGetBits8 : Bits32 -> ByteString -> Bits8
unsafeGetBits8 n (BS buf o _) = prim__getBits8 buf (o + n)

--------------------------------------------------------------------------------
--          Making ByteStrings
--------------------------------------------------------------------------------

export
empty : ByteString
empty = BS (prim__newBuffer 0) 0 0

||| Converts a list of values to a `ByteString` using
||| the given conversion function.
export
fromList : (a -> Bits8) -> List a -> ByteString
fromList f vs = 
  let len = cast {to = Bits32} $ length vs
   in BS (unsafePerformIO $ go' len) 0 len
  where go : List a -> Bits32 -> Buffer -> PrimIO Buffer
        go []        _  buf w = MkIORes buf w
        go (b :: bs) ix buf w =
          case prim__setBits8 buf ix (f b) w of
            -- this is a hack: Without this (completely useless) pattern
            -- match, the call to `prim__setBits8` is erased and ignored
            MkIORes 0 w2 => go bs (ix+1) buf w2
            MkIORes _ w2 => go bs (ix+1) buf w2

        go' : Bits32 -> IO Buffer
        go' l = fromPrim $ go vs 0 (prim__newBuffer l)

||| Converts a list of `Bits8` values to a `ByteString`.
export %inline
pack : List Bits8 -> ByteString
pack = fromList id

||| Creates a `ByteString` holding a single `Bits8` value.
export %inline
singleton : Bits8 -> ByteString
singleton = pack . (::[])

||| Converts a `String` to a `ByteString`.
|||
||| Note: All characters are truncated to 8 bits in the
||| process, so this will mangle UTF-8 encoded strings.
export %inline
FromString ByteString where
  fromString = fromList cast . fastUnpack

||| Converts a `ByteString` to a list of values using
||| the given conversion function.
export
toList : (Bits8 -> a) -> ByteString -> List a
toList f bs = go Nil bs.len
  where go : List a -> Bits32 -> List a
        go as 0 = as
        go as n = 
          let ix = assert_smaller n (n-1)
           in go (f (unsafeGetBits8 ix bs) :: as) ix

||| Converts a `ByteString` to a list of `Bits8` values.
export %inline
unpack : ByteString -> List Bits8
unpack = toList id

||| Converts a `ByteString` to a String. All characters
||| will be in the range [0,255], so this does not perform
||| any character decoding.
export %inline
Show ByteString where
  show = show . fastPack . toList cast

--------------------------------------------------------------------------------
--          Comparing ByteStrings
--------------------------------------------------------------------------------

comp : ByteString -> ByteString -> Ordering
comp (BS _ _ 0) (BS _ _ 0)      = EQ  -- short cut for empty strings
comp bs1      bs2 = go 0 (min bs1.len bs2.len)
  where go : (pos, maxPos : Bits32) -> Ordering
        go pos maxPos =
          if pos == maxPos then compare bs1.len bs2.len
          else case compare (unsafeGetBits8 pos bs1) (unsafeGetBits8 pos bs2) of
                 EQ => go (assert_smaller pos $ pos + 1) maxPos         
                 o  => o

export %inline
Eq ByteString where
  a == b = case comp a b of
             EQ => True
             _  => False

export %inline
Ord ByteString where
  compare = comp

--------------------------------------------------------------------------------
--          Core Functionality
--------------------------------------------------------------------------------

||| Length (number of `Bits8`) of the `ByteString`. O(1).
export %inline
length : ByteString -> Bits32
length = len

||| `True` if the given `ByteString` has zero length.
export %inline
null : ByteString -> Bool
null = (== 0) . length

export
append : ByteString -> ByteString -> ByteString
append (BS _  _  0)  bs2           = bs2
append bs1           (BS _  _  0)  = bs1
append (BS b1 o1 l1) (BS b2 o2 l2) =
  let buf = prim__newBuffer (l1 + l2)
   in ?implMissing

