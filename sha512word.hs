module SHA512Word where

import qualified Data.ByteString.Lazy as B
import qualified Data.Digest.Pure.SHA as SHA
import Data.Bits ((.|.), shiftL, testBit)
import Data.Word (Word8)

b2i :: Integral a => Bool -> a
b2i b = case b of { True -> 1 ; False -> 0 }

leBitsToBytes :: [Bool] -> [Word8]
leBitsToBytes [] = []
leBitsToBytes (a:b:c:d:e:f:g:h:bs) = (b2i a .|. (b2i b `shiftL` 1) .|. (b2i c `shiftL` 2) .|. (b2i d `shiftL` 3) .|. (b2i e `shiftL` 4) .|. (b2i f `shiftL` 5) .|. (b2i g `shiftL` 6) .|. (b2i h `shiftL` 7)) : leBitsToBytes bs
leBitsToBytes bs = error $ "byte must have exactly 8 bits, got " ++ show bs


bytesToLEBits :: [Word8] -> [Bool]
bytesToLEBits [] = []
bytesToLEBits (x:xs) = (x `testBit` 0) : (x `testBit` 1) : (x `testBit` 2) : (x `testBit` 3) : (x `testBit` 4) : (x `testBit` 5) : (x `testBit` 6) : (x `testBit` 7) : bytesToLEBits xs

h :: [Bool] -> [Bool]
h = bytesToLEBits . B.unpack . SHA.bytestringDigest . SHA.sha512 . B.pack . leBitsToBytes
