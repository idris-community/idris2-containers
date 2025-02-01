||| Ordered Nat Priority Search Queue Internals
module Data.NatPSQ.Internal

import Data.Bits

%default total

--------------------------------------------------------------------------------
--          Internal Utility
--------------------------------------------------------------------------------

||| Convenience interface for bitSize that doesn't use an implicit parameter.
private
bitSizeOf : (ty : Type) -> FiniteBits ty => Nat
bitSizeOf ty = bitSize {a = ty}

--------------------------------------------------------------------------------
--          Internals
--------------------------------------------------------------------------------

||| Size is a natural machine word
||| (Bits32/Bits64 or the size of an unsigned Int on the host system).
public export
Size : Type
Size = case bitSizeOf Int of
         32 => Bits32
         _  => Bits64

||| The Nat type are keys for the queue (Ordered Nat Priority Search Queue).
public export
Key : Type
Key = Nat

||| We store Masks as the index of the bit that determines the branching.
public export
Mask : Type
Mask = Nat

--------------------------------------------------------------------------------
--          Bit Manipulation
--------------------------------------------------------------------------------

private
natFromBits : Key -> Size
natFromBits = cast

private
bitsFromNat : Size -> Key
bitsFromNat = cast 

export
zero : Key -> Mask -> Bool
zero i m = (natFromBits i) .&. (natFromBits m) == 0

private
maskW : Size -> Size
maskW m = complement (m-1) `xor` m

export
noMatch : Key -> Key -> Mask -> Bool
noMatch k1 k2 m = natFromBits k1 .&. m' /= natFromBits k2 .&. m'
  where
    m' = maskW (natFromBits m)

private
highestBitMask : Size -> Size
highestBitMask x1 = 
  let x2 = x1 .|. x1 `shiftR` 1
      x3 = x2 .|. x2 `shiftR` 2
      x4 = x3 .|. x3 `shiftR` 4
      x5 = x4 .|. x4 `shiftR` 8
      x6 = x5 .|. x5 `shiftR` 16
      x7 = case bitSizeOf Int of
             32 =>
               x6
             _  =>
               x6 .|. x6 `shiftR` 32
    in x7 `xor` (x7 `shiftR` 1)

export
branchMask : Key -> Key -> Mask
branchMask k1 k2 = bitsFromNat (highestBitMask (natFromBits k1 `xor` natFromBits k2))

--------------------------------------------------------------------------------
--          NatPSQ
--------------------------------------------------------------------------------

||| A priority search queue with Nat keys
||| and priorities of type p and values of type v.
||| Many operations have a worst-case complexity of O(min(n,W)).
||| This means that the operation can become linear in the number of elements with a maximum of W
||| (the number of bits in an Int (32 or 64)).
||| It is generally much faster than an OrdPSQ.
public export
data NatPSQ p v = Bin Key
                      p
                      v
                      Mask
                      (NatPSQ p v)
                      (NatPSQ p v)
                | Tip Key
                      p
                      v
                | Nil

Show p => Show v => Show (NatPSQ p v) where
  show xs = show' xs  where
    show' : NatPSQ p v -> String
    show' Nil               = "Nil"
    show' (Bin k p v m l r) = "Bin "   ++
                              "("      ++
                              (show k) ++
                              " "      ++
                              (show p) ++
                              " "      ++
                              (show v) ++
                              " "      ++
                              (show m) ++
                              " "      ++
                              (show l) ++
                              " "      ++
                              (show r) ++
                              ")"
    show' (Tip k p v)       = "Tip "   ++
                              (show k) ++
                              " "      ++
                              (show p) ++
                              " "      ++
                              (show v) ++
                              ")"
