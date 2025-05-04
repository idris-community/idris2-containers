||| Linear RRB Vector Internals
module Data.RRBVector1.Internal

import Data.Array.Core
import Data.Array.Indexed
import Data.Array.Mutable
import Data.Bits
import Data.List
import Data.Linear.Ref1
import Data.Linear.Token
import Data.Nat
import Data.String
import Derive.Prelude

%default total
%hide Data.Vect.Quantifiers.All.get
%language ElabReflection

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

public export
Shift : Type
Shift = Nat

||| The number of bits used per level.
export
blockshift : Shift
blockshift = 4

||| The maximum size of a block.
export
blocksize : Nat
blocksize = integerToNat $ 1 `shiftL` blockshift

||| The mask used to extract the index into the array.
export
blockmask : Nat
blockmask = minus blocksize 1

export
up :  Shift
   -> Shift
up sh = plus sh blockshift

export
down :  Shift
     -> Shift
down sh = minus sh blockshift

export
radixIndex :  Nat
           -> Shift
           -> Nat
radixIndex i sh = integerToNat ((natToInteger i) `shiftR` sh .&. (natToInteger blockmask))

export
relaxedRadixIndex :  {n : _}
                  -> MArray s n Nat
                  -> Nat
                  -> Shift
                  -> F1 s (Nat, Nat)
relaxedRadixIndex sizes i sh t =
  let guess      := radixIndex i sh
      idx    # t := loop sizes guess t
      subidx # t := toSubIdx sizes idx t
    in (idx, subidx) # t
  where
    toSubIdx :  (sizes : MArray s n Nat)
             -> (idx : Nat)
             -> F1 s Nat
    toSubIdx sizes Z   t = i # t
    toSubIdx sizes idx t =
      case idx == 0 of
        True  =>
          i # t
        False =>
          let idx' := tryNatToFin $ minus idx 1
            in case idx' of
                 Nothing    =>
                   (assert_total $ idris_crash "Data.RRBVector1.Internal.relaxedRadixIndex: index out of bounds") # t
                 Just idx'' =>
                   let idx''' # t := get sizes idx'' t
                     in minus i idx''' # t
    loop :  (sizes : MArray s n Nat)
         -> (idx : Nat)
         -> F1 s Nat
    loop size idx t =
      case tryNatToFin idx of
        Nothing   =>
          (assert_total $ idris_crash "Data.RRBVector1.Internal.relaxedRadixIndex.loop: index out of bounds") # t
        Just idx' =>
          let current # t := get sizes idx' t
            in case i < current of
                 True  =>
                   idx # t
                 False =>
                   (assert_total $ loop sizes (plus idx 1)) t

--------------------------------------------------------------------------------
--          Internal Tree Representation
--------------------------------------------------------------------------------

||| A linear internal tree representation.
public export
data Tree1 : (s : Type) -> (bsize : Nat) -> (usize : Nat) -> (lsize : Nat) -> Type -> Type where
  Balanced   : MArray s bsize (Tree1 s bsize usize lsize a) -> Tree1 s bsize usize lsize a
  Unbalanced : MArray s usize (Tree1 s bsize usize lsize a) -> MArray s usize Nat -> Tree1 s bsize usize lsize a
  Leaf       : MArray s lsize a -> Tree1 s bsize usize lsize a

--------------------------------------------------------------------------------
--          Tree Utilities
--------------------------------------------------------------------------------

export
singleton :  a
          -> F1 s (MArray s 1 a)
singleton x t =
  let arr # t := marray1 1 x t 
    in arr # t

export
treeToArray :  Tree1 s bsize usize lsize a
            -> Either (MArray s bsize (Tree1 s bsize usize lsize a))
                      (MArray s usize (Tree1 s bsize usize lsize a))
treeToArray (Balanced arr)     = Left arr
treeToArray (Unbalanced arr _) = Right arr
treeToArray (Leaf _)           = assert_total $ idris_crash "Data.RRBVector1.Internal.treeToArray: leaf"

export
treeBalanced :  Tree1 s bsize usize lsize a
             -> Bool
treeBalanced (Balanced _)     = True
treeBalanced (Unbalanced _ _) = False
treeBalanced (Leaf _)         = True

||| Computes the size of a tree with shift.
export
treeSize :  {bsize : _}
         -> {usize : _}
         -> {lsize : _}
         -> Shift
         -> Tree1 s bsize usize lsize a
         -> F1 s Nat
treeSize t =
  go 0 t
  where
    go :  {bsize : _}
       -> {usize : _}
       -> {lsize : _}
       -> Shift
       -> Shift
       -> Tree1 s bsize usize lsize a
       -> F1 s Nat
    go acc _ (Leaf arr)             t =
      plus acc lsize # t
    go acc _ (Unbalanced arr sizes) t =
      let i := tryNatToFin $ minus usize 1
        in case i of
             Nothing =>
               (assert_total $ idris_crash "Data.RRBVector1.Internal.treeSize: index out of bounds") # t
             Just i' =>
               let i'' # t := get sizes i' t
                 in plus acc i'' # t
    go acc sh (Balanced arr) t =
      let i  := minus bsize 1
          i' := tryNatToFin i
        in case i' of
             Nothing  =>
               (assert_total $ idris_crash "Data.RRBVector1.Internal.treeSize: index out of bounds") # t
             Just i'' =>
               let i''' # t := get arr i'' t
                 in go (plus acc (mult i (integerToNat (1 `shiftL` sh))))
                       (down sh)
                       (assert_smaller arr i''')
                       t

export
countTrailingZeros :  Nat
                   -> Nat
countTrailingZeros x =
  go 0
  where
    w : Nat
    w = bitSizeOf Int
    go : Nat -> Nat
    go i =
      case i >= w of
        True  =>
          i
        False =>
          case tryNatToFin i of
            Nothing =>
              assert_total $ idris_crash "Data.RRBVector1.Internal.countTrailingZeros: can't convert Nat to Fin"
            Just i' =>
              case testBit (the Int (cast x)) i' of
                True  =>
                  i
                False =>
                  assert_total $ go (plus i 1)

||| Nat log base 2.
export
log2 :  Nat
     -> Nat
log2 x =
  let bitSizeMinus1 = minus (bitSizeOf Int) 1
    in minus bitSizeMinus1 (countLeadingZeros x)
  where
    countLeadingZeros : Nat -> Nat
    countLeadingZeros x =
      minus (minus w 1) (go (minus w 1))
      where
        w : Nat
        w = bitSizeOf Int
        go : Nat -> Nat
        go i =
          case i < 0 of
            True  =>
              i
            False =>
              case tryNatToFin i of
                Nothing =>
                  assert_total $ idris_crash "Data.RRBVector1.Internal.log2: can't convert Nat to Fin"
                Just i' =>
                  case testBit (the Int (cast x)) i' of
                    True  =>
                      i
                    False =>
                      assert_total $ go (minus i 1)

--------------------------------------------------------------------------------
--          Linear RRB Vectors
--------------------------------------------------------------------------------

||| A linear relaxed radix balanced vector (RRB-Vector).
||| It supports fast indexing, iteration, concatenation and splitting.
public export
data RRBVector1 : (s : Type) -> (bsize : Nat) -> (usize : Nat) -> (lsize : Nat) -> Type -> Type where
  Root  :  Nat   -- size
        -> Shift -- shift (blockshift * height)
        -> (Tree1 s bsize usize lsize a)
        -> RRBVector1 s bsize usize lsize a
  Empty : RRBVector1 s bsize usize lsize a
