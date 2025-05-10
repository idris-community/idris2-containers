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
relaxedRadixIndex :  Array Nat
                  -> Nat
                  -> Shift
                  -> (Nat, Nat)
relaxedRadixIndex sizes i sh =
  let guess  = radixIndex i sh -- guess <= idx
      idx    = loop sizes guess
      subIdx = case idx == 0 of
                 True  =>
                   i
                 False =>
                   let idx' = case tryNatToFin $ minus idx 1 of
                                Nothing    =>
                                  assert_total $ idris_crash "Data.RRBVector1.Internal.relaxedRadixIndex: index out of bounds"
                                Just idx'' =>
                                  idx''
                     in minus i (at sizes.arr idx')
    in (idx, subIdx)
  where
    loop : Array Nat -> Nat -> Nat
    loop sizes idx =
      let current = case tryNatToFin idx of
                      Nothing       =>
                        assert_total $ idris_crash "Data.RRBVector1.Internal.relaxedRadixIndex.loop: index out of bounds"
                      Just idx' =>
                        at sizes.arr idx' -- idx will always be in range for a well-formed tree
        in case i < current of
             True  =>
               idx
             False =>
               assert_total $ loop sizes (plus idx 1)

export
relaxedRadixIndex1 :  {n : _}
                   -> MArray s n Nat
                   -> Nat
                   -> Shift
                   -> F1 s (Nat, Nat)
relaxedRadixIndex1 sizes i sh t =
  let guess      := radixIndex i sh
      idx    # t := loop1 sizes guess t
      subidx # t := toSubIdx1 sizes idx t
    in (idx, subidx) # t
  where
    toSubIdx1 :  (sizes : MArray s n Nat)
              -> (idx : Nat)
              -> F1 s Nat
    toSubIdx1 sizes Z   t = i # t
    toSubIdx1 sizes idx t =
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
    loop1 :  (sizes : MArray s n Nat)
          -> (idx : Nat)
          -> F1 s Nat
    loop1 size idx t =
      case tryNatToFin idx of
        Nothing   =>
          (assert_total $ idris_crash "Data.RRBVector1.Internal.relaxedRadixIndex.loop: index out of bounds") # t
        Just idx' =>
          let current # t := get sizes idx' t
            in case i < current of
                 True  =>
                   idx # t
                 False =>
                   (assert_total $ loop1 sizes (plus idx 1)) t

--------------------------------------------------------------------------------
--          Internal Tree Representation
--------------------------------------------------------------------------------

||| A linear internal tree representation.
public export
data Tree1 : (s : Type) -> Type -> Type where
  Balanced   : (b : Nat) -> (b ** MArray s b (Tree1 s a)) -> Tree1 s a
  Unbalanced : (u : Nat) -> (u ** MArray s u (Tree1 s a)) -> MArray s u Nat -> Tree1 s a
  Leaf       : (l : Nat) -> (l ** MArray s l a) -> Tree1 s a

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
treeToArray :  Tree1 s a
            -> Either (b ** MArray s b (Tree1 s a))
                      (u ** MArray s u (Tree1 s a))
treeToArray (Balanced   _ arr)   = Left arr
treeToArray (Unbalanced _ arr _) = Right arr
treeToArray (Leaf       _ _)     = assert_total $ idris_crash "Data.RRBVector1.Internal.treeToArray: leaf"

export
treeBalanced :  Tree1 s a
             -> Bool
treeBalanced (Balanced   _ _)   = True
treeBalanced (Unbalanced _ _ _) = False
treeBalanced (Leaf       _ _ )  = True

||| Computes the size of a tree with shift.
export
treeSize :  Shift
         -> Tree1 s a
         -> F1 s Nat
treeSize t =
  go 0 t
  where
    go :  Shift
       -> Shift
       -> Tree1 s a
       -> F1 s Nat
    go acc _ (Leaf       l (_ ** arr))       t =
      plus acc l # t
    go acc _ (Unbalanced u (_ ** arr) sizes) t =
      let i := tryNatToFin $ minus u 1
        in case i of
             Nothing =>
               (assert_total $ idris_crash "Data.RRBVector1.Internal.treeSize: index out of bounds") # t
             Just i' =>
               let i'' # t := get sizes i' t
                 in plus acc i'' # t
    go acc sh (Balanced  b (_ ** arr))       t =
      let i  := minus b 1
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

||| Turns an array into a tree node by computing the sizes of its subtrees.
||| sh is the shift of the resulting tree.
export
computeSizes :  {n : Nat}
             -> Shift
             -> MArray s n (Tree1 s a)
             -> F1 s (Tree1 s a)
computeSizes sh arr t =
  let isbalanced # t := isBalanced arr t
    in case isbalanced of
         True  =>
           (Balanced n (n ** arr)) # t
         False =>
           let arrnat  # t := unsafeMArray1 n t
               arr'    # t := freeze arr t
               arrnat' # t := loop sh 0 0 n (toList arr') arrnat t
             in (Unbalanced n (n ** arr) arrnat') # t
  where
    loop :  (sh, cur, acc, n : Nat)
         -> List (Tree1 s a)
         -> MArray s n Nat
         -> F1 s (MArray s n Nat)
    loop sh _   acc n []        arr t =
      arr # t
    loop sh cur acc n (x :: xs) arr t =
      case tryNatToFin cur of
        Nothing   =>
          (assert_total $ idris_crash "Data.RRBVector.Internal.computeSizes.go: can't convert Nat to Fin") # t
        Just cur' =>
          let treesize # t := treeSize (down sh) x t
              acc'         := plus acc treesize
              ()       # t := set arr cur' acc' t
            in assert_total $ loop sh (S cur) acc' n xs arr t
    maxsize : Integer
    maxsize = 1 `shiftL` sh -- the maximum size of a subtree
    lenM1 : Nat
    lenM1 = minus n 1
    isBalanced :  {n : Nat}
               -> MArray s n (Tree1 s a)
               -> F1 s Bool
    isBalanced arr t =
      let bool' # t := go arr 0 t
        in bool' # t
      where
        go :  {n : Nat}
           -> MArray s n (Tree1 s a)
           -> Nat
           -> F1 s Bool
        go arr i t =
          case tryNatToFin i of
            Nothing =>
              (assert_total $ idris_crash "Data.RRBVector.Internal.computeSizes.isBalanced: can't convert Nat to Fin") # t
            Just i' =>
              let subtree # t := get arr i' t
                in case i < lenM1 of
                     True  =>
                       let go'      # t := assert_total $ go arr (plus i 1) t
                           treesize # t := treeSize (down sh) subtree t
                         in case go' of
                              False =>
                                treeBalanced subtree # t
                              True  =>
                                (assert_total $ natToInteger treesize == maxsize && go') # t
                     False =>
                       treeBalanced subtree # t

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
data RRBVector1 : (s : Type) -> Type -> Type where
  Root :  Nat   -- size
       -> Shift -- shift (blockshift * height)
       -> Tree1 s a
       -> RRBVector1 s a
  Empty : RRBVector1 s a
