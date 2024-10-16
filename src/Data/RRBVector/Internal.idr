||| RRB Vector Internals
module Data.RRBVector.Internal

import Data.Array.Core
import Data.Array.Index
import Data.Array.Indexed
import Data.Bits
import Data.List
import Data.Nat
import Data.Nat.Exponentiation
import Data.String
import Data.Vect
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Internal Utility
--------------------------------------------------------------------------------

||| Convenience interface for bitSize that doesn't use an implicit parameter.
private
bitSizeOf : (ty : Type) -> FiniteBits ty => Nat
bitSizeOf ty = bitSize {a = ty}

||| Custom shiftL function on Nat.
private
shiftL : Nat -> Nat -> Nat
shiftL n k = n * (pow 2 k)

||| Custom shiftR function on Nat.
private
shiftR : Nat -> Nat -> Nat
shiftR n k = n `div` pow 2 k

--------------------------------------------------------------------------------
--          Internals
--------------------------------------------------------------------------------

public export
Shift : Type
Shift = Nat

||| The number of bits used per level.
public export
blockshift : Shift
blockshift = 4

||| The maximum size of a block.
public export
blocksize : Nat
blocksize = shiftL 1 blockshift

||| The mask used to extract the index into the array.
blockmask : Nat
blockmask = minus blocksize 1

up : Shift -> Shift
up sh = plus sh blockshift

down : Shift -> Shift
down sh = minus sh blockshift

radixIndex : Nat -> Shift -> Nat
radixIndex i sh = 
  the Nat (cast ((the Int (cast $ shiftR i sh)) .&. (the Int (cast blockmask))))

partial
relaxedRadixIndex : Array Nat -> Nat -> Shift -> (Nat, Nat)
relaxedRadixIndex sizes i sh =
  let guess  = radixIndex i sh -- guess <= idx
      idx    = loop sizes guess
      subIdx = case idx == 0 of
                 True  =>
                   i
                 False =>
                   let idx' = case tryNatToFin $ minus idx 1 of
                                Nothing    =>
                                  assert_total $ idris_crash "Data.RRBVector.Internal.relaxedRadixIndex: index out of bounds"
                                Just idx'' =>
                                  idx''
                     in minus i (at sizes.arr idx')
    in (idx, subIdx)
  where
    loop : Array Nat -> Nat -> Nat
    loop sizes idx =
      let current = case tryNatToFin idx of
                      Nothing       =>
                        assert_total $ idris_crash "Data.RRBVector.Internal.relaxedRadixIndex.loop: index out of bounds"
                      Just idx' =>
                        at sizes.arr idx' -- idx will always be in range for a well-formed tree
        in case i < current of
             True  =>
               idx
             False =>
               loop sizes (plus idx 1)

--------------------------------------------------------------------------------
--          Internal Tree Representation
--------------------------------------------------------------------------------

||| An internal tree representation.
private
data Tree a = Balanced (Array (Tree a))
            | Unbalanced (Array (Tree a)) (Array Nat)
            | Leaf (Array a)

{-
Eq a => Eq (Tree a) where
  (Balanced x)      == (Balanced y)      = assert_total $ heq x.arr y.arr
  (Unbalanced x x') == (Unbalanced y y') = assert_total $ heq x.arr y.arr && heq x'.arr y'.arr
  (Leaf x)          == (Leaf y)          = heq x.arr y.arr
  _                 == _                 = False

||| Unbalanced < Balanced < Leaf
Ord a => Ord (Tree a) where
  compare (Balanced x)     (Balanced y)     = assert_total $ hcomp x.arr y.arr
  compare (Balanced _)     (Unbalanced _ _) = GT
  compare (Balanced _)     (Leaf _)         = LT
  compare (Unbalanced x _) (Unbalanced y _) = assert_total $ hcomp x.arr y.arr
  compare (Unbalanced _ _) (Balanced _)     = LT
  compare (Unbalanced _ _) (Leaf _)         = LT
  compare (Leaf x)         (Leaf y)         = hcomp x.arr y.arr
  compare (Leaf _)         (Balanced _)     = GT
  compare (Leaf _)         (Unbalanced _ _) = GT
-}

Show a => Show (Tree a) where
  show xs = show' xs where
    show' : Tree a -> String
    show' (Balanced x)     = assert_total $ show $ toVect x.arr
    show' (Unbalanced x _) = assert_total $ show $ toVect x.arr
    show' (Leaf x)         = show $ toVect x.arr

--------------------------------------------------------------------------------
--          Tree Utilities
--------------------------------------------------------------------------------

treeToArray : Tree a -> Array (Tree a)
treeToArray (Balanced arr)     = arr
treeToArray (Unbalanced arr _) = arr
treeToArray (Leaf _)           = assert_total $ idris_crash "Data.RRBVector.Internal.treeToArray: leaf"

treeBalanced : Tree a -> Bool
treeBalanced (Balanced _)     = True
treeBalanced (Unbalanced _ _) = False
treeBalanced (Leaf _)         = True

||| Computes the size of a tree with shift.
partial
treeSize : Shift -> Tree a -> Nat
treeSize = go 0
  where
    go : Shift -> Shift -> Tree a -> Nat
    go acc _  (Leaf arr)             = plus acc arr.size
    go acc _  (Unbalanced arr sizes) =
      let i = case tryNatToFin $ minus arr.size 1 of
                Nothing =>
                  assert_total $ idris_crash "Data.RRBVector.Internal.treeSize: index out of bounds"
                Just i' =>
                 i'
        in plus acc (at sizes.arr i)
    go acc sh (Balanced arr)         =
      let i  = minus arr.size 1
          i' = case tryNatToFin i of
                 Nothing  =>
                   assert_total $ idris_crash "Data.RRBVector.Internal.treeSize: index out of bounds"
                 Just i'' =>
                   i''
        in go (plus acc (mult i (shiftL 1 sh)))
              (down sh)
              (at arr.arr i')

||| Turns an array into a tree node by computing the sizes of its subtrees.
||| sh is the shift of the resulting tree.
partial
computeSizes : Shift -> Array (Tree a) -> Tree a
computeSizes sh arr =
  case isBalanced of
    True  =>
      Balanced arr
    False =>
      let arrnat = loop sh arr (fill arr.size 0) 0 0
        in Unbalanced arr (A arr.size arrnat)
  where
    loop : {n : Nat} -> Shift -> Array (Tree a) -> IArray n Nat -> Nat -> Nat -> IArray n Nat
    loop sh arr arrnat acc i =
      case i < arr.size of
        True  =>
          let size = case tryNatToFin i of
                       Nothing =>
                         assert_total $ idris_crash "Data.RRBVector.Internal.computeSizes.loop: can't convert Nat to Fin"
                       Just i' =>
                         treeSize (down sh) (at arr.arr i')
              acc' = plus acc size
            in case tryNatToFin i of
                 Nothing =>
                   assert_total $ idris_crash "Data.RRBVector.Internal.computeSizes.loop: can't convert Nat to Fin"
                 Just i' =>
                   loop sh arr (setAt i' acc' arrnat) acc' (plus i 1)
        False =>
          arrnat
    maxsize : Nat
    maxsize = shiftL 1 sh -- the maximum size of a subtree
    len : Nat
    len = arr.size
    lenM1 : Nat
    lenM1 = minus len 1 
    isBalanced : Bool
    isBalanced = go 0
      where
        go : Nat -> Bool
        go i =
          let subtree = case tryNatToFin i of
                          Nothing =>
                            assert_total $ idris_crash "Data.RRBVector.Internal.computeSizes.isBalanced: can't convert Nat to Fin"
                          Just i' =>
                            at arr.arr i'
            in case i < lenM1 of
                 True  =>
                   treeSize (down sh) subtree == maxsize && go (plus i 1)
                 False =>
                   treeBalanced subtree

||| Nat log base 2.
partial
export
log2 : Nat -> Nat
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
                  assert_total $ idris_crash "Data.RRBVector.Internal.log2: can't convert Nat to Fin"
                Just i' =>
                  case testBit (the Int (cast x)) i' of
                    True  =>
                      i
                    False =>
                      go (minus i 1)

--------------------------------------------------------------------------------
--          RRB Vectors
--------------------------------------------------------------------------------

||| A relaxed radix balanced vector (RRB-Vector).
||| It supports fast indexing, iteration, concatenation and splitting.
public export
data RRBVector a = Root Nat Shift (Tree a)
                 | Empty

{-
export
Eq a => Eq (Tree a) => Eq (RRBVector a) where
  (Root n s t) == (Root n' s' t') = n == n' && s == s' && t == t'
  Empty        == Empty           = True
  _            == _               = False
-}

export
Show a => Show (Tree a) => Show (RRBVector a) where
  show xs = show' xs where
    show' : RRBVector a -> String
    show' Empty        = ""
    show' (Root _ _ t) = show t
