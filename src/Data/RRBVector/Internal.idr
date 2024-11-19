||| RRB Vector Internals
module Data.RRBVector.Internal

import Data.Array
import Data.Array.Core
import Data.Array.Index
import Data.Array.Indexed
import Data.Bits
import Data.List
import Data.Nat
import Data.String
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

--------------------------------------------------------------------------------
--          Internals
--------------------------------------------------------------------------------

public export
Shift : Type
Shift = Nat--Integer

||| The number of bits used per level.
export
blockshift : Shift
blockshift = 4

||| The maximum size of a block.
export
blocksize : Nat
blocksize = integerToNat $ 1 `shiftL` blockshift--(integerToNat blockshift)

||| The mask used to extract the index into the array.
export
blockmask : Nat
blockmask = minus blocksize 1

export
up : Shift -> Shift
up sh = plus sh blockshift

export
down : Shift -> Shift
down sh = minus sh blockshift

export
radixIndex : Nat -> Shift -> Nat
radixIndex i sh = integerToNat ((natToInteger i) `shiftR` sh .&. (natToInteger blockmask))
--  the Nat (cast ((the Integer (cast $ shiftR i sh)) .&. (the Integer (cast blockmask))))

partial
export
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
public export
data Tree a = Balanced (Array (Tree a))
            | Unbalanced (Array (Tree a)) (Array Nat)
            | Leaf (Array a)

public export
Eq a => Eq (Tree a) where
  (Balanced x)      == (Balanced y)      = assert_total $ heq x.arr y.arr
  (Unbalanced x x') == (Unbalanced y y') = assert_total $ heq x.arr y.arr && heq x'.arr y'.arr
  (Leaf x)          == (Leaf y)          = heq x.arr y.arr
  _                 == _                 = False

partial
public export
Show a => Show (Tree a) where
  show (Balanced trees)     =
    show $ toList trees
  show (Unbalanced trees _) =
    show $ toList trees
  show (Leaf elems)         =
    show $ toList elems

--------------------------------------------------------------------------------
--          Show Utilities (Tree)
--------------------------------------------------------------------------------

partial
public export
showTreeRep : Show a => Show (Tree a) => Tree a -> String
showTreeRep (Balanced trees)     =
  "Balanced " ++ (show $ toList trees)
showTreeRep (Unbalanced trees _) =
  "Unbalanced " ++ (show $ toList trees)
showTreeRep (Leaf elems)         =
  "Leaf " ++ (show $ toList elems)

--------------------------------------------------------------------------------
--          Tree Utilities
--------------------------------------------------------------------------------

export
singleton : a -> Array a
singleton x = A 1 $ fill 1 x

export
treeToArray : Tree a -> Array (Tree a)
treeToArray (Balanced arr)     = arr
treeToArray (Unbalanced arr _) = arr
treeToArray (Leaf _)           = assert_total $ idris_crash "Data.RRBVector.Internal.treeToArray: leaf"

export
treeBalanced : Tree a -> Bool
treeBalanced (Balanced _)     = True
treeBalanced (Unbalanced _ _) = False
treeBalanced (Leaf _)         = True

||| Computes the size of a tree with shift.
partial
export
treeSize : Shift -> Tree a -> Nat
treeSize = go 0
  where
    go : Shift -> Shift -> Tree a -> Nat
    go acc _  (Leaf arr)             =
      plus acc arr.size
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
        in go (plus acc (mult i (integerToNat (1 `shiftL` sh))))
              (down sh)
              (at arr.arr i')

||| Turns an array into a tree node by computing the sizes of its subtrees.
||| sh is the shift of the resulting tree.
partial
export
computeSizes : Shift -> Array (Tree a) -> Tree a
computeSizes sh arr =
  case isBalanced of
    True  =>
      Balanced arr
    False =>
      let arrnat = unsafeCreate arr.size (loop sh 0 0 arr.size (toList arr))
        in Unbalanced arr arrnat
  where
    loop :  (sh,cur,acc,n : Nat)
         -> List (Tree a)
         -> FromMArray n Nat (Array Nat)
    loop sh _   acc n []        r = T1.do
      res <- freeze r
      pure $ A n res
    loop sh cur acc n (x :: xs) r =
      case tryNatToFin cur of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.Internal.computeSizes.go: can't convert Nat to Fin"
        Just cur' =>
          let acc' = plus acc (treeSize (down sh) x)
            in T1.do set r cur' acc'
                     loop sh (S cur) acc' n xs r
    maxsize : Integer
    maxsize = 1 `shiftL` sh -- the maximum size of a subtree
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
                   (natToInteger $ treeSize (down sh) subtree) == maxsize && go (plus i 1)
                 False =>
                   treeBalanced subtree

partial
export
countTrailingZeros : Nat -> Nat
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
              assert_total $ idris_crash "Data.RRBVector.Internal.countTrailingZeros: can't convert Nat to Fin"
            Just i' =>
              case testBit (the Int (cast x)) i' of
                True  =>
                  i
                False =>
                  go (plus i 1)

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
data RRBVector a = Root Nat   -- size
                        Shift -- shift (blockshift * height)
                        (Tree a)
                 | Empty

public export
Eq a => Eq (Tree a) => Eq (RRBVector a) where
  (Root n s t) == (Root n' s' t') = n == n' && s == s' && t == t'
  Empty        == Empty           = True
  _            == _               = False

public export
Show a => Show (Tree a) => Show (RRBVector a) where
  show xs = "[" ++ (show' xs) ++ "]" where
    show' : RRBVector a -> String
    show' Empty            = ""
    show' (Root size sh t) = show t
