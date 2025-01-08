||| RRB Vector Internals
module Data.RRBVector.Internal

--import Data.Array
import Data.Array.Core
--import Data.Array.Index
--import Data.Array.Indexed
import Data.Array.Mutable
import Data.Bits
import Data.List
import Data.Linear.Ref1
import Data.Linear.Token
import Data.Nat
import Data.String
import Derive.Prelude
import Syntax.T1 as T1

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
relaxedRadixIndex :  MArray n Nat
                  -> Nat
                  -> Shift
                  -> (Nat, Nat)
relaxedRadixIndex sizes i sh =
  run1 $ \t =>
    let guess    # t := ref1 (radixIndex i sh) t
        idx      # t := loop sizes guess t
        idx'     # t := case idx == 0 of
                          True  =>
                            ref1 i t
                          False =>
                            let idx' = case tryNatToFin $ minus idx 1 of
                                         Nothing    =>
                                           assert_total $ idris_crash "Data.RRBVector.Internal.relaxedRadixIndex: index out of bounds"
                                         Just idx'' =>
                                           ref idx'' t
        subidx   # t := get sizes idx' t
        subidx'  # t := ref1 (minus i subidx) t
        idx'     # t := readAndRelease idx t
        subidx'' # t := readAndRelease subidx' t
        _        # t := release guess t
      in (idx', subidx'') # t
  where
    loop :  MArray n Nat
         -> Nat
         -> F1 [MArray n Nat] Nat
    loop sizes idx t =
      let current = case tryNatToFin idx of
                      Nothing   =>
                        assert_total $ idris_crash "Data.RRBVector.Internal.relaxedRadixIndex.loop: index out of bounds"
                      Just idx' =>
                        --at sizes.arr idx' -- idx will always be in range for a well-formed tree
                        get sizes idx' t -- idx will always be in range for a well-formed tree
        in case i < current of
             True  =>
               idx
             False =>
               assert_total $ loop sizes (plus idx 1)

--------------------------------------------------------------------------------
--          Internal Tree Representation
--------------------------------------------------------------------------------

-- ||| An internal tree representation.
--public export
--data Tree a (bsize : Nat) (usize : Nat) (lsize : Nat) =
--    Balanced (MArray size (Tree a))
--  | Unbalanced (MArray size (Tree a)) (MArray size Nat)
--  | Leaf (MArray size a)

||| An internal tree representation.
public export
data Tree : (bsize : Nat) -> (usize : Nat) -> (lsize : Nat) -> Type -> Type where
  Balanced   : MArray bsize (Tree bsize usize lsize a) -> Tree bsize usize lsize a
  Unbalanced : MArray usize (Tree bsize usize lsize a) -> MArray usize Nat -> Tree bsize usize lsize a
  Leaf       : MArray lsize a -> Tree bsize usize lsize a

--public export
--Eq a => Eq (Tree bsize usize lsize a) where
--  (Balanced x)      == (Balanced y)      = assert_total $ heq x.arr y.arr
--  (Unbalanced x x') == (Unbalanced y y') = assert_total $ heq x.arr y.arr && heq x'.arr y'.arr
--  (Leaf x)          == (Leaf y)          = heq x.arr y.arr
--  _                 == _                 = False

{-
public export
Show a => Show (Tree bsize usize lsize a) where
  show (Balanced trees)     = do
    let trees'' = run1 $ \t =>
                    let trees' # t := freeze trees t
                      in trees' # t
    show $ toList trees''
  show (Unbalanced trees _) = do
    trees'' <-
      run1 $ \t =>
        let trees' # t := freeze trees t
          in trees' # t
    show trees''
  show (Leaf elems)         = do
    elems'' <-
      run1 $ \t =>
        let elems' # t := freeze elems t
          in elems' # t
    show elems''
-}

--------------------------------------------------------------------------------
--          Show Utilities (Tree)
--------------------------------------------------------------------------------

{-
public export
showTreeRep : Show a => Show (Tree a) => Tree a -> String
showTreeRep (Balanced trees)     =
  assert_total $ "Balanced " ++ (show $ toList trees)
showTreeRep (Unbalanced trees _) =
  assert_total $ "Unbalanced " ++ (show $ toList trees)
showTreeRep (Leaf elems)         =
  assert_total $ "Leaf " ++ (show $ toList elems)
  -}

--------------------------------------------------------------------------------
--          Tree Utilities
--------------------------------------------------------------------------------

export
singleton :  a
          -> (1 t : T1 rs)
          -> Res1 (MArray 1 a) (\x => x::rs)
singleton x t =
  newMArray 1 x t

export
treeToArray :  Tree bsize usize lsize a
            -> Either (MArray bsize (Tree bsize usize lsize a))
                      (MArray usize (Tree bsize usize lsize a))
treeToArray (Balanced arr)     = Left arr
treeToArray (Unbalanced arr _) = Right arr
treeToArray (Leaf _)           = assert_total $ idris_crash "Data.RRBVector.Internal.treeToArray: leaf"

export
treeBalanced :  Tree bsize usize lsize a
             -> Bool
treeBalanced (Balanced _)     = True
treeBalanced (Unbalanced _ _) = False
treeBalanced (Leaf _)         = True

||| Computes the size of a tree with shift.
export
treeSize :  Shift
         -> Tree bsize usize lsize a
         -> Nat
treeSize = go 0
  where
    go : Shift -> Shift -> Tree a -> Nat
    go acc _  (Leaf arr)             =
      plus acc lsize
    go acc _  (Unbalanced arr sizes) =
      let i = case tryNatToFin $ minus usize 1 of
                Nothing =>
                  assert_total $ idris_crash "Data.RRBVector.Internal.treeSize: index out of bounds"
                Just i' =>
                  i'
        in plus acc (at sizes.arr i)
    go acc sh (Balanced arr)         =
      let i  = minus bsize 1
          i' = case tryNatToFin i of
                 Nothing  =>
                   assert_total $ idris_crash "Data.RRBVector.Internal.treeSize: index out of bounds"
                 Just i'' =>
                   i''
        in go (plus acc (mult i (integerToNat (1 `shiftL` sh))))
              (down sh)
              (assert_smaller arr (at arr.arr i'))

||| Turns an array into a tree node by computing the sizes of its subtrees.
||| sh is the shift of the resulting tree.
export
computeSizes :  Shift
             -> Array (Tree a)
             -> Tree a
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
                     assert_total $ loop sh (S cur) acc' n xs r
    maxsize : Integer
    maxsize = 1 `shiftL` sh -- the maximum size of a subtree
    len : Nat
    len = arr.size
    lenM1 : Nat
    lenM1 = minus len 1
    isBalanced : Bool
    isBalanced = go 0
      where
        go :  Nat
           -> Bool
        go i =
          let subtree = case tryNatToFin i of
                          Nothing =>
                            assert_total $ idris_crash "Data.RRBVector.Internal.computeSizes.isBalanced: can't convert Nat to Fin"
                          Just i' =>
                            at arr.arr i'
            in case i < lenM1 of
                 True  =>
                   assert_total $ (natToInteger $ treeSize (down sh) subtree) == maxsize && go (plus i 1)
                 False =>
                   treeBalanced subtree

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
              assert_total $ idris_crash "Data.RRBVector.Internal.countTrailingZeros: can't convert Nat to Fin"
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
                  assert_total $ idris_crash "Data.RRBVector.Internal.log2: can't convert Nat to Fin"
                Just i' =>
                  case testBit (the Int (cast x)) i' of
                    True  =>
                      i
                    False =>
                      assert_total $ go (minus i 1)

--------------------------------------------------------------------------------
--          RRB Vectors
--------------------------------------------------------------------------------

||| A relaxed radix balanced vector (RRB-Vector).
||| It supports fast indexing, iteration, concatenation and splitting.
public export
data RRBVector : (bsize : Nat) -> (usize : Nat) -> (lsize : Nat) -> Type -> Type where
  Root  :  Nat   -- size
        -> Shift -- shift (blockshift * height)
        -> (Tree bsize usize lsize a)
        -> RRBVector bsize usize lsize a
  Empty : RRBVector bsize usize lsize a

public export
Eq a => Eq (Tree bsize usize lsize a) => Eq (RRBVector bsize usize lsize a) where
  (Root n s t) == (Root n' s' t') = n == n' && s == s' && t == t'
  Empty        == Empty           = True
  _            == _               = False

--public export
--Show a => Show (Tree a) => Show (RRBVector a) where
--  show xs = "[" ++ (show' xs) ++ "]" where
--    show' : RRBVector a -> String
--    show' Empty            = ""
--    show' (Root size sh t) = show t
