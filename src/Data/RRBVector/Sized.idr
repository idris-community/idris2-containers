||| Relaxed Radix Balanced Vectors (RRBVector)
module Data.RRBVector.Sized

import public Data.RRBVector.Sized.Internal

import Control.Monad.ST
import Data.Array
import Data.Array.Core
import Data.Array.Index
import Data.Array.Indexed
import Data.Bits
import Data.Maybe
import Data.List
import Data.List1
import Data.SnocList
import Data.Vect
import Data.Zippable
import Syntax.T1 as T1

%hide Prelude.null
%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Ops.infixl.(|>)

%default total

--------------------------------------------------------------------------------
--          Fixity
--------------------------------------------------------------------------------

export
infixr 5 ><

export
infixr 5 <|

export
infixl 5 |>

--------------------------------------------------------------------------------
--          Creating RRB-Vectors
--------------------------------------------------------------------------------

||| The empty vector. O(1)
export
empty : RRBVector n a
empty =
  Empty

||| A vector with a single element. O(1)
export
singleton :  a
          -> RRBVector 1 a
singleton x =
  Root 0 (Leaf {lsize=1} (1 ** A 1 $ fill 1 x))

||| Create a new vector from a list. O(n)
export
fromList :  (xs : List a)
         -> RRBVector (length xs) a
fromList []  =
  Empty
fromList [x] =
  singleton x
fromList xs  =
  case nodes xs of
    [tree] =>
      Root 0 tree -- tree is a single leaf
    xs'    =>
      assert_smaller xs (iterateNodes blockshift xs')
  where
    nodes :  List a
          -> List (Tree a)
    nodes trees =
      let (trees', rest) = unsafeAlloc blocksize (go 0 blocksize trees)
        in case rest of
             []    =>
               [trees']
             rest' =>
               (trees' :: nodes (assert_smaller trees rest'))
      where
        go :  (cur,n : Nat)
           -> List a
           -> WithMArray n a (Tree a,List a)
        go cur n []        r = T1.do
          res <- unsafeFreeze r
          pure $ (Leaf {lsize=cur} (cur ** force $ take cur $ A n res),[])
        go cur n (x :: xs) r =
          case cur == n of
            True  => T1.do
              res <- unsafeFreeze r
              pure $ (Leaf {lsize=n} (n ** A n res), x :: xs)
            False =>
              case tryNatToFin cur of
                Nothing   =>
                  assert_total $ idris_crash "Data.RRBVector.Sized.fromList.node: can't convert Nat to Fin"
                Just cur' => T1.do
                  set r cur' x
                  go (S cur) n xs r
    nodes' :  List (Tree a)
           -> List (Tree a)
    nodes' trees =
      let (trees', rest) = unsafeAlloc blocksize (go 0 blocksize trees)
        in case rest of
             []    =>
               [trees']
             rest' =>
               (trees' :: nodes' (assert_smaller trees rest'))
      where
        go :  (cur,n : Nat)
           -> List (Tree a)
           -> WithMArray n (Tree a) (Tree a,List (Tree a))
        go cur n []        r = T1.do
          res <- unsafeFreeze r
          pure $ (Balanced {bsize=cur} (cur ** force $ take cur $ A n res),[])
        go cur n (x :: xs) r =
          case cur == n of
            True  => T1.do
              res <- unsafeFreeze r
              pure $ (Balanced {bsize=n} (n ** A n res), x :: xs)
            False =>
              case tryNatToFin cur of
                Nothing   =>
                  assert_total $ idris_crash "Data.RRBVector.Sized.fromList.node': can't convert Nat to Fin"
                Just cur' => T1.do
                  set r cur' x
                  go (S cur) n xs r
    iterateNodes :  Nat
                 -> List (Tree a)
                 -> RRBVector n a
    iterateNodes sh trees =
      case nodes' trees of
        [tree] =>
          Root sh tree
        trees' =>
          iterateNodes (up sh) (assert_smaller trees trees')

||| Creates a vector of length n with every element set to x. O(log n)
export
replicate :  (n : Nat)
          -> a
          -> RRBVector n a
replicate n x =
  case compare n 0 of
    LT =>
      Empty
    EQ =>
      Empty
    GT =>
      case compare n blocksize of
        LT =>
          Root 0 (Leaf {lsize=n} (n ** A n $ fill n x))
        EQ =>
          Root 0 (Leaf {lsize=n} (n ** A n $ fill n x))
        GT =>
          let size' = integerToNat ((natToInteger $ minus n 1) .&. (natToInteger $ plus blockmask 1))
            in iterateNodes blockshift
                            (Leaf {lsize=blocksize} (blocksize ** A blocksize $ fill blocksize x))
                            (Leaf {lsize=size'} (size' ** A size' $ fill size' x))
  where
    iterateNodes :  Shift
                 -> Tree a
                 -> Tree a
                 -> RRBVector n a
    iterateNodes sh full rest =
      let subtreesm1  = (natToInteger $ minus n 1) `shiftR` sh
          restsize    = integerToNat (subtreesm1 .&. (natToInteger blockmask))
          rest'       = Balanced {bsize=plus restsize 1} ((plus restsize 1) ** A (plus restsize 1) $ append (fill restsize full) (fill 1 rest))
        in case compare subtreesm1 (natToInteger blocksize) of
             LT =>
               Root sh rest'
             EQ =>
               let full' = Balanced {bsize=blocksize} (blocksize ** A blocksize $ fill blocksize full)
                 in iterateNodes (up sh) (assert_smaller full full') (assert_smaller rest rest')
             GT =>
               let full' = Balanced {bsize=blocksize} (blocksize ** A blocksize $ fill blocksize full)
                 in iterateNodes (up sh) (assert_smaller full full') (assert_smaller rest rest')

--------------------------------------------------------------------------------
--          Creating Lists from RRB-Vectors
--------------------------------------------------------------------------------

||| Convert a vector to a list. O(n)
export
toList :  RRBVector n a
       -> List a
toList Empty         =
  []
toList (Root _ tree) =
  treeToList tree
  where
    treeToList :  Tree a
               -> List a
    treeToList (Balanced (_ ** arr))     =
      assert_total $ concat (map treeToList (toList arr))
    treeToList (Unbalanced (_ ** arr) _) =
      assert_total $ concat (map treeToList (toList arr))
    treeToList (Leaf (_ ** arr))         =
      toList arr

--------------------------------------------------------------------------------
--          Folds
--------------------------------------------------------------------------------

export
foldl :  (b -> a -> b)
      -> b
      -> RRBVector n a
      -> b
foldl f acc =
  go
  where
    foldlTree :  b
              -> Tree a
              -> b
    foldlTree acc' (Balanced (_ ** arr))     =
      assert_total $ foldl foldlTree acc' arr
    foldlTree acc' (Unbalanced (_ ** arr) _) =
      assert_total $ foldl foldlTree acc' arr
    foldlTree acc' (Leaf (_ ** arr))         =
      assert_total $ foldl f acc' arr
    go :  RRBVector n a
       -> b
    go Empty         =
      acc
    go (Root _ tree) =
      assert_total $ foldlTree acc tree

export
foldr :  (a -> b -> b)
      -> b
      -> RRBVector n a
      -> b
foldr f acc =
  go
  where
    foldrTree :  Tree a
              -> b
              -> b
    foldrTree (Balanced (_ ** arr)) acc'     =
      assert_total $ foldr foldrTree acc' arr
    foldrTree (Unbalanced (_ ** arr) _) acc' =
      assert_total $ foldr foldrTree acc' arr
    foldrTree (Leaf (_ ** arr)) acc'         =
      assert_total $ foldr f acc' arr
    go :  RRBVector n a
       -> b
    go Empty         =
      acc
    go (Root _ tree) =
      assert_total $ foldrTree tree acc

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Is the vector empty? O(1)
export
null :  RRBVector n a
     -> Bool
null Empty =
  True
null _     =
  False

||| Return the size of a vector. O(1)
export
length :  {n : Nat}
       -> RRBVector n a
       -> Nat
length _ = n

--------------------------------------------------------------------------------
--          Indexing
--------------------------------------------------------------------------------

||| The element at the index or Nothing if the index is out of range. O(log n)
export
lookup :  {n : Nat}
       -> Nat
       -> RRBVector n a
       -> Maybe a
lookup _ Empty          =
  Nothing
lookup i (Root sh tree) =
  case compare i 0 of
    LT =>
      Nothing -- index out of range
    GT =>
      case compare i n of
        EQ =>
          Nothing -- index out of range
        GT =>
          Nothing -- index out of range
        LT =>
          Just $ lookupTree i sh tree
    EQ =>
      case compare i n of
        EQ =>
          Nothing -- index out of range
        GT =>
          Nothing -- index out of range
        LT =>
          Just $ lookupTree i sh tree
  where
    lookupTree :  Nat
               -> Nat
               -> Tree a
               -> a
    lookupTree i sh (Balanced (_ ** arr))         =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.Sized.lookup: can't convert Nat to Fin"
        Just i' =>
          assert_total $ lookupTree i (down sh) (at arr.arr i')
    lookupTree i sh (Unbalanced (_ ** arr) sizes) =
      let (idx, subidx) = relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               assert_total $ idris_crash "Data.RRBVector.Sized.lookup: can't convert Nat to Fin"
             Just idx' =>
               assert_total $ lookupTree subidx (down sh) (at arr.arr idx')
    lookupTree i _ (Leaf (_ ** arr))              =
      let i' = integerToNat ((natToInteger i) .&. (natToInteger blockmask))
        in case tryNatToFin i' of
             Nothing =>
               assert_total $ idris_crash "Data.RRBVector.Sized.lookup: can't convert Nat to Fin"
             Just i'' =>
               at arr.arr i''

||| The element at the index.
||| Calls 'idris_crash' if the index is out of range. O(log n)
export
index :  {n : Nat}
      -> Nat
      -> RRBVector n a
      -> a
index i =
  fromMaybe (assert_total $ idris_crash "Data.RRBVector.Sized.index: index out of range") . lookup i

||| A flipped version of lookup. O(log n)
export
(!?) :  {n : Nat}
     -> RRBVector n a
     -> Nat
     -> Maybe a
(!?) =
  flip lookup

||| A flipped version of index. O(log n)
export
(!!) :  {n : Nat}
     -> RRBVector n a
     -> Nat
     -> a
(!!) =
  flip index

||| Update the element at the index with a new element.
||| If the index is out of range, the original vector is returned. O (log n)
export
update :  {n : Nat}
       -> Nat
       -> a
       -> RRBVector n a
       -> RRBVector n a
update _ _ Empty            =
  Empty
update i x v@(Root sh tree) =
  case compare i 0 of
    LT =>
      v -- index out of range
    GT =>
      case compare i n of
        EQ =>
          v -- index out of range
        GT =>
          v -- index out of range
        LT =>
          Root sh (updateTree i sh tree)
    EQ =>
      case compare i n of
        EQ =>
          v -- index out of range
        GT =>
          v -- index out of range
        LT =>
          Root sh (updateTree i sh tree)
  where
    updateTree :  Nat
               -> Nat
               -> Tree a
               -> Tree a
    updateTree i sh (Balanced (_ ** arr))         =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.Sized.update: can't convert Nat to Fin"
        Just i' =>
          assert_total $ Balanced {bsize=arr.size} (arr.size ** A arr.size (updateAt i' (updateTree i (down sh)) arr.arr))
    updateTree i sh (Unbalanced (_ ** arr) sizes) =
      let (idx, subidx) = relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               assert_total $ idris_crash "Data.RRBVector.Sized.update: can't convert Nat to Fin"
             Just idx' =>
               assert_total $ Unbalanced {usize=arr.size} (arr.size ** A arr.size (updateAt idx' (updateTree subidx (down sh)) arr.arr)) sizes
    updateTree i _ (Leaf (_ ** arr))              =
      let i' = integerToNat ((natToInteger i) .&. (natToInteger blockmask))
        in case tryNatToFin i' of
             Nothing =>
               assert_total $ idris_crash "Data.RRBVector.Sized.update: can't convert Nat to Fin"
             Just i'' =>
               Leaf {lsize=arr.size} (arr.size ** A arr.size (setAt i'' x arr.arr))

||| Adjust the element at the index by applying the function to it.
||| If the index is out of range, the original vector is returned. O(log n)
export
adjust :  {n : Nat}
       -> Nat
       -> (a -> a)
       -> RRBVector n a
       -> RRBVector n a
adjust _ _ Empty            =
  Empty
adjust i f v@(Root sh tree) =
  case compare i 0 of
    LT =>
      v -- index out of range
    GT =>
      case compare i n of
        EQ =>
          v -- index out of range
        GT =>
          v -- index out of range
        LT =>
          Root sh (adjustTree i sh tree)
    EQ =>
      case compare i n of
        EQ =>
          v -- index out of range
        GT =>
          v -- index out of range
        LT =>
          Root sh (adjustTree i sh tree)
  where
    adjustTree :  Nat
               -> Nat
               -> Tree a
               -> Tree a
    adjustTree i sh (Balanced (_ ** arr))         =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.Sized.adjust: can't convert Nat to Fin"
        Just i' =>
          assert_total $ Balanced {bsize=arr.size} (arr.size ** A arr.size (updateAt i' (adjustTree i (down sh)) arr.arr))
    adjustTree i sh (Unbalanced (_ ** arr) sizes) =
      let (idx, subidx) = relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               assert_total $ idris_crash "Data.RRBVector.Sized.adjust: can't convert Nat to Fin"
             Just idx' =>
               assert_total $ Unbalanced {usize=arr.size} (arr.size ** A arr.size (updateAt idx' (adjustTree subidx (down sh)) arr.arr)) sizes
    adjustTree i _ (Leaf (_ ** arr))              =
      let i' = integerToNat ((natToInteger i) .&. (natToInteger blockmask))
        in case tryNatToFin i' of
             Nothing =>
               assert_total $ idris_crash "Data.RRBVector.Sized.adjust: can't convert Nat to Fin"
             Just i'' =>
               Leaf {lsize=arr.size} (arr.size ** A arr.size (updateAt i'' f arr.arr))

private
normalize :  RRBVector n a
          -> RRBVector n a
normalize v@(Root sh (Balanced (_ ** arr)))     =
  case compare arr.size 1 of
    LT =>
      v
    EQ =>
      case tryNatToFin 0 of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.Sized.normalize: can't convert Nat to Fin"
        Just i  =>
          assert_total $ normalize $ Root (down sh) (at arr.arr i)
    GT =>
      v
normalize v@(Root sh (Unbalanced (_ ** arr) _)) =
  case compare arr.size 1 of
    LT =>
      v
    EQ =>
      case tryNatToFin 0 of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.Sized.normalize: can't convert Nat to Fin"
        Just i  =>
          assert_total $ normalize $ Root (down sh) (at arr.arr i)
    GT =>
      v
normalize v                                     =
  v

||| The initial i is n - 1 (the index of the last element in the new tree).
private
takeTree :  Nat
         -> Shift
         -> Tree a
         -> Tree a
takeTree i sh (Balanced (_ ** arr)) with (radixIndex i sh) | ((plus (radixIndex i sh) 1) <= arr.size) proof eq
  _ | i' | True  =
    case tryNatToFin i' of
      Nothing =>
        assert_total $ idris_crash "Data.RRBVector.Sized.takeTree: can't convert Nat to Fin"
      Just i'' =>
        let newarr = force $ take (plus (radixIndex i sh) 1) arr.arr @{lteOpReflectsLTE _ _ eq}
          in assert_total $ Balanced {bsize=plus (radixIndex i sh) 1} ((plus (radixIndex i sh) 1) ** A (plus (radixIndex i sh) 1) (updateAt i'' (takeTree i (down sh)) newarr))
  _ | _  | False =
    assert_total $ idris_crash "Data.RRBVector.Sized.takeTree: index out of bounds"
takeTree i sh (Unbalanced (_ ** arr) sizes) with (relaxedRadixIndex sizes i sh) | ((plus (fst (relaxedRadixIndex sizes i sh)) 1) <= arr.size) proof eq
  _ | (idx, subidx) | True  =
    case tryNatToFin idx of
      Nothing   =>
        assert_total $ idris_crash "Data.RRBVector.Sized.takeTree: can't convert Nat to Fin"
      Just idx' =>
        let newarr = force $ take (plus (fst (relaxedRadixIndex sizes i sh)) 1) arr.arr @{lteOpReflectsLTE _ _ eq}
          in assert_total $ computeSizes sh (A (plus (fst (relaxedRadixIndex sizes i sh)) 1) (updateAt idx' (takeTree subidx (down sh)) newarr))
  _ | _             | False =
    assert_total $ idris_crash "Data.RRBVector.Sized.takeTree: index out of bounds"
takeTree i _ (Leaf (_ ** arr)) with (integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1) <= arr.size) proof eq
  _ | True  =
    let newarr = force $ take (integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1)) arr.arr @{lteOpReflectsLTE _ _ eq}
      in Leaf {lsize=integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1)} ((integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1)) ** A (integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1)) newarr)
  _ | False =
    assert_total $ idris_crash "Data.RRBVector.Sized.takeTree: index out of bounds"

private
dropTree :  Nat
         -> Shift
         -> Tree a
         -> Tree a
dropTree n sh (Balanced (_ ** arr))         =
  case tryNatToFin 0 of
    Nothing   =>
      assert_total $ idris_crash "Data.RRBVector.Sized.dropTree: can't convert Nat to Fin"
    Just zero =>
      let newarr = force $ drop (radixIndex n sh) arr.arr
        in assert_total $ computeSizes sh (A (minus arr.size (radixIndex n sh)) (updateAt zero (dropTree n (down sh)) newarr))
dropTree n sh (Unbalanced (_ ** arr) sizes) =
  case tryNatToFin 0 of
    Nothing   =>
      assert_total $ idris_crash "Data.RRBVector.Sized.dropTree: can't convert Nat to Fin"
    Just zero =>
      let newarr = force $ drop (fst $ relaxedRadixIndex sizes n sh) arr.arr
        in assert_total $ computeSizes sh (A (minus arr.size (fst $ relaxedRadixIndex sizes n sh)) (updateAt zero (dropTree (snd $ relaxedRadixIndex sizes n sh) (down sh)) newarr))
dropTree n _  (Leaf (_ ** arr))             =
  let n      = integerToNat ((natToInteger n) .&. (natToInteger blockmask))
      newarr = force $ drop n arr.arr
    in Leaf {lsize=minus arr.size n} ((minus arr.size n) ** A (minus arr.size n) newarr)

||| The first i elements of the vector.
||| If the vector contains less than or equal to i elements, the whole vector is returned. O(log n)
export
take :  {n : Nat}
     -> Nat
     -> RRBVector n a
     -> (n' ** RRBVector n' a)
take _ Empty            =
  (0 ** empty)
take t v@(Root sh tree) =
  case compare t 0 of
    LT =>
      (0 ** empty)
    EQ =>
      (0 ** empty)
    GT =>
      case compare t n of
        LT =>
          ((minus t n) ** normalize $ Root sh (takeTree (minus t 1) sh tree))
        EQ =>
          (n ** v)
        GT =>
          (n ** v)

||| The vector without the first i elements.
||| If the vector contains less than or equal to i elements, the empty vector is returned. O(log n)
export
drop :  {n : Nat}
     -> Nat
     -> RRBVector n a
     -> (n' ** RRBVector n' a)
drop _ Empty            =
  (0 ** empty)
drop d v@(Root sh tree) =
  case compare d 0 of
    LT =>
      (n ** v)
    EQ =>
      (n ** v)
    GT =>
      case compare d n of
        LT =>
          ((minus n d) ** normalize $ Root sh (dropTree d sh tree))
        EQ =>
          (0 ** empty)
        GT =>
          (0 ** empty)

||| Split the vector at the given index. O(log n)
export
splitAt :  {n : Nat}
        -> Nat
        -> RRBVector n a
        -> ((n' ** RRBVector n' a), (n'' ** RRBVector n'' a))
splitAt _ Empty            =
  ((0 ** empty), (0 ** empty))
splitAt s v@(Root sh tree) =
  case compare s 0 of
    LT =>
      ((0 ** empty), (n ** v))
    EQ =>
      ((0 ** empty), (n ** v))
    GT =>
      case compare s n of
        LT =>
          let (t ** left)  = take s v
              (d ** right) = drop s v
            in ((t ** left), (d ** right))
        EQ =>
          ((n ** v), (0 ** empty))
        GT =>
          ((n ** v), (0 ** empty))

--------------------------------------------------------------------------------
--          Deconstruction
--------------------------------------------------------------------------------

||| The first element and the vector without the first element, or 'Nothing' if the vector is empty. O(log n)
export
viewl :  {n : Nat}
      -> RRBVector n a
      -> (n' ** Maybe (a, RRBVector n' a))
viewl Empty           =
  (0 ** Nothing)
viewl v@(Root _ tree) =
  let (d ** tail) = drop 1 v
    in (d ** Just (headTree tree, tail))
  where
    headTree :  Tree a
             -> a
    headTree (Balanced (_ ** arr))     =
      case tryNatToFin 0 of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.Sized.viewl: can't convert Nat to Fin"
        Just zero =>
          assert_total $ headTree (at arr.arr zero)
    headTree (Unbalanced (_ ** arr) _) =
      case tryNatToFin 0 of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.Sized.viewl: can't convert Nat to Fin"
        Just zero =>
          assert_total $ headTree (at arr.arr zero)
    headTree (Leaf (_ ** arr))         =
      case tryNatToFin 0 of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.Sized.viewl: can't convert Nat to Fin"
        Just zero =>
          at arr.arr zero

||| The vector without the last element and the last element, or 'Nothing' if the vector is empty. O(log n)
export
viewr :  {n : Nat}
      -> RRBVector n a
      -> (n' ** Maybe (RRBVector n' a, a))
viewr Empty           =
  (0 ** Nothing)
viewr v@(Root _ tree) =
  let (t ** init) = take (minus n 1) v
    in (t ** Just (init, lastTree tree))
  where
    lastTree :  Tree a
             -> a
    lastTree (Balanced (_ ** arr))     =
      case tryNatToFin (minus n 1) of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.Sized.viewr: can't convert Nat to Fin"
        Just last =>
          assert_total $ lastTree (at arr.arr last)
    lastTree (Unbalanced (_ ** arr) _) =
      case tryNatToFin (minus n 1) of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.Sized.viewr: can't convert Nat to Fin"
        Just last =>
          assert_total $ lastTree (at arr.arr last)
    lastTree (Leaf (_ ** arr))         =
      case tryNatToFin (minus n 1) of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.Sized.viewr: can't convert Nat to Fin"
        Just last =>
          at arr.arr last

--------------------------------------------------------------------------------
--          Transformation
--------------------------------------------------------------------------------

||| Apply the function to every element. O(n)
export
map :  (a -> b)
    -> RRBVector n a
    -> RRBVector n b
map _ Empty          =
  Empty
map f (Root sh tree) =
  Root sh (mapTree tree)
  where
    mapTree :  Tree a
            -> Tree b
    mapTree (Balanced (_ ** arr))         =
      assert_total $ Balanced {bsize=arr.size} (arr.size ** map mapTree arr)
    mapTree (Unbalanced (_ ** arr) sizes) =
      assert_total $ Unbalanced {usize=arr.size} (arr.size ** map mapTree arr) sizes
    mapTree (Leaf (_ ** arr))             =
      Leaf {lsize=arr.size} (arr.size ** map f arr)

||| Reverse the vector. O(n)
export
reverse :  {n : Nat}
        -> RRBVector n a
        -> (n' ** RRBVector n' a)
reverse v =
  case compare (length v) 1 of
    LT =>
      (n ** v)
    EQ =>
      (n ** v)
    GT =>
      case fromList $ toList v of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.Sized.reverse: can't convert to List1"
        Just v' =>
          ((length (forget (reverse v'))) ** fromList $ forget $ reverse v')

||| Take two vectors and return a vector of corresponding pairs.
||| If one input is longer, excess elements are discarded from the right end. O(min(n1,n2))
export
zip :  {n : Nat}
    -> RRBVector n a
    -> RRBVector n b
    -> (n' ** RRBVector n' (a, b))
zip v1 v2 =
  case fromList $ toList v1 of
    Nothing  =>
      assert_total $ idris_crash "Data.RRBVector.Sized.zip: can't convert to List1"
    Just v1' =>
      case fromList $ toList v2 of
        Nothing  =>
          assert_total $ idris_crash "Data.RRBVector.Sized.zip: can't convert to List1"
        Just v2' =>
          ((length (forget (v1' `zip` v2'))) ** fromList $ forget $ zip v1' v2')

--------------------------------------------------------------------------------
--          Concatenation
--------------------------------------------------------------------------------

||| Create a new tree with shift sh.
private
newBranch :  a
          -> Shift
          -> Tree a
newBranch x 0  =
  Leaf {lsize=1} (1 ** singleton x)
newBranch x sh =
  assert_total $ Balanced {bsize=1} (1 ** singleton $ newBranch x (down sh))

||| Add an element to the left end of the vector. O(log n)
export
(<|) :  {n : Nat}
     -> a
     -> RRBVector n a
     -> (n' ** RRBVector n' a)
x <| Empty        =
  (1 ** singleton x)
x <| Root sh tree =
  case compare insertshift sh of
    LT =>
      ((plus n 1) ** Root sh (consTree sh tree))
    EQ =>
      ((plus n 1) ** Root sh (consTree sh tree))
    GT =>
      let new = A 2 $ array $ fromList [(newBranch x sh), tree]
        in ((plus n 1) ** Root insertshift (computeSizes insertshift new))
  where
    -- compute the shift at which the new branch needs to be inserted (0 means there is space in the leaf)
    -- the size is computed for efficient calculation of the shift in a balanced subtree
    computeShift :  Nat
                 -> Nat
                 -> Nat
                 -> Tree a
                 -> Nat
    computeShift sz sh min (Balanced _)                 =
      -- @sz - 1@ is the index of the last element
      let hishift  = let comp = mult (log2 (minus sz 1) `div` blockshift) blockshift  -- the shift of the root when normalizing
                       in case compare comp 0 of
                            LT =>
                              0
                            EQ =>
                              0
                            GT =>
                              comp
          hi       = (natToInteger $ minus sz 1) `shiftR` hishift -- the length of the root node when normalizing minus 1
          newshift = case compare hi (natToInteger blockmask) of
                       LT =>
                         hishift
                       EQ =>
                         plus hishift blockshift
                       GT =>
                         plus hishift blockshift
        in case compare newshift sh of
             LT =>
               newshift
             EQ =>
               newshift
             GT =>
               min
    computeShift _ sh min (Unbalanced (_ ** arr) sizes) =
      let sz'     = case tryNatToFin 0 of
                      Nothing   =>
                        assert_total $ idris_crash "Data.RRBVector.Sized.(<|).computeShift.Unbalanced: can't convert Nat to Fin"
                      Just zero =>
                        at sizes.arr zero -- the size of the first subtree
          newtree = case tryNatToFin 0 of
                      Nothing   =>
                        assert_total $ idris_crash "Data.RRBVector.Sized.(<|).computeShift.Unbalanced: can't convert Nat to Fin"
                      Just zero =>
                        at arr.arr zero
          newmin  = case compare arr.size blocksize of
                      LT =>
                        sh
                      EQ =>
                        min
                      GT =>
                        min
        in assert_total $ computeShift sz' (down sh) newmin newtree
    computeShift _ _ min (Leaf (_ ** arr))              =
      case compare arr.size blocksize of
        LT =>
          0
        EQ =>
          min
        GT =>
          min
    insertshift : Nat
    insertshift = computeShift n sh (up sh) tree
    consTree :  Nat
             -> Tree a
             -> Tree a
    consTree sh (Balanced (_ ** arr))     =
      case compare sh insertshift of
        LT =>
          case tryNatToFin 0 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.Sized.(<|).consTree.Balanced: can't convert Nat to Fin"
            Just zero =>
              assert_total $ computeSizes sh (A arr.size $ updateAt zero (consTree (down sh)) arr.arr)
        EQ =>
          computeSizes sh (A (S arr.size) (append (fill 1 (newBranch x (down sh))) arr.arr))
        GT =>
          case tryNatToFin 0 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.Sized.(<|).consTree.Balanced: can't convert Nat to Fin"
            Just zero =>
              assert_total $ computeSizes sh (A arr.size $ updateAt zero (consTree (down sh)) arr.arr)
    consTree sh (Unbalanced (_ ** arr) _) =
      case compare sh insertshift of
        LT =>
          case tryNatToFin 0 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.Sized.(<|).consTree.Unbalanced: can't convert Nat to Fin"
            Just zero =>
              assert_total $ computeSizes sh (A arr.size $ updateAt zero (consTree (down sh)) arr.arr)
        EQ =>
          computeSizes sh (A (S arr.size) (append (fill 1 (newBranch x (down sh))) arr.arr))
        GT =>
          case tryNatToFin 0 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.Sized.(<|).consTree.Unbalanced: can't convert Nat to Fin"
            Just zero =>
              assert_total $ computeSizes sh (A arr.size $ updateAt zero (consTree (down sh)) arr.arr)
    consTree _ (Leaf (_ ** arr))          =
      Leaf {lsize=S arr.size} ((S arr.size) ** A (S arr.size) (append (fill 1 x) arr.arr))

||| Add an element to the right end of the vector. O(log n)
export
(|>) :  {n : Nat}
     -> RRBVector n a
     -> a
     -> (n' ** RRBVector n' a)
Empty        |> x =
  (1 ** singleton x)
Root sh tree |> x =
  case compare insertshift sh of
    LT =>
      ((plus n 1) ** Root sh (snocTree sh tree))
    EQ =>
      ((plus n 1) ** Root sh (snocTree sh tree))
    GT =>
      let new = A 2 $ array $ fromList [tree,(newBranch x sh)]
        in ((plus n 1) ** Root insertshift (computeSizes insertshift new))
  where
    -- compute the shift at which the new branch needs to be inserted (0 means there is space in the leaf)
    -- the size is computed for efficient calculation of the shift in a balanced subtree
    computeShift :  Nat
                 -> Nat
                 -> Nat
                 -> Tree a
                 -> Nat
    computeShift sz sh min (Balanced _)                 =
      -- @sz - 1@ is the index of the last element
      let newshift = mult (countTrailingZeros sz `div` blockshift) blockshift
        in case compare newshift sh of
             LT =>
               newshift
             EQ =>
               newshift
             GT =>
               min
    computeShift _ sh min (Unbalanced (_ ** arr) sizes) =
      let lastidx = minus arr.size 1
          sz'     = case tryNatToFin lastidx of
                      Nothing       =>
                        assert_total $ idris_crash "Data.RRBVector.Sized.(|>).computeShift.Unbalanced: can't convert Nat to Fin"
                      Just lastidx' =>
                        case tryNatToFin $ minus lastidx 1 of
                          Nothing        =>
                            assert_total $ idris_crash "Data.RRBVector.Sized.(|>).computeShift.Unbalanced: can't convert Nat to Fin"
                          Just lastidx'' =>
                            minus (at sizes.arr lastidx') (at sizes.arr lastidx'')
          newtree = case tryNatToFin lastidx of
                      Nothing       =>
                        assert_total $ idris_crash "Data.RRBVector.Sized.(|>).computeShift.Unbalanced: can't convert Nat to Fin"
                      Just lastidx' =>
                        at arr.arr lastidx'
          newmin  = case compare arr.size blocksize of
                      LT =>
                        sh
                      EQ =>
                        min
                      GT =>
                        min
        in assert_total $ computeShift sz' (down sh) newmin newtree
    computeShift _ _ min (Leaf (_ ** arr))              =
      case compare arr.size blocksize of
        LT =>
          0
        EQ =>
          min
        GT =>
          min
    insertshift : Nat
    insertshift = computeShift n sh (up sh) tree
    snocTree :  Nat
             -> Tree a
             -> Tree a
    snocTree sh (Balanced (_ ** arr)) =
      case compare sh insertshift of
        LT =>
          case tryNatToFin $ minus arr.size 1 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.Sized.(|>).snocTree.Balanced: can't convert Nat to Fin"
            Just lastidx =>
              assert_total $ Balanced {bsize=arr.size} (arr.size ** A arr.size $ updateAt lastidx (snocTree (down sh)) arr.arr)
        EQ =>
          Balanced {bsize=plus arr.size 1} ((plus arr.size 1) ** A (plus arr.size 1) (append arr.arr (fill 1 (newBranch x (down sh))))) -- the current subtree is fully balanced
        GT =>
          case tryNatToFin $ minus arr.size 1 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.Sized.(|>).snocTree.Balanced: can't convert Nat to Fin"
            Just lastidx =>
              assert_total $ Balanced {bsize=arr.size} (arr.size ** A arr.size $ updateAt lastidx (snocTree (down sh)) arr.arr)
    snocTree sh (Unbalanced (_ ** arr) sizes) =
      case compare sh insertshift of
        LT =>
          case tryNatToFin $ minus arr.size 1 of
            Nothing       =>
              assert_total $ idris_crash "Data.RRBVector.Sized.(|>).snocTree.Unbalanced: can't convert Nat to Fin"
            Just lastidxa =>
              case tryNatToFin $ minus sizes.size 1 of
                Nothing       =>
                  assert_total $ idris_crash "Data.RRBVector.Sized.(|>).snocTree.Unbalanced: can't convert Nat to Fin"
                Just lastidxs =>
                  let lastsize = plus (at sizes.arr lastidxs) 1
                    in assert_total $ Unbalanced {usize=arr.size} (arr.size ** A arr.size (updateAt lastidxa (snocTree (down sh)) arr.arr))
                                                                  (A sizes.size (setAt lastidxs lastsize sizes.arr))
        EQ =>
          case tryNatToFin $ minus sizes.size 1 of
            Nothing      =>
              assert_total $ idris_crash "Data.RRBVector.Sized.(|>).snocTree.Unbalanced: can't convert Nat to Fin"
            Just lastidx =>
              let lastsize = plus (at sizes.arr lastidx) 1
                in assert_total $ Unbalanced {usize=plus arr.size 1} ((plus arr.size 1) ** A (plus arr.size 1) (append arr.arr (fill 1 (newBranch x (down sh)))))
                                                                     (A (plus sizes.size 1) (append sizes.arr (fill 1 lastsize)))
        GT =>
          case tryNatToFin $ minus arr.size 1 of
            Nothing       =>
              assert_total $ idris_crash "Data.RRBVector.Sized.(|>).snocTree.Unbalanced: can't convert Nat to Fin"
            Just lastidxa =>
              case tryNatToFin $ minus sizes.size 1 of
                Nothing       =>
                  assert_total $ idris_crash "Data.RRBVector.Sized.(|>).snocTree.Unbalanced: can't convert Nat to Fin"
                Just lastidxs =>
                  let lastsize = plus (at sizes.arr lastidxs) 1
                    in assert_total $ Unbalanced {usize=arr.size} (arr.size ** A arr.size (updateAt lastidxa (snocTree (down sh)) arr.arr))
                                                                  (A sizes.size (setAt lastidxs lastsize sizes.arr))
    snocTree _  (Leaf (_ ** arr))             =
      Leaf {lsize=plus arr.size 1} ((plus arr.size 1) ** A (plus arr.size 1) (append arr.arr (fill 1 x)))

||| Concatenates two vectors. O(log(max(n1,n2)))
export
(><) :  {n1 : Nat}
     -> {n2 : Nat}
     -> RRBVector n1 a
     -> RRBVector n2 a
     -> (n' ** RRBVector n' a)
Empty                >< v                    =
  (n2 ** v)
v                    >< Empty                =
  (n1 ** v)
Root sh1 tree1 >< Root sh2 tree2 =
  let upmaxshift = case compare sh1 sh2 of
                     LT =>
                       up sh2
                     EQ =>
                       up sh1
                     GT =>
                       up sh1
      newarr     = mergeTrees tree1 sh1 tree2 sh2
    in ((plus n1 n2) ** normalize $ Root upmaxshift (computeSizes upmaxshift newarr))
  where
    viewlArr :  Array (Tree a)
             -> (Tree a, Array (Tree a))
    viewlArr arr =
      case tryNatToFin 0 of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.Sized.(><).viewlArr: can't convert Nat to Fin"
        Just zero =>
          (at arr.arr zero, drop 1 arr)
    viewrArr :  Array (Tree b)
             -> (Array (Tree b), Tree b)
    viewrArr arr =
      case tryNatToFin $ minus arr.size 1 of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.Sized.(><).viewrArr: can't convert Nat to Fin"
        Just last =>
          (take (minus arr.size 1) arr, at arr.arr last)
    mergeRebalance' :  Shift
                    -> Array (Tree a)
                    -> Array (Tree a)
                    -> Array (Tree a)
                    -> (Tree a -> Array (Tree a))
                    -> (Array (Tree a) -> Tree a)
                    -> Array (Tree a)
    mergeRebalance' sh left center right extract construct =
      runST $ do
        nodecounter    <- newSTRef 0
        subtreecounter <- newSTRef 0
        newnode        <- newSTRef Lin
        newsubtree     <- newSTRef Lin
        newroot        <- newSTRef Lin
        for_ (toList left ++ toList center ++ toList right) $ \subtree =>
          for_ (extract subtree) $ \x => do
            nodecounter' <- readSTRef nodecounter
            when (nodecounter' == (natToInteger blocksize)) $ do
              newnode' <- readSTRef newnode
              modifySTRef newsubtree (\y => y :< (construct $ A (SnocSize newnode')
                                                                (snocConcat newnode'))
                                    )
              writeSTRef newnode Lin
              writeSTRef nodecounter 0
              modifySTRef subtreecounter (\y => y + 1
                                         )
              subtreecounter' <- readSTRef subtreecounter
              when (subtreecounter' == (natToInteger blocksize)) $ do
                newsubtree' <- readSTRef newsubtree
                modifySTRef newroot (\y => y :< (computeSizes sh (fromList $ the (List (Tree a)) (cast newsubtree')))
                                    )
                writeSTRef newsubtree Lin
                writeSTRef subtreecounter 0
            modifySTRef newnode (\y => y :< (fill 1 x)
                                )
            modifySTRef nodecounter (\y => y + 1
                                    )
        newnode' <- readSTRef newnode
        modifySTRef newsubtree (\y => y :< (construct $ A (SnocSize newnode')
                                                          (snocConcat newnode'))
                                           )
        newsubtree' <- readSTRef newsubtree
        modifySTRef newroot (\y => y :< (computeSizes sh (fromList $ the (List (Tree a)) (cast newsubtree')))
                            )
        newroot' <- readSTRef newroot
        pure $ fromList $ the (List (Tree a)) (cast newroot')
    mergeRebalance'' :  Shift
                     -> Array (Tree a)
                     -> Array (Tree a)
                     -> Array (Tree a)
                     -> (Tree a -> Array a)
                     -> Array (Tree a)
    mergeRebalance'' sh left center right extract =
      runST $ do
        nodecounter    <- newSTRef 0
        subtreecounter <- newSTRef 0
        newnode        <- newSTRef Lin
        newsubtree     <- newSTRef Lin
        newroot        <- newSTRef Lin
        for_ (toList left ++ toList center ++ toList right) $ \subtree =>
          for_ (extract subtree) $ \x => do
            nodecounter' <- readSTRef nodecounter
            when (nodecounter' == (natToInteger blocksize)) $ do
              newnode' <- readSTRef newnode
              modifySTRef newsubtree (\y => y :< ( Leaf {lsize=SnocSize newnode'} ((SnocSize newnode') ** A (SnocSize newnode')
                                                                                                            (snocConcat newnode'))
                                                 )
                                     )
              writeSTRef newnode Lin
              writeSTRef nodecounter 0
              modifySTRef subtreecounter (\y => y + 1
                                         )
              subtreecounter' <- readSTRef subtreecounter
              when (subtreecounter' == (natToInteger blocksize)) $ do
                newsubtree' <- readSTRef newsubtree
                modifySTRef newroot (\y => y :< (computeSizes sh (fromList $ the (List (Tree a)) (cast newsubtree')))
                                    )
                writeSTRef newsubtree Lin
                writeSTRef subtreecounter 0
            modifySTRef newnode (\y => y :< (fill 1 x)
                                )
            modifySTRef nodecounter (\y => y + 1
                                    )
        newnode' <- readSTRef newnode
        modifySTRef newsubtree (\y => y :< ( Leaf {lsize=SnocSize newnode'} ((SnocSize newnode') ** A (SnocSize newnode')
                                                                                                      (snocConcat newnode'))
                                           )
                               )
        newsubtree' <- readSTRef newsubtree
        modifySTRef newroot (\y => y :< (computeSizes sh (fromList $ the (List (Tree a)) (cast newsubtree')))
                            )
        newroot' <- readSTRef newroot
        pure $ fromList $ the (List (Tree a)) (cast newroot')
    mergeRebalance :  Shift
                   -> Array (Tree a)
                   -> Array (Tree a)
                   -> Array (Tree a)
                   -> Array (Tree a)
    mergeRebalance sh left center right =
      case compare sh blockshift of
        LT =>
          assert_total $ mergeRebalance' sh left center right treeToArray (computeSizes (down sh))
        EQ =>
          assert_total $ mergeRebalance'' sh left center right (\(Leaf (_ ** arr)) => arr)
        GT =>
          assert_total $ mergeRebalance' sh left center right treeToArray (computeSizes (down sh))
    mergeTrees :  Tree a
               -> Nat
               -> Tree a
               -> Nat
               -> Array (Tree a)
    mergeTrees tree1@(Leaf (_ ** arr1)) _   tree2@(Leaf (_ ** arr2)) _   =
      case compare arr1.size blocksize of
        LT =>
          let arr' = A (plus arr1.size arr2.size) (append arr1.arr arr2.arr)
            in case compare arr'.size blocksize of
                 LT =>
                   singleton $ Leaf {lsize=plus arr1.size arr2.size} ((plus arr1.size arr2.size) ** arr')
                 EQ =>
                   singleton $ Leaf {lsize=plus arr1.size arr2.size} ((plus arr1.size arr2.size) ** arr')
                 GT =>
                   let (left, right) = (take blocksize arr',drop blocksize arr')
                       lefttree      = Leaf {lsize=left.size} (left.size ** left)
                       righttree     = Leaf {lsize=right.size} (right.size ** right)
                     in A 2 $ fromPairs 2 lefttree [(1,righttree)]
        EQ =>
          A 2 $ fromPairs 2 tree1 [(1,tree2)]
        GT =>
          let arr' = A (plus arr1.size arr2.size) (append arr1.arr arr2.arr)
            in case compare arr'.size blocksize of
                 LT =>
                   singleton $ Leaf {lsize=plus arr1.size arr2.size} ((plus arr1.size arr2.size) ** arr')
                 EQ =>
                   singleton $ Leaf {lsize=plus arr1.size arr2.size} ((plus arr1.size arr2.size) ** arr')
                 GT =>
                   let (left, right) = (take blocksize arr',drop blocksize arr')
                       lefttree      = Leaf {lsize=left.size} (left.size ** left)
                       righttree     = Leaf {lsize=right.size} (right.size ** right)
                     in A 2 $ fromPairs 2 lefttree [(1,righttree)]
    mergeTrees tree1                    sh1 tree2                    sh2 =
      case compare sh1 sh2 of
        LT =>
          let right                  = treeToArray tree2
              (righthead, righttail) = viewlArr right
              merged                 = assert_total $ mergeTrees tree1 sh1 righthead (down sh2)
            in mergeRebalance sh2 empty merged righttail
        GT =>
          let left                 = treeToArray tree1
              (leftinit, leftlast) = viewrArr left
              merged               = assert_total $ mergeTrees leftlast (down sh1) tree2 sh2
            in mergeRebalance sh1 leftinit merged empty
        EQ =>
          let left                   = treeToArray tree1
              right                  = treeToArray tree2
              (leftinit, leftlast)   = viewrArr left
              (righthead, righttail) = viewlArr right
              merged                 = assert_total $ mergeTrees leftlast (down sh1) righthead (down sh2)
            in mergeRebalance sh1 leftinit merged righttail

||| Insert an element at the given index, shifting the rest of the vector over.
||| If the index is negative, add the element to the left end of the vector.
||| If the index is bigger than or equal to the length of the vector, add the element to the right end of the vector. O(log n)
export
insertAt :  {n : Nat}
         -> Nat
         -> a
         -> RRBVector n a
         -> (n' ** RRBVector n' a)
insertAt i x v =
  let ((_ ** left), (_ ** right)) = splitAt i v
      (l' ** left')               = left |> x
    in left' >< right

||| Delete the element at the given index.
||| If the index is out of range, return the original vector. O(log n)
export
deleteAt :  {n : Nat}
         -> Nat
         -> RRBVector n a
         -> (n' ** RRBVector n' a)
deleteAt i v =
  let ((_ ** left), (_ ** right)) = splitAt (plus i 1) v
      (_ ** left')                = take i left
    in left' >< right

--------------------------------------------------------------------------------
--          Show Utilities (RRB-Vector)
--------------------------------------------------------------------------------

||| Show the full representation of the vector.
export
showRRBVectorRep :  {n : Nat}
                 -> Show a
                 => Show (Tree a)
                 => Show (RRBVector n a)
                 => RRBVector n a
                 -> String
showRRBVectorRep Empty       =
  ""
showRRBVectorRep (Root sh t) =
  "RRBVector "    ++
  (show n)        ++
  " "             ++
  "{ "            ++
  "Shift = "      ++
  (show sh)       ++
  ", Tree = "     ++
  (showTreeRep t) ++
  "}"

--------------------------------------------------------------------------------
--          Interfaces (RRBVector)
--------------------------------------------------------------------------------

export
{n : Nat} -> Eq a => Eq (RRBVector n a) where
  xs == ys = length xs == length ys && Data.RRBVector.Sized.toList xs == Data.RRBVector.Sized.toList ys

export
{n : Nat} -> Ord a => Ord (RRBVector n a) where
  compare xs ys = compare (Data.RRBVector.Sized.toList xs) (Data.RRBVector.Sized.toList ys)

export
Functor (RRBVector n) where
  map f v = map f v

export
Foldable (RRBVector n) where
  foldl f z           = Data.RRBVector.Sized.foldl f z
  foldr f z           = Data.RRBVector.Sized.foldr f z
  null                = null
