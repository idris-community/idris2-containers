||| Relaxed Radix Balanced Vectors (RRBVector)
module Data.RRBVector

import public Data.RRBVector.Internal

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
empty : RRBVector a
empty = Empty

||| A vector with a single element. O(1)
export
singleton :  a
          -> RRBVector a
singleton x = Root 1 0 (Leaf $ A 1 $ fill 1 x)

||| Create a new vector from a list. O(n)
export
fromList :  List a
         -> RRBVector a
fromList []  = Empty
fromList [x] = singleton x
fromList xs  =
  case nodes Leaf xs of
    [tree] =>
      Root (treeSize 0 tree) 0 tree -- tree is a single leaf
    xs'    =>
      assert_smaller xs (iterateNodes blockshift xs')
  where
    nodes :  (Array a -> Tree a)
          -> List a
          -> List (Tree a)
    nodes f trees =
      let (trees', rest) = unsafeAlloc blocksize (go 0 blocksize f trees)
        in case rest of
             []    =>
               [trees']
             rest' =>
               (trees' :: nodes f (assert_smaller trees rest'))
      where
        go :  (cur,n : Nat)
           -> (Array a -> Tree a)
           -> List a
           -> WithMArray n a (Tree a,List a)
        go cur n f []        r = T1.do
          res <- unsafeFreeze r
          pure $ (f $ force $ take cur $ A n res,[])
        go cur n f (x :: xs) r =
          case cur == n of
            True  => T1.do
              res <- unsafeFreeze r
              pure $ (f $ A n res, x :: xs)
            False =>
              case tryNatToFin cur of
                Nothing   =>
                  assert_total $ idris_crash "Data.RRBVector.fromList.node: can't convert Nat to Fin"
                Just cur' => T1.do
                  set r cur' x
                  go (S cur) n f xs r
    nodes' :  (Array (Tree a)-> Tree a)
           -> List (Tree a)
           -> List (Tree a)
    nodes' f trees =
      let (trees', rest) = unsafeAlloc blocksize (go 0 blocksize f trees)
        in case rest of
             []    =>
               [trees']
             rest' =>
               (trees' :: nodes' f (assert_smaller trees rest'))
      where
        go :  (cur,n : Nat)
           -> (Array (Tree a) -> Tree a)
           -> List (Tree a)
           -> WithMArray n (Tree a) (Tree a,List (Tree a))
        go cur n f []        r = T1.do
          res <- unsafeFreeze r
          pure $ (f $ force $ take cur $ A n res,[])
        go cur n f (x :: xs) r =
          case cur == n of
            True  => T1.do
              res <- unsafeFreeze r
              pure $ (f $ A n res, x :: xs)
            False =>
              case tryNatToFin cur of
                Nothing   =>
                  assert_total $ idris_crash "Data.RRBVector.fromList.node': can't convert Nat to Fin"
                Just cur' => T1.do
                  set r cur' x
                  go (S cur) n f xs r
    iterateNodes :  Nat
                 -> List (Tree a)
                 -> RRBVector a
    iterateNodes sh trees =
      case nodes' Balanced trees of
        [tree] =>
          Root (treeSize sh tree) sh tree
        trees' =>
          iterateNodes (up sh) (assert_smaller trees trees')

||| Creates a vector of length n with every element set to x. O(log n)
export
replicate :  Nat
          -> a
          -> RRBVector a
replicate n x =
  case compare n 0 of
    LT =>
      Empty
    EQ =>
      Empty
    GT =>
      case compare n blocksize of
        LT =>
          Root n 0 (Leaf $ A n $ fill n x)
        EQ =>
          Root n 0 (Leaf $ A n $ fill n x)
        GT =>
          let size' = integerToNat ((natToInteger $ minus n 1) .&. (natToInteger $ plus blockmask 1))
            in iterateNodes blockshift
                            (Leaf $ A blocksize $ fill blocksize x)
                            (Leaf $ A size' $ fill size' x)
  where
    iterateNodes :  Shift
                 -> Tree a
                 -> Tree a
                 -> RRBVector a
    iterateNodes sh full rest =
      let subtreesm1  = (natToInteger $ minus n 1) `shiftR` sh
          restsize    = integerToNat (subtreesm1 .&. (natToInteger blockmask))
          rest'       = Balanced $ A (plus restsize 1) $ append (fill restsize full) (fill 1 rest)
        in case compare subtreesm1 (natToInteger blocksize) of
             LT =>
               Root n sh rest'
             EQ =>
               let full' = Balanced (A blocksize $ fill blocksize full)
                 in iterateNodes (up sh) (assert_smaller full full') (assert_smaller rest rest')
             GT =>
               let full' = Balanced (A blocksize $ fill blocksize full)
                 in iterateNodes (up sh) (assert_smaller full full') (assert_smaller rest rest')

--------------------------------------------------------------------------------
--          Creating Lists from RRB-Vectors
--------------------------------------------------------------------------------

||| Convert a vector to a list. O(n)
export
toList :  RRBVector a
       -> List a
toList Empty           = []
toList (Root _ _ tree) = treeToList tree
  where
    treeToList :  Tree a
               -> List a
    treeToList (Balanced trees)     = assert_total $ concat (map treeToList (toList trees))
    treeToList (Unbalanced trees _) = assert_total $ concat (map treeToList (toList trees))
    treeToList (Leaf arr)           = toList arr

--------------------------------------------------------------------------------
--          Folds
--------------------------------------------------------------------------------

export
foldl :  (b -> a -> b)
      -> b
      -> RRBVector a
      -> b
foldl f acc = go
  where
    foldlTree :  b
              -> Tree a
              -> b
    foldlTree acc' (Balanced arr)     = assert_total $ foldl foldlTree acc' arr
    foldlTree acc' (Unbalanced arr _) = assert_total $ foldl foldlTree acc' arr
    foldlTree acc' (Leaf arr)         = assert_total $ foldl f acc' arr
    go :  RRBVector a
       -> b
    go Empty           = acc
    go (Root _ _ tree) = assert_total $ foldlTree acc tree

export
foldr :  (a -> b -> b)
      -> b
      -> RRBVector a
      -> b
foldr f acc = go
  where
    foldrTree :  Tree a
              -> b
              -> b
    foldrTree (Balanced arr) acc'     = assert_total $ foldr foldrTree acc' arr
    foldrTree (Unbalanced arr _) acc' = assert_total $ foldr foldrTree acc' arr
    foldrTree (Leaf arr) acc'         = assert_total $ foldr f acc' arr
    go :  RRBVector a
       -> b
    go Empty           = acc
    go (Root _ _ tree) = assert_total $ foldrTree tree acc

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Is the vector empty? O(1)
export
null :  RRBVector a
     -> Bool
null Empty = True
null _     = False

||| Return the size of a vector. O(1)
export
length :  RRBVector a
       -> Nat
length Empty        = 0
length (Root s _ _) = s

--------------------------------------------------------------------------------
--          Indexing
--------------------------------------------------------------------------------

||| The element at the index or Nothing if the index is out of range. O(log n)
export
lookup :  Nat
       -> RRBVector a
       -> Maybe a
lookup _ Empty               = Nothing
lookup i (Root size sh tree) =
  case compare i 0 of
    LT =>
      Nothing -- index out of range
    GT =>
      case compare i size of
        EQ =>
          Nothing -- index out of range
        GT =>
          Nothing -- index out of range
        LT =>
          Just $ lookupTree i sh tree
    EQ =>
      case compare i size of
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
    lookupTree i sh (Balanced arr)         =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.lookup: can't convert Nat to Fin"
        Just i' =>
          assert_total $ lookupTree i (down sh) (at arr.arr i')
    lookupTree i sh (Unbalanced arr sizes) =
      let (idx, subidx) = relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               assert_total $ idris_crash "Data.RRBVector.lookup: can't convert Nat to Fin"
             Just idx' =>
               assert_total $ lookupTree subidx (down sh) (at arr.arr idx')
    lookupTree i _ (Leaf arr)              =
      let i' = integerToNat ((natToInteger i) .&. (natToInteger blockmask))
        in case tryNatToFin i' of
             Nothing =>
               assert_total $ idris_crash "Data.RRBVector.lookup: can't convert Nat to Fin"
             Just i'' =>
               at arr.arr i''

||| The element at the index.
||| Calls 'idris_crash' if the index is out of range. O(log n)
export
index :  Nat
      -> RRBVector a
      -> a
index i = fromMaybe (assert_total $ idris_crash "Data.RRBVector.index: index out of range") . lookup i

||| A flipped version of lookup. O(log n)
export
(!?) :  RRBVector a
     -> Nat
     -> Maybe a
(!?) = flip lookup

||| A flipped version of index. O(log n)
export
(!!) :  RRBVector a
     -> Nat
     -> a
(!!) = flip index

||| Update the element at the index with a new element.
||| If the index is out of range, the original vector is returned. O (log n)
export
update :  Nat
       -> a
       -> RRBVector a
       -> RRBVector a
update _ _ Empty                 = Empty
update i x v@(Root size sh tree) =
  case compare i 0 of
    LT =>
      v -- index out of range
    GT =>
      case compare i size of
        EQ =>
          v -- index out of range
        GT =>
          v -- index out of range
        LT =>
          Root size sh (updateTree i sh tree)
    EQ =>
      case compare i size of
        EQ =>
          v -- index out of range
        GT =>
          v -- index out of range
        LT =>
          Root size sh (updateTree i sh tree)
  where
    updateTree :  Nat
               -> Nat
               -> Tree a
               -> Tree a
    updateTree i sh (Balanced arr)         =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.update: can't convert Nat to Fin"
        Just i' =>
          assert_total $ Balanced (A arr.size (updateAt i' (updateTree i (down sh)) arr.arr))
    updateTree i sh (Unbalanced arr sizes) =
      let (idx, subidx) = relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               assert_total $ idris_crash "Data.RRBVector.update: can't convert Nat to Fin"
             Just idx' =>
               assert_total $ Unbalanced (A arr.size (updateAt idx' (updateTree subidx (down sh)) arr.arr)) sizes
    updateTree i _ (Leaf arr)              =
      let i' = integerToNat ((natToInteger i) .&. (natToInteger blockmask))
        in case tryNatToFin i' of
             Nothing =>
               assert_total $ idris_crash "Data.RRBVector.update: can't convert Nat to Fin"
             Just i'' =>
               Leaf (A arr.size (setAt i'' x arr.arr))

||| Adjust the element at the index by applying the function to it.
||| If the index is out of range, the original vector is returned. O(log n)
export
adjust :  Nat
       -> (a -> a)
       -> RRBVector a
       -> RRBVector a
adjust _ _ Empty                 = Empty
adjust i f v@(Root size sh tree) =
  case compare i 0 of
    LT =>
      v -- index out of range
    GT =>
      case compare i size of
        EQ =>
          v -- index out of range
        GT =>
          v -- index out of range
        LT =>
          Root size sh (adjustTree i sh tree)
    EQ =>
      case compare i size of
        EQ =>
          v -- index out of range
        GT =>
          v -- index out of range
        LT =>
          Root size sh (adjustTree i sh tree)
  where
    adjustTree :  Nat
               -> Nat
               -> Tree a
               -> Tree a
    adjustTree i sh (Balanced arr)         =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.adjust: can't convert Nat to Fin"
        Just i' =>
          assert_total $ Balanced (A arr.size (updateAt i' (adjustTree i (down sh)) arr.arr))
    adjustTree i sh (Unbalanced arr sizes) =
      let (idx, subidx) = relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               assert_total $ idris_crash "Data.RRBVector.adjust: can't convert Nat to Fin"
             Just idx' =>
               assert_total $ Unbalanced (A arr.size (updateAt idx' (adjustTree subidx (down sh)) arr.arr)) sizes
    adjustTree i _ (Leaf arr)              =
      let i' = integerToNat ((natToInteger i) .&. (natToInteger blockmask))
        in case tryNatToFin i' of
             Nothing =>
               assert_total $ idris_crash "Data.RRBVector.adjust: can't convert Nat to Fin"
             Just i'' =>
               Leaf (A arr.size (updateAt i'' f arr.arr))

private
normalize :  RRBVector a
          -> RRBVector a
normalize v@(Root size sh (Balanced arr))     =
  case compare arr.size 1 of
    LT =>
      v
    EQ =>
      case tryNatToFin 0 of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.normalize: can't convert Nat to Fin"
        Just i  =>
          assert_total $ normalize $ Root size (down sh) (at arr.arr i)
    GT =>
      v
normalize v@(Root size sh (Unbalanced arr _)) =
  case compare arr.size 1 of
    LT =>
      v
    EQ =>
      case tryNatToFin 0 of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.normalize: can't convert Nat to Fin"
        Just i  =>
          assert_total $ normalize $ Root size (down sh) (at arr.arr i)
    GT =>
      v
normalize v                                   =
  v

||| The initial i is n - 1 (the index of the last element in the new tree).
private
takeTree :  Nat
         -> Shift
         -> Tree a
         -> Tree a
takeTree i sh (Balanced arr) with (radixIndex i sh) | ((plus (radixIndex i sh) 1) <= arr.size) proof eq
  _ | i' | True  =
    case tryNatToFin i' of
      Nothing =>
        assert_total $ idris_crash "Data.RRBVector.takeTree: can't convert Nat to Fin"
      Just i'' =>
        let newarr = force $ take (plus (radixIndex i sh) 1) arr.arr @{lteOpReflectsLTE _ _ eq}
          in assert_total $ Balanced (A (plus (radixIndex i sh) 1) (updateAt i'' (takeTree i (down sh)) newarr))
  _ | _  | False =
    assert_total $ idris_crash "Data.RRBVector.takeTree: index out of bounds"
takeTree i sh (Unbalanced arr sizes) with (relaxedRadixIndex sizes i sh) | ((plus (fst (relaxedRadixIndex sizes i sh)) 1) <= arr.size) proof eq
  _ | (idx, subidx) | True  =
    case tryNatToFin idx of
      Nothing   =>
        assert_total $ idris_crash "Data.RRBVector.takeTree: can't convert Nat to Fin"
      Just idx' =>
        let newarr = force $ take (plus (fst (relaxedRadixIndex sizes i sh)) 1) arr.arr @{lteOpReflectsLTE _ _ eq}
          in assert_total $ computeSizes sh (A (plus (fst (relaxedRadixIndex sizes i sh)) 1) (updateAt idx' (takeTree subidx (down sh)) newarr))
  _ | _             | False =
    assert_total $ idris_crash "Data.RRBVector.takeTree: index out of bounds"
takeTree i _ (Leaf arr) with (integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1) <= arr.size) proof eq
  _ | True  =
    let newarr = force $ take (integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1)) arr.arr @{lteOpReflectsLTE _ _ eq}
      in Leaf (A (integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1)) newarr)
  _ | False =
    assert_total $ idris_crash "Data.RRBVector.takeTree: index out of bounds"

private
dropTree :  Nat
         -> Shift
         -> Tree a
         -> Tree a
dropTree n sh (Balanced arr) =
  case tryNatToFin 0 of
    Nothing   =>
      assert_total $ idris_crash "Data.RRBVector.dropTree: can't convert Nat to Fin"
    Just zero =>
      let newarr = force $ drop (radixIndex n sh) arr.arr
        in assert_total $ computeSizes sh (A (minus arr.size (radixIndex n sh)) (updateAt zero (dropTree n (down sh)) newarr))
dropTree n sh (Unbalanced arr sizes) =
  case tryNatToFin 0 of
    Nothing   =>
      assert_total $ idris_crash "Data.RRBVector.dropTree: can't convert Nat to Fin"
    Just zero =>
      let newarr = force $ drop (fst $ relaxedRadixIndex sizes n sh) arr.arr
        in assert_total $ computeSizes sh (A (minus arr.size (fst $ relaxedRadixIndex sizes n sh)) (updateAt zero (dropTree (snd $ relaxedRadixIndex sizes n sh) (down sh)) newarr))
dropTree n _  (Leaf arr) =
  let n      = integerToNat ((natToInteger n) .&. (natToInteger blockmask))
      newarr = force $ drop n arr.arr
    in Leaf (A (minus arr.size n) newarr)

||| The first i elements of the vector.
||| If the vector contains less than or equal to i elements, the whole vector is returned. O(log n)
export
take :  Nat
     -> RRBVector a
     -> RRBVector a
take _ Empty                 = Empty
take n v@(Root size sh tree) =
  case compare n 0 of
    LT =>
      empty
    EQ =>
      empty
    GT =>
      case compare n size of
        LT =>
          normalize $ Root n sh (takeTree (minus n 1) sh tree)
        EQ =>
          v
        GT =>
          v

||| The vector without the first i elements.
||| If the vector contains less than or equal to i elements, the empty vector is returned. O(log n)
export
drop :  Nat
     -> RRBVector a
     -> RRBVector a
drop _ Empty                 = Empty
drop n v@(Root size sh tree) =
  case compare n 0 of
    LT =>
      v
    EQ =>
      v
    GT =>
      case compare n size of
        LT =>
          normalize $ Root (minus size n) sh (dropTree n sh tree)
        EQ =>
          empty
        GT =>
          empty

||| Split the vector at the given index. O(log n)
export
splitAt :  Nat
        -> RRBVector a
        -> (RRBVector a, RRBVector a)
splitAt _ Empty                 = (Empty, Empty)
splitAt n v@(Root size sh tree) =
  case compare n 0 of
    LT =>
      (empty, v)
    EQ =>
      (empty, v)
    GT =>
      case compare n size of
        LT =>
          let left  = normalize $ Root n sh (takeTree (minus n 1) sh tree)
              right = normalize $ Root (minus size n) sh (dropTree n sh tree)
            in (left, right)
        EQ =>
          (v, empty)
        GT =>
          (v, empty)

--------------------------------------------------------------------------------
--          Deconstruction
--------------------------------------------------------------------------------

||| The first element and the vector without the first element, or 'Nothing' if the vector is empty. O(log n)
export
viewl :  RRBVector a
      -> Maybe (a, RRBVector a)
viewl Empty             = Nothing
viewl v@(Root _ _ tree) =
  let tail = drop 1 v
    in Just (headTree tree, tail)
  where
    headTree : Tree a -> a
    headTree (Balanced arr)     =
      case tryNatToFin 0 of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.viewl: can't convert Nat to Fin"
        Just zero =>
          assert_total $ headTree (at arr.arr zero)
    headTree (Unbalanced arr _) =
      case tryNatToFin 0 of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.viewl: can't convert Nat to Fin"
        Just zero =>
          assert_total $ headTree (at arr.arr zero)
    headTree (Leaf arr)         =
      case tryNatToFin 0 of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.viewl: can't convert Nat to Fin"
        Just zero =>
          at arr.arr zero

||| The vector without the last element and the last element, or 'Nothing' if the vector is empty. O(log n)
export
viewr :  RRBVector a
      -> Maybe (RRBVector a, a)
viewr Empty                = Nothing
viewr v@(Root size _ tree) =
  let init = take (minus size 1) v
    in Just (init, lastTree tree)
  where
    lastTree : Tree a -> a
    lastTree (Balanced arr)     =
      case tryNatToFin (minus size 1) of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.viewr: can't convert Nat to Fin"
        Just last =>
          assert_total $ lastTree (at arr.arr last)
    lastTree (Unbalanced arr _) =
      case tryNatToFin (minus size 1) of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.viewr: can't convert Nat to Fin"
        Just last =>
          assert_total $ lastTree (at arr.arr last)
    lastTree (Leaf arr)         =
      case tryNatToFin (minus size 1) of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.viewr: can't convert Nat to Fin"
        Just last =>
          at arr.arr last

--------------------------------------------------------------------------------
--          Transformation
--------------------------------------------------------------------------------

||| Apply the function to every element. O(n)
export
map :  (a -> b)
    -> RRBVector a
    -> RRBVector b
map _ Empty               = Empty
map f (Root size sh tree) = Root size sh (mapTree tree)
  where
    mapTree : Tree a -> Tree b
    mapTree (Balanced arr)         =
      assert_total $ Balanced (map mapTree arr)
    mapTree (Unbalanced arr sizes) =
      assert_total $ Unbalanced (map mapTree arr) sizes
    mapTree (Leaf arr)             =
      Leaf (map f arr)

||| Reverse the vector. O(n)
export
reverse :  RRBVector a
        -> RRBVector a
reverse v =
  case compare (length v) 1 of
    LT =>
      v
    EQ =>
      v
    GT =>
      case fromList $ toList v of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.reverse: can't convert to List1"
        Just v' =>
          fromList $ forget $ reverse v'

||| Take two vectors and return a vector of corresponding pairs.
||| If one input is longer, excess elements are discarded from the right end. O(min(n1,n2))
export
zip :  RRBVector a
    -> RRBVector b
    -> RRBVector (a, b)
zip v1 v2 =
  case fromList $ toList v1 of
    Nothing  =>
      assert_total $ idris_crash "Data.RRBVector.zip: can't convert to List1"
    Just v1' =>
      case fromList $ toList v2 of
        Nothing  =>
          assert_total $ idris_crash "Data.RRBVector.zip: can't convert to List1"
        Just v2' =>
          fromList $ forget $ zip v1' v2'

--------------------------------------------------------------------------------
--          Concatenation
--------------------------------------------------------------------------------

||| Create a new tree with shift sh.
private
newBranch :  a
          -> Shift
          -> Tree a
newBranch x 0  = Leaf (singleton x)
newBranch x sh = assert_total $ Balanced (singleton $ newBranch x (down sh))

||| Add an element to the left end of the vector. O(log n)
export
(<|) :  a
     -> RRBVector a
     -> RRBVector a
x <| Empty             = singleton x
x <| Root size sh tree =
  case compare insertshift sh of
    LT =>
      Root (plus size 1) sh (consTree sh tree)
    EQ =>
      Root (plus size 1) sh (consTree sh tree)
    GT =>
      let new = A 2 $ array $ fromList [(newBranch x sh), tree]
        in Root (plus size 1) insertshift (computeSizes insertshift new)
  where
    -- compute the shift at which the new branch needs to be inserted (0 means there is space in the leaf)
    -- the size is computed for efficient calculation of the shift in a balanced subtree
    computeShift :  Nat
                 -> Nat
                 -> Nat
                 -> Tree a
                 -> Nat
    computeShift sz sh min (Balanced _)          =
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
    computeShift _ sh min (Unbalanced arr sizes) =
      let sz'     = case tryNatToFin 0 of
                      Nothing   =>
                        assert_total $ idris_crash "Data.RRBVector.(<|).computeShift.Unbalanced: can't convert Nat to Fin"
                      Just zero =>
                        at sizes.arr zero -- the size of the first subtree
          newtree = case tryNatToFin 0 of
                      Nothing   =>
                        assert_total $ idris_crash "Data.RRBVector.(<|).computeShift.Unbalanced: can't convert Nat to Fin"
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
    computeShift _ _ min (Leaf arr)              =
      case compare arr.size blocksize of
        LT =>
          0
        EQ =>
          min
        GT =>
          min
    insertshift : Nat
    insertshift = computeShift size sh (up sh) tree
    consTree :  Nat
             -> Tree a
             -> Tree a
    consTree sh (Balanced arr)     =
      case compare sh insertshift of
        LT =>
          case tryNatToFin 0 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.(<|).consTree.Balanced: can't convert Nat to Fin"
            Just zero =>
              assert_total $ computeSizes sh (A arr.size $ updateAt zero (consTree (down sh)) arr.arr)
        EQ =>
          computeSizes sh (A (S arr.size) (append (fill 1 (newBranch x (down sh))) arr.arr))
        GT =>
          case tryNatToFin 0 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.(<|).consTree.Balanced: can't convert Nat to Fin"
            Just zero =>
              assert_total $ computeSizes sh (A arr.size $ updateAt zero (consTree (down sh)) arr.arr)
    consTree sh (Unbalanced arr _) =
      case compare sh insertshift of
        LT =>
          case tryNatToFin 0 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.(<|).consTree.Unbalanced: can't convert Nat to Fin"
            Just zero =>
              assert_total $ computeSizes sh (A arr.size $ updateAt zero (consTree (down sh)) arr.arr)
        EQ =>
          computeSizes sh (A (S arr.size) (append (fill 1 (newBranch x (down sh))) arr.arr))
        GT =>
          case tryNatToFin 0 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.(<|).consTree.Unbalanced: can't convert Nat to Fin"
            Just zero =>
              assert_total $ computeSizes sh (A arr.size $ updateAt zero (consTree (down sh)) arr.arr)
    consTree _ (Leaf arr)          =
      Leaf (A (S arr.size) (append (fill 1 x) arr.arr))

||| Add an element to the right end of the vector. O(log n)
export
(|>) :  RRBVector a
     -> a
     -> RRBVector a
Empty             |> x = singleton x
Root size sh tree |> x =
  case compare insertshift sh of
    LT =>
      Root (plus size 1) sh (snocTree sh tree)
    EQ =>
      Root (plus size 1) sh (snocTree sh tree)
    GT =>
      let new = A 2 $ array $ fromList [tree,(newBranch x sh)]
        in Root (plus size 1) insertshift (computeSizes insertshift new)
  where
    -- compute the shift at which the new branch needs to be inserted (0 means there is space in the leaf)
    -- the size is computed for efficient calculation of the shift in a balanced subtree
    computeShift :  Nat
                 -> Nat
                 -> Nat
                 -> Tree a
                 -> Nat
    computeShift sz sh min (Balanced _)          =
      -- @sz - 1@ is the index of the last element
      let newshift = mult (countTrailingZeros sz `div` blockshift) blockshift
        in case compare newshift sh of
             LT =>
               newshift
             EQ =>
               newshift
             GT =>
               min
    computeShift _ sh min (Unbalanced arr sizes) =
      let lastidx = minus arr.size 1
          sz'     = case tryNatToFin lastidx of
                      Nothing       =>
                        assert_total $ idris_crash "Data.RRBVector.(|>).computeShift.Unbalanced: can't convert Nat to Fin"
                      Just lastidx' =>
                        case tryNatToFin $ minus lastidx 1 of
                          Nothing        =>
                            assert_total $ idris_crash "Data.RRBVector.(|>).computeShift.Unbalanced: can't convert Nat to Fin"
                          Just lastidx'' =>
                            minus (at sizes.arr lastidx') (at sizes.arr lastidx'')
          newtree = case tryNatToFin lastidx of
                      Nothing       =>
                        assert_total $ idris_crash "Data.RRBVector.(|>).computeShift.Unbalanced: can't convert Nat to Fin"
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
    computeShift _ _ min (Leaf arr)              =
      case compare arr.size blocksize of
        LT =>
          0
        EQ =>
          min
        GT =>
          min
    insertshift : Nat
    insertshift = computeShift size sh (up sh) tree
    snocTree :  Nat
             -> Tree a
             -> Tree a
    snocTree sh (Balanced arr) =
      case compare sh insertshift of
        LT =>
          case tryNatToFin $ minus arr.size 1 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.(|>).snocTree.Balanced: can't convert Nat to Fin"
            Just lastidx =>
              assert_total $ Balanced (A arr.size $ updateAt lastidx (snocTree (down sh)) arr.arr)
        EQ =>
          Balanced (A (plus arr.size 1) (append arr.arr (fill 1 (newBranch x (down sh))))) -- the current subtree is fully balanced
        GT =>
          case tryNatToFin $ minus arr.size 1 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.(|>).snocTree.Balanced: can't convert Nat to Fin"
            Just lastidx =>
              assert_total $ Balanced (A arr.size $ updateAt lastidx (snocTree (down sh)) arr.arr)
    snocTree sh (Unbalanced arr sizes) =
      case compare sh insertshift of
        LT =>
          case tryNatToFin $ minus arr.size 1 of
            Nothing       =>
              assert_total $ idris_crash "Data.RRBVector.(|>).snocTree.Unbalanced: can't convert Nat to Fin"
            Just lastidxa =>
              case tryNatToFin $ minus sizes.size 1 of
                Nothing       =>
                  assert_total $ idris_crash "Data.RRBVector.(|>).snocTree.Unbalanced: can't convert Nat to Fin"
                Just lastidxs =>
                  let lastsize = plus (at sizes.arr lastidxs) 1
                    in assert_total $ Unbalanced (A arr.size (updateAt lastidxa (snocTree (down sh)) arr.arr))
                                                 (A sizes.size (setAt lastidxs lastsize sizes.arr))
        EQ =>
          case tryNatToFin $ minus sizes.size 1 of
            Nothing      =>
              assert_total $ idris_crash "Data.RRBVector.(|>).snocTree.Unbalanced: can't convert Nat to Fin"
            Just lastidx =>
              let lastsize = plus (at sizes.arr lastidx) 1
                in assert_total $ Unbalanced (A (plus arr.size 1) (append arr.arr (fill 1 (newBranch x (down sh)))))
                                             (A (plus sizes.size 1) (append sizes.arr (fill 1 lastsize)))
        GT =>
          case tryNatToFin $ minus arr.size 1 of
            Nothing       =>
              assert_total $ idris_crash "Data.RRBVector.(|>).snocTree.Unbalanced: can't convert Nat to Fin"
            Just lastidxa =>
              case tryNatToFin $ minus sizes.size 1 of
                Nothing       =>
                  assert_total $ idris_crash "Data.RRBVector.(|>).snocTree.Unbalanced: can't convert Nat to Fin"
                Just lastidxs =>
                  let lastsize = plus (at sizes.arr lastidxs) 1
                    in assert_total $ Unbalanced (A arr.size (updateAt lastidxa (snocTree (down sh)) arr.arr))
                                                 (A sizes.size (setAt lastidxs lastsize sizes.arr))
    snocTree _ (Leaf arr) = Leaf (A (plus arr.size 1) (append arr.arr (fill 1 x)))

||| Concatenates two vectors. O(log(max(n1,n2)))
export
(><) :  RRBVector a
     -> RRBVector a
     -> RRBVector a
Empty                >< v                    = v
v                    >< Empty                = v
Root size1 sh1 tree1 >< Root size2 sh2 tree2 =
  let upmaxshift = case compare sh1 sh2 of
                     LT =>
                       up sh2
                     EQ =>
                       up sh1
                     GT =>
                       up sh1
      newarr     = mergeTrees tree1 sh1 tree2 sh2
    in normalize $ Root (plus size1 size2) upmaxshift (computeSizes upmaxshift newarr)
  where
    viewlArr : Array (Tree a) -> (Tree a, Array (Tree a))
    viewlArr arr =
      case tryNatToFin 0 of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.(><).viewlArr: can't convert Nat to Fin"
        Just zero =>
          (at arr.arr zero, drop 1 arr)
    viewrArr : Array (Tree b) -> (Array (Tree b), Tree b)
    viewrArr arr =
      case tryNatToFin $ minus arr.size 1 of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.(><).viewrArr: can't convert Nat to Fin"
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
                     -> (Array a -> Tree a)
                     -> Array (Tree a)
    mergeRebalance'' sh left center right extract construct =
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
          assert_total $ mergeRebalance'' sh left center right (\(Leaf arr) => arr) Leaf
        GT =>
          assert_total $ mergeRebalance' sh left center right treeToArray (computeSizes (down sh))
    mergeTrees :  Tree a
               -> Nat
               -> Tree a
               -> Nat
               -> Array (Tree a)
    mergeTrees tree1@(Leaf arr1) _   tree2@(Leaf arr2) _   =
      case compare arr1.size blocksize of
        LT =>
          let arr' = A (plus arr1.size arr2.size) (append arr1.arr arr2.arr)
            in case compare arr'.size blocksize of
                 LT =>
                   singleton $ Leaf arr'
                 EQ =>
                   singleton $ Leaf arr'
                 GT =>
                   let (left, right) = (take blocksize arr',drop blocksize arr')
                       lefttree      = Leaf left
                       righttree     = Leaf right
                     in A 2 $ fromPairs 2 lefttree [(1,righttree)]
        EQ =>
          A 2 $ fromPairs 2 tree1 [(1,tree2)]
        GT =>
          let arr' = A (plus arr1.size arr2.size) (append arr1.arr arr2.arr)
            in case compare arr'.size blocksize of
                 LT =>
                   singleton $ Leaf arr'
                 EQ =>
                   singleton $ Leaf arr'
                 GT =>
                   let (left, right) = (take blocksize arr',drop blocksize arr')
                       lefttree      = Leaf left
                       righttree     = Leaf right
                     in A 2 $ fromPairs 2 lefttree [(1,righttree)]
    mergeTrees tree1             sh1 tree2             sh2 =
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
insertAt :  Nat
         -> a
         -> RRBVector a
         -> RRBVector a
insertAt i x v =
  let (left, right) = splitAt i v
    in (left |> x) >< right

||| Delete the element at the given index.
||| If the index is out of range, return the original vector. O(log n)
export
deleteAt :  Nat
         -> RRBVector a
         -> RRBVector a
deleteAt i v =
  let (left, right) = splitAt (plus i 1) v
    in take i left >< right

--------------------------------------------------------------------------------
--          Show Utilities (RRB-Vector)
--------------------------------------------------------------------------------

||| Show the full representation of the vector.
export
showRRBVectorRep :  Show a
                 => Show (Tree a)
                 => Show (RRBVector a)
                 => RRBVector a
                 -> String
showRRBVectorRep Empty            =
  ""
showRRBVectorRep (Root size sh t) =
  "RRBVector "    ++
  "{ "            ++
  "Size = "       ++
  (show size)     ++
  ", Shift = "    ++
  (show sh)       ++
  ", Tree = "     ++
  (showTreeRep t) ++
  "}"

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Eq a => Eq (RRBVector a) where
  xs == ys = length xs == length ys && Data.RRBVector.toList xs == Data.RRBVector.toList ys

export
Ord a => Ord (RRBVector a) where
  compare xs ys = compare (Data.RRBVector.toList xs) (Data.RRBVector.toList ys)

export
Functor RRBVector where
  map f v = map f v

export
Foldable RRBVector where
  foldl f z           = Data.RRBVector.foldl f z
  foldr f z           = Data.RRBVector.foldr f z
  null                = null

export
Applicative RRBVector where
  pure      = singleton
  fs <*> xs = Data.RRBVector.foldl (\acc, f => acc >< map f xs) empty fs

export
Semigroup (RRBVector a) where
  (<+>) = (><)

export
Semigroup (RRBVector a) => Monoid (RRBVector a) where
  neutral = empty

export
Monad RRBVector where
  xs >>= f = Data.RRBVector.foldl (\acc, x => acc >< f x) empty xs
