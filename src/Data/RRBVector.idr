||| Relaxed Radix Balanced Vectors (RRB-Vectors)
module Data.RRBVector

import public Data.RRBVector.Internal

import Data.Array
import Data.Array.Core
import Data.Array.Index
import Data.Array.Indexed
import Data.Bits
import Data.Maybe
import Data.Vect
import Syntax.T1

%hide Prelude.null
%hide Prelude.toList

%default total

--------------------------------------------------------------------------------
--          Creating RRB-Vectors
--------------------------------------------------------------------------------

||| The empty vector. O(1)
export
empty : RRBVector a
empty = Empty

||| A vector with a single element. O(1)
export
singleton : a -> RRBVector a
singleton x = Root 1 0 (Leaf $ A 1 $ fill 1 x)

||| Create a new vector from a list. O(n)
partial
export
fromList : List a -> RRBVector a
fromList []  = Empty
fromList [x] = singleton x
fromList xs  =
  case nodes Leaf xs of
    [tree] =>
      Root (treeSize 0 tree) 0 tree -- tree is a single leaf
    xs'    =>
      iterateNodes blockshift xs'
  where
    nodes : (Array a -> Tree a) -> List a -> List (Tree a)
    nodes f trees =
      let (trees', rest) = unsafeCreate blocksize (go 0 blocksize f trees)
        in case rest of
             []    =>
               [trees']
             rest' =>
               (trees' :: nodes f rest)
      where
        go :  (cur,n : Nat)
           -> (Array a -> Tree a)
           -> List a
           -> FromMArray n a (Tree a,List a)
        go cur n f []        r = T1.do
          res <- freeze r
          pure $ (f $ A n res,[])
        go cur n f (x :: xs) r =
          case cur == n of
            True  => T1.do
              res <- freeze r
              pure $ (f $ A n res, x :: xs)
            False =>
              case tryNatToFin cur of
                Nothing   =>
                  assert_total $ idris_crash "Data.RRBVector.fromList.node: can't convert Nat to Fin"
                Just cur' => T1.do
                  set r cur' x
                  go (S cur) n f xs r
    nodes' : (Array (Tree a) -> Tree a) -> List (Tree a) -> List (Tree a)
    nodes' f trees =
      let (trees', rest) = unsafeCreate blocksize (go 0 blocksize f trees)
        in case rest of
             []    =>
               [trees']
             rest' =>
               (trees' :: nodes' f rest)
      where
        go :  (cur,n : Nat)
           -> (Array (Tree a) -> Tree a)
           -> List (Tree a)
           -> FromMArray n (Tree a) (Tree a,List (Tree a))
        go cur n f []        r = T1.do
          res <- freeze r
          pure $ (f $ A n res,[])
        go cur n f (x :: xs) r =
          case cur == n of
            True  => T1.do
              res <- freeze r
              pure $ (f $ A n res, x :: xs)
            False =>
              case tryNatToFin cur of
                Nothing   =>
                  assert_total $ idris_crash "Data.RRBVector.fromList.node': can't convert Nat to Fin"
                Just cur' => T1.do
                  set r cur' x
                  go (S cur) n f xs r
    iterateNodes : Nat -> List (Tree a) -> RRBVector a
    iterateNodes sh trees =
      case nodes' Balanced trees of
        [tree] => Root (treeSize sh tree) sh tree
        trees' => iterateNodes (up sh) trees'

||| Creates a vector of length n with every element set to x. O(log n)
partial
export
replicate : Nat -> a -> RRBVector a
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
          let size' = the Nat (cast ((the Int (cast (minus n 1))) .&. (the Int (cast (plus blockmask 1)))))
            in iterateNodes blockshift
                            (Leaf $ A blocksize $ fill blocksize x)
                            (Leaf $ A size' $ fill size' x)
  where
    iterateNodes : Shift -> Tree a -> Tree a -> RRBVector a
    iterateNodes sh full rest =
      let subtreesm1  = shiftR (minus n 1) sh
          restsize    = the Nat (cast ((the Int (cast subtreesm1)) .&. (the Int (cast blockmask))))
          rest'       = Balanced $ A (plus restsize 1) $ append (fill restsize full) (fill 1 rest)
        in case compare subtreesm1 blocksize of
             LT =>
               Root n sh rest'
             EQ =>
               let full' = Balanced (A blocksize $ fill blocksize full)
                 in iterateNodes (up sh) full' rest'
             GT =>
               let full' = Balanced (A blocksize $ fill blocksize full)
                 in iterateNodes (up sh) full' rest'

--------------------------------------------------------------------------------
--          Folds
--------------------------------------------------------------------------------

partial
export
foldl : (b -> a -> b) -> b -> RRBVector a -> b
foldl f acc = go
  where
    foldlTree : b -> Tree a -> b
    foldlTree acc' (Balanced arr)     = foldl foldlTree acc' arr
    foldlTree acc' (Unbalanced arr _) = foldl foldlTree acc' arr
    foldlTree acc' (Leaf arr)         = foldl f acc' arr
    go : RRBVector a -> b
    go Empty           = acc
    go (Root _ _ tree) = foldlTree acc tree

partial
export
foldr : (a -> b -> b) -> b -> RRBVector a -> b
foldr f acc = go
  where
    foldrTree : Tree a -> b -> b
    foldrTree (Balanced arr) acc'     = foldr foldrTree acc' arr
    foldrTree (Unbalanced arr _) acc' = foldr foldrTree acc' arr
    foldrTree (Leaf arr) acc'         = foldr f acc' arr
    go : RRBVector a -> b
    go Empty           = acc
    go (Root _ _ tree) = foldrTree tree acc

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Is the vector empty? O(1)
export
null : RRBVector a -> Bool
null Empty = True
null _     = False

--------------------------------------------------------------------------------
--          Indexing
--------------------------------------------------------------------------------

||| The element at the index or Nothing if the index is out of range. O (log n)
partial
export
lookup : Nat -> RRBVector a -> Maybe a
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
    lookupTree : Nat -> Nat -> Tree a -> a
    lookupTree i sh (Balanced arr)         =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.lookup: can't convert Nat to Fin"
        Just i' =>
          lookupTree i (down sh) (at arr.arr i')
    lookupTree i sh (Unbalanced arr sizes) =
      let (idx, subidx) = relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               assert_total $ idris_crash "Data.RRBVector.lookup: can't convert Nat to Fin"
             Just idx' =>
               lookupTree subidx (down sh) (at arr.arr idx')
    lookupTree i _ (Leaf arr)              =
      let i' = the Nat (cast ((the Int (cast i)) .&. (the Int (cast blockmask))))
        in case tryNatToFin i' of
             Nothing =>
               assert_total $ idris_crash "Data.RRBVector.lookup: can't convert Nat to Fin"
             Just i'' =>
               at arr.arr i''

||| The element at the index.
||| Calls 'idris_crash' if the index is out of range. O(log n)
partial
export
index : Nat -> RRBVector a -> a
index i = fromMaybe (assert_total $ idris_crash "index out of range") . lookup i

||| A flipped version of lookup. O(log n)
partial
export
(!?) : RRBVector a -> Nat -> Maybe a
(!?) = flip lookup

||| A flipped version of index. O(log n)
partial
export
(!!) : RRBVector a -> Nat -> a
(!!) = flip index

||| Update the element at the index with a new element.
||| If the index is out of range, the original vector is returned. O (log n)
partial
export
update : Nat -> a -> RRBVector a -> RRBVector a
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
    updateTree : Nat -> Nat -> Tree a -> Tree a
    updateTree i sh (Balanced arr)         =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.update: can't convert Nat to Fin"
        Just i' =>
          Balanced (A arr.size (updateAt i' (updateTree i (down sh)) arr.arr))
    updateTree i sh (Unbalanced arr sizes) =
      let (idx, subidx) = relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               assert_total $ idris_crash "Data.RRBVector.update: can't convert Nat to Fin"
             Just idx' =>
               Unbalanced (A arr.size (updateAt idx' (updateTree subidx (down sh)) arr.arr)) sizes
    updateTree i _ (Leaf arr)              =
      let i' = the Nat (cast ((the Int (cast i)) .&. (the Int (cast blockmask))))
        in case tryNatToFin i' of
             Nothing =>
               assert_total $ idris_crash "Data.RRBVector.update: can't convert Nat to Fin"
             Just i'' =>
               Leaf (A arr.size (setAt i'' x arr.arr))

||| Adjust the element at the index by applying the function to it.
||| If the index is out of range, the original vector is returned. O(log n)
partial
export
adjust : Nat -> (a -> a) -> RRBVector a -> RRBVector a
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
    adjustTree : Nat -> Nat -> Tree a -> Tree a
    adjustTree i sh (Balanced arr)         =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.adjust: can't convert Nat to Fin"
        Just i' =>
          Balanced (A arr.size (updateAt i' (adjustTree i (down sh)) arr.arr))
    adjustTree i sh (Unbalanced arr sizes) =
      let (idx, subidx) = relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               assert_total $ idris_crash "Data.RRBVector.adjust: can't convert Nat to Fin"
             Just idx' =>
               Unbalanced (A arr.size (updateAt idx' (adjustTree subidx (down sh)) arr.arr)) sizes
    adjustTree i _ (Leaf arr)              =
      let i' = the Nat (cast ((the Int (cast i)) .&. (the Int (cast blockmask))))
        in case tryNatToFin i' of
             Nothing =>
               assert_total $ idris_crash "Data.RRBVector.adjust: can't convert Nat to Fin"
             Just i'' =>
               Leaf (A arr.size (updateAt i'' f arr.arr))

partial
private
normalize : RRBVector a -> RRBVector a
normalize v@(Root size sh (Balanced arr))     =
  case compare arr.size 1 of
    LT =>
      v
    EQ =>
      case tryNatToFin 0 of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.normalize: can't convert Nat to Fin"
        Just i  =>
          normalize $ Root size (down sh) (at arr.arr i)
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
          normalize $ Root size (down sh) (at arr.arr i)
    GT =>
      v
normalize v                                   =
  v

||| The initial i is n - 1 (the index of the last element in the new tree).
partial
private
takeTree : Nat -> Shift -> Tree a -> Tree a
takeTree i sh (Balanced arr) with (radixIndex i sh) | ((plus (radixIndex i sh) 1) <= arr.size) proof eq
  _ | i' | True  =
    case tryNatToFin i' of
      Nothing =>
        assert_total $ idris_crash "Data.RRBVector.takeTree: can't convert Nat to Fin"
      Just i'' =>
        let newarr = force $ take (plus (radixIndex i sh) 1) arr.arr @{lteOpReflectsLTE _ _ eq}
          in Balanced (A (plus (radixIndex i sh) 1) (updateAt i'' (takeTree i (down sh)) newarr))
  _ | _  | False =
    assert_total $ idris_crash "Data.RRBVector.takeTree: index out of bounds"
takeTree i sh (Unbalanced arr sizes) with (relaxedRadixIndex sizes i sh) | ((plus (fst (relaxedRadixIndex sizes i sh)) 1) <= arr.size) proof eq
  _ | (idx, subidx) | True  =
    case tryNatToFin idx of
      Nothing   =>
        assert_total $ idris_crash "Data.RRBVector.takeTree: can't convert Nat to Fin"
      Just idx' =>
        let newarr = force $ take (plus (fst (relaxedRadixIndex sizes i sh)) 1) arr.arr @{lteOpReflectsLTE _ _ eq}
          in computeSizes sh (A (plus (fst (relaxedRadixIndex sizes i sh)) 1) (updateAt idx' (takeTree subidx (down sh)) newarr))
  _ | _             | False =
    assert_total $ idris_crash "Data.RRBVector.takeTree: index out of bounds"
takeTree i _ (Leaf arr) with ((plus (the Nat (cast ((the Int (cast i)) .&. (the Int (cast blockmask))))) 1) <= arr.size) proof eq
  _ | True  =
    let newarr = force $ take (plus (the Nat (cast ((the Int (cast i)) .&. (the Int (cast blockmask))))) 1) arr.arr @{lteOpReflectsLTE _ _ eq}
      in Leaf (A (plus (the Nat (cast ((the Int (cast i)) .&. (the Int (cast blockmask))))) 1) newarr)
  _ | False =
    assert_total $ idris_crash "Data.RRBVector.takeTree: index out of bounds"

partial
private
dropTree : Nat -> Shift -> Tree a -> Tree a
dropTree n sh (Balanced arr) =
  case tryNatToFin 0 of
    Nothing   =>
      assert_total $ idris_crash "Data.RRBVector.dropTree: can't convert Nat to Fin"
    Just zero =>
      let newarr = force $ drop (radixIndex n sh) arr.arr
        in computeSizes sh (A (minus arr.size (radixIndex n sh)) (updateAt zero (dropTree n (down sh)) newarr))
dropTree n sh (Unbalanced arr sizes) =
  case tryNatToFin 0 of
    Nothing   =>
      assert_total $ idris_crash "Data.RRBVector.dropTree: can't convert Nat to Fin"
    Just zero =>
      let newarr = force $ drop (fst $ relaxedRadixIndex sizes n sh) arr.arr
        in computeSizes sh (A (minus arr.size (fst $ relaxedRadixIndex sizes n sh)) (updateAt zero (dropTree (snd $ relaxedRadixIndex sizes n sh) (down sh)) newarr))
dropTree n _  (Leaf arr) =
  let newarr = force $ drop (the Nat (cast ((the Int (cast n)) .&. (the Int (cast blockmask))))) arr.arr
    in Leaf (A (minus arr.size (the Nat (cast ((the Int (cast n)) .&. (the Int (cast blockmask)))))) newarr)

||| The first i elements of the vector.
||| If the vector contains less than or equal to i elements, the whole vector is returned. O(log n)
partial
export
take : Nat -> RRBVector a -> RRBVector a
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
partial
export
drop : Nat  -> RRBVector a -> RRBVector a
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
partial
export
splitAt : Nat -> RRBVector a -> (RRBVector a, RRBVector a)
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
partial
export
viewl : RRBVector a -> Maybe (a, RRBVector a)
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
          headTree (at arr.arr zero)
    headTree (Unbalanced arr _) =
      case tryNatToFin 0 of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.viewl: can't convert Nat to Fin"
        Just zero =>
          headTree (at arr.arr zero)
    headTree (Leaf arr)         =
      case tryNatToFin 0 of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.viewl: can't convert Nat to Fin"
        Just zero =>
          at arr.arr zero

||| The vector without the last element and the last element, or 'Nothing' if the vector is empty. O(log n)
partial
export
viewr : RRBVector a -> Maybe (RRBVector a, a)
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
          lastTree (at arr.arr last)
    lastTree (Unbalanced arr _) =
      case tryNatToFin (minus size 1) of
        Nothing   =>
          assert_total $ idris_crash "Data.RRBVector.viewr: can't convert Nat to Fin"
        Just last =>
          lastTree (at arr.arr last)
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
partial
export
map : (a -> b) -> RRBVector a -> RRBVector b
map _ Empty               = Empty
map f (Root size sh tree) = Root size sh (mapTree tree)
  where
    mapTree : Tree a -> Tree b
    mapTree (Balanced arr)         =
      Balanced (map mapTree arr)
    mapTree (Unbalanced arr sizes) =
      Unbalanced (map mapTree arr) sizes
    mapTree (Leaf arr)             =
      Leaf (map f arr)

--------------------------------------------------------------------------------
--          Concatenation
--------------------------------------------------------------------------------

||| Create a new tree with shift sh.
partial
private
newBranch : a -> Shift -> Tree a
newBranch x 0  = Leaf (singleton x)
newBranch x sh = Balanced (singleton $ newBranch x (down sh))

||| Add an element to the left end of the vector. O(log n)
partial
export
(<|) : a -> RRBVector a -> RRBVector a
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
    computeShift : Nat -> Nat -> Nat -> Tree a -> Nat
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
          hi       = shiftR (minus sz 1) hishift -- the length of the root node when normalizing minus 1
          newshift = case compare hi blockmask of
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
                        assert_total $ idris_crash "Data.RRBVector.(<|): can't convert Nat to Fin"
                      Just zero =>
                        at sizes.arr zero -- the size of the first subtree
          newtree = case tryNatToFin 0 of
                      Nothing   =>
                        assert_total $ idris_crash "Data.RRBVector.(<|): can't convert Nat to Fin"
                      Just zero =>
                        at arr.arr zero
          newmin  = case compare arr.size blocksize of
                      LT =>
                        sh
                      EQ =>
                        min
                      GT =>
                        min
        in computeShift sz' (down sh) newmin newtree
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
    consTree : Nat -> Tree a -> Tree a
    consTree sh (Balanced arr)     =
      case compare sh insertshift of
        LT =>
          case tryNatToFin 0 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.(<|): can't convert Nat to Fin"
            Just zero =>
              computeSizes sh (A arr.size $ updateAt zero (consTree (down sh)) arr.arr)
        EQ =>
          computeSizes sh (A (S (arr.size)) (append (fill 1 (newBranch x (down sh))) arr.arr))
        GT =>
          case tryNatToFin 0 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.(<|): can't convert Nat to Fin"
            Just zero =>
              computeSizes sh (A arr.size $ updateAt zero (consTree (down sh)) arr.arr)
    consTree sh (Unbalanced arr _) =
      case compare sh insertshift of
        LT =>
          case tryNatToFin 0 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.(<|): can't convert Nat to Fin"
            Just zero =>
              computeSizes sh (A arr.size $ updateAt zero (consTree (down sh)) arr.arr)
        EQ =>
          computeSizes sh (A (S (arr.size)) (append (fill 1 (newBranch x (down sh))) arr.arr))
        GT =>
          case tryNatToFin 0 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.(<|): can't convert Nat to Fin"
            Just zero =>
              computeSizes sh (A arr.size $ updateAt zero (consTree (down sh)) arr.arr)
    consTree _ (Leaf arr)          =
      Leaf (A (S (arr.size)) (append (fill 1 x) arr.arr))

{-
||| Add an element to the right end of the vector. O(log n)
(|>) : RRBVector a -> a -> RRBVector a
Empty             |> x = singleton x
Root size sh tree |> x =
  case compare insertShift sh of
    LT =>
      Root (plus size 1) insertShift (computeSizes insertShift ())
    EQ =>
      Root (plus size 1) insertShift (computeSizes insertShift ())
    GT =>
      


    | insertShift > sh = Root (size + 1) insertShift (computeSizes insertShift (A.from2 tree $! newBranch x sh))
    | otherwise = Root (size + 1) sh (snocTree sh tree)
  where
    snocTree sh (Balanced arr)
        | sh == insertShift = Balanced (A.snoc arr $! newBranch x (down sh)) -- the current subtree is fully balanced
        | otherwise = Balanced $ A.adjust' arr (length arr - 1) (snocTree (down sh))
    snocTree sh (Unbalanced arr sizes)
        | sh == insertShift = Unbalanced (A.snoc arr $! newBranch x (down sh)) newSizesSnoc
        | otherwise = Unbalanced (A.adjust' arr (length arr - 1) (snocTree (down sh))) newSizesAdjust
      where
        len = length arr
        -- snoc the last size + 1
        newSizesSnoc = runST $ do
            newArr <- newPrimArray (len + 1)
            copyPrimArray newArr 0 sizes 0 len
            let lastSize = indexPrimArray sizes (len - 1)
            writePrimArray newArr len (lastSize + 1)
            unsafeFreezePrimArray newArr
        -- adjust the last size with (+ 1)
        newSizesAdjust = runST $ do
            newArr <- newPrimArray len
            copyPrimArray newArr 0 sizes 0 len
            let lastSize = indexPrimArray sizes (len - 1)
            writePrimArray newArr (len - 1) (lastSize + 1)
            unsafeFreezePrimArray newArr
    snocTree _ (Leaf arr) = Leaf $ A.snoc arr x

    insertShift = computeShift size sh (up sh) tree

    -- compute the shift at which the new branch needs to be inserted (0 means there is space in the leaf)
    -- the size is computed for efficient calculation of the shift in a balanced subtree
    computeShift !sz !sh !min (Balanced _) =
        let newShift = (countTrailingZeros sz `div` blockShift) * blockShift
        in if newShift > sh then min else newShift
    computeShift _ sh min (Unbalanced arr sizes) =
        let lastIdx = length arr - 1
            sz' = indexPrimArray sizes lastIdx - indexPrimArray sizes (lastIdx - 1) -- the size of the last subtree
            newMin = if length arr < blockSize then sh else min
        in computeShift sz' (down sh) newMin (A.last arr)
    computeShift _ _ min (Leaf arr) = if length arr < blockSize then 0 else min
-}

{-
||| Concatenates two vectors. O(log max(n1,n2))
(><) : Vector a -> Vector a -> Vector a
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
    in normalize $ Root (size1 + size2) upmaxshift (computeSizes upmaxshift newarr)
  where
    mergeTrees : Tree a -> Nat -> Tree a -> Nat -> Array (Tree a)
    mergeTrees tree1@(Leaf arr1) _ tree2@(Leaf arr2) _ =
      case compare arr1.size blocksize of
        LT =>
          case compare (plus arr1.size arr2.size) blocksize of
            LT =>
              singleton $ Leaf (append arr1.arr arr2.arr)
            EQ =>
              singleton $ Leaf (append arr1.arr arr2.arr)
            GT =>
               
        EQ =>
          A 2 $ fromPairs 2 (Leaf tree1) [tree1,tree2]
        GT =>


        | length arr1 == blockSize = A.from2 tree1 tree2
        | length arr1 + length arr2 <= blockSize = A.singleton $! Leaf (arr1 A.++ arr2)
        | otherwise =
            let (left, right) = A.splitAt (arr1 A.++ arr2) blockSize -- 'A.splitAt' doesn't copy anything
                !leftTree = Leaf left
                !rightTree = Leaf right
            in A.from2 leftTree rightTree


    mergeTrees tree1 sh1 tree2 sh2 = case compare sh1 sh2 of
        LT ->
            let !right = treeToArray tree2
                (rightHead, rightTail) = viewlArr right
                merged = mergeTrees tree1 sh1 rightHead (down sh2)
            in mergeRebalance sh2 A.empty merged rightTail
        GT ->
            let !left = treeToArray tree1
                (leftInit, leftLast) = viewrArr left
                merged = mergeTrees leftLast (down sh1) tree2 sh2
            in mergeRebalance sh1 leftInit merged A.empty
        EQ ->
            let !left = treeToArray tree1
                !right = treeToArray tree2
                (leftInit, leftLast) = viewrArr left
                (rightHead, rightTail) = viewlArr right
                merged = mergeTrees leftLast (down sh1) rightHead (down sh2)
            in mergeRebalance sh1 leftInit merged rightTail
      where
        viewlArr arr = (A.head arr, A.drop arr 1)

        viewrArr arr = (A.take arr (length arr - 1), A.last arr)

    -- the type signature is necessary to compile
    mergeRebalance :: forall a. Shift -> A.Array (Tree a) -> A.Array (Tree a) -> A.Array (Tree a) -> A.Array (Tree a)
    mergeRebalance !sh !left !center !right
        | sh == blockShift = mergeRebalance' (\(Leaf arr) -> arr) Leaf
        | otherwise = mergeRebalance' treeToArray (computeSizes (down sh))
      where
        mergeRebalance' :: (Tree a -> A.Array t) -> (A.Array t -> Tree a) -> A.Array (Tree a)
        mergeRebalance' extract construct = runST $ do
            newRoot <- Buffer.new blockSize
            newSubtree <- Buffer.new blockSize
            newNode <- Buffer.new blockSize
            for_ (toList left ++ toList center ++ toList right) $ \subtree ->
                for_ (extract subtree) $ \x -> do
                    lenNode <- Buffer.size newNode
                    when (lenNode == blockSize) $ do
                        pushTo construct newNode newSubtree
                        lenSubtree <- Buffer.size newSubtree
                        when (lenSubtree == blockSize) $ pushTo (computeSizes sh) newSubtree newRoot
                    Buffer.push newNode x
            pushTo construct newNode newSubtree
            pushTo (computeSizes sh) newSubtree newRoot
            Buffer.get newRoot
        {-# INLINE mergeRebalance' #-}

        pushTo f from to = do
            result <- Buffer.get from
            Buffer.push to $! f result
        {-# INLINE pushTo #-}
-}

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

partial
export
Functor RRBVector where
  map f m = map f m

partial
export
Foldable RRBVector where
  foldl f z = Data.RRBVector.foldl f z
  foldr f z = Data.RRBVector.foldr f z
  null      = null
