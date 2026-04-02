||| Relaxed Radix Balanced Vectors (RRBVector)
module Data.RRBVector1.Unsized

import        Data.RRBVector.Unsized
import public Data.RRBVector.Unsized.Internal
import public Data.RRBVector1.Unsized.Internal

import Data.Array
import Data.Array.Core
import Data.Array.Index
import Data.Array.Indexed
import Data.Bits
import Data.Maybe
import Data.Linear.Ref1
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
empty : F1 s (RRBVector1 s a)
empty t =
  let rrbvector # t := ref1 Empty t
    in MkRRBVector1 rrbvector # t

||| A vector with a single element. O(1)
export
singleton :  a
          -> F1 s (RRBVector1 s a)
singleton x t =
  let rrbvector # t := ref1 (Root 1 0 (Leaf $ A 1 $ fill 1 x)) t
    in MkRRBVector1 rrbvector # t

||| Create a new vector from a list. O(n)
export
fromList :  List a
         -> F1 s (RRBVector1 s a)
fromList []  t = empty t
fromList [x] t = singleton x t
fromList xs  t =
  case nodes Leaf xs of
    [tree] =>
      let rrbvector # t := ref1 (Root (treeSize 0 tree) 0 tree) t -- tree is a single leaf
        in MkRRBVector1 rrbvector # t
    xs'    =>
      let rrbvector # t := ref1 (assert_smaller xs (iterateNodes blockshift xs')) t
        in MkRRBVector1 rrbvector # t
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
                  assert_total $ idris_crash "Data.RRBVector1.Unsized.fromList.node: can't convert Nat to Fin"
                Just cur' => T1.do
                  set r cur' x
                  go (S cur) n f xs r
    nodes' :  (Array (Tree a) -> Tree a)
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
                  assert_total $ idris_crash "Data.RRBVector1.Unsized.fromList.node': can't convert Nat to Fin"
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
          -> F1 s (RRBVector1 s a)
replicate n x t =
  case compare n 0 of
    LT =>
      empty t
    EQ =>
      empty t
    GT =>
      case compare n blocksize of
        LT =>
          let rrbvector # t := ref1 (Root n 0 (Leaf $ A n $ fill n x)) t
            in MkRRBVector1 rrbvector # t
        EQ =>
          let rrbvector # t := ref1 (Root n 0 (Leaf $ A n $ fill n x)) t
            in MkRRBVector1 rrbvector # t
        GT =>
          let size'         := integerToNat ((natToInteger $ minus n 1) .&. (natToInteger $ plus blockmask 1))
              rrbvector # t := ref1 (iterateNodes blockshift
                                                  (Leaf $ A blocksize $ fill blocksize x)
                                                  (Leaf $ A size' $ fill size' x)) t
            in MkRRBVector1 rrbvector # t
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
toList :  RRBVector1 s a
       -> F1 s (List a)
toList (MkRRBVector1 rrbvector) t =
  let rrbvector' # t := read1 rrbvector t
    in case rrbvector' of
         Empty         =>
           [] # t
         Root _ _ tree =>
           treeToList tree # t
  where
    treeToList :  Tree a
               -> List a
    treeToList (Balanced trees)     = assert_total $ concat (map treeToList (toList trees))
    treeToList (Unbalanced trees _) = assert_total $ concat (map treeToList (toList trees))
    treeToList (Leaf arr)           = toList arr

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Is the vector empty? O(1)
export
null :  RRBVector1 s a
     -> F1 s Bool
null (MkRRBVector1 rrbvector) t =
  let rrbvector' # t := read1 rrbvector t
    in case rrbvector' of
         Empty =>
           True # t
         _     =>
           False # t

||| Return the size of a vector. O(1)
export
length :  RRBVector1 s a
       -> F1 s Nat
length (MkRRBVector1 rrbvector) t =
  let rrbvector' # t := read1 rrbvector t
    in case rrbvector' of
         Empty      =>
           Z # t
         Root s _ _ =>
           s # t

--------------------------------------------------------------------------------
--          Indexing
--------------------------------------------------------------------------------

||| The element at the index or Nothing if the index is out of range. O(log n)
export
lookup :  Nat
       -> RRBVector1 s a
       -> F1 s (Maybe a)
lookup i (MkRRBVector1 rrbvector) t =
  let rrbvector' # t := read1 rrbvector t
    in case rrbvector' of
         Empty             =>
           Nothing # t
         Root size sh tree =>
           case compare i 0 of
             LT =>
               Nothing # t -- index out of range
             GT =>
               case compare i size of
                 EQ =>
                   Nothing # t -- index out of range
                 GT =>
                   Nothing # t -- index out of range
                 LT =>
                   (Just $ lookupTree i sh tree) # t
             EQ =>
               case compare i size of
                 EQ =>
                   Nothing # t -- index out of range
                 GT =>
                   Nothing # t-- index out of range
                 LT =>
                   (Just $ lookupTree i sh tree) # t
  where
    lookupTree :  Nat
               -> Nat
               -> Tree a
               -> a
    lookupTree i sh (Balanced arr)         =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector1.Unsized.lookup: can't convert Nat to Fin"
        Just i' =>
          assert_total $ lookupTree i (down sh) (at arr.arr i')
    lookupTree i sh (Unbalanced arr sizes) =
      let (idx, subidx) = relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               assert_total $ idris_crash "Data.RRBVector1.Unsized.lookup: can't convert Nat to Fin"
             Just idx' =>
               assert_total $ lookupTree subidx (down sh) (at arr.arr idx')
    lookupTree i _ (Leaf arr)              =
      let i' = integerToNat ((natToInteger i) .&. (natToInteger blockmask))
        in case tryNatToFin i' of
             Nothing =>
               assert_total $ idris_crash "Data.RRBVector1.Unsized.lookup: can't convert Nat to Fin"
             Just i'' =>
               at arr.arr i''

||| Update the element at the index with a new element.
||| If the index is out of range, the original vector is returned. O (log n)
export
update :  Nat
       -> a
       -> RRBVector1 s a
       -> F1' s
update i x (MkRRBVector1 rrbvector) t =
  casmod1 rrbvector (\rrbvector' =>
                      case rrbvector' of
                        Empty             =>
                          rrbvector'
                        Root size sh tree =>
                          case compare i 0 of
                            LT =>
                              rrbvector' -- index out of range
                            GT =>
                              case compare i size of
                                EQ =>
                                  rrbvector' -- index out of range
                                GT =>
                                  rrbvector' -- index out of range
                                LT =>
                                  Root size sh (updateTree i sh tree)
                            EQ =>
                              case compare i size of
                                EQ =>
                                  rrbvector' -- index out of range
                                GT =>
                                  rrbvector' -- index out of range
                                LT =>
                                  Root size sh (updateTree i sh tree)
                    ) t
  where
    updateTree :  Nat
               -> Nat
               -> Tree a
               -> Tree a
    updateTree i sh (Balanced arr)         =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector1.Unsized.update: can't convert Nat to Fin"
        Just i' =>
          assert_total $ Balanced (A arr.size (updateAt i' (updateTree i (down sh)) arr.arr))
    updateTree i sh (Unbalanced arr sizes) =
      let (idx, subidx) = relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               assert_total $ idris_crash "Data.RRBVector1.Unsized.update: can't convert Nat to Fin"
             Just idx' =>
               assert_total $ Unbalanced (A arr.size (updateAt idx' (updateTree subidx (down sh)) arr.arr)) sizes
    updateTree i _ (Leaf arr)              =
      let i' = integerToNat ((natToInteger i) .&. (natToInteger blockmask))
        in case tryNatToFin i' of
             Nothing =>
               assert_total $ idris_crash "Data.RRBVector1.Unsized.update: can't convert Nat to Fin"
             Just i'' =>
               Leaf (A arr.size (setAt i'' x arr.arr))

||| Adjust the element at the index by applying the function to it.
||| If the index is out of range, the original vector is returned. O(log n)
export
adjust :  Nat
       -> (a -> a)
       -> RRBVector1 s a
       -> F1' s
adjust i f (MkRRBVector1 rrbvector) t =
  casmod1 rrbvector (\rrbvector' =>
                      case rrbvector' of
                        Empty             =>
                          rrbvector'
                        Root size sh tree =>
                          case compare i 0 of
                            LT =>
                              rrbvector' -- index out of range
                            GT =>
                              case compare i size of
                                EQ =>
                                  rrbvector' -- index out of range
                                GT =>
                                  rrbvector' -- index out of range
                                LT =>
                                  Root size sh (adjustTree i sh tree)
                            EQ =>
                              case compare i size of
                                EQ =>
                                  rrbvector' -- index out of range
                                GT =>
                                  rrbvector' -- index out of range
                                LT =>
                                  Root size sh (adjustTree i sh tree)
                    ) t
  where
    adjustTree :  Nat
               -> Nat
               -> Tree a
               -> Tree a
    adjustTree i sh (Balanced arr)         =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector1.Unsized.adjust: can't convert Nat to Fin"
        Just i' =>
          assert_total $ Balanced (A arr.size (updateAt i' (adjustTree i (down sh)) arr.arr))
    adjustTree i sh (Unbalanced arr sizes) =
      let (idx, subidx) = relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               assert_total $ idris_crash "Data.RRBVector1.Unsized.adjust: can't convert Nat to Fin"
             Just idx' =>
               assert_total $ Unbalanced (A arr.size (updateAt idx' (adjustTree subidx (down sh)) arr.arr)) sizes
    adjustTree i _ (Leaf arr)              =
      let i' = integerToNat ((natToInteger i) .&. (natToInteger blockmask))
        in case tryNatToFin i' of
             Nothing =>
               assert_total $ idris_crash "Data.RRBVector1.Unsized.adjust: can't convert Nat to Fin"
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
          assert_total $ idris_crash "Data.RRBVector1.Unsized.normalize: can't convert Nat to Fin"
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
          assert_total $ idris_crash "Data.RRBVector1.Unsized.normalize: can't convert Nat to Fin"
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
        assert_total $ idris_crash "Data.RRBVector1.Unsized.takeTree: can't convert Nat to Fin"
      Just i'' =>
        let newarr = force $ take (plus (radixIndex i sh) 1) arr.arr @{lteOpReflectsLTE _ _ eq}
          in assert_total $ Balanced (A (plus (radixIndex i sh) 1) (updateAt i'' (takeTree i (down sh)) newarr))
  _ | _  | False =
    assert_total $ idris_crash "Data.RRBVector1.Unsized.takeTree: index out of bounds"
takeTree i sh (Unbalanced arr sizes) with (relaxedRadixIndex sizes i sh) | ((plus (fst (relaxedRadixIndex sizes i sh)) 1) <= arr.size) proof eq
  _ | (idx, subidx) | True  =
    case tryNatToFin idx of
      Nothing   =>
        assert_total $ idris_crash "Data.RRBVector1.Unsized.takeTree: can't convert Nat to Fin"
      Just idx' =>
        let newarr = force $ take (plus (fst (relaxedRadixIndex sizes i sh)) 1) arr.arr @{lteOpReflectsLTE _ _ eq}
          in assert_total $ computeSizes sh (A (plus (fst (relaxedRadixIndex sizes i sh)) 1) (updateAt idx' (takeTree subidx (down sh)) newarr))
  _ | _             | False =
    assert_total $ idris_crash "Data.RRBVector1.Unsized.takeTree: index out of bounds"
takeTree i _ (Leaf arr) with (integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1) <= arr.size) proof eq
  _ | True  =
    let newarr = force $ take (integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1)) arr.arr @{lteOpReflectsLTE _ _ eq}
      in Leaf (A (integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1)) newarr)
  _ | False =
    assert_total $ idris_crash "Data.RRBVector1.Unsized.takeTree: index out of bounds"

private
dropTree :  Nat
         -> Shift
         -> Tree a
         -> Tree a
dropTree n sh (Balanced arr) =
  case tryNatToFin 0 of
    Nothing   =>
      assert_total $ idris_crash "Data.RRBVector1.Unsized.dropTree: can't convert Nat to Fin"
    Just zero =>
      let newarr = force $ drop (radixIndex n sh) arr.arr
        in assert_total $ computeSizes sh (A (minus arr.size (radixIndex n sh)) (updateAt zero (dropTree n (down sh)) newarr))
dropTree n sh (Unbalanced arr sizes) =
  case tryNatToFin 0 of
    Nothing   =>
      assert_total $ idris_crash "Data.RRBVector1.Unsized.dropTree: can't convert Nat to Fin"
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
     -> RRBVector1 s a
     -> F1' s
take n (MkRRBVector1 rrbvector) t =
  casmod1 rrbvector (\rrbvector' =>
                      case rrbvector' of
                        Empty             =>
                          rrbvector'
                        Root size sh tree =>
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
                                  rrbvector'
                                GT =>
                                  rrbvector'
                    ) t

||| The vector without the first i elements.
||| If the vector contains less than or equal to i elements, the empty vector is returned. O(log n)
export
drop :  Nat
     -> RRBVector1 s a
     -> F1' s
drop n (MkRRBVector1 rrbvector) t =
  casmod1 rrbvector (\rrbvector' =>
                      case rrbvector' of
                        Empty             =>
                          rrbvector'
                        Root size sh tree =>
                          case compare n 0 of
                            LT =>
                              rrbvector'
                            EQ =>
                              rrbvector'
                            GT =>
                              case compare n size of
                                LT =>
                                  normalize $ Root (minus size n) sh (dropTree n sh tree)
                                EQ =>
                                  empty
                                GT =>
                                  empty
                    ) t

--------------------------------------------------------------------------------
--          Transformation
--------------------------------------------------------------------------------

||| Apply the function to every element. O(n)
export
map :  (a -> a)
    -> RRBVector1 s a
    -> F1' s
map f (MkRRBVector1 rrbvector) t =
  casmod1 rrbvector (\rrbvector' =>
                      case rrbvector' of
                        Empty             =>
                          rrbvector'
                        Root size sh tree =>
                          Root size sh (mapTree tree)
                    ) t
  where
    mapTree : Tree a -> Tree a
    mapTree (Balanced arr)         =
      assert_total $ Balanced (map mapTree arr)
    mapTree (Unbalanced arr sizes) =
      assert_total $ Unbalanced (map mapTree arr) sizes
    mapTree (Leaf arr)             =
      Leaf (map f arr)

||| Reverse the vector. O(n)
export
reverse :  RRBVector1 s a
        -> F1' s
reverse (MkRRBVector1 rrbvector) t =
  casmod1 rrbvector (\rrbvector' =>
                      case compare (Data.RRBVector.Unsized.length rrbvector') 1 of
                        LT =>
                          rrbvector'
                        EQ =>
                          rrbvector'
                        GT =>
                          case fromList $ Data.RRBVector.Unsized.toList rrbvector' of
                            Nothing          =>
                              assert_total $ idris_crash "Data.RRBVector1.Unsized.reverse: can't convert to List1"
                            Just rrbvector'' =>
                              fromList $ forget $ reverse rrbvector''
                    ) t

--------------------------------------------------------------------------------
--          Concatenation
--------------------------------------------------------------------------------

||| Add an element to the left end of the vector. O(log n)
export
(<|) :  a
     -> RRBVector1 s a
     -> F1' s
(x <| (MkRRBVector1 rrbvector)) t =
  casmod1 rrbvector (\rrbvector' =>
                      x <| rrbvector'
                    ) t

||| Add an element to the right end of the vector. O(log n)
export
(|>) :  RRBVector1 s a
     -> a
     -> F1' s
((MkRRBVector1 rrbvector) |> x) t =
  casmod1 rrbvector (\rrbvector' =>
                      rrbvector' |> x
                    ) t

||| Insert an element at the given index, shifting the rest of the vector over.
||| If the index is negative, add the element to the left end of the vector.
||| If the index is bigger than or equal to the length of the vector, add the element to the right end of the vector. O(log n)
export
insertAt :  Nat
         -> a
         -> RRBVector1 s a
         -> F1' s
insertAt i x (MkRRBVector1 rrbvector) t =
  casmod1 rrbvector (\rrbvector' =>
                      let (left, right) = splitAt i rrbvector'
                        in (Data.RRBVector.Unsized.(|>) left x) >< right
                    ) t

||| Delete the element at the given index.
||| If the index is out of range, return the original vector. O(log n)
export
deleteAt :  Nat
         -> RRBVector1 s a
         -> F1' s
deleteAt i (MkRRBVector1 rrbvector) t =
  casmod1 rrbvector (\rrbvector' =>
                      let (left, right) = splitAt (plus i 1) rrbvector'
                        in Data.RRBVector.Unsized.(><) (Data.RRBVector.Unsized.take i left) right
                    ) t

||| Show the full representation of the vector.
export
showRRBVectorRep :  Show a
                 => Show (Tree a)
                 => Show (RRBVector a)
                 => RRBVector1 s a
                 -> F1 s String
showRRBVectorRep (MkRRBVector1 rrbvector) t =
  let rrbvector' # t := read1 rrbvector t
    in case rrbvector' of
         Empty             =>
           "" # t
         Root size sh tree =>
           ( "RRBVector "       ++
             "{ "               ++
             "Size = "          ++
             (show size)        ++
             ", Shift = "       ++
             (show sh)          ++
             ", Tree = "        ++
             (showTreeRep tree) ++
             "}"
           ) # t
