||| Linear Relaxed Radix Balanced Vectors (RRBVector1)
module Data.RRBVector1

import public Data.RRBVector1.Internal

import Data.Array.Core
import Data.Array.Index
import Data.Array.Mutable
import Data.Bits
import Data.Maybe
import Data.List
import Data.List1
import Data.SnocList
import Data.Vect
import Data.Zippable

%hide Data.Array.Core.take
%hide Data.Linear.(::)
%hide Data.List.drop
%hide Data.List.lookup
%hide Data.List.take
%hide Data.List.singleton
%hide Data.List1.singleton
%hide Data.Vect.drop
%hide Data.Vect.lookup
%hide Data.Vect.take
%hide Data.Vect.Stream.take
%hide Data.Vect.(::)
%hide Prelude.null
%hide Prelude.take
%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Stream.(::)

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
--          Creating linear RRB-Vectors
--------------------------------------------------------------------------------

||| The empty vector. O(1)
export
empty : F1 s (RRBVector1 s a)
empty t =
  Empty # t

||| A vector with a single element. O(1)
export
singleton :  a
          -> F1 s (RRBVector1 s a)
singleton x t =
  let newarr # t := marray1 1 x t
    in Root 1 0 (Leaf {lsize=1} (1 ** newarr)) # t

||| Create a new vector from a list. O(n)
export
fromList :  List a
         -> F1 s (RRBVector1 s a)
fromList []  t = empty t
fromList [x] t = singleton x t
fromList xs  t =
  let trees # t := nodes xs Lin t
    in case trees of
         [tree] =>
           let treesize # t := treeSize 0 tree t
             in (Root treesize 0 tree) # t
         xs'    =>
           assert_smaller xs (iterateNodes blockshift xs' t)
  where
    nodes :  List a
          -> SnocList (Tree1 s a)
          -> F1 s (List (Tree1 s a))
    nodes l sl with (splitAt blocksize l) | ((length (fst (splitAt blocksize l))) <= (length l)) proof eq
      _ | (cl, cl') | True  = \t =>
        let trees'  # t := unsafeMArray1 (length l) t
            ()      # t := writeList trees' l t
            trees'' # t := mtake trees' (length (fst (splitAt blocksize l))) @{lteOpReflectsLTE _ _ eq} t
          in case cl' of
               []   =>
                 let trees''' := Leaf {lsize=(length (fst (splitAt blocksize l)))} ((length (fst (splitAt blocksize l))) ** trees'')
                     sl'      := sl :< trees'''
                   in (sl' <>> []) # t
               cl'' =>
                 let trees''' := Leaf {lsize=(length (fst (splitAt blocksize l)))} ((length (fst (splitAt blocksize l))) ** trees'')
                     sl'      := sl :< trees'''
                   in (nodes (assert_smaller l cl'') sl') t
      _ | _         | False = \t =>
        (assert_total $ idris_crash "Data.RRBVector1.fromList.nodes: index out of bounds") # t
    nodes' :  Nat
           -> List (Tree1 s a)
           -> SnocList (Tree1 s a)
           -> F1 s (List (Tree1 s a))
    nodes' sh l sl with (splitAt blocksize l) | ((length (fst (splitAt blocksize l))) <= (length l)) proof eq
      _ | (cl, cl') | True  = \t =>
        let trees'  # t := unsafeMArray1 (length l) t
            ()      # t := writeList trees' l t
            trees'' # t := mtake trees' (length (fst (splitAt blocksize l))) @{lteOpReflectsLTE _ _ eq} t
          in case cl' of
               []   =>
                 let trees''' := Balanced {bsize=(length (fst (splitAt blocksize l)))} ((length (fst (splitAt blocksize l))) ** trees'')
                     sl'      := sl :< trees'''
                   in (sl' <>> []) # t
               cl'' =>
                 let trees''' := Balanced {bsize=(length (fst (splitAt blocksize l)))} ((length (fst (splitAt blocksize l))) ** trees'')
                     sl'      := sl :< trees'''
                   in (nodes' sh (assert_smaller l cl'') sl') t
      _ | _         | False = \t =>
        (assert_total $ idris_crash "Data.RRBVector1.fromList.nodes': index out of bounds") # t
    iterateNodes :  Nat
                 -> List (Tree1 s a)
                 -> F1 s (RRBVector1 s a)
    iterateNodes sh trees t =
      let trees' # t := nodes' sh trees Lin t
        in case trees' of
             [tree]  =>
               let treesize # t := treeSize sh tree t
                 in (Root treesize sh tree) # t
             trees'' =>
               iterateNodes (up sh) (assert_smaller trees trees'') t

||| Creates a vector of length n with every element set to x. O(log n)
export
replicate :  Nat
          -> a
          -> F1 s (RRBVector1 s a)
replicate n x t =
  case compare n 0 of
    LT =>
      Empty # t
    EQ =>
      Empty # t
    GT =>
      case compare n blocksize of
        LT =>
          let newarr # t := marray1 n x t
            in Root n 0 (Leaf {lsize=n} (n ** newarr)) # t
        EQ =>
          let newarr # t := marray1 n x t
            in Root n 0 (Leaf {lsize=n} (n ** newarr)) # t
        GT =>
          let size'       := integerToNat ((natToInteger $ minus n 1) .&. (natToInteger $ plus blockmask 1))
              newarr1 # t := marray1 blocksize x t
              newarr2 # t := marray1 size' x t
              tree1       := Leaf {lsize=blocksize} (blocksize ** newarr1)
              tree2       := Leaf {lsize=size'} (size' ** newarr2)
            in iterateNodes blockshift
                            tree1
                            tree2
                            t
  where
    iterateNodes :  (sh : Shift)
                 -> (full : Tree1 s a)
                 -> (rest : Tree1 s a)
                 -> F1 s (RRBVector1 s a)
    iterateNodes sh full rest t =
      let subtreesm1   := (natToInteger $ minus n 1) `shiftR` sh
          restsize     := integerToNat (subtreesm1 .&. (natToInteger blockmask))
          mappend1 # t := marray1 restsize full t
          mappend2 # t := marray1 1 rest t
          rest'    # t := mappend mappend1 mappend2 t
          rest''       := Balanced {bsize=plus restsize 1} ((plus restsize 1) ** rest')
        in case compare subtreesm1 (natToInteger blocksize) of
             LT =>
               (Root n sh rest'') # t
             EQ =>
               let newarr # t := marray1 blocksize full t
                   full'      := Balanced {bsize=blocksize} (blocksize ** newarr)
                 in iterateNodes (up sh)
                                 (assert_smaller full full')
                                 (assert_smaller rest rest'')
                                 t
             GT =>
               let newarr # t := marray1 blocksize full t
                   full'      := Balanced {bsize=blocksize} (blocksize ** newarr)
                 in iterateNodes (up sh)
                                 (assert_smaller full full')
                                 (assert_smaller rest rest'')
                                 t

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Is the vector empty? O(1)
export
null :  RRBVector1 s a
     -> F1 s Bool
null Empty t =
  True # t
null _     t =
  False # t

||| Return the size of a vector. O(1)
export
length :  RRBVector1 s a
       -> F1 s Nat
length Empty        t =
  0 # t
length (Root s _ _) t =
  s # t

--------------------------------------------------------------------------------
--          Indexing
--------------------------------------------------------------------------------

||| The element at the index or Nothing if the index is out of range. O(log n)
export
lookup :  Nat
       -> RRBVector1 s a
       -> F1 s (Maybe a)
lookup _ Empty               t = Nothing # t
lookup i (Root size sh tree) t =
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
          let lookup' # t := lookupTree i sh tree t
            in Just lookup' # t
    EQ =>
      case compare i size of
        EQ =>
          Nothing # t -- index out of range
        GT =>
          Nothing # t -- index out of range
        LT =>
          let lookup' # t := lookupTree i sh tree t
            in Just lookup' # t
  where
    lookupTree :  Nat
               -> Nat
               -> Tree1 s a
               -> F1 s a
    lookupTree i sh (Balanced (_ ** arr))         t =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          (assert_total $ idris_crash "Data.RRBVector.lookup.lookupTree: can't convert Nat to Fin") # t
        Just i' =>
          let i'' # t := get arr i' t
            in assert_total $ lookupTree i (down sh) i'' t
    lookupTree i sh (Unbalanced (_ ** arr) sizes) t =
      let (idx, subidx) := relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing =>
               (assert_total $ idris_crash "Data.RRBVector.lookup.lookupTree: can't convert Nat to Fin") # t
             Just i' =>
               let i'' # t := get arr i' t
                 in assert_total $ lookupTree subidx (down sh) i'' t
    lookupTree i _  (Leaf (_ ** arr))             t =
      let i' = integerToNat ((natToInteger i) .&. (natToInteger blockmask))
        in case tryNatToFin i' of
             Nothing  =>
               (assert_total $ idris_crash "Data.RRBVector.lookup.lookupTree: can't convert Nat to Fin") # t
             Just i'' =>
               let i''' # t := get arr i'' t
                 in i''' # t

||| The element at the index.
||| Calls 'idris_crash' if the index is out of range. O(log n)
export
index :  Nat
      -> RRBVector1 s a
      -> F1 s a
index i v t =
  let lookup' # t := lookup i v t
    in case lookup' of
         Nothing       =>
           (assert_total $ idris_crash "Data.RRBVector.index: index out of range") # t
         Just lookup'' =>
           lookup'' # t

||| A flipped version of lookup. O(log n)
export
(!?) :  RRBVector1 s a
     -> Nat
     -> F1 s (Maybe a)
(!?) t = flip lookup t

||| A flipped version of index. O(log n)
export
(!!) :  RRBVector1 s a
     -> Nat
     -> F1 s a
(!!) t = flip index t

||| Update the element at the index with a new element.
||| If the index is out of range, the original vector is returned. O(log n)
export
update :  Nat
       -> a
       -> RRBVector1 s a
       -> F1 s (RRBVector1 s a)
update _ _ Empty                 t = Empty # t
update i x v@(Root size sh tree) t =
  case compare i 0 of
    LT =>
      v # t -- index out of range
    GT =>
      case compare i size of
        EQ =>
          v # t -- index out of range
        GT =>
          v # t -- index out of range
        LT =>
          let update' # t := updateTree i sh tree t
            in ( Root size
                      sh
                      update'
               ) # t
    EQ =>
      case compare i size of
        EQ =>
          v # t -- index out of range
        GT =>
          v # t -- index out of range
        LT =>
          let update' # t := updateTree i sh tree t
            in ( Root size
                      sh
                      update'
               ) # t
  where
    updateTree :  Nat
               -> Nat
               -> Tree1 s a
               -> F1 s (Tree1 s a)
    updateTree i sh (Balanced (b ** arr))         t =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          (assert_total $ idris_crash "Data.RRBVector.update.updateTree: can't convert Nat to Fin") # t
        Just i' =>
          let newtree # t := assert_total $ updateTree i (down sh) (Balanced {bsize=b} (b ** arr)) t
              ()      # t := set arr i' newtree t
            in (Balanced {bsize=b} (b ** arr)) # t
    updateTree i sh (Unbalanced (u ** arr) sizes) t =
      let (idx, subidx) := relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               (assert_total $ idris_crash "Data.RRBVector.update.updateTree: can't convert Nat to Fin") # t
             Just idx' =>
               let newtree # t := assert_total $ updateTree subidx (down sh) (Unbalanced (u ** arr) sizes) t
                   ()      # t := set arr idx' newtree t
                 in (Unbalanced (u ** arr) sizes) # t
    updateTree i _  (Leaf (l ** arr))             t =
      let i' = integerToNat ((natToInteger i) .&. (natToInteger blockmask))
        in case tryNatToFin i' of
             Nothing =>
               (assert_total $ idris_crash "Data.RRBVector.update: can't convert Nat to Fin") # t
             Just i'' =>
               let () # t := set arr i'' x t
                 in (Leaf {lsize=l} (l ** arr)) # t

||| Adjust the element at the index by applying the function to it.
||| If the index is out of range, the original vector is returned. O(log n)
export
adjust :  Nat
       -> (a -> a)
       -> RRBVector1 s a
       -> F1 s (RRBVector1 s a)
adjust _ _ Empty                 t = Empty # t
adjust i f v@(Root size sh tree) t =
  case compare i 0 of
    LT =>
      v # t -- index out of range
    GT =>
      case compare i size of
        EQ =>
          v # t -- index out of range
        GT =>
          v # t -- index out of range
        LT =>
          let adjust' # t := adjustTree i sh tree t
            in ( Root size
                      sh
                      adjust'
               ) # t
    EQ =>
      case compare i size of
        EQ =>
          v # t -- index out of range
        GT =>
          v # t -- index out of range
        LT =>
          let adjust' # t := adjustTree i sh tree t
            in ( Root size
                      sh
                      adjust'
               ) # t
  where
    adjustTree :  Nat
               -> Nat
               -> Tree1 s a
               -> F1 s (Tree1 s a)
    adjustTree i sh (Balanced (b ** arr))         t =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          (assert_total $ idris_crash "Data.RRBVector.adjust: can't convert Nat to Fin") # t
        Just i' =>
          let newtree # t := assert_total $ adjustTree i (down sh) (Balanced {bsize=b} (b ** arr)) t
              ()      # t := set arr i' newtree t
            in (Balanced {bsize=b} (b ** arr)) # t
    adjustTree i sh (Unbalanced (u ** arr) sizes) t =
      let (idx, subidx) := relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               (assert_total $ idris_crash "Data.RRBVector.adjust: can't convert Nat to Fin") # t
             Just idx' =>
               let newtree # t := assert_total $ adjustTree subidx (down sh) (Unbalanced (u ** arr) sizes) t
                   ()      # t := set arr idx' newtree t
                 in (Unbalanced (u ** arr) sizes) # t
    adjustTree i _  (Leaf (l ** arr))             t =
      let i' = integerToNat ((natToInteger i) .&. (natToInteger blockmask))
        in case tryNatToFin i' of
             Nothing =>
               (assert_total $ idris_crash "Data.RRBVector.adjust: can't convert Nat to Fin") # t
             Just i'' =>
               let () # t := modify arr i'' f t
                 in (Leaf {lsize=l} (l ** arr)) # t

private
normalize :  RRBVector1 s a
          -> F1 s (RRBVector1 s a)
normalize v@(Root size sh (Balanced (b ** arr)))         t =
  case compare b 1 of
    LT =>
      v # t
    EQ =>
      case tryNatToFin 0 of
        Nothing =>
          (assert_total $ idris_crash "Data.RRBVector.normalize: can't convert Nat to Fin") # t
        Just i  =>
          let arr' # t := get arr i t
            in assert_total $ (normalize (Root size (down sh) arr') t)
    GT =>
      v # t
normalize v@(Root size sh (Unbalanced (u ** arr) sizes)) t =
  case compare u 1 of
    LT =>
      v # t
    EQ =>
      case tryNatToFin 0 of
        Nothing =>
          (assert_total $ idris_crash "Data.RRBVector.normalize: can't convert Nat to Fin") # t
        Just i  =>
          let arr' # t := get arr i t
            in assert_total $ (normalize (Root size (down sh) arr') t)
    GT =>
      v # t
normalize v                                                 t =
  v # t

||| The initial i is n - 1 (the index of the last element in the new tree).
private
takeTree :  Nat
         -> Shift
         -> Tree1 s a
         -> F1 s (Tree1 s a)
takeTree i sh (Balanced (b ** arr)) with (radixIndex i sh) | ((plus (radixIndex i sh) 1) <= b) proof eq
  _ | i' | True  = \t =>
    case tryNatToFin i' of
      Nothing  =>
        (assert_total $ idris_crash "Data.RRBVector1.takeTree: can't convert Nat to Fin") # t
      Just i'' =>
        let arr'     # t := mtake arr (plus (radixIndex i sh) 1) @{lteOpReflectsLTE _ _ eq} t
            newtree  # t := get arr' i'' t
            newtree' # t := assert_total $ takeTree i (down sh) newtree t
            ()       # t := set arr' i'' newtree' t
          in (Balanced {bsize=(plus (radixIndex i sh) 1)} ((plus (radixIndex i sh) 1) ** arr')) # t
  _ | _  | False = \t =>
    (assert_total $ idris_crash "Data.RRBVector1.takeTree: index out of bounds") # t
takeTree i sh (Unbalanced (u ** arr) sizes) with (relaxedRadixIndex sizes i sh) | ((plus (fst (relaxedRadixIndex sizes i sh)) 1) <= u) proof eq
  _ | (idx, subidx) | True  = \t =>
    case tryNatToFin idx of
      Nothing   =>
        (assert_total $ idris_crash "Data.RRBVector1.takeTree: can't convert Nat to Fin") # t
      Just idx' =>
        let arr'      # t := mtake arr (plus (fst (relaxedRadixIndex sizes i sh)) 1) @{lteOpReflectsLTE _ _ eq} t
            newtree   # t := get arr' idx' t
            newtree'  # t := assert_total $ takeTree subidx (down sh) newtree t
            ()        # t := set arr' idx' newtree' t
            newtree'' # t := computeSizes sh arr' t
          in newtree'' # t
  _ | _             | False = \t =>
    (assert_total $ idris_crash "Data.RRBVector1.takeTree: index out of bounds") # t
takeTree i _ (Leaf (l ** arr)) with (integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1) <= l) proof eq
  _ | True  = \t =>
    case ((integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1)) <= l) of
      True  =>
        let arr' # t := mtake arr (integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1)) @{lteOpReflectsLTE _ _ eq} t
          in (Leaf {lsize=(integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1))} ((integerToNat (((natToInteger i) .&. (natToInteger blockmask)) + 1)) ** arr')) # t
      False =>
        (assert_total $ idris_crash "Data.RRBVector1.takeTree: index out of bounds") # t
  _ | False = \t =>
    (assert_total $ idris_crash "Data.RRBVector1.takeTree: index out of bounds") # t

private
dropTree :  Nat
         -> Shift
         -> Tree1 s a
         -> F1 s (Tree1 s a)
dropTree n sh (Balanced (b ** arr))         t =
  case tryNatToFin 0 of
    Nothing   =>
      (assert_total $ idris_crash "Data.RRBVector.dropTree: can't convert Nat to Fin") # t
    Just zero =>
      let arr'      # t := mdrop (radixIndex n sh) arr t
          newtree   # t := get arr' zero t
          newtree'  # t := assert_total $ dropTree n (down sh) newtree t
          ()        # t := set arr' zero newtree' t
          newtree'' # t := computeSizes sh arr' t
        in newtree'' # t
dropTree n sh (Unbalanced (u ** arr) sizes) t =
  case tryNatToFin 0 of
    Nothing   =>
      (assert_total $ idris_crash "Data.RRBVector.dropTree: can't convert Nat to Fin") # t
    Just zero =>
      let arr'      # t := mdrop (fst $ relaxedRadixIndex sizes n sh) arr t
          newtree   # t := get arr' zero t
          newtree'  # t := assert_total $ dropTree (snd $ relaxedRadixIndex sizes n sh) (down sh) newtree t
          ()        # t := set arr' zero newtree' t
          newtree'' # t := computeSizes sh arr' t
        in newtree'' # t
dropTree n _  (Leaf (l ** arr))             t =
  let n'       := integerToNat ((natToInteger n) .&. (natToInteger blockmask))
      arr' # t := mdrop n' arr t
      in (Leaf {lsize=minus l n'} ((minus l n') ** arr')) # t

||| The first i elements of the vector.
||| If the vector contains less than or equal to i elements, the whole vector is returned. O(log n)
export
take :  Nat
     -> RRBVector1 s a
     -> F1 s (RRBVector1 s a)
take _ Empty                 t = empty t
take n v@(Root size sh tree) t =
  case compare n 0 of
    LT =>
      empty t
    EQ =>
      empty t
    GT =>
      case compare n size of
        LT =>
          let tt  # t := takeTree (minus n 1) sh tree t
              tt' # t := normalize (Root n sh tt) t
            in tt' # t
        EQ =>
          v # t
        GT =>
          v # t

||| The vector without the first i elements.
||| If the vector contains less than or equal to i elements, the empty vector is returned. O(log n)
export
drop :  Nat
     -> RRBVector1 s a
     -> F1 s (RRBVector1 s a)
drop _ Empty                 t = empty t
drop n v@(Root size sh tree) t =
  case compare n 0 of
    LT =>
      v # t
    EQ =>
      v # t
    GT =>
      case compare n size of
        LT =>
          let dt  # t := dropTree n sh tree t
              dt' # t := normalize (Root (minus size n) sh dt) t
            in dt' # t
        EQ =>
          empty t
        GT =>
          empty t

||| Split the vector at the given index. O(log n)
export
splitAt :  Nat
        -> RRBVector1 s a
        -> F1 s (RRBVector1 s a, RRBVector1 s a)
splitAt _ Empty                 t = (Empty, Empty) # t
splitAt n v@(Root size sh tree) t =
  case compare n 0 of
    LT =>
      (Empty, v) # t
    EQ =>
      (Empty, v) # t
    GT =>
      case compare n size of
        LT =>
          let tt    # t := takeTree (minus n 1) sh tree t
              left  # t := normalize (Root n sh tt) t
              dt    # t := dropTree n sh tree t
              right # t := normalize (Root (minus size n) sh dt) t
            in (left, right) # t
        EQ =>
          (v, Empty) # t
        GT =>
          (v, Empty) # t

--------------------------------------------------------------------------------
--          Deconstruction
--------------------------------------------------------------------------------

||| The first element and the vector without the first element, or 'Nothing' if the vector is empty. O(log n)
export
viewl :  RRBVector1 s a
      -> F1 s (Maybe (a, RRBVector1 s a))
viewl Empty             t = Nothing # t
viewl v@(Root _ _ tree) t =
  let tail # t := drop 1 v t
      head # t := headTree tree t
    in (Just (head, tail)) # t
  where
    headTree :  Tree1 s a
             -> F1 s a
    headTree (Balanced (_ ** arr))     t =
      case tryNatToFin 0 of
        Nothing   =>
          (assert_total $ idris_crash "Data.RRBVector.viewl: can't convert Nat to Fin") # t
        Just zero =>
          let headtree # t := get arr zero t
            in assert_total $ headTree headtree t
    headTree (Unbalanced (_ ** arr) _) t =
      case tryNatToFin 0 of
        Nothing   =>
          (assert_total $ idris_crash "Data.RRBVector.viewl: can't convert Nat to Fin") # t
        Just zero =>
          let headtree # t := get arr zero t
            in assert_total $ headTree headtree t
    headTree (Leaf (_ ** arr))         t =
      case tryNatToFin 0 of
        Nothing   =>
          (assert_total $ idris_crash "Data.RRBVector.viewl: can't convert Nat to Fin") # t
        Just zero =>
          get arr zero t

||| The vector without the last element and the last element, or 'Nothing' if the vector is empty. O(log n)
export
viewr :  RRBVector1 s a
      -> F1 s (Maybe (RRBVector1 s a, a))
viewr Empty                t = Nothing # t
viewr v@(Root size _ tree) t =
  let init # t := take (minus size 1) v t
      last # t := lastTree tree t
    in (Just (init, last)) # t
  where
    lastTree :  Tree1 s a
             -> F1 s a
    lastTree (Balanced (_ ** arr))     t =
      case tryNatToFin (minus size 1) of
        Nothing   =>
          (assert_total $ idris_crash "Data.RRBVector.viewr: can't convert Nat to Fin") # t
        Just last =>
          let lasttree # t := get arr last t
            in assert_total $ lastTree lasttree t
    lastTree (Unbalanced (_ ** arr) _) t =
      case tryNatToFin (minus size 1) of
        Nothing   =>
          (assert_total $ idris_crash "Data.RRBVector.viewr: can't convert Nat to Fin") # t
        Just last =>
          let lasttree # t := get arr last t
            in assert_total $ lastTree lasttree t
    lastTree (Leaf (_ ** arr))         t =
      case tryNatToFin (minus size 1) of
        Nothing   =>
          (assert_total $ idris_crash "Data.RRBVector.viewr: can't convert Nat to Fin") # t
        Just last =>
          get arr last t

--------------------------------------------------------------------------------
--          Transformation
--------------------------------------------------------------------------------

||| Apply the function to every element. O(n)
export
map :  (F1 s a -> F1 s b)
    -> (F1 s (Tree1 s a) -> F1 s (Tree1 s b))
    -> RRBVector1 s a
    -> F1 s (RRBVector1 s b)
map _ _  Empty               t = empty t
map f f' (Root size sh tree) t =
  let maptree # t := mapTree tree t
    in (Root size sh maptree) # t
  where
    mapTree :  Tree1 s a
            -> F1 s (Tree1 s b)
    mapTree (Balanced (b ** arr))         t =
      let arr' # t := mmap f' arr t
        in (Balanced {bsize=b} (b ** arr')) # t
    mapTree (Unbalanced (u ** arr) sizes) t =
      let arr' # t := mmap f' arr t
        in (Unbalanced (u ** arr') sizes) # t
    mapTree (Leaf (l ** arr))             t =
      let arr' # t := mmap f arr t
        in (Leaf {lsize=l} (l ** arr')) # t

--------------------------------------------------------------------------------
--          Concatenation
--------------------------------------------------------------------------------

||| Create a new tree with shift sh.
private
newBranch :  a
          -> Shift
          -> F1 s (Tree1 s a)
newBranch x 0  t =
  let x' # t := Data.RRBVector1.Internal.singleton x t
    in (Leaf {lsize=1} (1 ** x')) # t
newBranch x sh t =
  let branch # t := assert_total $ newBranch x (down sh) t
      x'     # t := Data.RRBVector1.Internal.singleton branch t
    in (Balanced {bsize=1} (1 ** x')) # t

||| Create a new tree with shift sh.
private
newBranch' :  Tree1 s a
           -> Shift
           -> F1 s (Tree1 s a)
newBranch' tree 0  t =
  let tree' # t := singleton' tree t
    in (Balanced {bsize=1} (1 ** tree')) # t
newBranch' tree sh t =
  let branch  # t := assert_total $ newBranch' tree (down sh) t
      tree'   # t := singleton' branch t
    in (Balanced {bsize=1} (1 ** tree')) # t

{-
||| Add an element to the left end of the vector. O(log n)
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
    consTree : Nat -> Tree a -> Tree a
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
(|>) : RRBVector a -> a -> RRBVector a
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
    computeShift : Nat -> Nat -> Nat -> Tree a -> Nat
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
    snocTree : Nat -> Tree a -> Tree a
    snocTree sh (Balanced arr) =
      case compare sh insertshift of
        LT =>
          case tryNatToFin $ minus arr.size 1 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.(<|).snocTree.Balanced: can't convert Nat to Fin"
            Just lastidx =>
              assert_total $ Balanced (A arr.size $ updateAt lastidx (snocTree (down sh)) arr.arr)
        EQ =>
          Balanced (A (plus arr.size 1) (append arr.arr (fill 1 (newBranch x (down sh))))) -- the current subtree is fully balanced
        GT =>
          case tryNatToFin $ minus arr.size 1 of
            Nothing   =>
              assert_total $ idris_crash "Data.RRBVector.(<|).snocTree.Balanced: can't convert Nat to Fin"
            Just lastidx =>
              assert_total $ Balanced (A arr.size $ updateAt lastidx (snocTree (down sh)) arr.arr)
    snocTree sh (Unbalanced arr sizes) =
      case compare sh insertshift of
        LT =>
          case tryNatToFin $ minus arr.size 1 of
            Nothing       =>
              assert_total $ idris_crash "Data.RRBVector.(<|).snocTree.Unbalanced: can't convert Nat to Fin"
            Just lastidxa =>
              case tryNatToFin $ minus sizes.size 1 of
                Nothing       =>
                  assert_total $ idris_crash "Data.RRBVector.(<|).snocTree.Unbalanced: can't convert Nat to Fin"
                Just lastidxs =>
                  let lastsize = plus (at sizes.arr lastidxs) 1
                    in assert_total $ Unbalanced (A arr.size (updateAt lastidxa (snocTree (down sh)) arr.arr))
                                                 (A sizes.size (setAt lastidxs lastsize sizes.arr))
        EQ =>
          case tryNatToFin $ minus sizes.size 1 of
            Nothing      =>
              assert_total $ idris_crash "Data.RRBVector.(<|).snocTree.Unbalanced: can't convert Nat to Fin"
            Just lastidx =>
              let lastsize = plus (at sizes.arr lastidx) 1
                in assert_total $ Unbalanced (A (plus arr.size 1) (append arr.arr (fill 1 (newBranch x (down sh)))))
                                             (A (plus sizes.size 1) (append sizes.arr (fill 1 lastsize)))
        GT =>
          case tryNatToFin $ minus arr.size 1 of
            Nothing       =>
              assert_total $ idris_crash "Data.RRBVector.(<|).snocTree.Unbalanced: can't convert Nat to Fin"
            Just lastidxa =>
              case tryNatToFin $ minus sizes.size 1 of
                Nothing       =>
                  assert_total $ idris_crash "Data.RRBVector.(<|).snocTree.Unbalanced: can't convert Nat to Fin"
                Just lastidxs =>
                  let lastsize = plus (at sizes.arr lastidxs) 1
                    in assert_total $ Unbalanced (A arr.size (updateAt lastidxa (snocTree (down sh)) arr.arr))
                                                 (A sizes.size (setAt lastidxs lastsize sizes.arr))
    snocTree _ (Leaf arr) = Leaf (A (plus arr.size 1) (append arr.arr (fill 1 x)))

||| Concatenates two vectors. O(log(max(n1,n2)))
export
(><) : RRBVector a -> RRBVector a -> RRBVector a
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
    mergeRebalance' : Shift -> Array (Tree a) -> Array (Tree a) -> Array (Tree a) -> (Tree a -> Array (Tree a)) -> (Array (Tree a) -> Tree a) -> Array (Tree a)
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
            case nodecounter' == (natToInteger blocksize) of
              True  => do
                subtreecounter' <- readSTRef subtreecounter
                case subtreecounter' == (natToInteger blocksize) of
                  True  => do
                    newnode' <- readSTRef newnode
                    modifySTRef newsubtree (\y => y :< (construct $ A (SnocSize newnode')
                                                                      (snocConcat newnode'))
                                           )
                    writeSTRef newnode Lin
                    writeSTRef nodecounter 0
                    modifySTRef subtreecounter (\y => y + 1
                                               )
                    newsubtree' <- readSTRef newsubtree
                    modifySTRef newroot (\y => y :< (computeSizes sh (fromList $ the (List (Tree a)) (cast newsubtree')))
                                        )
                    writeSTRef newsubtree Lin
                    writeSTRef subtreecounter 0
                  False => do
                    newnode' <- readSTRef newnode
                    modifySTRef newsubtree (\y => y :< (construct $ A (SnocSize newnode')
                                                                      (snocConcat newnode'))
                                           )
                    writeSTRef newnode Lin
                    writeSTRef nodecounter 0
                    modifySTRef subtreecounter (\y => y + 1)
              False => do
                modifySTRef newnode (\y => y :< (extract x)
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
    mergeRebalance'' : Shift -> Array (Tree a) -> Array (Tree a) -> Array (Tree a) -> (Tree a -> Array a) -> (Array a -> Tree a) -> Array (Tree a)
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
            case nodecounter' == (natToInteger blocksize) of
              True  => do
                subtreecounter' <- readSTRef subtreecounter
                case subtreecounter' == (natToInteger blocksize) of
                  True  => do
                    newnode' <- readSTRef newnode
                    modifySTRef newsubtree (\y => y :< (construct $ A (SnocSize newnode')
                                                                      (snocConcat newnode'))
                                           )
                    writeSTRef newnode Lin
                    writeSTRef nodecounter 0
                    modifySTRef subtreecounter (\y => y + 1
                                               )
                    newsubtree' <- readSTRef newsubtree
                    modifySTRef newroot (\y => y :< (computeSizes sh (fromList $ the (List (Tree a)) (cast newsubtree')))
                                        )
                    writeSTRef newsubtree Lin
                    writeSTRef subtreecounter 0
                  False => do
                    newnode' <- readSTRef newnode
                    modifySTRef newsubtree (\y => y :< (construct $ A (SnocSize newnode')
                                                                      (snocConcat newnode'))
                                           )
                    writeSTRef newnode Lin
                    writeSTRef nodecounter 0
                    modifySTRef subtreecounter (\y => y + 1)
              False => do
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
    mergeRebalance : Shift -> Array (Tree a) -> Array (Tree a) -> Array (Tree a) -> Array (Tree a)
    mergeRebalance sh left center right =
      case compare sh blockshift of
        LT =>
          assert_total $ mergeRebalance' sh left center right treeToArray (computeSizes (down sh))
        EQ =>
          assert_total $ mergeRebalance'' sh left center right (\(Leaf arr) => arr) Leaf
        GT =>
          assert_total $ mergeRebalance' sh left center right treeToArray (computeSizes (down sh))
    mergeTrees : Tree a -> Nat -> Tree a -> Nat -> Array (Tree a)
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
insertAt : Nat -> a -> RRBVector a -> RRBVector a
insertAt i x v =
  let (left, right) = splitAt i v
    in (left |> x) >< right

||| Delete the element at the given index.
||| If the index is out of range, return the original vector. O(log n)
export
deleteAt : Nat -> RRBVector a -> RRBVector a
deleteAt i v =
  let (left, right) = splitAt (plus i 1) v
    in take i left >< right

--------------------------------------------------------------------------------
--          Show Utilities (RRB-Vector)
--------------------------------------------------------------------------------

||| Show the full representation of the vector.
export
showRRBVectorRep : Show a => Show (Tree a) => Show (RRBVector a) => RRBVector a -> String
showRRBVectorRep Empty            = ""
showRRBVectorRep (Root size sh t) = "rrbvector " ++ "[" ++ "size " ++ (show size) ++ " shift " ++ (show sh) ++ " tree " ++ (showTreeRep t) ++ "]"

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Ord a => Ord (RRBVector a) where
  compare xs ys = compare (Data.RRBVector.toList xs) (Data.RRBVector.toList ys)

export
Eq a => Eq (RRBVector a) where
  xs == ys = length xs == length ys && Data.RRBVector.toList xs == Data.RRBVector.toList ys

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
-}
