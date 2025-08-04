||| Linear Relaxed Radix Balanced Vectors (RRBVector1)
module Data.RRBVector1.Sized

import public Data.RRBVector1.Sized.Internal

import Data.Array.Core
import Data.Array.Index
import Data.Array.Indexed
import Data.Array.Mutable
import Data.Bits
import Data.Maybe
import Data.Linear.Ref1
import Data.List
import Data.List1
import Data.SnocList
import Data.Vect
import Data.Zippable

%hide Data.Array.Core.take
%hide Data.Array.Indexed.drop
%hide Data.Linear.splitAt
%hide Data.Linear.(::)
%hide Data.List.drop
%hide Data.List.lookup
%hide Data.List.take
%hide Data.List.singleton
%hide Data.List1.singleton
%hide Data.Vect.drop
%hide Data.Vect.lookup
%hide Data.Vect.splitAt
%hide Data.Vect.take
%hide Data.Vect.Stream.take
%hide Data.Vect.(::)
%hide Prelude.null
%hide Prelude.take
%hide Prelude.(|>)
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
empty : F1 s (RRBVector1 s Z a)
empty t =
  Empty # t

||| A vector with a single element. O(1)
export
singleton :  a
          -> F1 s (RRBVector1 s 1 a)
singleton x t =
  let newarr # t := marray1 1 x t
    in Root 0 (Leaf {lsize=1} (1 ** newarr)) # t

||| Create a new vector from a list. O(n)
export
fromList :  (xs : List a)
         -> F1 s (RRBVector1 s (length xs) a)
fromList []  t = empty t
fromList [x] t = singleton x t
fromList xs  t =
  let trees # t := nodes xs Lin t
    in case trees of
         [tree] =>
           (Root 0 tree) # t
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
                 -> F1 s (RRBVector1 s n a)
    iterateNodes sh trees t =
      let trees' # t := nodes' sh trees Lin t
        in case trees' of
             [tree]  =>
               (Root sh tree) # t
             trees'' =>
               iterateNodes (up sh) (assert_smaller trees trees'') t

||| Creates a vector of length n with every element set to x. O(log n)
export
replicate :  (n : Nat)
          -> a
          -> F1 s (RRBVector1 s n a)
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
            in Root 0 (Leaf {lsize=n} (n ** newarr)) # t
        EQ =>
          let newarr # t := marray1 n x t
            in Root 0 (Leaf {lsize=n} (n ** newarr)) # t
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
                 -> F1 s (RRBVector1 s n a)
    iterateNodes sh full rest t =
      let subtreesm1   := (natToInteger $ minus n 1) `shiftR` sh
          restsize     := integerToNat (subtreesm1 .&. (natToInteger blockmask))
          mappend1 # t := marray1 restsize full t
          mappend2 # t := marray1 1 rest t
          rest'    # t := mappend mappend1 mappend2 t
          rest''       := Balanced {bsize=plus restsize 1} ((plus restsize 1) ** rest')
        in case compare subtreesm1 (natToInteger blocksize) of
             LT =>
               (Root sh rest'') # t
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
--          Creating linear lists from linear RRB-Vectors
--------------------------------------------------------------------------------

private
treeToList :  (n ** MArray s n (Tree1 s a))
           -> F1 s (List a)
treeToList (n ** arr) t =
  go 0 n Lin t
  where
    go :  (m, x : Nat)
       -> (sl : SnocList a)
       -> {auto v : Ix x n}
       -> F1 s (List a)
    go m Z     sl t =
      (sl <>> []) # t
    go m (S j) sl t =
      let j' # t := getIx arr j t
        in case j' of
             (Balanced (b ** arr'))     =>
               let arr'' # t := assert_total $ treeToList (b ** arr') t
                   sl'       := sl <>< arr''
                 in go (S m) j sl' t
             (Unbalanced (u ** arr') _) =>
               let arr'' # t := assert_total $ treeToList (u ** arr') t
                   sl'       := sl <>< arr''
                 in go (S m) j sl' t
             (Leaf (_ ** arr'))         =>
               let arr'' # t := freeze arr' t
                   arr'''    := toList arr''
                   sl'       := sl <>< arr'''
                 in go (S m) j sl' t

||| Convert a vector to a list. O(n)
export
toList :  RRBVector1 s n a
       -> F1 s (List a)
toList Empty                              t =
  [] # t
toList (Root _ (Balanced (b ** arr)))     t =
  treeToList (b ** arr) t
toList (Root _ (Unbalanced (u ** arr) _)) t =
  treeToList (u ** arr) t
toList (Root _ (Leaf (_ ** arr)))         t =
  let arr' # t := freeze arr t
    in toList arr' # t

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Is the vector empty? O(1)
export
null :  RRBVector1 s n a
     -> F1 s Bool
null Empty t =
  True # t
null _     t =
  False # t

||| Return the size of a vector. O(1)
export
length :  {n : Nat}
       -> RRBVector1 s n a
       -> F1 s Nat
length _ t =
  n # t

--------------------------------------------------------------------------------
--          Indexing
--------------------------------------------------------------------------------

||| The element at the index or Nothing if the index is out of range. O(log n)
export
lookup :  {n : Nat}
       -> Nat
       -> RRBVector1 s n a
       -> F1 s (Maybe a)
lookup _ Empty          t =
  Nothing # t
lookup i (Root sh tree) t =
  case compare i 0 of
    LT =>
      Nothing # t -- index out of range
    GT =>
      case compare i n of
        EQ =>
          Nothing # t -- index out of range
        GT =>
          Nothing # t -- index out of range
        LT =>
          let lookup' # t := lookupTree i sh tree t
            in Just lookup' # t
    EQ =>
      case compare i n of
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
index :  {n : Nat}
      -> Nat
      -> RRBVector1 s n a
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
(!?) :  {n : Nat}
     -> RRBVector1 s n a
     -> Nat
     -> F1 s (Maybe a)
(!?) t =
  flip lookup t

||| A flipped version of index. O(log n)
export
(!!) :  {n : Nat}
     -> RRBVector1 s n a
     -> Nat
     -> F1 s a
(!!) t =
  flip index t

||| Update the element at the index with a new element.
||| If the index is out of range, the original vector is returned. O(log n)
export
update :  {n : Nat}
       -> Nat
       -> a
       -> RRBVector1 s n a
       -> F1 s (RRBVector1 s n a)
update _ _ Empty            t =
  Empty # t
update i x v@(Root sh tree) t =
  case compare i 0 of
    LT =>
      v # t -- index out of range
    GT =>
      case compare i n of
        EQ =>
          v # t -- index out of range
        GT =>
          v # t -- index out of range
        LT =>
          let update' # t := updateTree i sh tree t
            in ( Root sh
                      update'
               ) # t
    EQ =>
      case compare i n of
        EQ =>
          v # t -- index out of range
        GT =>
          v # t -- index out of range
        LT =>
          let update' # t := updateTree i sh tree t
            in ( Root sh
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
          let newtree  # t := get arr i' t
              newtree' # t := assert_total $ updateTree i (down sh) newtree t
              ()       # t := set arr i' newtree' t
            in (Balanced {bsize=b} (b ** arr)) # t
    updateTree i sh (Unbalanced (u ** arr) sizes) t =
      let (idx, subidx) := relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               (assert_total $ idris_crash "Data.RRBVector.update.updateTree: can't convert Nat to Fin") # t
             Just idx' =>
               let newtree  # t := get arr idx' t
                   newtree' # t := assert_total $ updateTree subidx (down sh) newtree t
                   ()       # t := set arr idx' newtree' t
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
adjust :  {n : Nat}
       -> Nat
       -> (a -> a)
       -> RRBVector1 s n a
       -> F1 s (RRBVector1 s n a)
adjust _ _ Empty            t =
  Empty # t
adjust i f v@(Root sh tree) t =
  case compare i 0 of
    LT =>
      v # t -- index out of range
    GT =>
      case compare i n of
        EQ =>
          v # t -- index out of range
        GT =>
          v # t -- index out of range
        LT =>
          let adjust' # t := adjustTree i sh tree t
            in ( Root sh
                      adjust'
               ) # t
    EQ =>
      case compare i n of
        EQ =>
          v # t -- index out of range
        GT =>
          v # t -- index out of range
        LT =>
          let adjust' # t := adjustTree i sh tree t
            in ( Root sh
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
          let newtree  # t := get arr i' t
              newtree' # t := assert_total $ adjustTree i (down sh) newtree t
              ()       # t := set arr i' newtree' t
            in (Balanced {bsize=b} (b ** arr)) # t
    adjustTree i sh (Unbalanced (u ** arr) sizes) t =
      let (idx, subidx) := relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               (assert_total $ idris_crash "Data.RRBVector.adjust: can't convert Nat to Fin") # t
             Just idx' =>
               let newtree  # t := get arr idx' t
                   newtree' # t := assert_total $ adjustTree subidx (down sh) newtree t
                   ()       # t := set arr idx' newtree' t
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
normalize :  RRBVector1 s n a
          -> F1 s (RRBVector1 s n a)
normalize v@(Root sh (Balanced (b ** arr)))         t =
  case compare b 1 of
    LT =>
      v # t
    EQ =>
      case tryNatToFin 0 of
        Nothing   =>
          (assert_total $ idris_crash "Data.RRBVector.normalize: can't convert Nat to Fin") # t
        Just zero =>
          let arr' # t := get arr zero t
            in assert_total $ (normalize (Root (down sh) arr') t)
    GT =>
      v # t
normalize v@(Root sh (Unbalanced (u ** arr) sizes)) t =
  case compare u 1 of
    LT =>
      v # t
    EQ =>
      case tryNatToFin 0 of
        Nothing   =>
          (assert_total $ idris_crash "Data.RRBVector.normalize: can't convert Nat to Fin") # t
        Just zero =>
          let arr' # t := get arr zero t
            in assert_total $ (normalize (Root (down sh) arr') t)
    GT =>
      v # t
normalize v                                         t =
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
  let idx := radixIndex n sh
    in case tryNatToFin 0 of
         Nothing   =>
           (assert_total $ idris_crash "Data.RRBVector.dropTree: can't convert Nat to Fin") # t
         Just zero =>
           let arr'      # t := mdrop idx arr t
               newtree   # t := get arr' zero t
               newtree'  # t := assert_total $ dropTree n (down sh) newtree t
               ()        # t := set arr' zero newtree' t
               newtree'' # t := computeSizes sh arr' t
             in newtree'' # t
dropTree n sh (Unbalanced (u ** arr) sizes) t =
  let (idx, subidx) := relaxedRadixIndex sizes n sh
    in case tryNatToFin 0 of
         Nothing   =>
           (assert_total $ idris_crash "Data.RRBVector.dropTree: can't convert Nat to Fin") # t
         Just zero =>
           let arr'      # t := mdrop idx arr t
               newtree   # t := get arr' zero t
               newtree'  # t := assert_total $ dropTree subidx (down sh) newtree t
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
take :  {n : Nat}
     -> Nat
     -> RRBVector1 s n a
     -> F1 s (n' ** RRBVector1 s n' a)
take _ Empty            t =
  (0 ** Empty) # t
take i v@(Root sh tree) t =
  case compare i 0 of
    LT =>
      (0 ** Empty) # t
    EQ =>
      (0 ** Empty) # t
    GT =>
      case compare i n of
        LT =>
          let tt  # t := takeTree (minus i 1) sh tree t
              tt' # t := normalize (Root sh tt) t
            in (i ** tt') # t
        EQ =>
          (n ** v) # t
        GT =>
          (n ** v) # t

||| The vector without the first i elements.
||| If the vector contains less than or equal to i elements, the empty vector is returned. O(log n)
export
drop :  {n : Nat}
     -> Nat
     -> RRBVector1 s n a
     -> F1 s (n' ** RRBVector1 s n' a)
drop _ Empty            t =
  (0 ** Empty) # t
drop i v@(Root sh tree) t =
  case compare i 0 of
    LT =>
      (n ** v) # t
    EQ =>
      (n ** v) # t
    GT =>
      case compare i n of
        LT =>
          let dt  # t := dropTree i sh tree t
              dt' # t := normalize (Root sh dt) t
            in (i ** dt') # t
        EQ =>
          (0 ** Empty) # t
        GT =>
          (0 ** Empty) # t

||| Split the vector at the given index. O(log n)
export
splitAt :  {n : Nat}
        -> Nat
        -> RRBVector1 s n a
        -> F1 s ((n' ** RRBVector1 s n' a), (n'' ** RRBVector1 s n'' a))
splitAt _ Empty            t =
  ((0 ** Empty), (0 ** Empty)) # t
splitAt i v@(Root sh tree) t =
  case compare i 0 of
    LT =>
      ((0 ** Empty), (n ** v)) # t
    EQ =>
      ((0 ** Empty), (n ** v)) # t
    GT =>
      case compare i n of
        LT =>
          let (dt ** right) # t := drop i v t 
              (tt ** left)  # t := take i v t
            in ((tt ** left), (dt ** right)) # t
        EQ =>
          ((n ** v), (0 ** Empty)) # t
        GT =>
          ((n ** v), (0 ** Empty)) # t

--------------------------------------------------------------------------------
--          Deconstruction
--------------------------------------------------------------------------------

||| The first element and the vector without the first element, or 'Nothing' if the vector is empty. O(log n)
export
viewl :  {n : Nat}
      -> RRBVector1 s n a
      -> F1 s (n' ** Maybe (a, RRBVector1 s n' a))
viewl Empty           t =
  (0 ** Nothing) # t
viewl v@(Root _ tree) t =
  let (dt ** tail) # t := drop 1 v t
      head         # t := headTree tree t
    in (dt ** Just (head, tail)) # t
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
viewr :  {n : Nat}
      -> RRBVector1 s n a
      -> F1 s (n' ** Maybe (RRBVector1 s n' a, a))
viewr Empty           t =
  (0 ** Nothing) # t
viewr v@(Root _ tree) t =
  let (tt ** init) # t := take (minus n 1) v t
      last         # t := lastTree tree t
    in (tt ** Just (init, last)) # t
  where
    lastTree :  Tree1 s a
             -> F1 s a
    lastTree (Balanced (_ ** arr))     t =
      case tryNatToFin (minus n 1) of
        Nothing   =>
          (assert_total $ idris_crash "Data.RRBVector.viewr: can't convert Nat to Fin") # t
        Just last =>
          let lasttree # t := get arr last t
            in assert_total $ lastTree lasttree t
    lastTree (Unbalanced (_ ** arr) _) t =
      case tryNatToFin (minus n 1) of
        Nothing   =>
          (assert_total $ idris_crash "Data.RRBVector.viewr: can't convert Nat to Fin") # t
        Just last =>
          let lasttree # t := get arr last t
            in assert_total $ lastTree lasttree t
    lastTree (Leaf (_ ** arr))         t =
      case tryNatToFin (minus n 1) of
        Nothing   =>
          (assert_total $ idris_crash "Data.RRBVector.viewr: can't convert Nat to Fin") # t
        Just last =>
          get arr last t

--------------------------------------------------------------------------------
--          Transformation
--------------------------------------------------------------------------------

private
mapTree :  {n : Nat}
        -> (F1 s a -> F1 s b)
        -> (arr : MArray s n (Tree1 s a))
        -> F1 s (MArray s n (Tree1 s b))
mapTree f arr t =
  let tmt # t := unsafeMArray1 n t
    in go 0 n tmt t
  where
    go :  (m, x : Nat)
       -> (arr' : MArray s n (Tree1 s b))
       -> {auto v : Ix x n}
       -> F1 s (MArray s n (Tree1 s b))
    go m Z     arr' t =
      arr' # t
    go m (S j) arr' t =
      let j' # t := getIx arr j t
        in case j' of
             (Balanced (b ** arr''))         =>
               case tryNatToFin m of
                 Nothing =>
                   (assert_total $ idris_crash "Data.RRBVector.mapTree: can't convert Nat to Fin") # t
                 Just m' =>
                   let arr''' # t := assert_total $ mapTree f arr'' t
                       arr''''    := Balanced {bsize=b} (b ** arr''')
                       ()     # t := set arr' m' arr'''' t
                     in go (S m) j arr' t
             (Unbalanced (u ** arr'') sizes) =>
               case tryNatToFin m of
                 Nothing =>
                   (assert_total $ idris_crash "Data.RRBVector.mapTree.go: can't convert Nat to Fin") # t
                 Just m' =>
                   let arr''' # t := assert_total $ mapTree f arr'' t
                       arr''''    := Unbalanced (u ** arr''') sizes
                       ()     # t := set arr' m' arr'''' t
                     in go (S m) j arr' t
             (Leaf (l ** arr''))             =>
               case tryNatToFin m of
                 Nothing =>
                   (assert_total $ idris_crash "Data.RRBVector.mapTree.go: can't convert Nat to Fin") # t
                 Just m' =>
                   let arr''' # t := mmap f arr'' t
                       arr''''    := Leaf {lsize=l} (l ** arr''')
                       ()     # t := set arr' m' arr'''' t
                     in go (S m) j arr' t

||| Apply the function to every element. O(n)
export
map :  {n : Nat}
    -> (F1 s a -> F1 s b)
    -> RRBVector1 s n a
    -> F1 s (n' ** RRBVector1 s n' b)
map _ Empty                                   t =
  (0 ** Empty) # t
map f (Root sh (Balanced (b ** arr)))         t =
  let arr' # t := mapTree f arr t
      arr''    := Balanced {bsize=b} (b ** arr')
    in (n ** Root sh arr'') # t
map f (Root sh (Unbalanced (u ** arr) sizes)) t =
  let arr' # t := mapTree f arr t
      arr''    := Unbalanced (u ** arr') sizes
    in (n ** Root sh arr'') # t
map f (Root sh (Leaf (l ** arr)))             t =
  let arr' # t := mmap f arr t
      arr''    := Leaf {lsize=l} (l ** arr')
    in (n ** Root sh arr'') # t

--------------------------------------------------------------------------------
--          Concatenation
--------------------------------------------------------------------------------

||| Create a new tree with shift sh.
private
newBranch :  a
          -> Shift
          -> F1 s (Tree1 s a)
newBranch x 0  t =
  let x' # t := Data.RRBVector1.Sized.Internal.singleton x t
    in (Leaf {lsize=1} (1 ** x')) # t
newBranch x sh t =
  let branch # t := assert_total $ newBranch x (down sh) t
      x'     # t := Data.RRBVector1.Sized.Internal.singleton' branch t
    in (Balanced {bsize=1} (1 ** x')) # t

||| Create a new tree with shift sh.
private
newBranch' :  Tree1 s a
           -> Shift
           -> F1 s (Tree1 s (Tree1 s a))
newBranch' tree 0  t =
  (assert_total $ idris_crash "Data.RRBVector1.newBranch': impossible zero shift with a (Tree1 s a).") # t
newBranch' tree sh t =
  let branch  # t := assert_total $ newBranch' tree (down sh) t
      tree'   # t := Data.RRBVector1.Sized.Internal.singleton' branch t
    in (Balanced {bsize=1} (1 ** tree')) # t

||| Add an element to the left end of the vector. O(log n)
export
(<|) :  {n : Nat}
     -> a
     -> RRBVector1 s n a
     -> F1 s (n' ** RRBVector1 s n' a)
(x <| Empty)          t =
  let s # t := Data.RRBVector1.Sized.singleton x t
    in (1 ** s) # t
(x <| (Root sh tree)) t =
  let sh' # t := insertshift t
    in case compare sh' sh of
         LT =>
           let constree # t := consTree sh tree t
             in ((plus n 1) ** Root sh constree) # t
         EQ =>
           let constree # t := consTree sh tree t
             in ((plus n 1) ** Root sh constree) # t
         GT =>
           let newtree # t := newBranch x sh t
               newlist     := [newtree, tree]
               new     # t := unsafeMArray1 (length newlist) t
               ()      # t := writeList new newlist t
               new'    # t := computeSizes sh' new t
             in ((plus n 1) ** Root sh' new') # t
  where
    -- compute the shift at which the new branch needs to be inserted (0 means there is space in the leaf)
    -- the size is computed for efficient calculation of the shift in a balanced subtree
    computeShift :  Nat
                 -> Nat
                 -> Nat
                 -> Tree1 s a
                 -> F1 s Nat
    computeShift sz sh min (Balanced _)                  t =
      -- sz - 1 is the index of the last element
      let comp     := mult (log2 (minus sz 1) `div` blockshift) blockshift -- the shift of the root when normalizing
          hishift  := case compare comp 0 of
                        LT =>
                          0
                        EQ =>
                          0
                        GT =>
                          comp
          hi       := (natToInteger $ minus sz 1) `shiftR` hishift -- the length of the root node when normalizing minus 1
          newshift := case compare hi (natToInteger blockmask) of
                        LT =>
                          hishift
                        EQ =>
                          plus hishift blockshift
                        GT =>
                          plus hishift blockshift
        in case compare newshift sh of
             LT =>
               newshift # t
             EQ =>
               newshift # t
             GT =>
               min # t
    computeShift _  sh min (Unbalanced (u ** arr) sizes) t =
      case tryNatToFin 0 of
        Nothing   =>
          (assert_total $ idris_crash "Data.RRBVector1.(<|).computeShift.Unbalanced: can't convert Nat to Fin") # t
        Just zero =>
          let newtree # t := get arr zero t
            in case tryNatToFin 0 of
                 Nothing    =>
                   (assert_total $ idris_crash "Data.RRBVector1.(<|).computeShift.Unbalanced: can't convert Nat to Fin") # t
                 Just zero' =>
                   let sz' := at sizes zero'
                     in case compare u blocksize of
                          LT =>
                            assert_total $ computeShift sz' (down sh) sh newtree t
                          EQ =>
                            assert_total $ computeShift sz' (down sh) min newtree t
                          GT =>
                            assert_total $ computeShift sz' (down sh) min newtree t
    computeShift _  _  min (Leaf (l ** _))               t =
      case compare l blocksize of
        LT =>
          0 # t
        EQ =>
          min # t
        GT =>
          min # t
    insertshift : F1 s Nat
    insertshift t =
      computeShift n sh (up sh) tree t
    consTree :  Nat
             -> Tree1 s a
             -> F1 s (Tree1 s a)
    consTree sh (Balanced (_ ** arr))     t =
      let sh' # t := insertshift t
        in case compare sh sh' of
             LT =>
               case tryNatToFin 0 of
                 Nothing   =>
                   (assert_total $ idris_crash "Data.RRBVector1.(<|).consTree.Balanced: can't convert Nat to Fin") # t
                 Just zero =>
                   let newtree   # t := get arr zero t
                       newtree'  # t := assert_total $ consTree (down sh) newtree t
                       ()        # t := set arr zero newtree' t
                       newtree'' # t := computeSizes sh arr t
                     in newtree'' # t
             EQ =>
               let newtree   # t := newBranch x (down sh) t
                   arr'      # t := marray1 1 newtree t
                   arr''     # t := mappend arr' arr t
                   newtree'' # t := computeSizes sh arr'' t
                 in newtree'' # t
             GT =>
               case tryNatToFin 0 of
                 Nothing   =>
                   (assert_total $ idris_crash "Data.RRBVector1.(<|).consTree.Balanced: can't convert Nat to Fin") # t
                 Just zero =>
                   let newtree   # t := get arr zero t
                       newtree'  # t := assert_total $ consTree (down sh) newtree t
                       ()        # t := set arr zero newtree' t
                       newtree'' # t := computeSizes sh arr t
                     in newtree'' # t
    consTree sh (Unbalanced (_ ** arr) _) t =
      let sh' # t := insertshift t
        in case compare sh sh' of
             LT =>
               case tryNatToFin 0 of
                 Nothing   =>
                   (assert_total $ idris_crash "Data.RRBVector1.(<|).consTree.Unbalanced: can't convert Nat to Fin") # t
                 Just zero =>
                   let newtree   # t := get arr zero t
                       newtree'  # t := assert_total $ consTree (down sh) newtree t
                       ()        # t := set arr zero newtree' t
                       newtree'' # t := computeSizes sh arr t
                     in newtree'' # t
             EQ =>
               let newtree   # t := newBranch x (down sh) t
                   arr'      # t := marray1 1 newtree t
                   arr''     # t := mappend arr' arr t
                   newtree'' # t := computeSizes sh arr'' t
                 in newtree'' # t
             GT =>
               case tryNatToFin 0 of
                 Nothing   =>
                   (assert_total $ idris_crash "Data.RRBVector1.(<|).consTree.Unbalanced: can't convert Nat to Fin") # t
                 Just zero =>
                   let newtree   # t := get arr zero t
                       newtree'  # t := assert_total $ consTree (down sh) newtree t
                       ()        # t := set arr zero newtree' t
                       newtree'' # t := computeSizes sh arr t
                     in newtree'' # t
    consTree _  (Leaf (l ** arr))         t =
      let arr'  # t := marray1 1 x t
          arr'' # t := mappend arr' arr t
        in (Leaf {lsize=(S l)} ((S l) ** arr'')) # t

||| Add an element to the right end of the vector. O(log n)
export
(|>) :  {n : Nat}
     -> RRBVector1 s n a
     -> a
     -> F1 s (n' ** RRBVector1 s n' a)
(Empty |> x)        t =
  let s # t := Data.RRBVector1.Sized.singleton x t
    in (1 ** s) # t
(Root sh tree |> x) t =
  let sh' # t := insertshift t
    in case compare sh' sh of
         LT =>
           let snoctree # t := snocTree sh tree t
             in ((plus n 1) ** Root sh snoctree) # t
         EQ =>
           let snoctree # t := snocTree sh tree t
             in ((plus n 1) ** Root sh snoctree) # t
         GT =>
           let newtree # t := newBranch x sh t
               newlist     := [tree, newtree]
               new     # t := unsafeMArray1 (length newlist) t
               ()      # t := writeList new newlist t
               new'    # t := computeSizes sh' new t
             in ((plus n 1) ** Root sh' new') # t
  where
    -- compute the shift at which the new branch needs to be inserted (0 means there is space in the leaf)
    -- the size is computed for efficient calculation of the shift in a balanced subtree
    computeShift :  Nat
                 -> Nat
                 -> Nat
                 -> Tree1 s a
                 -> F1 s Nat
    computeShift sz sh min (Balanced _)                  t =
      -- sz - 1 is the index of the last element
      let newshift := mult (countTrailingZeros sz `div` blockshift) blockshift
        in case compare newshift sh of
             LT =>
               newshift # t
             EQ =>
               newshift # t
             GT =>
               min # t
    computeShift _  sh min (Unbalanced (u ** arr) sizes) t =
      case tryNatToFin $ minus u 1 of
        Nothing       =>
          (assert_total $ idris_crash "Data.RRBVector1.(|>).computeShift.Unbalanced: can't convert Nat to Fin") # t
        Just lastidx' =>
          let newtree # t := get arr lastidx' t
            in case tryNatToFin $ minus u 1 of
                 Nothing       =>
                   (assert_total $ idris_crash "Data.RRBVector1.(|>).computeShift.Unbalanced: can't convert Nat to Fin") # t
                 Just lastidx' =>
                   let sizes' := at sizes lastidx'
                     in case tryNatToFin $ minus (minus u 1) 1 of
                          Nothing    =>
                            (assert_total $ idris_crash "Data.RRBVector1.(|>).computeShift.Unbalanced: can't convert Nat to Fin") # t
                          Just lastidx'' =>
                            let sizes''     := at sizes lastidx''
                                sz'         := minus sizes' sizes''
                              in case compare u blocksize of
                                   LT =>
                                     assert_total $ computeShift sz' (down sh) sh newtree t
                                   EQ =>
                                     assert_total $ computeShift sz' (down sh) min newtree t
                                   GT =>
                                     assert_total $ computeShift sz' (down sh) min newtree t
    computeShift _  _  min (Leaf (l ** arr))             t =
      case compare l blocksize of
        LT =>
          0 # t
        EQ =>
          min # t
        GT =>
          min # t
    insertshift : F1 s Nat
    insertshift t =
      computeShift n sh (up sh) tree t
    snocTree :  Nat
             -> Tree1 s a
             -> F1 s (Tree1 s a)
    snocTree sh (Balanced (b ** arr))     t =
      let sh' # t := insertshift t
        in case compare sh sh' of
             LT =>
               case tryNatToFin $ minus b 1 of
                 Nothing      =>
                   (assert_total $ idris_crash "Data.RRBVector1.(|>).snocTree.Balanced: can't convert Nat to Fin") # t
                 Just lastidx =>
                   let newtree   # t := get arr lastidx t
                       newtree'  # t := assert_total $ snocTree (down sh) newtree t
                       ()        # t := set arr lastidx newtree' t
                       in (Balanced {bsize=b} (b ** arr)) # t
             EQ => -- the current subtree is fully balanced
               let newtree   # t := newBranch x (down sh) t
                   arr'      # t := marray1 1 newtree t
                   arr''     # t := mappend arr' arr t
                 in (Balanced {bsize=(S b)} ((S b) ** arr'')) # t
             GT =>
               case tryNatToFin $ minus b 1 of
                 Nothing      =>
                   (assert_total $ idris_crash "Data.RRBVector1.(|>).snocTree.Balanced: can't convert Nat to Fin") # t
                 Just lastidx =>
                   let newtree   # t := get arr lastidx t
                       newtree'  # t := assert_total $ snocTree (down sh) newtree t
                       ()        # t := set arr lastidx newtree' t
                     in (Balanced {bsize=b} (b ** arr)) # t
    snocTree sh (Unbalanced (u ** arr) sizes) t =
      let sh' # t := insertshift t
        in case compare sh sh' of
             LT =>
               case tryNatToFin $ minus u 1 of
                 Nothing       =>
                   (assert_total $ idris_crash "Data.RRBVector1.(|>).snocTree.Unbalanced: can't convert Nat to Fin") # t
                 Just lastidxa =>
                   let newtree  # t := get arr lastidxa t
                       newtree' # t := assert_total $ snocTree (down sh) newtree t
                       ()       # t := set arr lastidxa newtree' t
                     in case tryNatToFin $ minus u 1 of
                          Nothing       =>
                            (assert_total $ idris_crash "Data.RRBVector1.(|>).snocTree.Unbalanced: can't convert Nat to Fin") # t
                          Just lastidxs =>
                            let lastsize := plus (at sizes lastidxs) 1
                              in (Unbalanced (u ** arr)
                                             (setAt lastidxs lastsize sizes)
                                 ) # t
             EQ =>
                case tryNatToFin $ minus u 1 of
                  Nothing      =>
                    (assert_total $ idris_crash "Data.RRBVector1.(|>).snocTree.Unbalanced: can't convert Nat to Fin") # t
                  Just lastidx =>
                    let lastsize      := plus (at sizes lastidx) 1
                        newtree   # t := newBranch x (down sh) t
                        arr'      # t := marray1 1 newtree t
                        arr''     # t := mappend arr arr' t
                      in (Unbalanced ((plus u 1) ** arr'')
                                     (append sizes (fill 1 lastsize))
                         ) # t
             GT =>
               case tryNatToFin $ minus u 1 of
                 Nothing       =>
                   (assert_total $ idris_crash "Data.RRBVector1.(|>).snocTree.Unbalanced: can't convert Nat to Fin") # t
                 Just lastidxa =>
                   let newtree  # t := get arr lastidxa t
                       newtree' # t := assert_total $ snocTree (down sh) newtree t
                       ()       # t := set arr lastidxa newtree' t
                     in case tryNatToFin $ minus u 1 of
                          Nothing       =>
                            (assert_total $ idris_crash "Data.RRBVector1.(|>).snocTree.Unbalanced: can't convert Nat to Fin") # t
                          Just lastidxs =>
                            let lastsize := plus (at sizes lastidxs) 1
                              in (Unbalanced (u ** arr)
                                             (setAt lastidxs lastsize sizes)
                                 ) # t
    snocTree _  (Leaf (l ** arr))         t =
      let arr'  # t := marray1 1 x t
          arr'' # t := mappend arr arr' t
        in (Leaf {lsize=(plus l 1)} ((plus l 1) ** arr'')) # t

||| Concatenates two vectors. O(log(max(n1,n2)))
export
(><) :  {n1 : Nat}
     -> {n2 : Nat}
     -> RRBVector1 s n1 a
     -> RRBVector1 s n2 a
     -> F1 s (n' ** RRBVector1 s n' a)
(Empty          >< v)              t =
  (n2 ** v) # t
(v              >< Empty)          t =
  (n1 ** v) # t
(Root sh1 tree1 >< Root sh2 tree2) t =
  let upmaxshift := case compare sh1 sh2 of
                      LT =>
                        up sh2
                      EQ =>
                        up sh1
                      GT =>
                        up sh1
      (_ ** arr) # t := mergeTrees tree1 sh1 tree2 sh2 t
      arr'       # t := computeSizes upmaxshift arr t
      arr''          := Root upmaxshift arr'
      arr'''     # t := normalize arr'' t
    in ((plus n1 n2) ** arr''') #  t
  where
    viewlArr :  {n : Nat}
             -> MArray s n (Tree1 s a)
             -> F1 s (Tree1 s a, MArray s (n `minus` 1) (Tree1 s a))
    viewlArr arr t =
      case tryNatToFin 0 of
        Nothing   =>
          (assert_total $ idris_crash "Data.RRBVector1.(><).viewlArr: can't convert Nat to Fin") # t
        Just zero =>
          let arr'  # t := get arr zero t
              arr'' # t := mdrop 1 arr t
            in (arr', arr'') # t
    viewrArr :  {n : Nat}
             -> MArray s n (Tree1 s a)
             -> F1 s (MArray s (n `minus` 1) (Tree1 s a), Tree1 s a)
    viewrArr arr with ((minus n 1) <= n) proof eq
      _ | True  = \t =>
        case tryNatToFin $ minus n 1 of
          Nothing   =>
            (assert_total $ idris_crash "Data.RRBVector.(><).viewrArr: can't convert Nat to Fin") # t
          Just last =>
            let arr'  # t := get arr last t
                arr'' # t := mtake arr (minus n 1) @{lteOpReflectsLTE _ _ eq} t
              in (arr'', arr') # t
      _ | False = \t =>
        (assert_total $ idris_crash "Data.RRBVector1.(><).viewrArr: index out of bounds") # t
    takeArr :  {n : Nat}
            -> {blocksize : Nat}
            -> MArray s n a
            -> F1 s (MArray s blocksize a)
    takeArr arr with (blocksize <= n) proof eq
      _ | True  = \t =>
        mtake arr blocksize @{lteOpReflectsLTE _ _ eq} t
      _ | False = \t =>
        (assert_total $ idris_crash "Data.RRBVector1.(><).takeArr: index out of bounds") # t
    mergeRebalanceInternalGo' :  (x : Nat)
                              -> (sh : Shift)
                              -> MArray s n (Tree1 s a)
                              -> (o ** MArray s o (Tree1 s a))
                              -> (p ** MArray s p (Tree1 s a))
                              -> (q ** MArray s q (Tree1 s a))
                              -> {auto v : Ix x n}
                              -> F1 s ((o' ** MArray s o' (Tree1 s a)), (p' ** MArray s p' (Tree1 s a)), (q' ** MArray s q' (Tree1 s a)))
    mergeRebalanceInternalGo' Z      _  _    (o ** newnode'') (p ** newsubtree'') (q ** newroot'') t =
      ((o ** newnode''), (p ** newsubtree''), (q ** newroot'')) # t
    mergeRebalanceInternalGo' (S j') sh arr' (o ** newnode'') (p ** newsubtree'') (q ** newroot'') t =
      case o == blocksize of
        True  =>
          case p == blocksize of
            True  =>
              let newnode'''       # t := computeSizes (down sh) newnode'' t
                  newnode''''      # t := marray1 1 newnode''' t
                  newsubtree'''    # t := mappend newsubtree'' newnode'''' t
                  newnode'''''     # t := unsafeMArray1 0 t
                  newsubtree''''   # t := computeSizes sh newsubtree''' t
                  newsubtree'''''  # t := marray1 1 newsubtree'''' t
                  newroot'''       # t := mappend newroot'' newsubtree''''' t
                  newsubtree'''''' # t := unsafeMArray1 0 t
                  j''              # t := getIx arr' j' t
                  newnode''''''    # t := marray1 1 j'' t
                  newnode'''''''   # t := mappend newnode''''' newnode'''''' t
                in mergeRebalanceInternalGo' j' sh arr' (1 ** newnode''''''') (0  ** newsubtree'''''') ((plus q 1) ** newroot''') t
            False =>
              let newnode'''       # t := computeSizes (down sh) newnode'' t
                  newnode''''      # t := marray1 1 newnode''' t
                  newsubtree'''    # t := mappend newsubtree'' newnode'''' t
                  newnode'''''     # t := unsafeMArray1 0 t
                  j''              # t := getIx arr' j' t
                  newnode''''''    # t := marray1 1 j'' t
                  newnode'''''''   # t := mappend newnode''''' newnode'''''' t
                in mergeRebalanceInternalGo' j' sh arr' (1 ** newnode''''''') ((plus p 1) ** newsubtree''') (q ** newroot'') t
        False =>
          let j''           # t := getIx arr' j' t
              newnode'''    # t := marray1 1 j'' t
              newnode''''   # t := mappend newnode'' newnode''' t
            in mergeRebalanceInternalGo' j' sh arr' ((plus o 1) ** newnode'''') (p ** newsubtree'') (q ** newroot'') t
    mergeRebalanceInternalGo :  (x : Nat)
                             -> (sh : Shift)
                             -> MArray s n (Tree1 s a)
                             -> (o ** MArray s o (Tree1 s a))
                             -> (p ** MArray s p (Tree1 s a))
                             -> (q ** MArray s q (Tree1 s a))
                             -> {auto v : Ix x n}
                             -> F1 s (r ** MArray s r (Tree1 s a))
    mergeRebalanceInternalGo Z     sh arr (_ ** newnode') (_ ** newsubtree') (q ** newroot') t =
      let newnode''      # t := computeSizes (down sh) newnode' t
          newnode'''     # t := marray1 1 newnode'' t
          newsubtree''   # t := mappend newsubtree' newnode''' t
          newsubtree'''  # t := computeSizes sh newsubtree'' t
          newsubtree'''' # t := marray1 1 newsubtree''' t
          newroot''      # t := mappend newroot' newsubtree'''' t
        in ((plus q 1) ** newroot'') # t
    mergeRebalanceInternalGo (S j) sh arr (o ** newnode') (p ** newsubtree') (q ** newroot') t =
      let j'  # t := getIx arr j t
          j''     := treeToArray j'
        in case j'' of
             Left  (b ** arr') =>
               let ((o' ** newnode''), (p' ** newsubtree''), (q' ** newroot'')) # t := mergeRebalanceInternalGo' b sh arr' (o ** newnode') (p ** newsubtree') (q ** newroot') t
                 in mergeRebalanceInternalGo j sh arr (o' ** newnode'') (p' ** newsubtree'') (q' ** newroot'') t
             Right (u ** arr') =>
               let ((o' ** newnode''), (p' ** newsubtree''), (q' ** newroot'')) # t := mergeRebalanceInternalGo' u sh arr' (o ** newnode') (p ** newsubtree') (q ** newroot') t
                 in mergeRebalanceInternalGo j sh arr (o' ** newnode'') (p' ** newsubtree'') (q' ** newroot'') t
    mergeRebalanceInternal' :  {n : Nat}
                            -> Shift
                            -> MArray s n (Tree1 s a)
                            -> F1 s (r ** MArray s r (Tree1 s a))
    mergeRebalanceInternal' sh lcr t =
      let newnode        # t := unsafeMArray1 0 t
          newsubtree     # t := unsafeMArray1 0 t
          newroot        # t := unsafeMArray1 0 t
        in mergeRebalanceInternalGo n sh lcr (0 ** newnode) (0 ** newsubtree) (0 ** newroot) t
    mergeRebalance' :  {n : Nat}
                    -> {m : Nat}
                    -> {o : Nat}
                    -> Shift
                    -> MArray s n (Tree1 s a)
                    -> MArray s m (Tree1 s a)
                    -> MArray s o (Tree1 s a)
                    -> F1 s (r ** MArray s r (Tree1 s a))
    mergeRebalance' sh left center right t =
      let centerright     # t := mappend center right t
          leftcenterright # t := mappend left centerright t
        in mergeRebalanceInternal' sh
                                   leftcenterright
                                   t
    mergeRebalanceInternalGo''' :  (x : Nat)
                                -> (sh : Shift)
                                -> MArray s n a
                                -> (o ** MArray s o a)
                                -> (p ** MArray s p (Tree1 s a))
                                -> (q ** MArray s q (Tree1 s a))
                                -> {auto v : Ix x n}
                                -> F1 s ((o' ** MArray s o' a), (p' ** MArray s p' (Tree1 s a)), (q' ** MArray s q' (Tree1 s a)))
    mergeRebalanceInternalGo''' Z      _  _    (o ** newnode'') (p ** newsubtree'') (q ** newroot'') t =
      ((o ** newnode''), (p ** newsubtree''), (q ** newroot'')) # t
    mergeRebalanceInternalGo''' (S j') sh arr' (o ** newnode'') (p ** newsubtree'') (q ** newroot'') t =
      case o == blocksize of
        True  =>
          case p == blocksize of
            True  =>
              let newnode'''           := Leaf {lsize=0} (o ** newnode'')
                  newnode''''      # t := marray1 1 newnode''' t
                  newsubtree'''    # t := mappend newsubtree'' newnode'''' t
                  newnode'''''     # t := unsafeMArray1 0 t
                  newsubtree''''   # t := computeSizes sh newsubtree''' t
                  newsubtree'''''  # t := marray1 1 newsubtree'''' t
                  newroot'''       # t := mappend newroot'' newsubtree''''' t
                  newsubtree'''''' # t := unsafeMArray1 0 t
                  j''              # t := getIx arr' j' t
                  newnode''''''    # t := marray1 1 j'' t
                  newnode'''''''   # t := mappend newnode''''' newnode'''''' t
                in mergeRebalanceInternalGo''' j' sh arr' (1 ** newnode''''''') (0  ** newsubtree'''''') ((plus q 1) ** newroot''') t
            False =>
              let newnode'''           := Leaf {lsize=0} (o ** newnode'')
                  newnode''''      # t := marray1 1 newnode''' t
                  newsubtree'''    # t := mappend newsubtree'' newnode'''' t
                  newnode'''''     # t := unsafeMArray1 0 t
                  j''              # t := getIx arr' j' t
                  newnode''''''    # t := marray1 1 j'' t
                  newnode'''''''   # t := mappend newnode''''' newnode'''''' t
                in mergeRebalanceInternalGo''' j' sh arr' (1 ** newnode''''''') ((plus p 1) ** newsubtree''') (q ** newroot'') t
        False =>
          let j''           # t := getIx arr' j' t
              newnode'''    # t := marray1 1 j'' t
              newnode''''   # t := mappend newnode'' newnode''' t
            in mergeRebalanceInternalGo''' j' sh arr' ((plus o 1) ** newnode'''') (p ** newsubtree'') (q ** newroot'') t
    mergeRebalanceInternalGo'' :  (x : Nat)
                               -> (sh : Shift)
                               -> MArray s n (Tree1 s a)
                               -> (o ** MArray s o a)
                               -> (p ** MArray s p (Tree1 s a))
                               -> (q ** MArray s q (Tree1 s a))
                               -> {auto v : Ix x n}
                               -> F1 s (r ** MArray s r (Tree1 s a))
    mergeRebalanceInternalGo'' Z     sh arr (o ** newnode') (_ ** newsubtree') (q ** newroot') t =
      let newnode''          := Leaf {lsize=o} (o ** newnode')
          newnode'''     # t := marray1 1 newnode'' t
          newsubtree''   # t := mappend newsubtree' newnode''' t
          newsubtree'''  # t := computeSizes sh newsubtree'' t
          newsubtree'''' # t := marray1 1 newsubtree''' t
          newroot''      # t := mappend newroot' newsubtree'''' t
        in ((plus q 1) ** newroot'') # t
    mergeRebalanceInternalGo'' (S j) sh arr (o ** newnode') (p ** newsubtree') (q ** newroot') t =
      let j'                                                           # t := getIx arr j t
          (l ** arr')                                                      := treeToArray' j'
          ((o' ** newnode''), (p' ** newsubtree''), (q' ** newroot'')) # t := mergeRebalanceInternalGo''' l sh arr' (o ** newnode') (p ** newsubtree') (q ** newroot') t
        in mergeRebalanceInternalGo'' j sh arr (o' ** newnode'') (p' ** newsubtree'') (q' ** newroot'') t
    mergeRebalanceInternal'' :  {n : Nat}
                             -> Shift
                             -> MArray s n (Tree1 s a)
                             -> F1 s (r ** MArray s r (Tree1 s a))
    mergeRebalanceInternal'' sh lcr t =
      let newnode        # t := unsafeMArray1 0 t
          newsubtree     # t := unsafeMArray1 0 t
          newroot        # t := unsafeMArray1 0 t
        in mergeRebalanceInternalGo'' n sh lcr (0 ** newnode) (0 ** newsubtree) (0 ** newroot) t
    mergeRebalance'' :  {n : Nat}
                     -> {m : Nat}
                     -> {o : Nat}
                     -> Shift
                     -> MArray s n (Tree1 s a)
                     -> MArray s m (Tree1 s a)
                     -> MArray s o (Tree1 s a)
                     -> F1 s (r ** MArray s r (Tree1 s a))
    mergeRebalance'' sh left center right t =
      let centerright     # t := mappend center right t
          leftcenterright # t := mappend left centerright t
        in mergeRebalanceInternal'' sh
                                    leftcenterright
                                    t
    mergeRebalance :  {n : Nat}
                   -> {m : Nat}
                   -> {o : Nat}
                   -> Shift
                   -> MArray s n (Tree1 s a)
                   -> MArray s m (Tree1 s a)
                   -> MArray s o (Tree1 s a)
                   -> F1 s (r ** MArray s r (Tree1 s a))
    mergeRebalance sh left center right t =
      case compare sh blockshift of
        LT =>
          mergeRebalance' sh left center right t
        EQ =>
          mergeRebalance'' sh left center right t
        GT =>
          mergeRebalance' sh left center right t
    mergeTrees :  Tree1 s a
               -> Nat
               -> Tree1 s a
               -> Nat
               -> F1 s (r ** MArray s r (Tree1 s a))
    mergeTrees tree1@(Leaf (l1 ** arr1)) _   tree2@(Leaf (l2 ** arr2)) _   t =
      case compare l1 blocksize of
        LT =>
          let arr' # t := mappend arr1 arr2 t
            in case compare (plus l1 l2) blocksize of
                 LT =>
                   let newtree   := Leaf {lsize=(plus l1 l2)} ((plus l1 l2) ** arr')
                       arr'' # t := singleton' newtree t
                     in (1 ** arr'') # t
                 EQ =>
                   let newtree   := Leaf {lsize=(plus l1 l2)} ((plus l1 l2) ** arr')
                       arr'' # t := singleton' newtree t
                     in (1 ** arr'') # t
                 GT =>
                   let left  # t := takeArr arr' t
                       right # t := mdrop blocksize arr' t
                       lefttree  := Leaf {lsize=blocksize} (blocksize ** left)
                       righttree := Leaf {lsize=(minus (plus l1 l2) blocksize)} ((minus (plus l1 l2) blocksize) ** right)
                       newlist   := [lefttree, righttree]
                       arr'' # t := unsafeMArray1 (length newlist) t
                       ()    # t := writeList arr'' newlist t
                     in ((length newlist) ** arr'') # t
        EQ =>
          let newlist   := [tree1, tree2]
              arr'' # t := unsafeMArray1 (length newlist) t
              ()    # t := writeList arr'' newlist t
            in ((length newlist) ** arr'') # t
        GT =>
          let arr' # t := mappend arr1 arr2 t
            in case compare (plus l1 l2) blocksize of
                 LT =>
                   let newtree   := Leaf {lsize=(plus l1 l2)} ((plus l1 l2) ** arr')
                       arr'' # t := singleton' newtree t
                     in (1 ** arr'') # t
                 EQ =>
                   let newtree   := Leaf {lsize=(plus l1 l2)} ((plus l1 l2) ** arr')
                       arr'' # t := singleton' newtree t
                     in (1 ** arr'') # t
                 GT =>
                   let left  # t := takeArr arr' t
                       right # t := mdrop blocksize arr' t
                       lefttree  := Leaf {lsize=blocksize} (blocksize ** left)
                       righttree := Leaf {lsize=(minus (plus l1 l2) blocksize)} ((minus (plus l1 l2) blocksize) ** right)
                       newlist   := [lefttree, righttree]
                       arr'' # t := unsafeMArray1 (length newlist) t
                       ()    # t := writeList arr'' newlist t
                     in ((length newlist) ** arr'') # t
    mergeTrees tree1                     sh1 tree2                     sh2 t =
      case compare sh1 sh2 of
        LT =>
          let right := treeToArray tree2
            in case right of
                 Left  (_ ** arr) =>
                   let (righthead, righttail) # t := viewlArr arr t
                       (_ ** merged)          # t := assert_total $ mergeTrees tree1 sh1 righthead (down sh2) t
                       emptyarr               # t := unsafeMArray1 0 t
                     in mergeRebalance sh2 emptyarr merged righttail t
                 Right (_ ** arr) =>
                   let (righthead, righttail) # t := viewlArr arr t
                       (_ ** merged)          # t := assert_total $ mergeTrees tree1 sh1 righthead (down sh2) t
                       emptyarr               # t := unsafeMArray1 0 t
                     in mergeRebalance sh2 emptyarr merged righttail t
        EQ =>
          let left := treeToArray tree1
            in case left of
                 Left  (_ ** arr) =>
                   let right := treeToArray tree2
                     in case right of
                          Left  (_ ** arr') =>
                            let (leftinit, leftlast)   # t := viewrArr arr t
                                (righthead, righttail) # t := viewlArr arr' t
                                (_ ** merged)          # t := assert_total $ mergeTrees leftlast (down sh1) righthead (down sh2) t
                              in mergeRebalance sh1 leftinit merged righttail t
                          Right (_ ** arr') =>
                            let (leftinit, leftlast)   # t := viewrArr arr t
                                (righthead, righttail) # t := viewlArr arr' t
                                (_ ** merged)          # t := assert_total $ mergeTrees leftlast (down sh1) righthead (down sh2) t
                              in mergeRebalance sh1 leftinit merged righttail t
                 Right (_ ** arr) =>
                   let right := treeToArray tree2
                     in case right of
                          Left  (_ ** arr') =>
                            let (leftinit, leftlast)   # t := viewrArr arr t
                                (righthead, righttail) # t := viewlArr arr' t
                                (_ ** merged)          # t := assert_total $ mergeTrees leftlast (down sh1) righthead (down sh2) t
                              in mergeRebalance sh1 leftinit merged righttail t
                          Right (_ ** arr') =>
                            let (leftinit, leftlast)   # t := viewrArr arr t
                                (righthead, righttail) # t := viewlArr arr' t
                                (_ ** merged)          # t := assert_total $ mergeTrees leftlast (down sh1) righthead (down sh2) t
                              in mergeRebalance sh1 leftinit merged righttail t
        GT =>
          let left := treeToArray tree1
            in case left of
                 Left  (_ ** arr) =>
                   let (leftinit, leftlast) # t := viewrArr arr t
                       (_ ** merged)        # t := assert_total $ mergeTrees leftlast (down sh1) tree2 sh2 t
                       emptyarr             # t := unsafeMArray1 0 t
                     in mergeRebalance sh1 leftinit merged emptyarr t
                 Right (_ ** arr) =>
                   let (leftinit, leftlast) # t := viewrArr arr t
                       (_ ** merged)        # t := assert_total $ mergeTrees leftlast (down sh1) tree2 sh2 t
                       emptyarr             # t := unsafeMArray1 0 t
                     in mergeRebalance sh1 leftinit merged emptyarr t

||| Insert an element at the given index, shifting the rest of the vector over.
||| If the index is negative, add the element to the left end of the vector.
||| If the index is bigger than or equal to the length of the vector, add the element to the right end of the vector. O(log n)
export
insertAt :  {n : Nat}
         -> Nat
         -> a
         -> RRBVector1 s n a
         -> F1 s (n' ** RRBVector1 s n' a)
insertAt i x v t =
  let ((tt ** left), (dt ** right)) # t := Data.RRBVector1.Sized.splitAt i v t
      (l  ** left')                 # t := ((|>) left x) t
    in (><) left' right t

||| Delete the element at the given index.
||| If the index is out of range, return the original vector. O(log n)
export
deleteAt :  {n : Nat}
         -> Nat
         -> RRBVector1 s n a
         -> F1 s (n' ** RRBVector1 s n' a)
deleteAt i v t =
  let ((tt ** left), (dt ** right)) # t := Data.RRBVector1.Sized.splitAt (plus i 1) v t
      (l' ** left')                 # t := take i left t
    in (><) left' right t
