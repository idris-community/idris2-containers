||| General purpose linear two-end finite sequences.
|||
||| This is implemented by finger tree.
module Data.Seq1.Unsized

import Control.WellFounded
import Data.Linear.Ref1
import public Data.Zippable

import Data.Seq.Internal

%default total

||| A linear two-end finite sequence.
export
data Seq1 : (s : Type) -> (e : Type) -> Type where
  MkSeq1 : Ref s (FingerTree (Elem e))
        -> Seq1 s e

||| O(1). The empty sequence.
export
empty : F1 s (Seq1 s e)
empty t =
  let tr # t := ref1 Empty t
    in (MkSeq1 tr) # t

||| O(1). A singleton sequence.
export
singleton :  e
          -> F1 s (Seq1 s e)
singleton a t =
  let tr # t := ref1 (Single (MkElem a)) t
    in (MkSeq1 tr) # t

||| O(n). A sequence of length n with a the value of every element.
export
replicate :  (n : Nat)
          -> (a : e)
          -> F1 s (Seq1 s e)
replicate n a t =
  let tr # t := ref1 (replicate' n a) t
    in (MkSeq1 tr) # t

||| O(1). The number of elements in the sequence.
export
length :  Seq1 s a
       -> F1 s Nat
length (MkSeq1 tr) t =
  let tr' # t := read1 tr t
    in (length' tr') # t

||| O(n). Reverse the sequence.
export
reverse :  Seq1 s a
        -> F1' s
reverse (MkSeq1 tr) t =
  let tr' # t := read1 tr t
    in casswap1 tr (reverseTree id tr') t

export infixr 5 `cons`
||| O(1). Add an element to the left end of a sequence.
export
cons :  e
     -> Seq1 s e
     -> F1' s
(a `cons` (MkSeq1 tr)) t =
  let tr' # t := read1 tr t
    in casswap1 tr (MkElem a `consTree` tr') t

export infixl 5 `snoc`
||| O(1). Add an element to the right end of a sequence.
export
snoc :  Seq1 s e
     -> e
     -> F1' s
((MkSeq1 tr) `snoc` a) t =
  let tr' # t := read1 tr t
    in casswap1 tr (tr' `snocTree` MkElem a) t

||| O(log(min(m, n))). Concatenate two sequences.
export
(++) :  Seq1 s e
     -> Seq1 s e
     -> F1 s (Seq1 s e)
((MkSeq1 t1) ++ (MkSeq1 t2)) t =
  let t1'  # t := read1 t1 t
      t2'  # t := read1 t2 t
      t1t2 # t := ref1 (addTree0 t1' t2') t
    in (MkSeq1 t1t2) # t

||| O(1). View from the left of the sequence.
export
viewl :  Seq1 s e
      -> F1 s (Maybe (e, Seq1 s e))
viewl (MkSeq1 tr) t =
  let tr' # t := read1 tr t
    in case viewLTree tr' of
         Just (MkElem a, tr') =>
           let () # t := casswap1 tr tr' t
             in (Just (a, MkSeq1 tr)) # t
         Nothing              =>
           Nothing # t

||| O(1). The first element of the sequence.
export
head :  Seq1 s e
     -> F1 s (Maybe e)
head seq t =
  let seq' # t := viewl seq t
    in case seq' of
         Nothing     =>
           Nothing # t
         Just (h, _) =>
           (Just h) # t
||| O(1). The elements after the head of the sequence.
||| Returns an empty sequence when the sequence is empty.
export
tail :  Seq1 s e
     -> F1 s (Seq1 s e)
tail seq t =
  let seq' # t := viewl seq t
    in case seq' of
         Just (_, seq'') =>
           seq'' # t
         Nothing          =>
           empty t

||| O(1). View from the right of the sequence.
export
viewr :  Seq1 s e
      -> F1 s (Maybe (Seq1 s e, e))
viewr (MkSeq1 tr) t =
  let tr' # t := read1 tr t
    in case viewRTree tr' of
         Just (tr', MkElem a) =>
           let () # t := casswap1 tr tr' t
             in (Just (MkSeq1 tr, a)) # t
         Nothing              =>
          Nothing # t

||| O(1). The elements before the last element of the sequence.
||| Returns an empty sequence when the sequence is empty.
export
init :  Seq1 s e
     -> F1 s (Seq1 s e)
init seq t =
  let seq' # t := viewr seq t
    in case seq' of
         Just (seq'', _) =>
           seq'' # t
         Nothing         =>
           empty t

||| O(1). The last element of the sequence.
export
last :  Seq1 s e
     -> F1 s (Maybe e)
last seq t =
  let seq' # t := viewr seq t
    in case seq' of
         Nothing     =>
           Nothing # t
         Just (_, l) =>
           (Just l) # t

||| O(n). Turn a list into a sequence.
export
fromList :  List e
         -> F1 s (Seq1 s e)
fromList xs t =
  let seq # t := ref1 (foldr (\x, t => MkElem x `consTree` t) Empty xs) t
    in (MkSeq1 seq) # t

||| Turn a sequence into a list. O(n)
export
toList :  Seq1 s e
       -> F1 s (List e)
toList seq t =
  go seq Lin t
  where
    go :  Seq1 s e
       -> (sl : SnocList e)
       -> F1 s (List e)
    go seq sl t =
      let seq' # t := viewl seq t
        in case seq' of
             Nothing         =>
               (sl <>> []) # t
             Just (x, seq'') =>
               (assert_total (go seq'' (sl :< x))) t

||| O(log(min(i, n-i))). The element at the specified position.
export
index :  Nat
      -> Seq1 s e
      -> F1 s (Maybe e)
index i (MkSeq1 tr) t =
  let tr' # t := read1 tr t
    in case i < length' tr' of
         True  =>
           let (_, MkElem a) := lookupTree i tr'
             in (Just a) # t
         False =>
           Nothing # t

||| O(log(min(i, n-i))). Update the element at the specified position.
||| If the position is out of range, the original sequence is returned.
export
adjust :  (e -> e)
       -> Nat
       -> Seq1 s e
       -> F1 s (Seq1 s e)
adjust f i (MkSeq1 tr) t =
  let tr' # t := read1 tr t
    in case i < length' tr' of
         True  =>
           let () # t := casswap1 tr (adjustTree (const (map f)) i tr') t
             in (MkSeq1 tr) # t
         False =>
           (MkSeq1 tr) # t

||| O(log(min(i, n-i))). Replace the element at the specified position.
||| If the position is out of range, the original sequence is returned.
export
update :  Nat
       -> e
       -> Seq1 s e
       -> F1 s (Seq1 s e)
update i a seq t =
  adjust (const a) i seq t

||| O(log(min(i, n-i))). Split a sequence at a given position.
||| splitAt i s = (take i s, drop i s)
export
splitAt :  Nat
        -> Seq1 s e
        -> F1 s ((Seq1 s e, Seq1 s e))
splitAt i (MkSeq1 tr) t =
  let tr' # t := read1 tr t
    in case i < length' tr' of
         True  =>
           let (l, r) := split i tr'
               l' # t := ref1 l t
               r' # t := ref1 r t
             in (MkSeq1 l', MkSeq1 r') # t
         False =>
           let seq' # t := Data.Seq1.Unsized.empty t
             in (MkSeq1 tr, seq') # t

||| O(log(min(i,n-i))). The first i elements of a sequence.
||| If the sequence contains fewer than i elements, the whole sequence is returned.
export
take :  Nat
     -> Seq1 s e
     -> F1 s (Seq1 s e)
take i seq t =
  let (seq1, _) # t := Data.Seq1.Unsized.splitAt i seq t
    in seq1 # t

||| O(log(min(i,n-i))). Elements of a sequence after the first i.
||| If the sequence contains fewer than i elements, the empty sequence is returned.
export
drop :  Nat
     -> Seq1 s e
     -> F1 s (Seq1 s e)
drop i seq t =
  let (_, seq2) # t := Data.Seq1.Unsized.splitAt i seq t
    in seq2 # t

||| Dump the internal structure of the finger tree.
export
show' :  Show e
      => Seq1 s e
      -> F1 s String
show' (MkSeq1 tr) t =
  let tr' # t := read1 tr t
    in (showPrec Open tr') # t
