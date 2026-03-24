||| General purpose linear two-end finite sequences.
|||
||| This is implemented by finger tree.
module Data.Seq1.Unsized

import Control.WellFounded
import Data.Linear.Ref1
import public Data.Zippable

import Data.Seq.Internal
import Data.Seq.Unsized

%default total

||| A linear two-end finite sequence.
export
data Seq1 : (s : Type) -> (e : Type) -> Type where
  MkSeq1 : Ref s (Seq e)
        -> Seq1 s e

||| O(1). The empty sequence.
export
empty : F1 s (Seq1 s e)
empty t =
  let seq # t := ref1 (MkSeq Empty) t
    in (MkSeq1 seq) # t

||| O(1). A singleton sequence.
export
singleton :  e
          -> F1 s (Seq1 s e)
singleton a t =
  let seq # t := ref1 (MkSeq (Single (MkElem a))) t
    in (MkSeq1 seq) # t

||| O(n). A sequence of length n with a the value of every element.
export
replicate :  (n : Nat)
          -> (a : e)
          -> F1 s (Seq1 s e)
replicate n a t =
  let seq # t := ref1 (MkSeq (replicate' n a)) t
    in (MkSeq1 seq) # t

||| O(1). The number of elements in the sequence.
export
length :  Seq1 s a
       -> F1 s Nat
length (MkSeq1 seq) t =
  let (MkSeq seq') # t := read1 seq t
    in (length' seq') # t

||| O(n). Reverse the sequence.
export
reverse :  Seq1 s a
        -> F1' s
reverse (MkSeq1 seq) t =
  casupdate1 seq (\(MkSeq tr) => (MkSeq (reverseTree id tr), ())) t

export infixr 5 `cons`
||| O(1). Add an element to the left end of a sequence.
export
cons :  e
     -> Seq1 s e
     -> F1' s
(a `cons` (MkSeq1 seq)) t =
  casupdate1 seq (\(MkSeq tr) => (MkSeq (MkElem a `consTree` tr), ())) t

export infixl 5 `snoc`
||| O(1). Add an element to the right end of a sequence.
export
snoc :  Seq1 s e
     -> e
     -> F1' s
((MkSeq1 seq) `snoc` a) t =
  casupdate1 seq (\(MkSeq tr) => (MkSeq (tr `snocTree` MkElem a), ())) t

||| O(1). View from the left of the sequence.
export
viewl :  Seq1 s e
      -> F1 s (Maybe (e, Seq1 s e))
viewl (MkSeq1 seq) t =
  casupdate1 seq
    (\(MkSeq tr) =>
      case viewLTree tr of
        Just (MkElem a, tr') =>
          (MkSeq tr', Just (a, MkSeq1 seq))
        Nothing               =>
          (MkSeq tr, Nothing)
    ) t

||| O(1). The first element of the sequence.
export
head :  Seq1 s e
     -> F1 s (Maybe e)
head (MkSeq1 seq) t =
  let MkSeq tr # t := read1 seq t
   in case viewLTree tr of
        Just (MkElem a, _) =>
          Just a # t
        Nothing            =>
          Nothing # t

||| O(1). The elements after the head of the sequence.
||| Returns an empty sequence when the sequence is empty.
export
tail :  Seq1 s e
     -> F1 s (Seq1 s e)
tail (MkSeq1 seq) t =
  casupdate1 seq
    (\(MkSeq tr) =>
      case viewLTree tr of
        Just (MkElem _, tr') =>
          (MkSeq tr', MkSeq1 seq)
        Nothing               =>
          (MkSeq tr, MkSeq1 seq)
    ) t

||| O(1). View from the right of the sequence.
export
viewr :  Seq1 s e
      -> F1 s (Maybe (Seq1 s e, e))
viewr (MkSeq1 seq) t =
  casupdate1 seq
    (\(MkSeq tr) =>
      case viewRTree tr of
        Just (tr', MkElem a) =>
          (MkSeq tr', Just (MkSeq1 seq, a))
        Nothing               =>
          (MkSeq tr, Nothing)
    ) t

||| O(1). The elements before the last element of the sequence.
||| Returns an empty sequence when the sequence is empty.
export
init :  Seq1 s e
     -> F1 s (Seq1 s e)
init (MkSeq1 seq) t =
  casupdate1 seq
    (\(MkSeq tr) =>
      case viewRTree tr of
        Just (tr', MkElem _) =>
          (MkSeq tr', MkSeq1 seq)
        Nothing               =>
          (MkSeq tr, MkSeq1 seq)
    ) t

||| O(1). The last element of the sequence.
export
last :  Seq1 s e
     -> F1 s (Maybe e)
last (MkSeq1 seq) t =
  let MkSeq tr # t := read1 seq t
    in case viewRTree tr of
         Just (_, MkElem a) =>
           Just a # t
         Nothing            =>
           Nothing # t

||| O(n). Turn a list into a sequence.
export
fromList :  List e
         -> F1 s (Seq1 s e)
fromList xs t =
  let seq # t := ref1 (MkSeq (foldr (\x, tr => MkElem x `consTree` tr) Empty xs)) t
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
      let tr # t := Data.Seq1.Unsized.viewl seq t
        in case tr of
             Nothing       =>
               (sl <>> []) # t
             Just (x, tr') =>
               (assert_total (go tr' (sl :< x))) t

||| O(log(min(i, n-i))). The element at the specified position.
export
index :  Nat
      -> Seq1 s e
      -> F1 s (Maybe e)
index i (MkSeq1 seq) t =
  let MkSeq tr # t := read1 seq t
    in case i < length' tr of
         True  =>
           let (_, MkElem a) := lookupTree i tr
            in Just a # t
         False =>
           Nothing # t

||| O(log(min(i, n-i))). Update the element at the specified position.
||| If the position is out of range, the original sequence is returned.
export
adjust :  (e -> e)
       -> Nat
       -> Seq1 s e
       -> F1' s
adjust f i (MkSeq1 seq) t =
  casupdate1 seq
    (\(MkSeq tr) =>
      case i < length' tr of
        True  =>
          (MkSeq (adjustTree (const (map f)) i tr), ())
        False =>
          (MkSeq tr, ())
    ) t

||| O(log(min(i, n-i))). Replace the element at the specified position.
||| If the position is out of range, the original sequence is returned.
export
update :  Nat
       -> e
       -> Seq1 s e
       -> F1' s
update i a seq t =
  adjust (const a) i seq t

||| Dump the internal structure of the finger tree.
export
show' :  Show e
      => Seq1 s e
      -> F1 s String
show' (MkSeq1 seq) t =
  let MkSeq tr # t := read1 seq t
    in (showPrec Open tr) # t
