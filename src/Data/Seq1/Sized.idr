||| General purpose linear two-end finite sequences,
||| with length in its type.
|||
||| This is implemented by finger tree.
module Data.Seq1.Sized

import Control.WellFounded

import public Data.Fin
import Data.Linear.Ref1
import public Data.Nat
import public Data.Vect
import public Data.Zippable

import Data.Seq.Internal

%default total

||| A linear two-end finite sequence, with length in its type.
export
data Seq1 : (s : Type) -> (n : Nat) -> (e : Type) -> Type where
  MkSeq1 :  Ref s (FingerTree (Elem e))
        -> Seq1 s n e

||| The empty sequence. O(1)
export
empty : F1 s (Seq1 s 0 e)
empty t =
  let seq # t := ref1 Empty t
    in (MkSeq1 seq) # t

||| A singleton sequence. O(1)
export
singleton :  e
          -> F1 s (Seq1 s 1 e)
singleton a t =
  let seq # t := ref1 (Single (MkElem a)) t
    in (MkSeq1 seq) # t

||| A sequence of length n with a the value of every element. O(n)
export
replicate :  (n : Nat)
          -> (a : e)
          -> F1 s (Seq1 s n e)
replicate n a t =
  let seq # t := ref1 (replicate' n a) t
    in (MkSeq1 seq) # t

||| The number of elements in the sequence. O(1)
export
length :  {n : Nat}
       -> Seq1 s n e
       -> F1 s Nat
length _ t =
  n # t

||| Reverse the sequence. O(n)
export
reverse :  Seq1 s n e
        -> F1' s
reverse (MkSeq1 tr) t =
  let tr' # t := read1 tr t
    in casswap1 tr (reverseTree id tr') t

export infixr 5 `cons`
||| Add an element to the left end of a sequence. O(1)
export
cons :  e
     -> Seq1 s n e
     -> F1 s (Seq1 s (S n) e)
(a `cons` MkSeq1 tr) t =
  let tr' # t := read1 tr t
      ()  # t := casswap1 tr (MkElem a `consTree` tr') t
    in (MkSeq1 tr) # t

export infixl 5 `snoc`
||| Add an element to the right end of a sequence. O(1)
export
snoc :  Seq1 s n e
     -> e
     -> F1 s (Seq1 s (S n) e)
(MkSeq1 tr `snoc` a) t =
  let tr' # t := read1 tr t
      ()  # t := casswap1 tr (tr' `snocTree` MkElem a) t
    in (MkSeq1 tr) # t

||| Concatenate two sequences. O(log(min(m, n)))
export
(++) :  Seq1 s m e
     -> Seq1 s n e
     -> F1 s (Seq1 s (m + n) e)
(MkSeq1 t1 ++ MkSeq1 t2) t =
  let t1'  # t := read1 t1 t
      t2'  # t := read1 t2 t
      t1t2 # t := ref1 (addTree0 t1' t2') t
    in (MkSeq1 t1t2) # t

||| View from the left of the sequence. O(1)
export
viewl :  Seq1 s (S n) e
      -> F1 s (Maybe (e, Seq1 s n e))
viewl (MkSeq1 tr) t =
  let tr' # t := read1 tr t
    in case viewLTree tr' of
         Just (MkElem a, tr'') =>
           let () # t := casswap1 tr tr'' t
             in (Just (a, MkSeq1 tr)) # t
         Nothing               =>
           Nothing # t

||| The first element of the sequence. O(1)
export
head :  Seq1 s (S n) e
     -> F1 s (Maybe e)
head seq t =
  let seq' # t := viewl seq t
    in case seq' of
         Nothing     =>
           Nothing # t
         Just (h, _) =>
           (Just h) # t

||| The elements after the head of the sequence. O(1)
export
tail :  Seq1 s (S n) e
     -> F1 s (Maybe (Seq1 s n e))
tail seq t =
  let seq' # t := viewl seq t
    in case seq' of
         Nothing         =>
           Nothing # t
         Just (_, seq'') =>
           (Just seq'') # t

||| View from the right of the sequence. O(1)
export
viewr :  Seq1 s (S n) e
      -> F1 s (Maybe (Seq1 s n e, e))
viewr (MkSeq1 tr) t =
  let tr' # t := read1 tr t
    in case viewRTree tr' of
         Just (tr'', MkElem a) =>
           let () # t := casswap1 tr tr'' t
             in (Just (MkSeq1 tr, a)) # t
         Nothing              =>
           Nothing # t

||| The elements before the last element of the sequence. O(1)
export
init :  Seq1 s (S n) e
     -> F1 s (Maybe (Seq1 s n e))
init seq t =
  let seq' # t := viewr seq t
    in case seq' of
         Nothing         =>
           Nothing # t
         Just (seq'', _) =>
           (Just seq'') # t

||| The last element of the sequence. O(1)
export
last :  Seq1 s (S n) e
     -> F1 s (Maybe e)
last seq t =
  let seq' # t := viewr seq t
    in case seq' of
         Nothing     =>
           Nothing # t
         Just (_, l) =>
           (Just l) # t

||| Turn a vector into a sequence. O(n)
export
fromVect :  Vect n e
         -> F1 s (Seq1 s n e)
fromVect xs t =
  let seq # t := ref1 (foldr (\x, tr => MkElem x `consTree` tr) Empty xs) t
    in (MkSeq1 seq) # t

||| Turn a list into a sequence. O(n)
export
fromList :  (xs : List e)
         -> F1 s (Seq1 s (length xs) e)
fromList xs t =
  let vect := Vect.fromList xs
    in fromVect vect t

||| Turn a sequence into a list. O(n)
export
toList :  {n : Nat}
       -> Seq1 s n e
       -> F1 s (List e)
toList _  {n = 0}    t =
  [] # t
toList seq {n = S _} t =
  go seq Lin t
  where
    go :  {n : Nat}
       -> Seq1 s n e
       -> (sl : SnocList e)
       -> F1 s (List e)
    go _   sl {n = 0}   t =
      (sl <>> []) # t
    go seq sl {n = S _} t =
      let seq' # t := viewl seq t
        in case seq' of
             Nothing         =>
               (sl <>> []) # t
             Just (x, seq'') =>
               go seq'' (sl :< x) t

||| The element at the specified position. O(log(min(i, n-i)))
export
index :  (i : Nat)
      -> (t : Seq1 s n e)
      -> {auto ok : LT i n}
      -> F1 s e
index i (MkSeq1 tr) t =
  let tr'       # t := read1 tr t
      (_, MkElem a) := lookupTree i tr'
    in a # t

||| The element at the specified position.
||| Use Fin n to index instead. O(log(min(i, n-i)))
export
index' :  (t : Seq1 s n e)
       -> (i : Fin n)
       -> F1 s e
index' (MkSeq1 tr) fn t =
  let tr'       # t := read1 tr t
      (_, MkElem a) := lookupTree (finToNat fn) tr'
    in a # t

||| Update the element at the specified position. O(log(min(i, n-i)))
export
adjust :  (f : e -> e)
       -> (i : Nat)
       -> (t : Seq1 s n e)
       -> {auto ok : LT i n}
       -> F1' s
adjust f i (MkSeq1 tr) t =
  let tr' # t := read1 tr t
    in casswap1 tr (adjustTree (const (map f)) i tr') t

||| Replace the element at the specified position. O(log(min(i, n-i)))
export
update :  (i : Nat)
       -> e
       -> (seq : Seq1 s n e)
       -> {auto ok : LT i n}
       -> F1' s
update i a seq t =
  adjust (const a) i seq t

||| Split a sequence at a given position. O(log(min(i, n-i)))
export
splitAt :  (i : Nat)
        -> Seq1 s (i + j) e
        -> F1 s (Seq1 s i e, Seq1 s j e)
splitAt i (MkSeq1 tr) t =
  let tr' # t := read1 tr t
      (l, r)  := split i tr'
      l'  # t := ref1 l t
      r'  # t := ref1 r t
    in (MkSeq1 l', MkSeq1 r') # t

||| The first i elements of a sequence. O(log(min(i, n-i)))
export
take :  (i : Nat)
     -> Seq1 s (i + j) e
     -> F1 s (Seq1 s i e)
take i seq t =
  let (seq1, _) # t := Data.Seq1.Sized.splitAt i seq t
    in seq1 # t

||| Elements of a sequence after the first i. O(log(min(i, n-i)))
export
drop :  (i : Nat)
     -> Seq1 s (i + j) e
     -> F1 s (Seq1 s j e)
drop i seq t =
  let (_, seq2) # t := Data.Seq1.Sized.splitAt i seq t
    in seq2 # t

||| Dump the internal structure of the finger tree.
export
show' :  Show e
      => Seq1 s n e
      -> F1 s String
show' (MkSeq1 tr) t =
  let tr' # t := read1 tr t
    in (showPrec Open tr') # t
