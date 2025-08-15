||| General purpose two-end finite sequences,
||| with length in its type.
|||
||| This is implemented by finger tree.
module Data.Seq.Sized

import Control.WellFounded

import public Data.Fin
import public Data.Nat
import public Data.Vect
import public Data.Zippable

import Data.Seq.Internal

%default total

err :  String
    -> a
err s = assert_total (idris_crash s)

||| A two-end finite sequence, with length in its type.
export
data Seq : Nat -> Type -> Type where
  MkSeq :  FingerTree (Elem e)
        -> Seq n e

||| The empty sequence. O(1)
export
empty : Seq 0 e
empty =
  MkSeq Empty

||| A singleton sequence. O(1)
export
singleton :  e
          -> Seq 1 e
singleton a =
  MkSeq (Single (MkElem a))

||| A sequence of length n with a the value of every element. O(n)
export
replicate :  (n : Nat)
          -> (a : e)
          -> Seq n e
replicate n a =
  MkSeq (replicate' n a)

||| The number of elements in the sequence. O(1)
export
length :  {n : Nat}
       -> Seq n a
       -> Nat
length _ =
  n

||| Reverse the sequence. O(n)
export
reverse :  Seq n a
        -> Seq n a
reverse (MkSeq tr) =
  MkSeq (reverseTree id tr)

export infixr 5 `cons`
||| Add an element to the left end of a sequence. O(1)
export
cons :  e
     -> Seq n e
     -> Seq (S n) e
a `cons` MkSeq tr =
  MkSeq (MkElem a `consTree` tr)

export infixl 5 `snoc`
||| Add an element to the right end of a sequence. O(1)
export
snoc :  Seq n e
     -> e
     -> Seq (S n) e
MkSeq tr `snoc` a =
  MkSeq (tr `snocTree` MkElem a)

||| Concatenate two sequences. O(log(min(m, n)))
export
(++) :  Seq m e
     -> Seq n e
     -> Seq (m + n) e
MkSeq t1 ++ MkSeq t2 =
  MkSeq (addTree0 t1 t2)

||| View from the left of the sequence. O(1)
export
viewl :  Seq (S n) a
      -> (a, Seq n a)
viewl (MkSeq tr) =
  case viewLTree tr of
    Just (MkElem a, tr') =>
      (a, MkSeq tr')
    Nothing              =>
      err "viewl"

||| The first element of the sequence. O(1)
export
head :  Seq (S n) a
     -> a
head =
  fst . viewl

||| The elements after the head of the sequence. O(1)
export
tail :  Seq (S n) a
     -> Seq n a
tail =
  snd . viewl

||| View from the right of the sequence. O(1)
export
viewr :  Seq (S n) a
      -> (Seq n a, a)
viewr (MkSeq tr) =
  case viewRTree tr of
    Just (tr', MkElem a) =>
      (MkSeq tr', a)
    Nothing              =>
      err "viewr"

||| The elements before the last element of the sequence. O(1)
export
init :  Seq (S n) a
     -> Seq n a
init =
  fst . viewr

||| The last element of the sequence. O(1)
export
last :  Seq (S n) a
     -> a
last =
  snd . viewr

||| Turn a vector into a sequence. O(n)
export
fromVect :  Vect n a
         -> Seq n a
fromVect xs =
  MkSeq (foldr (\x, t => MkElem x `consTree` t) Empty xs)

||| Turn a list into a sequence. O(n)
export
fromList :  (xs : List a)
         -> Seq (length xs) a
fromList xs =
  fromVect (Vect.fromList xs)

||| Turn a sequence into a vector. O(n)
export
toVect :  {n : Nat}
       -> Seq n a
       -> Vect n a
toVect _  {n = 0}   =
  []
toVect ft {n = S _} =
  let (x, ft') = viewl ft
    in x :: toVect ft'

||| The element at the specified position. O(log(min(i, n-i)))
export
index :  (i : Nat)
      -> (t : Seq n a)
      -> {auto ok : LT i n}
      -> a
index i (MkSeq t) =
  let (_, MkElem a) = lookupTree i t
    in a

||| The element at the specified position.
||| Use Fin n to index instead. O(log(min(i, n-i)))
export
index' :  (t : Seq n a)
       -> (i : Fin n)
       -> a
index' (MkSeq t) fn =
  let (_, MkElem a) = lookupTree (finToNat fn) t
    in a

||| Update the element at the specified position. O(log(min(i, n-i)))
export
adjust :  (f : a -> a)
       -> (i : Nat)
       -> (t : Seq n a)
       -> {auto ok : LT i n}
       -> Seq n a
adjust f i (MkSeq t) =
  MkSeq $ adjustTree (const (map f)) i t

||| Replace the element at the specified position. O(log(min(i, n-i)))
export
update :  (i : Nat)
       -> a
       -> (t : Seq n a)
       -> {auto ok : LT i n}
       -> Seq n a
update i a t =
  adjust (const a) i t

||| Split a sequence at a given position. O(log(min(i, n-i)))
export
splitAt :  (i : Nat)
        -> Seq (i + j) a
        -> (Seq i a, Seq j a)
splitAt i (MkSeq xs) =
  let (l, r) = split i xs
    in (MkSeq l, MkSeq r)

||| The first i elements of a sequence. O(log(min(i, n-i)))
export
take :  (i : Nat)
     -> Seq (i + j) a
     -> Seq i a
take i seq =
  fst (splitAt i seq)

||| Elements of a sequence after the first i. O(log(min(i, n-i)))
export
drop :  (i : Nat)
     -> Seq (i + j) a
     -> Seq j a
drop i seq =
  snd (splitAt i seq)

||| Dump the internal structure of the finger tree.
export
show' :  Show a
      => Seq n a
      -> String
show' (MkSeq tr) =
  showPrec Open tr

public export
implementation Eq a => Eq (Seq n a) where
  MkSeq x == MkSeq y = x == y

public export
implementation Ord a => Ord (Seq n a) where
  compare (MkSeq x) (MkSeq y) = compare x y

public export
implementation Functor (Seq n) where
  map f (MkSeq tr) = MkSeq (map (map f) tr)

public export
implementation Foldable (Seq n) where
  foldr f z (MkSeq tr) = foldr (f . unElem) z tr
  foldl f z (MkSeq tr) = foldl (\acc, (MkElem elem) => f acc elem) z tr
  toList (MkSeq tr) = toList' tr
  null (MkSeq Empty) = True
  null _ = False

public export
implementation Traversable (Seq n) where
  traverse f (MkSeq tr) = MkSeq <$> traverse (map MkElem . f . unElem) tr

public export
implementation Show a => Show (Seq n a) where
  showPrec p = showPrec p . toList

public export
implementation Zippable (Seq n) where
  zipWith f (MkSeq x) (MkSeq y) = MkSeq (zipWith' f x y)
  zipWith3 f (MkSeq x) (MkSeq y) (MkSeq z) = MkSeq (zipWith3' f x y z)
  unzipWith f (MkSeq zs) = let (xs, ys) = unzipWith' f zs in (MkSeq xs, MkSeq ys)
  unzipWith3 f (MkSeq ws) = let (xs, ys, zs) = unzipWith3' f ws in (MkSeq xs, MkSeq ys, MkSeq zs)

||| This implementation works like a ZipList,
||| and is differnt from that of Seq.Unsized.
public export
implementation {n : Nat} -> Applicative (Seq n) where
  pure = replicate n
  (<*>) = zipWith ($)

public export
implementation Sized (Seq n a) where
  size (MkSeq s) = size s
