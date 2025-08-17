||| Bounded Queues
module Data.BoundedQueue.Sized

import Data.BoundedQueue.Sized.Internal

import Data.Seq.Sized
import Derive.Prelude

%hide Data.Vect.length
%hide Prelude.take

%language ElabReflection

%default total

||| The empty `BoundedQueue`. O(1)
export
empty :  (l : Nat)
      -> BoundedQueue l 0 a
empty _ =
  MkBoundedQueue empty

||| Is the `BoundedQueue` empty? O(1)
export
null :  {n : Nat}
     -> BoundedQueue m n a
     -> Bool
null (MkBoundedQueue _) =
  case n of
    0 =>
      True
    _ =>
      False

||| Naively keeps the first `o` values of a list, and converts
||| into a `BoundedQueue` (keeps the order of the elements). O(1)
export
fromList :  (o : Nat)
         -> (vs : List a)
         -> BoundedQueue o (length $ take o vs) a
fromList o vs =
  MkBoundedQueue (fromList $ take o vs)

||| Naively keeps the first `o` values of a `SnocList`, and converts
||| into a `BoundedQueue` (keeps the order of the elements). O(1)
export
fromSnocList :  (o : Nat)
             -> (sv : SnocList a)
             -> BoundedQueue o (Prelude.List.length $ take o $ cast {to=List a} sv) a
fromSnocList o sv =
  MkBoundedQueue (fromList $ take o $ cast sv)

||| Converts a `BoundedQueue` to a `List`, keeping the order
||| of elements. O(n)
export
toList :  BoundedQueue m n a
       -> List a
toList (MkBoundedQueue queue) =
  toList queue

||| Converts a `BoundedQueue` to a `SnocList`, keeping the order
||| of elements. O(n)
export
toSnocList :  BoundedQueue m n a
           -> SnocList a
toSnocList (MkBoundedQueue queue) =
  cast $ toList queue

||| Append a value at the back of the `BoundedQueue`. O(1)
export
enqueue :  {m : Nat}
        -> {n : Nat}
        -> BoundedQueue m n a
        -> a
        -> (n' ** BoundedQueue m n' a)
enqueue (MkBoundedQueue queue) v {n = 0}   =
  (1 ** MkBoundedQueue (queue `snoc` v))
enqueue (MkBoundedQueue queue) v {n = S n} =
  case m == n of
    True  =>
      let (_, queue') = viewl queue
        in ((S n) ** MkBoundedQueue (queue' `snoc` v))
    False =>
      ((S (S n)) ** MkBoundedQueue (queue `snoc` v))

||| Take a value from the front of the `BoundedQueue`. O(1)
export
dequeue :  {n : Nat}
        -> BoundedQueue m n a
        -> Maybe (a, (n' ** BoundedQueue m n' a))
dequeue (MkBoundedQueue queue) {n = 0}   =
  Nothing
dequeue (MkBoundedQueue queue) {n = S n} =
  let (h, queue') = viewl queue
    in Just (h, (n ** MkBoundedQueue queue')
            )

||| We can prepend an element to our `BoundedQueue`, making it the new
||| "oldest" element. O(1)
|||
||| This is against the typical use case for a FIFO data
||| structure, but it allows us to conveniently implement
||| `peekOldest`.
export
prepend :  {m : Nat}
        -> {n : Nat}
        -> (x : a)
        -> BoundedQueue m n a
        -> (n' ** BoundedQueue m n' a)
prepend x (MkBoundedQueue queue) {n = 0}   =
  (1 ** MkBoundedQueue (x `cons` queue))
prepend x (MkBoundedQueue queue) {n = S n} =
  case m == n of
    True  =>
      let (_, queue') = viewl queue
        in ((S n) ** MkBoundedQueue (x `cons` queue'))
    False =>
      ((S (S n)) ** MkBoundedQueue (x `cons` queue))

||| Return the last element of the `BoundedQueue`, plus the unmodified
||| queue.
|||
||| Note: `peekOldest` might involve a rearrangement of the elements
|||       just like `dequeue`. In order to keep our amortized O(1)
|||       runtime behavior, the newly arranged queue should be used
|||       henceforth.
export
peekOldest :  {n : Nat}
           -> BoundedQueue m n a
           -> Maybe (a, (n' ** BoundedQueue m n' a))
peekOldest q =
  case dequeue q of
    Just (v, (n' ** MkBoundedQueue queue)
         ) =>
      Just (v, ((S n') ** MkBoundedQueue (v `cons` queue))
           )
    Nothing                                =>
      Nothing

||| Appends two `BoundedQueues`. O(m + n)
export
(++) :  BoundedQueue m1 n1 a
     -> BoundedQueue m2 n2 a
     -> BoundedQueue (m1 `plus` m2) (n1 `plus` n2) a
(MkBoundedQueue queue1) ++ (MkBoundedQueue queue2) =
  MkBoundedQueue (queue1 ++ queue2)

||| Returns the length of the `BoundedQueue`. O(1).
export
length :  {n : Nat}
       -> BoundedQueue m n a
       -> Nat
length (MkBoundedQueue _) =
  n

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
{n : Nat} -> Eq a => Eq (BoundedQueue m n a) where
  xs == ys = length xs == length ys && Data.BoundedQueue.Sized.toList xs == Data.BoundedQueue.Sized.toList ys

export
{n : Nat} -> Ord a => Ord (BoundedQueue m n a) where
  compare xs ys = compare (Data.BoundedQueue.Sized.toList xs) (Data.BoundedQueue.Sized.toList ys)

export
Functor (BoundedQueue m n) where
  map f (MkBoundedQueue queue) =
    MkBoundedQueue (map f queue)

export
Show a => Show (BoundedQueue m n a) where
  show (MkBoundedQueue queue) = show queue
