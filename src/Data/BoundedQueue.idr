module Data.BoundedQueue

import Data.Seq.Unsized
import Derive.Prelude

%language ElabReflection

%default total

||| An immutable, bounded first-in first-out structure which keeps
||| track of its size, with amortized O(1) enqueue and dequeue operations.
export
record BoundedQueue a where
  constructor Q
  queue      : Seq a
  queuelimit : Nat
  queuesize  : Nat

||| The empty `BoundedQueue`. O(1)
export
empty : Nat -> BoundedQueue a
empty l = Q empty l 0

||| Naively keeps the first `n` values of a list, and converts
||| into a `BoundedQueue` (keeps the order of the elements). O(1)
export
fromList : Nat -> List a -> BoundedQueue a
fromList n vs =
  let vs' = take n vs
    in Q (fromList vs') n (length vs')

||| Naively keeps the first `n` values of a `SnocList`, and converts
||| into a `BoundedQueue` (keeps the order of the elements). O(1)
export
fromSnocList : Nat -> SnocList a -> BoundedQueue a
fromSnocList n sv =
  let sv' = take n $ cast sv
    in Q (fromList sv') n (length sv')

||| Converts a `BoundedQueue` to a `List`, keeping the order
||| of elements. O(n)
export
toList : BoundedQueue a -> List a
toList (Q queue _ _) = toList queue

||| Converts a `BoundedQueue` to a `SnocList`, keeping the order
||| of elements. O(n)
export
toSnocList : BoundedQueue a -> SnocList a
toSnocList (Q queue _ _) = cast $ toList queue

||| Append a value at the back of the `BoundedQueue`. O(1)
export
enqueue : BoundedQueue a -> a -> BoundedQueue a
enqueue (Q queue queuelimit queuesize) v =
  case queuelimit == queuesize of
    True  =>
      case viewl queue of
        Nothing          =>
          Q queue queuelimit queuesize
        Just (_, queue') =>
          Q (queue' `snoc` v) queuelimit queuesize
    False =>
      Q (queue `snoc` v) queuelimit (queuesize `plus` 1)

||| Take a value from the front of the `BoundedQueue`. O(1)
export
dequeue : BoundedQueue a -> Maybe (a, BoundedQueue a)
dequeue (Q queue queuelimit queuesize) =
  case viewl queue of
    Nothing          =>
      Nothing
    Just (h, queue') =>
      Just (h, Q queue' queuelimit (queuesize `minus` 1))

||| We can prepend an element to our `BoundedQueue`, making it the new
||| "oldest" element. O(1)
|||
||| This is against the typical use case for a FIFO data
||| structure, but it allows us to conveniently implement
||| `peekOldest`.
export
prepend : a -> BoundedQueue a -> BoundedQueue a
prepend x (Q queue queuelimit queuesize) =
  case queuelimit == queuesize of
    True  =>
      case viewl queue of
        Nothing          =>
          Q queue queuelimit queuesize
        Just (_, queue') =>
          Q (x `cons` queue') queuelimit queuesize
    False =>
      Q (x `cons` queue) queuelimit (queuesize `plus` 1)

||| Return the last element of the `BoundedQueue`, plus the unmodified
||| queue.
|||
||| Note: `peekOldest` might involve a rearrangement of the elements
|||       just like `dequeue`. In order to keep our amortized O(1)
|||       runtime behavior, the newly arranged queue should be used
|||       henceforth.
export
peekOldest : BoundedQueue a -> Maybe (a, BoundedQueue a)
peekOldest q =
  case dequeue q of
    Just (v, Q queue queuelimit queuesize) =>
      Just (v, Q (v `cons` queue) queuelimit (queuesize `plus` 1))
    Nothing                                =>
      Nothing

||| Appends two `BoundedQueues`. O(m + n)
export
(++) : BoundedQueue a -> BoundedQueue a -> BoundedQueue a
(Q queue1 queuelimit1 queuesize1) ++ (Q queue2 queuelimit2 queuesize2) =
  Q (queue1 ++ queue2) (queuelimit1 `plus` queuelimit2) (queuesize1 `plus` queuesize2)

||| Returns the length of the `BoundedQueue`. O(1).
export
length : BoundedQueue a -> Nat
length (Q _ _ queuesize) = queuesize

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

%runElab derive "BoundedQueue" [Show,Eq]

export
Semigroup (BoundedQueue a) where
  (<+>) = (++)

export
Monoid (BoundedQueue a) where
  neutral = empty 0

export
Functor BoundedQueue where
  map f (Q queue queuelimit queuesize) = Q (map f queue) queuelimit queuesize
