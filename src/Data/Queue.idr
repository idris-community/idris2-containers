module Data.Queue

import Derive.Prelude

%language ElabReflection

%default total

||| An immutable first-in first-out structure with amortized
||| O(1) enqueue and dequeue operations.
export
record Queue a where
  constructor Q
  front : List a
  back  : SnocList a

||| The empty `Queue`. O(1)
export %inline
empty : Queue a
empty = Q [] [<]

||| Converts a list to a `Queue`, keeping the order of
||| elements. O(1)
export %inline
fromList : List a -> Queue a
fromList vs = Q vs [<]

||| Converts a `SnocList` to a `Queue`, keeping the order of
||| elements. O(1)
export %inline
fromSnocList : SnocList a -> Queue a
fromSnocList sv = Q [] sv

||| Converts a `Queue` to a `SnocList`, keeping the order
||| of elements. O(n)
export %inline
toSnocList : Queue a -> SnocList a
toSnocList (Q f b) = b <>< f

||| Append a value at the back of the `Queue`. O(1)
export
enqueue : Queue a -> a -> Queue a
enqueue (Q f b) v = Q f (b :< v)

||| Append a list of values at the back of the `Queue`. O(1)
export
enqueueAll : Queue a -> List a -> Queue a
enqueueAll (Q f b) vs = Q f (b <>< vs)

||| Take a value from the front of the `Queue`.
|||
||| In case of the front being empty, this transfers
||| the back to the front, which runs in O(n). However,
||| every element in the `Queue` is thus shifted at most
||| once before being dequeued, so this runs in amortized
||| O(1).
export
dequeue : Queue a -> Maybe (a, Queue a)
dequeue (Q front back) =
  case front of
    h::t => Just (h, Q t back)
    []   =>
      case back <>> [] of
        h::t => Just (h, Q t [<])
        []   => Nothing

||| We can prepend an element to our `Queue`, making it the new
||| "oldest" element. O(1)
|||
||| This is against the typical use case for a FIFO data
||| structure, but it allows us to conveniently implement
||| `peekOldest`.
export
prepend : a -> Queue a -> Queue a
prepend x (Q f b) = Q (x::f) b

||| Return the last element of the `Queue`, plus the unmodified
||| `Queue`.
|||
||| Note: `peekOldest` might involve a rearrangement of the elements
|||       just like `dequeue`. In order to keep our amortized O(1)
|||       runtime behavior, the newly arranged `Queue` should be used
|||       henceforth.
export
peekOldest : Queue a -> Maybe (a, Queue a)
peekOldest q =
  case dequeue q of
    Just (v,Q f b) => Just (v, Q (v::f) b)
    Nothing     => Nothing

||| Appends two `Queue`s. O(m + n)
export
(++) : Queue a -> Queue a -> Queue a
Q f1 b1 ++ Q f2 b2 = Q (f1 ++ (b1 <>> f2)) b2

||| Returns the length of the `Queue`. O(n).
export
length : Queue a -> Nat
length (Q f b) = length f + length b

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

%runElab derive "Queue" [Show,Eq]

export %inline
Semigroup (Queue a) where
  (<+>) = (++)

export %inline
Monoid (Queue a) where
  neutral = empty

export
Functor Queue where
  map f (Q front back) = Q (map f front) (map f back)

export
Foldable Queue where
  toList (Q f b) = b <>> f
  foldr f acc = foldr f acc . toSnocList
  foldl f acc = foldl f acc . toList
  foldMap f = foldMap f . toList
  foldlM f acc = foldlM f acc . toList
  null (Q f b) = null f || null b

export
Traversable Queue where
  traverse f (Q front back) = [| Q (traverse f front) (traverse f back) |]
