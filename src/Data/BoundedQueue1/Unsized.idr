||| Linear Bounded Queues
module Data.BoundedQueue1.Unsized

import Data.BoundedQueue.Unsized.Internal
import Data.BoundedQueue1.Unsized.Internal
import Data.Seq.Unsized

import Data.Linear.Ref1
import Derive.Prelude

%language ElabReflection

%default total

||| The empty `BoundedQueue1`. O(1)
export
empty :  Nat
      -> F1 s (BoundedQueue1 s a)
empty l t =
  let bq # t := ref1 ( MkBoundedQueue Data.Seq.Unsized.empty
                                      l
                                      Z
                     ) t
    in (MkBoundedQueue1 bq) # t

||| Is the `BoundedQueuei1` empty? O(1)
export
null :  BoundedQueue1 s a
     -> F1 s Bool
null (MkBoundedQueue1 bq) t =
  let (MkBoundedQueue _ _ s) # t := read1 bq t
    in case s of
         Z =>
           True # t
         _ =>
           False # t

||| Naively keeps the first `n` values of a list, and converts
||| into a `BoundedQueue1` (keeps the order of the elements). O(1)
export
fromList :  (n : Nat)
         -> (vs : List a)
         -> F1 s (BoundedQueue1 s a)
fromList n vs t =
  let vs'    := take n vs
      bq # t := ref1 ( MkBoundedQueue (Data.Seq.Unsized.fromList vs')
                                      n
                                      (Prelude.List.length vs')
                     ) t
    in (MkBoundedQueue1 bq) # t

||| Naively keeps the first `n` values of a `SnocList`, and converts
||| into a `BoundedQueue1` (keeps the order of the elements). O(1)
export
fromSnocList :  (n : Nat)
             -> (sv : SnocList a)
             -> F1 s (BoundedQueue1 s a)
fromSnocList n sv t =
  let sv'    := take n $ cast sv
      bq # t := ref1 ( MkBoundedQueue (Data.Seq.Unsized.fromList sv')
                                      n
                                      (Prelude.List.length sv')
                     ) t
    in (MkBoundedQueue1 bq) # t

||| Converts a `BoundedQueue1` to a `List`, keeping the order
||| of elements. O(n)
export
toList :  BoundedQueue1 s a
       -> F1 s (List a)
toList (MkBoundedQueue1 bq) t =
  let (MkBoundedQueue q _ _) # t := read1 bq t
    in (toList q) # t

||| Converts a `BoundedQueue1` to a `SnocList`, keeping the order
||| of elements. O(n)
export
toSnocList :  BoundedQueue1 s a
           -> F1 s (SnocList a)
toSnocList (MkBoundedQueue1 bq) t =
  let (MkBoundedQueue q _ _) # t := read1 bq t
    in (cast $ toList q) # t

||| Append a value at the back of the `BoundedQueue1`.
||| This function returns True if the value was enqueued,
||| and False if the queue was full. O(1)
export
enqueue :  BoundedQueue1 s a
        -> a
        -> F1 s Bool
enqueue (MkBoundedQueue1 bq) v t =
  casupdate1 bq
    (\(MkBoundedQueue q l s) =>
      case l == s of
        True  =>
          (MkBoundedQueue q l s, False)
        False =>
          (MkBoundedQueue (q `snoc` v) l (s `plus` 1), True)
    ) t

||| Take a value from the front of the `BoundedQueue1`. O(1)
export
dequeue :  BoundedQueue1 s a
        -> F1 s (Maybe a)
dequeue (MkBoundedQueue1 bq) t =
  casupdate1 bq
    (\(MkBoundedQueue q l s) =>
      case viewl q of
        Nothing      =>
          (MkBoundedQueue q l s, Nothing)
        Just (h, q') =>
          ( MkBoundedQueue q' l (s `minus` 1)
          , Just h
          )
    ) t

||| We can prepend an element to our `BoundedQueue1`, making it the new
||| "oldest" element. O(1)
|||
||| This is against the typical use case for a FIFO data
||| structure, but it allows us to conveniently implement
||| `peekOldest`.
export
prepend :  a
        -> BoundedQueue1 s a
        -> F1' s
prepend x (MkBoundedQueue1 bq) t =
  casmod1 bq
    (\(MkBoundedQueue q l s) =>
      case l == s of
        True  =>
          case viewl q of
            Nothing =>
              MkBoundedQueue q l s
            Just (_, q') =>
              MkBoundedQueue (x `cons` q') l s
        False =>
          MkBoundedQueue (x `cons` q) l (s `plus` 1)
    ) t

||| Return the last element of the `BoundedQueue1`, plus the unmodified
||| queue.
|||
||| Note: `peekOldest` might involve a rearrangement of the elements
|||       just like `dequeue`. In order to keep our amortized O(1)
|||       runtime behavior, the newly arranged queue should be used
|||       henceforth.
export
peekOldest :  BoundedQueue1 s a
           -> F1 s (Maybe (a, BoundedQueue1 s a))
peekOldest (MkBoundedQueue1 bq) t =
  let (MkBoundedQueue q l s) # t := read1 bq t
    in case viewl q of
         Nothing     =>
           Nothing # t
         Just (v, _) =>
           Just (v, MkBoundedQueue1 bq) # t

||| Returns the length of the `BoundedQueue1`. O(1).
export
length :  BoundedQueue1 s a
       -> F1 s Nat
length (MkBoundedQueue1 bq) t =
  let (MkBoundedQueue _ _ s) # t := read1 bq t
    in s # t
