||| Linear Bounded Queues
module Data.BoundedQueue1.Unsized

import Data.BoundedQueue1.Unsized.Internal

import Data.Linear.Ref1
import Data.Seq.Unsized
import Derive.Prelude

%language ElabReflection

%default total

||| The empty `BoundedQueue1`. O(1)
export
empty :  Nat
      -> F1 s (BoundedQueue1 s a)
empty l t =
  let seq # t := ref1 Data.Seq.Unsized.empty t
      l'  # t := ref1 l t
      s   # t := ref1 Z t
    in ( MkBoundedQueue1 seq
                         l'
                         s
       ) # t

||| Is the `BoundedQueuei1` empty? O(1)
export
null :  BoundedQueue1 s a
     -> F1 s Bool
null (MkBoundedQueue1 _ _ s) t =
  let s' # t := read1 s t
    in case s' of
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
  let vs'     := take n vs
      seq # t := ref1 (Data.Seq.Unsized.fromList vs') t
      l   # t := ref1 n t
      s   # t := ref1 (length vs') t
    in ( MkBoundedQueue1 seq
                         l
                         s
       ) # t

||| Naively keeps the first `n` values of a `SnocList`, and converts
||| into a `BoundedQueue1` (keeps the order of the elements). O(1)
export
fromSnocList :  (n : Nat)
             -> (sv : SnocList a)
             -> F1 s (BoundedQueue1 s a)
fromSnocList n sv t =
  let sv'     := take n $ cast sv
      seq # t := ref1 (Data.Seq.Unsized.fromList sv') t
      l   # t := ref1 n t
      s   # t := ref1 (Prelude.List.length sv') t
    in ( MkBoundedQueue1 seq
                         l
                         s
       ) # t

||| Converts a `BoundedQueue1` to a `List`, keeping the order
||| of elements. O(n)
export
toList :  BoundedQueue1 s a
       -> F1 s (List a)
toList (MkBoundedQueue1 queue _ _) t =
  let queue' # t := read1 queue t
    in (toList queue') # t

||| Converts a `BoundedQueue1` to a `SnocList`, keeping the order
||| of elements. O(n)
export
toSnocList :  BoundedQueue1 s a
           -> F1 s (SnocList a)
toSnocList (MkBoundedQueue1 queue _ _) t =
  let queue' # t := read1 queue t
    in (cast $ toList queue') # t

||| Append a value at the back of the `BoundedQueue1`. O(1)
export
enqueue :  BoundedQueue1 s a
        -> a
        -> F1' s
enqueue (MkBoundedQueue1 queue queuelimit queuesize) v t =
  let queue'      # t := read1 queue t
      queuelimit' # t := read1 queuelimit t
      queuesize'  # t := read1 queuesize t
    in case queuelimit' == queuesize' of
         True  =>
           case viewl queue' of
             Nothing           =>
               () # t
             Just (_, queue'') =>
               casswap1 queue (queue'' `snoc` v) t
         False =>
           let () # t := casswap1 queue (queue' `snoc` v) t
             in casmod1 queuesize (`plus` 1) t

||| Take a value from the front of the `BoundedQueue1`. O(1)
export
dequeue :  BoundedQueue1 s a
        -> F1 s (Maybe (a, BoundedQueue1 s a))
dequeue (MkBoundedQueue1 queue queuelimit queuesize) t =
  let queue' # t := read1 queue t
    in case viewl queue' of
         Nothing           =>
           Nothing # t
         Just (h, queue'') =>
           let () # t := casmod1 queuesize (`minus` 1) t
               () # t := casswap1 queue queue'' t
             in Just (h, MkBoundedQueue1 queue
                                         queuelimit
                                         queuesize
                     ) # t

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
prepend x bq@(MkBoundedQueue1 queue queuelimit queuesize) t =
  let queue'      # t := read1 queue t
      queuelimit' # t := read1 queuelimit t
      queuesize'  # t := read1 queuesize t
    in case queuelimit' == queuesize' of
         True  =>
           case viewl queue' of
             Nothing           =>
               () # t
             Just (_, queue'') =>
               casswap1 queue (x `cons` queue'') t
         False =>
           let () # t := casswap1 queue (x `cons` queue') t
             in casmod1 queuesize (`plus` 1) t

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
peekOldest q t =
  let q' # t := dequeue q t
    in case q' of
         Just (v, MkBoundedQueue1 queue
                                  queuelimit
                                  queuesize
              )  =>
           let queue' # t := read1 queue t
               ()     # t := casswap1 queue (v `cons` queue') t
               ()     # t := casmod1 queuesize (`plus` 1) t
             in (Just (v, q)) # t
         Nothing =>
           Nothing # t

||| Returns the length of the `BoundedQueue1`. O(1).
export
length :  BoundedQueue1 s a
       -> F1 s Nat
length (MkBoundedQueue1 _ _ queuesize) t =
  read1 queuesize t
