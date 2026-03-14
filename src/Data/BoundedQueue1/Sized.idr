||| Bounded Queues
module Data.BoundedQueue1.Sized

import Data.BoundedQueue1.Sized.Internal

import Data.Linear.Ref1
import Data.Seq.Sized
import Derive.Prelude

%hide Data.Vect.length
%hide Prelude.take

%language ElabReflection

%default total

||| The empty `BoundedQueue1`. O(1)
export
empty :  (l : Nat)
      -> F1 s (BoundedQueue1 s l 0 a)
empty _ t =
  let seq # t := ref1 Data.Seq.Sized.empty t
    in (MkBoundedQueue1 seq) # t

||| Is the `BoundedQueue1` empty? O(1)
export
null :  {n : Nat}
     -> BoundedQueue1 s m n a
     -> F1 s Bool
null (MkBoundedQueue1 _) t =
  case n of
    0 =>
      True # t
    _ =>
      False # t

||| Naively keeps the first `o` values of a list, and converts
||| into a `BoundedQueue1` (keeps the order of the elements). O(1)
export
fromList :  (o : Nat)
         -> (vs : List a)
         -> F1 s (BoundedQueue1 s o (length $ take o vs) a)
fromList o vs t =
  let seq # t := ref1 (Data.Seq.Sized.fromList $ take o vs) t
    in (MkBoundedQueue1 seq) # t

||| Naively keeps the first `o` values of a `SnocList`, and converts
||| into a `BoundedQueue1` (keeps the order of the elements). O(1)
export
fromSnocList :  (o : Nat)
             -> (sv : SnocList a)
             -> F1 s (BoundedQueue1 s o (Prelude.List.length $ take o $ cast {to=List a} sv) a)
fromSnocList o sv t =
  let seq # t := ref1 (Data.Seq.Sized.fromList $ take o $ cast sv) t
    in (MkBoundedQueue1 seq) # t

||| Converts a `BoundedQueue1` to a `List`, keeping the order
||| of elements. O(n)
export
toList :  BoundedQueue1 s m n a
       -> F1 s (List a)
toList (MkBoundedQueue1 queue) t =
  let queue' # t := read1 queue t
    in (toList queue') # t

||| Converts a `BoundedQueue1` to a `SnocList`, keeping the order
||| of elements. O(n)
export
toSnocList :  BoundedQueue1 s m n a
           -> F1 s (SnocList a)
toSnocList (MkBoundedQueue1 queue) t =
  let queue' # t := read1 queue t
    in (cast $ toList queue') # t

||| Append a value at the back of the `BoundedQueue1`. O(1)
export
enqueue :  {m : Nat}
        -> {n : Nat}
        -> BoundedQueue1 s m n a
        -> a
        -> F1 s ((n' ** BoundedQueue1 s m n' a))
enqueue (MkBoundedQueue1 queue) v {m = 0}   {n = 0}   t =
  (0 ** MkBoundedQueue1 queue) # t
enqueue (MkBoundedQueue1 queue) v {m = S m} {n = 0}   t =
  let queue'  # t := read1 queue t
      queue'' # t := ref1 (queue' `snoc` v) t
    in (1 ** MkBoundedQueue1 queue'') # t
enqueue (MkBoundedQueue1 queue) v {m = 0}   {n = S n} t =
  (assert_total $ idris_crash "Data.BoundedQueue1.Sized.enqueue: impossible case") # t
enqueue (MkBoundedQueue1 queue) v {m = S m} {n = S n} t =
  let queue' # t := read1 queue t
    in case m == n of
         True  =>
           let (_, queue'') := viewl queue'
               queue''' # t := ref1 (queue'' `snoc` v) t
             in ((S n) ** MkBoundedQueue1 queue''') # t
         False =>
           let queue'' # t := ref1 (queue' `snoc` v) t
             in ((S (S n)) ** MkBoundedQueue1 queue'') # t

||| Take a value from the front of the `BoundedQueue1`. O(1)
export
dequeue :  {n : Nat}
        -> BoundedQueue1 s m n a
        -> F1 s (Maybe (a, (n' ** BoundedQueue1 s m n' a)))
dequeue (MkBoundedQueue1 queue) {n = 0}   t =
  Nothing # t
dequeue (MkBoundedQueue1 queue) {n = S n} t =
  let queue'   # t := read1 queue t
      (h, queue'') := viewl queue'
      queue''' # t := ref1 queue'' t
    in ( Just (h, (n ** MkBoundedQueue1 queue''')
              )
       ) # t

||| We can prepend an element to our `BoundedQueue1`, making it the new
||| "oldest" element. O(1)
|||
||| This is against the typical use case for a FIFO data
||| structure, but it allows us to conveniently implement
||| `peekOldest`.
export
prepend :  {m : Nat}
        -> {n : Nat}
        -> (x : a)
        -> BoundedQueue1 s m n a
        -> F1 s (n' ** BoundedQueue1 s m n' a)
prepend x (MkBoundedQueue1 queue) {m = 0}   {n = 0}   t =
  (0 ** MkBoundedQueue1 queue) # t
prepend x (MkBoundedQueue1 queue) {m = S m} {n = 0}   t =
  let queue'  # t := read1 queue t
      queue'' # t := ref1 (x `cons` queue') t
    in (1 ** MkBoundedQueue1 queue'') # t
prepend x (MkBoundedQueue1 queue) {m = 0} {n = S n}   t =
  (assert_total $ idris_crash "Data.BoundedQueue1.Sized.prepend: impossible case") # t
prepend x (MkBoundedQueue1 queue) {m = S m} {n = S n} t =
  case m == n of
    True  =>
      let queue'   # t := read1 queue t
          (_, queue'') := viewl queue'
          queue''' # t := ref1 (x `cons` queue'') t
        in ((S n) ** MkBoundedQueue1 queue''') # t
    False =>
      let queue'  # t := read1 queue t
          queue'' # t := ref1 (x `cons` queue') t
        in ((S (S n)) ** MkBoundedQueue1 queue'') # t

||| Return the last element of the `BoundedQueue1`, plus the unmodified
||| queue.
|||
||| Note: `peekOldest` might involve a rearrangement of the elements
|||       just like `dequeue`. In order to keep our amortized O(1)
|||       runtime behavior, the newly arranged queue should be used
|||       henceforth.
export
peekOldest :  {n : Nat}
           -> BoundedQueue1 s m n a
           -> F1 s (Maybe (a, (n' ** BoundedQueue1 s m n' a)))
peekOldest q t =
  let q' # t := dequeue q t
    in case q' of
         Just (v, (n' ** MkBoundedQueue1 queue)
              )  =>
           let queue'  # t := read1 queue t
               queue'' # t := ref1 (v `cons` queue') t
             in ( Just (v, ((S n') ** MkBoundedQueue1 queue'')
                       )
                ) # t
         Nothing =>
           Nothing # t

||| Appends two `BoundedQueue1`. O(m + n)
export
(++) :  BoundedQueue1 s m1 n1 a
     -> BoundedQueue1 s m2 n2 a
     -> F1 s (BoundedQueue1 s (m1 `plus` m2) (n1 `plus` n2) a)
((MkBoundedQueue1 queue1) ++ (MkBoundedQueue1 queue2)) t =
  let queue1' # t := read1 queue1 t
      queue2' # t := read1 queue2 t
      queue12 # t := ref1 (queue1' ++ queue2') t
    in (MkBoundedQueue1 queue12) # t

||| Returns the length of the `BoundedQueue1`. O(1).
export
length :  {n : Nat}
       -> BoundedQueue1 s m n a
       -> F1 s Nat
length (MkBoundedQueue1 _) t =
  n # t
