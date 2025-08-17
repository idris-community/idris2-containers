||| Bounded Queue Internals
module Data.BoundedQueue.Sized.Internal

import Data.Seq.Sized

%default total

||| An immutable, bounded first-in first-out structure which keeps
||| track of its size, with amortized O(1) enqueue and dequeue operations.
||| The `m` argument tracks the `BoundedQueue`s limit,
||| and the `n` argument tracks the `BoundedQueue`s size.
public export
data BoundedQueue : (m : Nat) -> (n : Nat) -> (a : Type) -> Type where
  MkBoundedQueue :  Seq n a -- queue
                 -> BoundedQueue m n a
