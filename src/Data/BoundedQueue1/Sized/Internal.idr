||| Bounded Queue Internals
module Data.BoundedQueue1.Sized.Internal

import Data.Linear.Ref1
import Data.Seq.Unsized

%default total

||| A linear, immutable, bounded first-in first-out structure which keeps
||| track of its size, with amortized O(1) enqueue and dequeue operations.
||| The `m` argument tracks the `BoundedQueue1`s limit,
||| and the `n` argument tracks the `BoundedQueue1`s size.
public export
data BoundedQueue1 : (s : Type) -> (m : Nat) -> (n : Nat) -> (a : Type) -> Type where
  MkBoundedQueue1 : Ref s (Seq a) -- queue
                 -> BoundedQueue1 s m n a
