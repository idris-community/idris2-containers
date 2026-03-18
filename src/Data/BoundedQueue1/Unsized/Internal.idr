||| Linear Bounded Queue Internals
module Data.BoundedQueue1.Unsized.Internal

import Data.BoundedQueue.Unsized.Internal

import Data.Linear.Ref1
import Derive.Prelude

%language ElabReflection

%default total

||| A linear, immutable, bounded first-in first-out structure which keeps
||| track of its size, with amortized O(1) enqueue and dequeue operations.
public export
data BoundedQueue1 : (s : Type) -> (a : Type) -> Type where
  MkBoundedQueue1 : Ref s (BoundedQueue a)
                 -> BoundedQueue1 s a
