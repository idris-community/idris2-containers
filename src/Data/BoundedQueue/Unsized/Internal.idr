||| Bounded Queue Internals
module Data.BoundedQueue.Unsized.Internal

import Data.Seq.Unsized
import Derive.Prelude

%language ElabReflection

%default total

||| An immutable, bounded first-in first-out structure which keeps
||| track of its size, with amortized O(1) enqueue and dequeue operations.
public export
data BoundedQueue : (a : Type) -> Type where
  MkBoundedQueue :  Seq a -- queue
                 -> Nat   -- limit
                 -> Nat   -- size
                 -> BoundedQueue a

%runElab derive "BoundedQueue" [Show,Eq,Ord]
