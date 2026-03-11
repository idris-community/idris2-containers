||| Linear Least Recently Used (LRU) Cache Internals
module Data.LRUCache1.Internal

import Data.HashPSQ
import Derive.Prelude
import Data.Linear.Ref1

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Priority
--------------------------------------------------------------------------------

||| Logical time at which an element was last accessed.
public export
Priority : Type
Priority = Nat

--------------------------------------------------------------------------------
--          LRUCache1
--------------------------------------------------------------------------------

||| Linear Least Recently Used (LRU) Cache based on hashing.
public export
data LRUCache1 : (s : Type) -> (k : Type) -> (v : Type) -> Type where
  MkLRUCache1 :  (capacity : Ref s Nat)                 -- The maximum number of elements in the queue.
              -> (size : Ref s Nat)                     -- The current number of elements in the queue.
              -> (tick : Ref s Priority)                -- The next logical time.
              -> (queue : Ref s (HashPSQ k Priority v)) -- The underlying priority queue.
              -> LRUCache1 s k v
