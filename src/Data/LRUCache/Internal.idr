||| Least Recently Used (LRU) Cache Internals
module Data.LRUCache.Internal

import Data.HashPSQ
import Derive.Prelude

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
--          HashPSQ
--------------------------------------------------------------------------------

||| Least Recently Used (LRU) Cache based on hashing.
public export
data LRUCache : (k : Type) -> (v : Type) -> Type where
  MkLRUCache :  (capacity : Nat)               -- The maximum number of elements in the queue.
             -> (size : Nat)                   -- The current number of elements in the queue.
             -> (tick : Priority)              -- The next logical time.
             -> (queue : HashPSQ k Priority v) -- The underlying priority queue.
             -> LRUCache k v

%runElab derive "LRUCache" [Eq,Ord,Show]
