||| Linear Least Recently Used (LRU) Cache Internals
module Data.LRUCache1.Internal

import Data.HashPSQ
import Data.LRUCache.Internal

import Derive.Prelude
import Data.Linear.Ref1

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          LRUCache1
--------------------------------------------------------------------------------

||| Linear Least Recently Used (LRU) Cache based on hashing.
public export
data LRUCache1 : (s : Type) -> (k : Type) -> (v : Type) -> Type where
  MkLRUCache1 :  (lrucache : Ref s (LRUCache k v))
              -> LRUCache1 s k v
