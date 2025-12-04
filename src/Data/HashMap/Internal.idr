module Data.HashMap.Internal

import Data.HashMap.Internal.HAMT

import public Data.Hashable

--------------------------------------------------------------------------------
--          HashMap
--------------------------------------------------------------------------------

||| A high-level hash map type implemented using a HAMT (Hash Array Mapped Trie).
||| `Empty` represents an empty map.
||| `Trie` wraps a HAMT containing the key–value pairs.
public export
data HashMap : (key : Type) -> (val : Type) -> Type where
  Empty : Hashable key => Eq key => HashMap key val
  Trie  : Hashable key => Eq key => HAMT key (const val) -> HashMap key val
