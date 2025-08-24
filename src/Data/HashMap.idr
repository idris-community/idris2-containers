module Data.HashMap

import Data.HashMap.Internal.HAMT

import public Data.Hashable

--------------------------------------------------------------------------------
--          HashMap
--------------------------------------------------------------------------------

||| A high-level hash map type implemented using a HAMT (Hash Array Mapped Trie).
||| `Empty` represents an empty map.
||| `Trie` wraps a HAMT containing the key–value pairs.
export
data HashMap : (key : Type) -> (val : Type) -> Type where
  Empty : Hashable key => Eq key => HashMap key val
  Trie  : Hashable key => Eq key => HAMT key (const val) -> HashMap key val

--------------------------------------------------------------------------------
--          Creating HashMaps
--------------------------------------------------------------------------------

||| Constructs an empty `HashMap`.
export
empty :  Hashable key
      => Eq key
      => HashMap key val
empty =
  Empty

--------------------------------------------------------------------------------
--          Lookups
--------------------------------------------------------------------------------

||| Looks up a key in the `HashMap`.
||| Returns `Just val` if found or `Nothing` if the key is absent.
export
lookup :  key
       -> HashMap key val
       -> Maybe val
lookup key Empty       =
  Nothing
lookup key (Trie hamt) =
  let lookup' = lookup (==)
                       key
                       hamt
    in case lookup' of
         Nothing             =>
           Nothing
         Just (_ ** val') =>
           Just val'

--------------------------------------------------------------------------------
--          Insertion
--------------------------------------------------------------------------------

||| Inserts a key–value pair into the `HashMap`.
||| Replaces any existing value for the key.
export
insert :  key
       -> val
       -> HashMap key val
       -> HashMap key val
insert key val Empty       =
  Trie ( singleton key val
       )
insert key val (Trie hamt) =
  Trie ( insert (==) key val hamt
       )

--------------------------------------------------------------------------------
--          Deletion
--------------------------------------------------------------------------------

||| Deletes a key from the `HashMap`.
||| If the key is not present, returns the map unchanged.
export
delete :  key
       -> HashMap key val
       -> HashMap key val
delete key Empty       =
  Empty
delete key (Trie hamt) =
  case delete (==) key hamt of
    Nothing    =>
      Empty
    Just hamt' =>
      Trie hamt'

--------------------------------------------------------------------------------
--          Maps/Folds
--------------------------------------------------------------------------------

||| Folds over all key–value pairs in the `HashMap`,
||| combining them with an accumulator.
export
foldWithKey :  (f : k -> v -> acc -> acc)
            -> acc
            -> HashMap k v
            -> acc
foldWithKey f z Empty       =
  z
foldWithKey f z (Trie hamt) =
  foldWithKey f
              z
              hamt

--------------------------------------------------------------------------------
--          Creating Lists from HashMaps
--------------------------------------------------------------------------------

||| Converts the `HashMap` to a list of key–value pairs.
export
toList :  HashMap k v
       -> List (k, v)
toList hm =
  foldWithKey (\key, val, acc => (key, val) :: acc)
              []
              hm

--------------------------------------------------------------------------------
--         Creating HashMaps from Lists
--------------------------------------------------------------------------------

||| Constructs a `HashMap` from a list of key–value pairs.
export
fromList :  Hashable k
         => Eq k
         => List (k, v)
         -> HashMap k v
fromList xs =
  foldr (\(k, v) => insert k v)
        empty
        xs

--------------------------------------------------------------------------------
--          Keys
--------------------------------------------------------------------------------

||| Returns a list of all keys in the `HashMap`.
export
keys :  HashMap k v
     -> List k
keys hm =
  foldWithKey (\key, val, acc => key :: acc)
              []
              hm

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Functor (HashMap key) where
  map f Empty       =
    Empty
  map f (Trie hamt) =
    Trie ( trieMap f hamt
         )

export
Show key => Show val => Show (HashMap key val) where
  show hm = "fromList \{show $ HashMap.toList hm}"
