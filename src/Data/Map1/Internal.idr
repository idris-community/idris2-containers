||| Linear Finite Map Internals
module Data.Map1.Internal

import Data.Map.Internal
import Data.SortedMap
import Data.Linear.Ref1

%default total

--------------------------------------------------------------------------------
--          MapStore1
--------------------------------------------------------------------------------

||| A shared atomic store containing multiple maps.
||| All maps in the store share a single CAS-updated reference.
public export
data MapStore1 : (s : Type) -> (k : Type) -> (v : Type) -> Type where
  MkMapStore1 :  Ref s (SortedMap Nat (Map k v))
              -> MapStore1 s k v

--------------------------------------------------------------------------------
--          Map1
--------------------------------------------------------------------------------

||| A handle identifying one map within a shared store.
||| The numeric identifier is unique within that store only.
public export
data Map1 : (s : Type) -> (k : Type) -> (v : Type) -> Type where
  MkMap1 :  MapStore1 s k v
         -> Nat
         -> Map1 s k v

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Retrieve a map by its store-local identifier.
||| Returns Nothing for a missing identifier. O(log n)
export
getAt :  Nat
      -> SortedMap Nat (Map k v)
      -> Maybe (Map k v)
getAt i maps =
  Data.SortedMap.lookup i maps

--------------------------------------------------------------------------------
--          Modification
--------------------------------------------------------------------------------

||| Replace an existing map without creating a new identifier.
||| Returns Nothing for a missing identifier. O(log n)
export
replaceAt :  Nat
          -> Map k v
          -> SortedMap Nat (Map k v)
          -> Maybe (SortedMap Nat (Map k v))
replaceAt i map maps =
  case Data.SortedMap.lookup i maps of
    Nothing => Nothing
    Just _  => Just (Data.SortedMap.insert i map maps)

--------------------------------------------------------------------------------
--          Allocation
--------------------------------------------------------------------------------

||| Find the next store-local identifier. O(log n)
||| Assumes entries are never removed and identifiers are not forged.
export
nextId :  SortedMap Nat (Map k v)
       -> Nat
nextId maps =
  case Data.SortedMap.rightMost maps of
    Nothing     => 0
    Just (i, _) => S i
