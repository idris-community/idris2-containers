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
|||
||| All maps belonging to the store are held in a single mutable
||| reference, allowing multiple maps to be updated atomically.
public export
data MapStore1 : (s : Type) -> (k : Type) -> (v : Type) -> Type where
  MkMapStore1 :  Ref s (SortedMap Nat (Map k v))
               -> MapStore1 s k v

--------------------------------------------------------------------------------
--          Map1
--------------------------------------------------------------------------------

||| A handle identifying one map within a shared store.
|||
||| The identifier is unique within its store and is never reused.
||| A Map1 remains associated with its original store.
public export
data Map1 : (s : Type) -> (k : Type) -> (v : Type) -> Type where
  MkMap1 :  MapStore1 s k v
         -> Nat
         -> Map1 s k v

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Retrieve a map from a store snapshot by its identifier.
||| Calls idris_crash if the identifier does not exist.
||| O(log n), where n is the number of maps in the store.
export
getAt :  Nat
      -> SortedMap Nat (Map k v)
      -> Map k v
getAt i maps =
  case Data.SortedMap.lookup i maps of
    Just map =>
      map
    Nothing  =>
      assert_total $
        idris_crash "Data.Map1.Internal.getAt: invalid map identifier"

--------------------------------------------------------------------------------
--          Modification
--------------------------------------------------------------------------------

||| Replace an existing map in a store snapshot.
||| Calls idris_crash if the identifier does not exist.
||| O(log n), where n is the number of maps in the store.
export
replaceAt :  Nat
          -> Map k v
          -> SortedMap Nat (Map k v)
          -> SortedMap Nat (Map k v)
replaceAt i map maps =
  case Data.SortedMap.lookup i maps of
    Just _  =>
      Data.SortedMap.insert i map maps
    Nothing =>
      assert_total $
        idris_crash "Data.Map1.Internal.replaceAt: invalid map identifier"

--------------------------------------------------------------------------------
--          Allocation
--------------------------------------------------------------------------------

||| Find the next available identifier in a store snapshot.
||| Identifiers are allocated monotonically and never reused.
||| O(log n), where n is the number of maps in the store.
export
nextId :  SortedMap Nat (Map k v)
       -> Nat
nextId maps =
  case Data.SortedMap.rightMost maps of
    Nothing     => 0
    Just (i, _) => S i
