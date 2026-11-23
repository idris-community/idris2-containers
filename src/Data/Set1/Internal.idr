||| Linear Finite Set Internals
module Data.Set1.Internal

import Data.Set.Internal
import Data.SortedMap
import Data.Linear.Ref1

%default total

--------------------------------------------------------------------------------
--          SetStore1
--------------------------------------------------------------------------------

||| A shared atomic store containing multiple sets.
|||
||| All sets belonging to the store are held in a single mutable
||| reference, allowing multiple sets to be updated atomically.
public export
data SetStore1 : (s : Type) -> (a : Type) -> Type where
  MkSetStore1 :  Ref s (SortedMap Nat (Set a))
              -> SetStore1 s a

--------------------------------------------------------------------------------
--          Set1
--------------------------------------------------------------------------------

||| A handle identifying one set within a shared store.
|||
||| The identifier is unique within its store and is never reused.
||| A Set1 remains associated with its original store.
public export
data Set1 : (s : Type) -> (a : Type) -> Type where
  MkSet1 :  SetStore1 s a
         -> Nat
         -> Set1 s a

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Retrieve a set from a store snapshot by its identifier.
||| Calls idris_crash if the identifier does not exist.
||| O(log n), where n is the number of sets in the store.
export
getAt :  Nat
      -> SortedMap Nat (Set a)
      -> Set a
getAt i sets =
  case Data.SortedMap.lookup i sets of
    Just set =>
      set
    Nothing  =>
      assert_total $
        idris_crash "Data.Set1.Internal.getAt: invalid set identifier"

--------------------------------------------------------------------------------
--          Modification
--------------------------------------------------------------------------------

||| Replace an existing set in a store snapshot.
||| Calls idris_crash if the identifier does not exist.
||| O(log n), where n is the number of sets in the store.
export
replaceAt :  Nat
          -> Set a
          -> SortedMap Nat (Set a)
          -> SortedMap Nat (Set a)
replaceAt i set sets =
  case Data.SortedMap.lookup i sets of
    Just _  =>
      Data.SortedMap.insert i set sets
    Nothing =>
      assert_total $
        idris_crash "Data.Set1.Internal.replaceAt: invalid set identifier"

--------------------------------------------------------------------------------
--          Allocation
--------------------------------------------------------------------------------

||| Find the next available identifier in a store snapshot.
||| Identifiers are allocated monotonically and never reused.
||| O(log n), where n is the number of sets in the store.
export
nextId :  SortedMap Nat (Set a)
       -> Nat
nextId sets =
  case Data.SortedMap.rightMost sets of
    Nothing     => 0
    Just (i, _) => S i
