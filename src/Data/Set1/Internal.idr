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
||| All sets in the store share a single CAS-updated reference.
public export
data SetStore1 : (s : Type) -> (a : Type) -> Type where
  MkSetStore1 :  Ref s (SortedMap Nat (Set a))
              -> SetStore1 s a

--------------------------------------------------------------------------------
--          Set1
--------------------------------------------------------------------------------

||| A handle identifying one set within a shared store.
||| The numeric identifier is unique within that store only.
public export
data Set1 : (s : Type) -> (a : Type) -> Type where
  MkSet1 :  SetStore1 s a
         -> Nat
         -> Set1 s a

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Retrieve a set by its store-local identifier.
||| Returns Nothing for a missing identifier. O(log n)
export
getAt :  Nat
      -> SortedMap Nat (Set a)
      -> Maybe (Set a)
getAt i sets =
  Data.SortedMap.lookup i sets

--------------------------------------------------------------------------------
--          Modification
--------------------------------------------------------------------------------

||| Replace an existing set without creating a new identifier.
||| Returns Nothing for a missing identifier. O(log n)
export
replaceAt :  Nat
          -> Set a
          -> SortedMap Nat (Set a)
          -> Maybe (SortedMap Nat (Set a))
replaceAt i set sets =
  case Data.SortedMap.lookup i sets of
    Nothing => Nothing
    Just _  => Just (Data.SortedMap.insert i set sets)

--------------------------------------------------------------------------------
--          Allocation
--------------------------------------------------------------------------------

||| Find the next store-local identifier. O(log n)
||| Assumes entries are never removed and identifiers are not forged.
export
nextId :  SortedMap Nat (Set a)
       -> Nat
nextId sets =
  case Data.SortedMap.rightMost sets of
    Nothing     => 0
    Just (i, _) => S i
