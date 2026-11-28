||| Linear Finite Set Internals
module Data.Set1.Internal

import Data.Set.Internal
import Data.SortedMap
import Data.Linear.Ref1

%default total

--------------------------------------------------------------------------------
--          Store State
--------------------------------------------------------------------------------

||| The store's monotonic allocation counter and immutable containers.
private
record SetStoreState a where
  constructor MkSetStoreState
  nextid : Nat
  sets : SortedMap Nat (Set a)

--------------------------------------------------------------------------------
--          SetStore1
--------------------------------------------------------------------------------

||| An opaque atomic store holding multiple sets.
||| The counter and contents are committed together through one CAS.
export
data SetStore1 : (s : Type) -> (region : Type) -> (a : Type) -> Type where
  MkSetStore1 : Ref s (SetStoreState a) -> SetStore1 s region a

--------------------------------------------------------------------------------
--          Set1
--------------------------------------------------------------------------------

||| An opaque handle containing a store and its allocated identifier.
||| Identifiers cannot be supplied by external callers.
export
data Set1 : (s : Type) -> (region : Type) -> (a : Type) -> Type where
  MkSet1 : SetStore1 s region a -> Nat -> Set1 s region a

--------------------------------------------------------------------------------
--          Query and Modification
--------------------------------------------------------------------------------

||| Find an existing container in an immutable snapshot.
private
getAt : Nat -> SortedMap Nat (Set a) -> Maybe (Set a)
getAt i sets = Data.SortedMap.lookup i sets

||| Replace an existing container, without introducing new identifiers.
private
replaceAt : Nat -> Set a -> SortedMap Nat (Set a)
         -> Maybe (SortedMap Nat (Set a))
replaceAt i value sets =
  case Data.SortedMap.lookup i sets of
    Nothing => Nothing
    Just _  => Just (Data.SortedMap.insert i value sets)

--------------------------------------------------------------------------------
--          Allocation
--------------------------------------------------------------------------------

||| Create a new store with an empty map and identifier counter zero.
private
newStore : F1 s (SetStore1 s region a)
newStore t =
  let ref # t := ref1 (MkSetStoreState 0 Data.SortedMap.empty) t
    in MkSetStore1 ref # t

||| Run a state-token computation with one generatively scoped store.
||| The callback is polymorphic in `region`, preventing handles from
||| different store scopes from being mixed or returned directly.
export
withStore :
     (forall region . SetStore1 s region a -> F1 s b)
  -> F1 s b
withStore f t =
  let store # t := newStore {region = ()} t
    in f store t

||| Run an IO computation with one generatively scoped store.
||| This supports concurrent users of handles created within the scope.
export
withStoreIO :
     (forall region . SetStore1 World region a -> IO b)
  -> IO b
withStoreIO f = do
  store <- runIO (newStore {region = ()})
  f store

||| Allocate a fresh identifier and a container in one CAS operation.
||| The counter does not depend on whether older entries remain present.
export
allocateSet : SetStore1 s region a -> Set a -> F1 s (Set1 s region a)
allocateSet store@(MkSetStore1 ref) value t =
  casupdate1 ref
    (\(MkSetStoreState i sets) =>
      ( MkSetStoreState (S i) (Data.SortedMap.insert i value sets)
      , MkSet1 store i
      )
    ) t

--------------------------------------------------------------------------------
--          Internal Operations
--------------------------------------------------------------------------------

||| Apply a query to a single snapshot, Nothing means invalid handle.
export
querySet : (Set a -> b) -> Set1 s region a -> F1 s (Maybe b)
querySet f (MkSet1 (MkSetStore1 ref) i) t =
  let state # t := read1 ref t
      MkSetStoreState _ sets = state
    in (f <$> getAt i sets) # t

||| Atomically modify an existing container, False means invalid handle.
export
modifySet : (Set a -> Set a) -> Set1 s region a -> F1 s Bool
modifySet f (MkSet1 (MkSetStore1 ref) i) t =
  casupdate1 ref
    (\state@(MkSetStoreState next sets) =>
      case getAt i sets of
        Nothing  => (state, False)
        Just old =>
          case replaceAt i (f old) sets of
            Nothing      => (state, False)
            Just updated => (MkSetStoreState next updated, True)
    ) t

||| Atomically update a container and return the committed result.
export
updateSet : (Set a -> (Set a, b))
          -> Set1 s region a -> F1 s (Maybe b)
updateSet f (MkSet1 (MkSetStore1 ref) i) t =
  casupdate1 ref
    (\state@(MkSetStoreState next sets) =>
      case getAt i sets of
        Nothing  => (state, Nothing)
        Just old =>
          let (new, result) = f old
           in case replaceAt i new sets of
                Nothing      => (state, Nothing)
                Just updated =>
                  (MkSetStoreState next updated, Just result)
    ) t

||| Query two containers from one shared-store snapshot.
||| Both handles must belong to the same store.
export
querySets : (Set a -> Set a -> b)
           -> Set1 s region a -> Set1 s region a -> F1 s (Maybe b)
querySets f (MkSet1 (MkSetStore1 ref) i) (MkSet1 _ j) t =
  let state # t := read1 ref t
      MkSetStoreState _ sets = state
    in case (getAt i sets, getAt j sets) of
         (Just first, Just second) => Just (f first second) # t
         _                         => Nothing # t

||| Atomically modify the first of two containers in one CAS.
||| Both handles must belong to the same store.
export
modifySets : (Set a -> Set a -> Set a)
            -> Set1 s region a -> Set1 s region a -> F1 s Bool
modifySets f (MkSet1 (MkSetStore1 ref) i) (MkSet1 _ j) t =
  casupdate1 ref
    (\state@(MkSetStoreState next sets) =>
      case (getAt i sets, getAt j sets) of
        (Just first, Just second) =>
          case replaceAt i (f first second) sets of
            Nothing      => (state, False)
            Just updated => (MkSetStoreState next updated, True)
        _ => (state, False)
    ) t

||| Atomically update two distinct containers and return a result.
||| Identical handles and invalid identifiers return Nothing.
||| Both handles must belong to the same store.
export
updateSets :
     (Set a -> Set a -> (Set a, Set a, b))
  -> Set1 s region a -> Set1 s region a -> F1 s (Maybe b)
updateSets f (MkSet1 (MkSetStore1 ref) i) (MkSet1 _ j) t =
  casupdate1 ref
    (\state@(MkSetStoreState next sets) =>
      if i == j
        then (state, Nothing)
        else case (getAt i sets, getAt j sets) of
          (Just first, Just second) =>
            let (first', second', result) = f first second
             in case replaceAt i first' sets of
                  Nothing      => (state, Nothing)
                  Just updated =>
                    case replaceAt j second' updated of
                      Nothing         => (state, Nothing)
                      Just resultMaps =>
                        (MkSetStoreState next resultMaps, Just result)
          _ => (state, Nothing)
    ) t
