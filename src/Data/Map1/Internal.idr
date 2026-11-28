||| Linear Finite Map Internals
module Data.Map1.Internal

import Data.Map.Internal
import Data.SortedMap
import Data.Linear.Ref1

%default total

--------------------------------------------------------------------------------
--          Store State
--------------------------------------------------------------------------------

||| The store's monotonic allocation counter and immutable containers.
private
record MapStoreState k v where
  constructor MkMapStoreState
  nextid : Nat
  maps   : SortedMap Nat (Map k v)

--------------------------------------------------------------------------------
--          MapStore1
--------------------------------------------------------------------------------

||| An opaque atomic store holding multiple maps.
||| The counter and contents are committed together through one CAS.
export
data MapStore1 : (s : Type) ->  (k : Type) -> (v : Type) -> Type where
  MkMapStore1 : Ref s (MapStoreState k v) -> MapStore1 s k v

--------------------------------------------------------------------------------
--          Map1
--------------------------------------------------------------------------------

||| An opaque handle containing a store and its allocated identifier.
||| Identifiers cannot be supplied by external callers.
export
data Map1 : (s : Type) ->  (k : Type) -> (v : Type) -> Type where
  MkMap1 : MapStore1 s k v -> Nat -> Map1 s k v

--------------------------------------------------------------------------------
--          Query and Modification
--------------------------------------------------------------------------------

||| Find an existing container in an immutable snapshot.
private
getAt : Nat -> SortedMap Nat (Map k v) -> Maybe (Map k v)
getAt i maps = Data.SortedMap.lookup i maps

||| Replace an existing container, without introducing new identifiers.
private
replaceAt : Nat -> Map k v -> SortedMap Nat (Map k v)
         -> Maybe (SortedMap Nat (Map k v))
replaceAt i value maps =
  case Data.SortedMap.lookup i maps of
    Nothing => Nothing
    Just _  => Just (Data.SortedMap.insert i value maps)

--------------------------------------------------------------------------------
--          Allocation
--------------------------------------------------------------------------------

||| Create a new store with an empty map and identifier counter zero.
export
newStore : F1 s (MapStore1 s k v)
newStore t =
  let ref # t := ref1 (MkMapStoreState 0 Data.SortedMap.empty) t
    in MkMapStore1 ref # t

||| Allocate a fresh identifier and a container in one CAS operation.
||| The counter does not depend on whether older entries remain present.
export
allocateMap : MapStore1 s k v -> Map k v -> F1 s (Map1 s k v)
allocateMap store@(MkMapStore1 ref) value t =
  casupdate1 ref
    (\(MkMapStoreState i maps) =>
      ( MkMapStoreState (S i) (Data.SortedMap.insert i value maps)
      , MkMap1 store i
      )
    ) t

--------------------------------------------------------------------------------
--          Internal Operations
--------------------------------------------------------------------------------

||| Apply a query to a single snapshot; Nothing means invalid handle.
export
queryMap : (Map k v -> b) -> Map1 s k v -> F1 s (Maybe b)
queryMap f (MkMap1 (MkMapStore1 ref) i) t =
  let state # t := read1 ref t
      MkMapStoreState _ maps = state
    in (f <$> getAt i maps) # t

||| Atomically modify an existing container; False means invalid handle.
export
modifyMap : (Map k v -> Map k v) -> Map1 s k v -> F1 s Bool
modifyMap f (MkMap1 (MkMapStore1 ref) i) t =
  casupdate1 ref
    (\state@(MkMapStoreState next maps) =>
      case getAt i maps of
        Nothing  => (state, False)
        Just old =>
          case replaceAt i (f old) maps of
            Nothing      => (state, False)
            Just updated => (MkMapStoreState next updated, True)
    ) t

||| Atomically update a container and return the committed result.
export
updateMap : (Map k v -> (Map k v, b))
          -> Map1 s k v -> F1 s (Maybe b)
updateMap f (MkMap1 (MkMapStore1 ref) i) t =
  casupdate1 ref
    (\state@(MkMapStoreState next maps) =>
      case getAt i maps of
        Nothing  => (state, Nothing)
        Just old =>
          let (new, result) = f old
           in case replaceAt i new maps of
                Nothing      => (state, Nothing)
                Just updated => (MkMapStoreState next updated, Just result)
    ) t

||| Query two containers from one shared-store snapshot.
||| Both handles must belong to the same store.
export
queryMaps : (Map k v -> Map k v -> b)
           -> Map1 s k v -> Map1 s k v -> F1 s (Maybe b)
queryMaps f (MkMap1 (MkMapStore1 ref) i) (MkMap1 _ j) t =
  let state # t := read1 ref t
      MkMapStoreState _ maps = state
    in case (getAt i maps, getAt j maps) of
         (Just first, Just second) => Just (f first second) # t
         _                         => Nothing # t

||| Atomically modify the first of two containers in one CAS.
||| Both handles must belong to the same store.
export
modifyMaps : (Map k v -> Map k v -> Map k v)
            -> Map1 s k v -> Map1 s k v -> F1 s Bool
modifyMaps f (MkMap1 (MkMapStore1 ref) i) (MkMap1 _ j) t =
  casupdate1 ref
    (\state@(MkMapStoreState next maps) =>
      case (getAt i maps, getAt j maps) of
        (Just first, Just second) =>
          case replaceAt i (f first second) maps of
            Nothing      => (state, False)
            Just updated => (MkMapStoreState next updated, True)
        _ => (state, False)
    ) t

||| Atomically update two distinct containers and return a result.
||| Identical handles and invalid identifiers return Nothing.
||| Both handles must belong to the same store.
export
updateMaps :
     (Map k v -> Map k v -> (Map k v, Map k v, b))
  -> Map1 s k v -> Map1 s k v -> F1 s (Maybe b)
updateMaps f (MkMap1 (MkMapStore1 ref) i) (MkMap1 _ j) t =
  casupdate1 ref
    (\state@(MkMapStoreState next maps) =>
      if i == j
        then (state, Nothing)
        else case (getAt i maps, getAt j maps) of
          (Just first, Just second) =>
            let (first', second', result) = f first second
             in case replaceAt i first' maps of
                  Nothing      => (state, Nothing)
                  Just updated =>
                    case replaceAt j second' updated of
                      Nothing         => (state, Nothing)
                      Just resultMaps => (MkMapStoreState next resultMaps, Just result)
          _ => (state, Nothing)
    ) t

--------------------------------------------------------------------------------
--          Swap
--------------------------------------------------------------------------------

||| Atomically swap two maps in one store; self-swap is a valid no-op.
||| Both handles must belong to the same store.
export
swapMaps : Map1 s k v -> Map1 s k v -> F1 s Bool
swapMaps (MkMap1 (MkMapStore1 ref) i) (MkMap1 _ j) t =
  casupdate1 ref
    (\state@(MkMapStoreState next maps) =>
      case (getAt i maps, getAt j maps) of
        (Just first, Just second) =>
          if i == j
            then (state, True)
            else case replaceAt i second maps of
                   Nothing      => (state, False)
                   Just updated =>
                     case replaceAt j first updated of
                       Nothing         => (state, False)
                       Just resultMaps => (MkMapStoreState next resultMaps, True)
        _ => (state, False)
    ) t
