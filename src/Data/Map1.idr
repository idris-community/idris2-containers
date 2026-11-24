||| Linear Finite Maps
module Data.Map1

import public Data.Map1.Internal

import Data.Map
import Data.Map.Internal
import Data.SortedMap
import Data.Linear.Ref1

%hide Prelude.null
%hide Prelude.toList

%default total

--------------------------------------------------------------------------------
--          Internal Operations
--------------------------------------------------------------------------------

||| Apply a pure query to one immutable store snapshot.
||| Nothing indicates an invalid map handle.
private
queryMap :  (Map k v -> b)
           -> Map1 s k v
           -> F1 s (Maybe b)
queryMap f (MkMap1 (MkMapStore1 ref) i) t =
  let maps # t := read1 ref t
    in (f <$> Data.Map1.Internal.getAt i maps) # t

||| Atomically modify an existing map in the shared store.
||| False indicates an invalid handle; the state is then unchanged.
private
modifyMap :  (Map k v -> Map k v)
            -> Map1 s k v
            -> F1 s Bool
modifyMap f (MkMap1 (MkMapStore1 ref) i) t =
  casupdate1 ref
    (\maps =>
      case Data.Map1.Internal.getAt i maps of
        Nothing => (maps, False)
        Just old =>
          case Data.Map1.Internal.replaceAt i (f old) maps of
            Nothing       => (maps, False)
            Just maps' => (maps', True)
    ) t

||| Atomically modify a map and return a value from the committed CAS.
||| Nothing indicates an invalid handle, not a missing element or key.
private
updateMap :  (Map k v -> (Map k v, b))
            -> Map1 s k v
            -> F1 s (Maybe b)
updateMap f (MkMap1 (MkMapStore1 ref) i) t =
  casupdate1 ref
    (\maps =>
      case Data.Map1.Internal.getAt i maps of
        Nothing => (maps, Nothing)
        Just old =>
          let (new, result) = f old
           in case Data.Map1.Internal.replaceAt i new maps of
                Nothing       => (maps, Nothing)
                Just maps' => (maps', Just result)
    ) t

||| Query two maps from one atomic store snapshot.
||| Both handles must belong to the same store.
private
queryMaps :  (Map k v -> Map k v -> b)
             -> Map1 s k v
             -> Map1 s k v
             -> F1 s (Maybe b)
queryMaps f (MkMap1 (MkMapStore1 ref) i) (MkMap1 _ j) t =
  let maps # t := read1 ref t
    in case (Data.Map1.Internal.getAt i maps,
             Data.Map1.Internal.getAt j maps) of
         (Just first, Just second) => Just (f first second) # t
         _                         => Nothing # t

||| Atomically modify the first map from one two-map snapshot.
||| Both handles must belong to the same store.
private
modifyMaps :  (Map k v -> Map k v -> Map k v)
              -> Map1 s k v
              -> Map1 s k v
              -> F1 s Bool
modifyMaps f (MkMap1 (MkMapStore1 ref) i) (MkMap1 _ j) t =
  casupdate1 ref
    (\maps =>
      case (Data.Map1.Internal.getAt i maps,
            Data.Map1.Internal.getAt j maps) of
        (Just first, Just second) =>
          case Data.Map1.Internal.replaceAt i (f first second) maps of
            Nothing       => (maps, False)
            Just maps' => (maps', True)
        _ => (maps, False)
    ) t

||| Atomically update two distinct maps and return a result.
||| Nothing indicates an invalid handle or identical identifiers.
||| Both handles must belong to the same store.
private
updateMaps :  (Map k v -> Map k v -> (Map k v, Map k v, b))
              -> Map1 s k v
              -> Map1 s k v
              -> F1 s (Maybe b)
updateMaps f (MkMap1 (MkMapStore1 ref) i) (MkMap1 _ j) t =
  casupdate1 ref
    (\maps =>
      if i == j
        then (maps, Nothing)
        else case (Data.Map1.Internal.getAt i maps,
                   Data.Map1.Internal.getAt j maps) of
          (Just first, Just second) =>
            let (first', second', result) = f first second
             in case Data.Map1.Internal.replaceAt i first' maps of
                  Nothing => (maps, Nothing)
                  Just updated =>
                    case Data.Map1.Internal.replaceAt j second' updated of
                      Nothing       => (maps, Nothing)
                      Just maps' => (maps', Just result)
          _ => (maps, Nothing)
    ) t

--------------------------------------------------------------------------------
--          Construction
--------------------------------------------------------------------------------

||| Create an empty shared atomic map store. O(1)
export
newStore : F1 s (MapStore1 s k v)
newStore t =
  let ref # t := ref1 Data.SortedMap.empty t
    in MkMapStore1 ref # t

||| Allocate a new map from an immutable value, using one CAS.
||| Returns a handle with a unique store-local identifier. O(log n)
export
fromMap :  MapStore1 s k v
          -> Map k v
          -> F1 s (Map1 s k v)
fromMap store@(MkMapStore1 ref) value t =
  casupdate1 ref
    (\maps =>
      let i = nextId maps
        in (Data.SortedMap.insert i value maps, MkMap1 store i)
    ) t

||| Allocate an empty map in an existing store. O(log n)
export
empty :  MapStore1 s k v
      -> F1 s (Map1 s k v)
empty store t = fromMap store Data.Map.empty t

||| Allocate a singleton map in an existing store. O(log n)
export
singleton :  k -> v -> MapStore1 s k v -> F1 s (Map1 s k v)
singleton k v store t =
  fromMap store (Data.Map.Internal.singleton k v) t

||| Allocate a map from a list. Duplicate keys use Data.Map semantics.
export
fromList :  Ord k
         => Eq v
         => Eq (Map k v)
         => List (k, v)
         -> MapStore1 s k v
         -> F1 s (Map1 s k v)
fromList xs store t = fromMap store (Data.Map.fromList xs) t

--------------------------------------------------------------------------------
--          Conversion
--------------------------------------------------------------------------------

||| Return an immutable snapshot; Nothing indicates an invalid handle.
export
freeze :  Map1 s k v -> F1 s (Maybe (Map k v))
freeze = queryMap id

--------------------------------------------------------------------------------
--          Insertion
--------------------------------------------------------------------------------

||| Atomically perform insert; False means invalid handle.
export
insert :  Eq (Map k v) => Eq v => Ord k => k -> v -> Map1 s k v -> F1 s Bool
insert =
  \k => \v => modifyMap (Data.Map.insert k v)

||| Atomically perform insertWith; False means invalid handle.
export
insertWith :  Ord k => (v -> v -> v) -> k -> v -> Map1 s k v -> F1 s Bool
insertWith =
  \f => \k => \v => modifyMap (Data.Map.insertWith f k v)

||| Atomically perform insertWithKey; False means invalid handle.
export
insertWithKey :  Ord k
              => (k -> v -> v -> v)
              -> k -> v -> Map1 s k v -> F1 s Bool
insertWithKey =
  \f => \k => \v => modifyMap (Data.Map.insertWithKey f k v)

||| Atomically insert and return the previous value, when present.
||| Outer Nothing means invalid handle; inner Nothing means no old value.
export
insertLookupWithKey : Ord k
                    => (k -> v -> v -> v)
                    -> k
                    -> v
                    -> Map1 s k v
                    -> F1 s (Maybe (Maybe v))
insertLookupWithKey f k v =
  updateMap (\m =>
    let (old, m') = Data.Map.insertLookupWithKey f k v m
      in (m', old))

--------------------------------------------------------------------------------
--          Deletion/Update
--------------------------------------------------------------------------------

||| Atomically perform delete; False means invalid handle.
export
delete :  Eq (Map k v) => Eq k => Ord k => k -> Map1 s k v -> F1 s Bool
delete =
  \k => modifyMap (Data.Map.delete k)

||| Atomically perform adjust; False means invalid handle.
export
adjust :  Ord k => (v -> v) -> k -> Map1 s k v -> F1 s Bool
adjust =
  \f => \k => modifyMap (Data.Map.adjust f k)

||| Atomically perform adjustWithKey; False means invalid handle.
export
adjustWithKey :  Ord k => (k -> v -> v) -> k -> Map1 s k v -> F1 s Bool
adjustWithKey =
  \f => \k => modifyMap (Data.Map.adjustWithKey f k)

||| Atomically perform update; False means invalid handle.
export
update :  Ord k => (v -> Maybe v) -> k -> Map1 s k v -> F1 s Bool
update =
  \f => \k => modifyMap (Data.Map.update f k)

||| Atomically perform updateWithKey; False means invalid handle.
export
updateWithKey :  Ord k => (k -> v -> Maybe v) -> k -> Map1 s k v -> F1 s Bool
updateWithKey =
  \f => \k => modifyMap (Data.Map.updateWithKey f k)

||| Atomically perform alter; False means invalid handle.
export
alter :  Ord k => (Maybe v -> Maybe v) -> k -> Map1 s k v -> F1 s Bool
alter =
  \f => \k => modifyMap (Data.Map.alter f k)

||| Update an existing key and return its previous or replacement value.
||| The outer Nothing means an invalid map handle.
export
updateLookupWithKey : Ord k
                    => (k -> v -> Maybe v)
                    -> k
                    -> Map1 s k v
                    -> F1 s (Maybe (Maybe v))
updateLookupWithKey f k =
  updateMap (\m =>
    let (value, m') = Data.Map.updateLookupWithKey f k m
      in (m', value))

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Query lookup; outer Nothing indicates an invalid map handle.
export
lookup :  Ord k => k -> Map1 s k v -> F1 s (Maybe (Maybe v))
lookup =
  \k => queryMap (Data.Map.lookup k)

||| Query member; outer Nothing indicates an invalid map handle.
export
member :  Ord k => k -> Map1 s k v -> F1 s (Maybe Bool)
member =
  \k => queryMap (Data.Map.member k)

||| Query notMember; outer Nothing indicates an invalid map handle.
export
notMember :  Ord k => k -> Map1 s k v -> F1 s (Maybe Bool)
notMember =
  \k => queryMap (Data.Map.notMember k)

||| Query find; outer Nothing indicates an invalid map handle.
export
find :  Ord k => k -> Map1 s k v -> F1 s (Maybe (Maybe v))
find =
  \k => queryMap (Data.Map.lookup k)

||| Query findWithDefault; outer Nothing indicates an invalid map handle.
export
findWithDefault :  Ord k => v -> k -> Map1 s k v -> F1 s (Maybe v)
findWithDefault =
  \def => \k => queryMap (Data.Map.findWithDefault def k)

||| Query null; outer Nothing indicates an invalid map handle.
export
null :  Map1 s k v -> F1 s (Maybe Bool)
null =
  queryMap Data.Map.null

||| Query size; outer Nothing indicates an invalid map handle.
export
size :  Map1 s k v -> F1 s (Maybe Nat)
size =
  queryMap Data.Map.Internal.size

||| Look up ordered neighbor lookupLT; outer Nothing means invalid handle.
export
lookupLT :  Ord k => k -> Map1 s k v -> F1 s (Maybe (Maybe (k, v)))
lookupLT =
  \k => queryMap (Data.Map.lookupLT k)

||| Look up ordered neighbor lookupGT; outer Nothing means invalid handle.
export
lookupGT :  Ord k => k -> Map1 s k v -> F1 s (Maybe (Maybe (k, v)))
lookupGT =
  \k => queryMap (Data.Map.lookupGT k)

||| Look up ordered neighbor lookupLE; outer Nothing means invalid handle.
export
lookupLE :  Ord k => k -> Map1 s k v -> F1 s (Maybe (Maybe (k, v)))
lookupLE =
  \k => queryMap (Data.Map.lookupLE k)

||| Look up ordered neighbor lookupGE; outer Nothing means invalid handle.
export
lookupGE :  Ord k => k -> Map1 s k v -> F1 s (Maybe (Maybe (k, v)))
lookupGE =
  \k => queryMap (Data.Map.lookupGE k)

--------------------------------------------------------------------------------
--          Indexed
--------------------------------------------------------------------------------

||| Total lookupIndex; missing keys and invalid handles are distinguished.
export
lookupIndex :  Ord k => k -> Map1 s k v -> F1 s (Maybe (Maybe Nat))
lookupIndex =
  \k => queryMap (Data.Map.lookupIndex k)

||| Total findIndex; missing keys and invalid handles are distinguished.
export
findIndex :  Ord k => k -> Map1 s k v -> F1 s (Maybe (Maybe Nat))
findIndex =
  \k => queryMap (Data.Map.lookupIndex k)

||| Safely index an ordered list without any partial functions.
private
atList : Nat -> List a -> Maybe a
atList Z (x :: xs) = Just x
atList (S k) (_ :: xs) = atList k xs
atList _ [] = Nothing

||| Retrieve the indexed key/value pair if present.
||| Outer Nothing indicates an invalid map handle.
export
elemAt : Nat -> Map1 s k v -> F1 s (Maybe (Maybe (k, v)))
elemAt i = queryMap (atList i . Data.Map.toAscList)

||| Atomically update an entry by index, if it exists.
||| Just False means out of range; Nothing means invalid map handle.
export
updateAt : (k -> v -> Maybe v)
         -> Nat
         -> Map1 s k v
         -> F1 s (Maybe Bool)
updateAt f i =
  updateMap (\m =>
    case atList i (Data.Map.toAscList m) of
      Nothing => (m, False)
      Just _  => (Data.Map.updateAt f i m, True))

--------------------------------------------------------------------------------
--          Min/Max
--------------------------------------------------------------------------------

||| Total lookupMin; outer Nothing means invalid handle, inner empty map.
export
lookupMin :  Map1 s k v -> F1 s (Maybe (Maybe (k, v)))
lookupMin =
  queryMap Data.Map.lookupMin

||| Total lookupMax; outer Nothing means invalid handle, inner empty map.
export
lookupMax :  Map1 s k v -> F1 s (Maybe (Maybe (k, v)))
lookupMax =
  queryMap Data.Map.lookupMax

||| Total findMin; outer Nothing means invalid handle, inner empty map.
export
findMin :  Map1 s k v -> F1 s (Maybe (Maybe (k, v)))
findMin =
  queryMap Data.Map.lookupMin

||| Total findMax; outer Nothing means invalid handle, inner empty map.
export
findMax :  Map1 s k v -> F1 s (Maybe (Maybe (k, v)))
findMax =
  queryMap Data.Map.lookupMax

||| Atomically perform deleteMin; False means invalid handle.
export
deleteMin :  Map1 s k v -> F1 s Bool
deleteMin =
  modifyMap Data.Map.deleteMin

||| Atomically perform deleteMax; False means invalid handle.
export
deleteMax :  Map1 s k v -> F1 s Bool
deleteMax =
  modifyMap Data.Map.deleteMax

||| Atomically perform updateMin; False means invalid handle.
export
updateMin :  (v -> Maybe v) -> Map1 s k v -> F1 s Bool
updateMin =
  \f => modifyMap (Data.Map.updateMin f)

||| Atomically perform updateMax; False means invalid handle.
export
updateMax :  (v -> Maybe v) -> Map1 s k v -> F1 s Bool
updateMax =
  \f => modifyMap (Data.Map.updateMax f)

||| Atomically perform updateMinWithKey; False means invalid handle.
export
updateMinWithKey :  (k -> v -> Maybe v) -> Map1 s k v -> F1 s Bool
updateMinWithKey =
  \f => modifyMap (Data.Map.updateMinWithKey f)

||| Atomically perform updateMaxWithKey; False means invalid handle.
export
updateMaxWithKey :  (k -> v -> Maybe v) -> Map1 s k v -> F1 s Bool
updateMaxWithKey =
  \f => modifyMap (Data.Map.updateMaxWithKey f)

--------------------------------------------------------------------------------
--          Views
--------------------------------------------------------------------------------

||| Atomically remove and return the minimum entry.
||| Outer Nothing means invalid handle; inner Nothing means empty map.
export
minView : Map1 s k v -> F1 s (Maybe (Maybe v))
minView =
  updateMap (\m =>
    case Data.Map.minView m of
      Nothing => (m, Nothing)
      Just (value, m') => (m', Just value))

||| Atomically remove and return the maximum entry.
||| Outer Nothing means invalid handle; inner Nothing means empty map.
export
maxView : Map1 s k v -> F1 s (Maybe (Maybe v))
maxView =
  updateMap (\m =>
    case Data.Map.maxView m of
      Nothing => (m, Nothing)
      Just (value, m') => (m', Just value))

||| Atomically remove and return the minimum entry.
||| Outer Nothing means invalid handle; inner Nothing means empty map.
export
minViewWithKey : Map1 s k v -> F1 s (Maybe (Maybe (k, v)))
minViewWithKey =
  updateMap (\m =>
    case Data.Map.minViewWithKey m of
      Nothing => (m, Nothing)
      Just (value, m') => (m', Just value))

||| Atomically remove and return the maximum entry.
||| Outer Nothing means invalid handle; inner Nothing means empty map.
export
maxViewWithKey : Map1 s k v -> F1 s (Maybe (Maybe (k, v)))
maxViewWithKey =
  updateMap (\m =>
    case Data.Map.maxViewWithKey m of
      Nothing => (m, Nothing)
      Just (value, m') => (m', Just value))

||| Total deleteFindMin; returns Nothing when the map is empty.
export
deleteFindMin :  Map1 s k v -> F1 s (Maybe (Maybe (k, v)))
deleteFindMin =
  minViewWithKey

||| Total deleteFindMax; returns Nothing when the map is empty.
export
deleteFindMax :  Map1 s k v -> F1 s (Maybe (Maybe (k, v)))
deleteFindMax =
  maxViewWithKey

--------------------------------------------------------------------------------
--          Combine
--------------------------------------------------------------------------------

||| Atomically perform union on two maps sharing one store.
export
union :  Eq (Map k v) => Eq v => Ord k => Map1 s k v -> Map1 s k v -> F1 s Bool
union =
  modifyMaps Data.Map.union

||| Atomically perform unionWith on two maps sharing one store.
export
unionWith :  Ord k => (v -> v -> v) -> Map1 s k v -> Map1 s k v -> F1 s Bool
unionWith =
  \f => modifyMaps (Data.Map.unionWith f)

||| Atomically perform unionWithKey on two maps sharing one store.
export
unionWithKey :  Ord k
             => (k -> v -> v -> v)
             -> Map1 s k v -> Map1 s k v -> F1 s Bool
unionWithKey =
  \f => modifyMaps (Data.Map.unionWithKey f)

||| Atomically perform difference on two maps sharing one store.
export
difference :  Ord k => Map1 s k v -> Map1 s k v -> F1 s Bool
difference =
  modifyMaps Data.Map.difference

||| Atomically perform intersection on two maps sharing one store.
export
intersection :  Eq (Map k v) => Ord k => Map1 s k v -> Map1 s k v -> F1 s Bool
intersection =
  modifyMaps Data.Map.intersection

||| Atomically swap two distinct maps in one shared store.
||| Returns False for invalid handles, True for a valid no-op self-swap.
export
swap : Map1 s k v -> Map1 s k v -> F1 s Bool
swap (MkMap1 (MkMapStore1 ref) i) (MkMap1 _ j) t =
  casupdate1 ref (\maps =>
    case (Data.Map1.Internal.getAt i maps,
          Data.Map1.Internal.getAt j maps) of
      (Just first, Just second) =>
        if i == j
          then (maps, True)
          else case Data.Map1.Internal.replaceAt i second maps of
                 Nothing => (maps, False)
                 Just updated =>
                   case Data.Map1.Internal.replaceAt j first updated of
                     Nothing    => (maps, False)
                     Just maps' => (maps', True)
      _ => (maps, False)) t

--------------------------------------------------------------------------------
--          Submap
--------------------------------------------------------------------------------

||| Compare maps via isSubmapOf in one atomic snapshot.
export
isSubmapOf :  Eq v => Ord k => Map1 s k v -> Map1 s k v -> F1 s (Maybe Bool)
isSubmapOf =
  queryMaps Data.Map.isSubmapOf

||| Compare maps via isProperSubmapOf in one atomic snapshot.
export
isProperSubmapOf :  Eq v => Ord k
                 => Map1 s k v -> Map1 s k v -> F1 s (Maybe Bool)
isProperSubmapOf =
  queryMaps Data.Map.isProperSubmapOf

||| Compare maps via isSubmapOfBy in one atomic snapshot.
export
isSubmapOfBy :  Ord k => (v -> v -> Bool)
             -> Map1 s k v -> Map1 s k v -> F1 s (Maybe Bool)
isSubmapOfBy =
  \f => queryMaps (Data.Map.isSubmapOfBy f)

||| Compare maps via isProperSubmapOfBy in one atomic snapshot.
export
isProperSubmapOfBy :  Ord k => (v -> v -> Bool)
                   -> Map1 s k v -> Map1 s k v -> F1 s (Maybe Bool)
isProperSubmapOfBy =
  \f => queryMaps (Data.Map.isProperSubmapOfBy f)

--------------------------------------------------------------------------------
--          Filter
--------------------------------------------------------------------------------

||| Atomically filter via filter; False means invalid handle.
export
filter :  Eq (Map k v) => (v -> Bool) -> Map1 s k v -> F1 s Bool
filter =
  \p => modifyMap (Data.Map.filter p)

||| Atomically filter via filterWithKey; False means invalid handle.
export
filterWithKey :  Eq (Map k v) => (k -> v -> Bool) -> Map1 s k v -> F1 s Bool
filterWithKey =
  \p => modifyMap (Data.Map.filterWithKey p)

--------------------------------------------------------------------------------
--          Folds
--------------------------------------------------------------------------------

||| Fold map entries using foldl; Nothing means invalid handle.
export
foldl :  (a -> v -> a) -> a -> Map1 s k v -> F1 s (Maybe a)
foldl =
  \f => \z => queryMap (Data.Map.foldl f z)

||| Fold map entries using foldr; Nothing means invalid handle.
export
foldr :  (v -> a -> a) -> a -> Map1 s k v -> F1 s (Maybe a)
foldr =
  \f => \z => queryMap (Data.Map.foldr f z)

||| Fold map entries using foldlWithKey; Nothing means invalid handle.
export
foldlWithKey :  (a -> k -> v -> a) -> a -> Map1 s k v -> F1 s (Maybe a)
foldlWithKey =
  \f => \z => queryMap (Data.Map.foldlWithKey f z)

||| Fold map entries using foldrWithKey; Nothing means invalid handle.
export
foldrWithKey :  (k -> v -> a -> a) -> a -> Map1 s k v -> F1 s (Maybe a)
foldrWithKey =
  \f => \z => queryMap (Data.Map.foldrWithKey f z)

--------------------------------------------------------------------------------
--          Lists
--------------------------------------------------------------------------------

||| Return toAscList entries; Nothing means invalid handle.
export
toAscList :  Map1 s k v -> F1 s (Maybe (List (k, v)))
toAscList =
  queryMap Data.Map.toAscList

||| Return toDescList entries; Nothing means invalid handle.
export
toDescList :  Map1 s k v -> F1 s (Maybe (List (k, v)))
toDescList =
  queryMap Data.Map.toDescList

||| Return toList entries; Nothing means invalid handle.
export
toList :  Map1 s k v -> F1 s (Maybe (List (k, v)))
toList =
  queryMap Data.Map.toList

--------------------------------------------------------------------------------
--          Keys/Values
--------------------------------------------------------------------------------

||| Return keys in ascending key order; Nothing means invalid handle.
export
keys :  Map1 s k v -> F1 s (Maybe (List k))
keys =
  queryMap Data.Map.keys

||| Return values in ascending key order; Nothing means invalid handle.
export
values :  Map1 s k v -> F1 s (Maybe (List v))
values =
  queryMap Data.Map.values

--------------------------------------------------------------------------------
--          Map
--------------------------------------------------------------------------------

||| Transform values into a new map in the destination store.
||| Returns Nothing for an invalid source handle.
||| Source snapshot and destination allocation are separate operations.
export
map : MapStore1 s k b
    -> (a -> b)
    -> Map1 s k a
    -> F1 s (Maybe (Map1 s k b))
map store f source t =
  let original # t := queryMap id source t
    in case original of
         Nothing => Nothing # t
         Just m =>
           let mapped = Data.Map.map f m
               result # t := fromMap store mapped t
             in Just result # t

||| Transform values into a new map in the destination store.
||| Returns Nothing for an invalid source handle.
||| Source snapshot and destination allocation are separate operations.
export
mapWithKey : MapStore1 s k b
    -> (k -> a -> b)
    -> Map1 s k a
    -> F1 s (Maybe (Map1 s k b))
mapWithKey store f source t =
  let original # t := queryMap id source t
    in case original of
         Nothing => Nothing # t
         Just m =>
           let mapped = Data.Map.mapWithKey f m
               result # t := fromMap store mapped t
             in Just result # t

||| Transform values into a new map in the destination store.
||| Returns Nothing for an invalid source handle.
||| Source snapshot and destination allocation are separate operations.
export
mapMaybe : MapStore1 s k b
    -> (a -> Maybe b)
    -> Map1 s k a
    -> F1 s (Maybe (Map1 s k b))
mapMaybe store f source t =
  let original # t := queryMap id source t
    in case original of
         Nothing => Nothing # t
         Just m =>
           let mapped = Data.Map.mapMaybe f m
               result # t := fromMap store mapped t
             in Just result # t

||| Transform values into a new map in the destination store.
||| Returns Nothing for an invalid source handle.
||| Source snapshot and destination allocation are separate operations.
export
mapMaybeWithKey : MapStore1 s k b
    -> (k -> a -> Maybe b)
    -> Map1 s k a
    -> F1 s (Maybe (Map1 s k b))
mapMaybeWithKey store f source t =
  let original # t := queryMap id source t
    in case original of
         Nothing => Nothing # t
         Just m =>
           let mapped = Data.Map.mapMaybeWithKey f m
               result # t := fromMap store mapped t
             in Just result # t
