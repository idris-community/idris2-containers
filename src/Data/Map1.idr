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

||| Apply a read-only operation to a map using one store snapshot.
||| The map is not modified.
private
queryMap :  (Map k v -> a)
         -> Map1 s k v
         -> F1 s a
queryMap f (MkMap1 (MkMapStore1 ref) i) t =
  let maps # t := read1 ref t
    in f (getAt i maps) # t

||| Atomically modify a map using a CAS loop on its shared store.
||| The operation is retried if the store changes concurrently.
private
modifyMap :  (Map k v -> Map k v)
          -> Map1 s k v
          -> F1' s
modifyMap f (MkMap1 (MkMapStore1 ref) i) t =
  casmod1 ref
    (\maps =>
      replaceAt i (f (getAt i maps)) maps
    ) t

||| Atomically modify a map and return an additional result.
||| The result corresponds to the successfully committed update.
private
updateMap :  (Map k v -> (Map k v, a))
          -> Map1 s k v
          -> F1 s a
updateMap f (MkMap1 (MkMapStore1 ref) i) t =
  casupdate1 ref
    (\maps =>
      let (map, result) = f (getAt i maps)
        in (replaceAt i map maps, result)
    ) t

||| Query two maps using a single atomic store snapshot.
|||
||| Both handles must belong to the same store.
private
queryMaps :  (Map k v -> Map k v -> a)
          -> Map1 s k v
          -> Map1 s k v
          -> F1 s a
queryMaps f (MkMap1 (MkMapStore1 ref) i) (MkMap1 _ j) t =
  let maps # t := read1 ref t
      map1     := getAt i maps
      map2     := getAt j maps
    in f map1 map2 # t

||| Atomically update the first of two maps using both maps.
|||
||| Both handles must belong to the same store.
||| Both maps are read from the same snapshot inside the CAS loop.
||| The second map is not modified.
private
modifyMaps :  (Map k v -> Map k v -> Map k v)
           -> Map1 s k v
           -> Map1 s k v
           -> F1' s
modifyMaps f (MkMap1 (MkMapStore1 ref) i) (MkMap1 _ j) t =
  casmod1 ref
    (\maps =>
      let map1 = getAt i maps
          map2 = getAt j maps
        in replaceAt i (f map1 map2) maps
    ) t

||| Atomically exchange the contents of two maps.
|||
||| Both handles must belong to the same store.
||| When both handles identify the same map, nothing changes.
private
swapMaps :  Map1 s k v
         -> Map1 s k v
         -> F1' s
swapMaps (MkMap1 (MkMapStore1 ref) i) (MkMap1 _ j) t =
  casmod1 ref
    (\maps =>
      let map1 = getAt i maps
          map2 = getAt j maps
        in case i == j of
             True  =>
               maps
             False =>
               let maps' = replaceAt i map2 maps
                 in replaceAt j map1 maps'
    ) t

--------------------------------------------------------------------------------
--          Construction
--------------------------------------------------------------------------------

||| Create an empty shared atomic store. O(1)
export
newStore : F1 s (MapStore1 s k v)
newStore t =
  let ref # t := ref1 Data.SortedMap.empty t
    in MkMapStore1 ref # t

||| Create a new Map1 containing the given immutable map.
|||
||| A unique identifier is allocated atomically within the store.
||| O(log n), where n is the number of maps in the store.
export
fromMap :  MapStore1 s k v
        -> Map k v
        -> F1 s (Map1 s k v)
fromMap store@(MkMapStore1 ref) map t =
  casupdate1 ref
    (\maps =>
      let i = nextId maps
        in ( Data.SortedMap.insert i map maps
           , MkMap1 store i
           )
    ) t

||| Create an empty Map1 within the given store.
||| O(log n), where n is the number of maps in the store.
export
empty :  MapStore1 s k v
      -> F1 s (Map1 s k v)
empty store t =
  fromMap store Data.Map.empty t

||| Create a Map1 containing a single key and value.
||| O(log n), where n is the number of maps in the store.
export
singleton :  k
          -> v
          -> MapStore1 s k v
          -> F1 s (Map1 s k v)
singleton k v store t =
  fromMap store (Data.Map.Internal.singleton k v) t

||| Create a Map1 from a list of key/value pairs.
||| Duplicate keys retain the last associated value.
||| O(m log m + log n) in the general case.
export
fromList :  Ord k
         => Eq v
         => Eq (Map k v)
         => List (k, v)
         -> MapStore1 s k v
         -> F1 s (Map1 s k v)
fromList xs store t =
  fromMap store (Data.Map.fromList xs) t

--------------------------------------------------------------------------------
--          Conversion
--------------------------------------------------------------------------------

||| Return an immutable snapshot of a Map1.
||| Subsequent updates do not modify the returned snapshot.
||| O(log n), where n is the number of maps in the store.
export
freeze :  Map1 s k v
       -> F1 s (Map k v)
freeze =
  queryMap id

--------------------------------------------------------------------------------
--          Insertion
--------------------------------------------------------------------------------

||| Atomically insert a key and value into a Map1.
||| If the key already exists, its associated value is replaced.
||| O(log m + log n)
export
insert :  Eq (Map k v)
       => Eq v
       => Ord k
       => k
       -> v
       -> Map1 s k v
       -> F1' s
insert k v =
  modifyMap (Data.Map.insert k v)

||| Atomically insert a key and value using a combining function.
||| When the key exists, the new value is combined with the old value.
||| The combining function receives the new value first.
||| O(log m + log n)
export
insertWith :  Ord k
           => (v -> v -> v)
           -> k
           -> v
           -> Map1 s k v
           -> F1' s
insertWith f k v =
  modifyMap (Data.Map.insertWith f k v)

||| Atomically insert a key and value using a key-aware function.
||| The function receives the key, new value, and old value.
||| O(log m + log n)
export
insertWithKey :  Ord k
              => (k -> v -> v -> v)
              -> k
              -> v
              -> Map1 s k v
              -> F1' s
insertWithKey f k v =
  modifyMap (Data.Map.insertWithKey f k v)

||| Atomically insert a key and value while retrieving the old value.
||| Returns Nothing if the key did not previously exist.
||| O(log m + log n)
export
insertLookupWithKey :  Ord k
                    => (k -> v -> v -> v)
                    -> k
                    -> v
                    -> Map1 s k v
                    -> F1 s (Maybe v)
insertLookupWithKey f k v =
  updateMap
    (\map =>
      let (old, map') = Data.Map.insertLookupWithKey f k v map
        in (map', old)
    )

--------------------------------------------------------------------------------
--          Deletion/Update
--------------------------------------------------------------------------------

||| Atomically delete a key and its associated value.
||| If the key does not exist, the map remains unchanged.
||| O(log m + log n)
export
delete :  Eq (Map k v)
       => Eq k
       => Ord k
       => k
       -> Map1 s k v
       -> F1' s
delete k =
  modifyMap (Data.Map.delete k)

||| Atomically adjust the value associated with a key.
||| If the key does not exist, the map remains unchanged.
||| O(log m + log n)
export
adjust :  Ord k
       => (v -> v)
       -> k
       -> Map1 s k v
       -> F1' s
adjust f k =
  modifyMap (Data.Map.adjust f k)

||| Atomically adjust a value using a key-aware function.
||| If the key does not exist, the map remains unchanged.
||| O(log m + log n)
export
adjustWithKey :  Ord k
              => (k -> v -> v)
              -> k
              -> Map1 s k v
              -> F1' s
adjustWithKey f k =
  modifyMap (Data.Map.adjustWithKey f k)

||| Atomically update the value associated with a key.
||| Returning Nothing from the function deletes the entry.
||| If the key does not exist, the map remains unchanged.
||| O(log m + log n)
export
update :  Ord k
       => (v -> Maybe v)
       -> k
       -> Map1 s k v
       -> F1' s
update f k =
  modifyMap (Data.Map.update f k)

||| Atomically update a value using a key-aware function.
||| Returning Nothing from the function deletes the entry.
||| O(log m + log n)
export
updateWithKey :  Ord k
              => (k -> v -> Maybe v)
              -> k
              -> Map1 s k v
              -> F1' s
updateWithKey f k =
  modifyMap (Data.Map.updateWithKey f k)

||| Atomically update an entry and return the updated value.
||| If the entry is deleted, returns its original value.
||| Returns Nothing if the key does not exist.
||| O(log m + log n)
export
updateLookupWithKey :  Ord k
                    => (k -> v -> Maybe v)
                    -> k
                    -> Map1 s k v
                    -> F1 s (Maybe v)
updateLookupWithKey f k =
  updateMap
    (\map =>
      let (result, map') = Data.Map.updateLookupWithKey f k map
        in (map', result)
    )

||| Atomically alter the presence or value of a key.
||| The function receives Nothing when the key is absent.
||| Returning Nothing deletes the entry or leaves it absent.
||| O(log m + log n)
export
alter :  Ord k
      => (Maybe v -> Maybe v)
      -> k
      -> Map1 s k v
      -> F1' s
alter f k =
  modifyMap (Data.Map.alter f k)

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Look up the value associated with a key.
||| Returns Nothing if the key does not exist.
||| O(log m + log n)
export
lookup :  Ord k
       => k
       -> Map1 s k v
       -> F1 s (Maybe v)
lookup k =
  queryMap (Data.Map.lookup k)

||| Check whether a key exists in a Map1. O(log m + log n)
export
member :  Ord k
       => k
       -> Map1 s k v
       -> F1 s Bool
member k =
  queryMap (Data.Map.member k)

||| Check whether a key does not exist in a Map1.
||| O(log m + log n)
export
notMember :  Ord k
          => k
          -> Map1 s k v
          -> F1 s Bool
notMember k =
  queryMap (Data.Map.notMember k)

||| Retrieve the value associated with a key.
||| Calls idris_crash if the key does not exist.
||| O(log m + log n)
export
find :  Ord k
     => k
     -> Map1 s k v
     -> F1 s v
find k =
  queryMap (Data.Map.find k)

||| Retrieve the value associated with a key or a default value.
||| Returns the default when the key does not exist.
||| O(log m + log n)
export
findWithDefault :  Ord k
                => v
                -> k
                -> Map1 s k v
                -> F1 s v
findWithDefault def k =
  queryMap (Data.Map.findWithDefault def k)

||| Check whether a Map1 is empty. O(log n)
export
null :  Map1 s k v
     -> F1 s Bool
null =
  queryMap Data.Map.null

||| Return the number of entries in a Map1. O(log n)
export
size :  Map1 s k v
     -> F1 s Nat
size =
  queryMap Data.Map.Internal.size

||| Find the largest key strictly smaller than the given key.
||| Returns its key/value pair or Nothing.
||| O(log m + log n)
export
lookupLT :  Ord k
         => k
         -> Map1 s k v
         -> F1 s (Maybe (k, v))
lookupLT k =
  queryMap (Data.Map.lookupLT k)

||| Find the smallest key strictly greater than the given key.
||| Returns its key/value pair or Nothing.
||| O(log m + log n)
export
lookupGT :  Ord k
         => k
         -> Map1 s k v
         -> F1 s (Maybe (k, v))
lookupGT k =
  queryMap (Data.Map.lookupGT k)

||| Find the largest key smaller than or equal to the given key.
||| Returns its key/value pair or Nothing.
||| O(log m + log n)
export
lookupLE :  Ord k
         => k
         -> Map1 s k v
         -> F1 s (Maybe (k, v))
lookupLE k =
  queryMap (Data.Map.lookupLE k)

||| Find the smallest key greater than or equal to the given key.
||| Returns its key/value pair or Nothing.
||| O(log m + log n)
export
lookupGE :  Ord k
         => k
         -> Map1 s k v
         -> F1 s (Maybe (k, v))
lookupGE k =
  queryMap (Data.Map.lookupGE k)

--------------------------------------------------------------------------------
--          Indexed
--------------------------------------------------------------------------------

||| Find the zero-based index of a key in ascending order.
||| Returns Nothing if the key does not exist.
||| O(log m + log n)
export
lookupIndex :  Ord k
            => k
            -> Map1 s k v
            -> F1 s (Maybe Nat)
lookupIndex k =
  queryMap (Data.Map.lookupIndex k)

||| Find the zero-based index of a key in ascending order.
||| Calls idris_crash if the key does not exist.
||| O(log m + log n)
export
findIndex :  Ord k
          => k
          -> Map1 s k v
          -> F1 s Nat
findIndex k =
  queryMap (Data.Map.findIndex k)

||| Retrieve a key/value pair at its zero-based index.
||| Calls idris_crash if the index is out of bounds.
||| O(log m + log n)
export
elemAt :  Nat
       -> Map1 s k v
       -> F1 s (k, v)
elemAt i =
  queryMap (Data.Map.elemAt i)

||| Atomically update an entry at its zero-based index.
||| Returning Nothing from the function deletes the entry.
||| Calls idris_crash if the index is out of bounds.
||| O(log m + log n)
export
updateAt :  (k -> v -> Maybe v)
         -> Nat
         -> Map1 s k v
         -> F1' s
updateAt f i =
  modifyMap (Data.Map.updateAt f i)

--------------------------------------------------------------------------------
--          Min/Max
--------------------------------------------------------------------------------

||| Retrieve the smallest key/value pair.
||| Returns Nothing if the map is empty. O(log m + log n)
export
lookupMin :  Map1 s k v
          -> F1 s (Maybe (k, v))
lookupMin =
  queryMap Data.Map.lookupMin

||| Retrieve the largest key/value pair.
||| Returns Nothing if the map is empty. O(log m + log n)
export
lookupMax :  Map1 s k v
          -> F1 s (Maybe (k, v))
lookupMax =
  queryMap Data.Map.lookupMax

||| Retrieve the smallest key/value pair.
||| Calls idris_crash if the map is empty. O(log m + log n)
export
findMin :  Map1 s k v
        -> F1 s (k, v)
findMin =
  queryMap Data.Map.findMin

||| Retrieve the largest key/value pair.
||| Calls idris_crash if the map is empty. O(log m + log n)
export
findMax :  Map1 s k v
        -> F1 s (k, v)
findMax =
  queryMap Data.Map.findMax

||| Atomically delete the entry with the smallest key.
||| An empty map remains unchanged. O(log m + log n)
export
deleteMin :  Map1 s k v
          -> F1' s
deleteMin =
  modifyMap Data.Map.deleteMin

||| Atomically delete the entry with the largest key.
||| An empty map remains unchanged. O(log m + log n)
export
deleteMax :  Map1 s k v
          -> F1' s
deleteMax =
  modifyMap Data.Map.deleteMax

||| Atomically update the entry with the smallest key.
||| Returning Nothing deletes the entry. O(log m + log n)
export
updateMin :  (v -> Maybe v)
          -> Map1 s k v
          -> F1' s
updateMin f =
  modifyMap (Data.Map.updateMin f)

||| Atomically update the entry with the largest key.
||| Returning Nothing deletes the entry. O(log m + log n)
export
updateMax :  (v -> Maybe v)
          -> Map1 s k v
          -> F1' s
updateMax f =
  modifyMap (Data.Map.updateMax f)

||| Atomically update the entry with the smallest key.
||| The function receives both the key and its value.
||| Returning Nothing deletes the entry. O(log m + log n)
export
updateMinWithKey :  (k -> v -> Maybe v)
                 -> Map1 s k v
                 -> F1' s
updateMinWithKey f =
  modifyMap (Data.Map.updateMinWithKey f)

||| Atomically update the entry with the largest key.
||| The function receives both the key and its value.
||| Returning Nothing deletes the entry. O(log m + log n)
export
updateMaxWithKey :  (k -> v -> Maybe v)
                 -> Map1 s k v
                 -> F1' s
updateMaxWithKey f =
  modifyMap (Data.Map.updateMaxWithKey f)

--------------------------------------------------------------------------------
--          Views
--------------------------------------------------------------------------------

||| Atomically retrieve and remove the smallest value.
||| Returns Nothing if the map is empty. O(log m + log n)
export
minView :  Map1 s k v
        -> F1 s (Maybe v)
minView =
  updateMap
    (\map =>
      case Data.Map.minView map of
        Nothing        => (map, Nothing)
        Just (v, map') => (map', Just v)
    )

||| Atomically retrieve and remove the largest value.
||| Returns Nothing if the map is empty. O(log m + log n)
export
maxView :  Map1 s k v
        -> F1 s (Maybe v)
maxView =
  updateMap
    (\map =>
      case Data.Map.maxView map of
        Nothing        => (map, Nothing)
        Just (v, map') => (map', Just v)
    )

||| Atomically retrieve and remove the smallest key/value pair.
||| Returns Nothing if the map is empty. O(log m + log n)
export
minViewWithKey :  Map1 s k v
               -> F1 s (Maybe (k, v))
minViewWithKey =
  updateMap
    (\map =>
      case Data.Map.minViewWithKey map of
        Nothing             => (map, Nothing)
        Just (entry, map')  => (map', Just entry)
    )

||| Atomically retrieve and remove the largest key/value pair.
||| Returns Nothing if the map is empty. O(log m + log n)
export
maxViewWithKey :  Map1 s k v
               -> F1 s (Maybe (k, v))
maxViewWithKey =
  updateMap
    (\map =>
      case Data.Map.maxViewWithKey map of
        Nothing             => (map, Nothing)
        Just (entry, map')  => (map', Just entry)
    )

||| Atomically retrieve and remove the smallest key/value pair.
||| Calls idris_crash if the map is empty. O(log m + log n)
export
deleteFindMin :  Map1 s k v
              -> F1 s (k, v)
deleteFindMin =
  updateMap
    (\map =>
      let (entry, map') = Data.Map.deleteFindMin map
        in (map', entry)
    )

||| Atomically retrieve and remove the largest key/value pair.
||| Calls idris_crash if the map is empty. O(log m + log n)
export
deleteFindMax :  Map1 s k v
              -> F1 s (k, v)
deleteFindMax =
  updateMap
    (\map =>
      let (entry, map') = Data.Map.deleteFindMax map
        in (map', entry)
    )

--------------------------------------------------------------------------------
--          Combine
--------------------------------------------------------------------------------

||| Atomically insert all entries of the second Map1 into the first.
||| The union is left-biased, preserving values from the first map.
|||
||| Both handles must belong to the same store.
||| Both maps are read from the same atomic snapshot.
||| The second map is not modified.
export
union :  Eq (Map k v)
      => Eq v
      => Ord k
      => Map1 s k v
      -> Map1 s k v
      -> F1' s
union =
  modifyMaps Data.Map.union

||| Atomically combine two maps using a value-combining function.
||| The function receives the value from the first map first.
|||
||| Both handles must belong to the same store.
||| The second map is not modified.
export
unionWith :  Ord k
          => (v -> v -> v)
          -> Map1 s k v
          -> Map1 s k v
          -> F1' s
unionWith f =
  modifyMaps (Data.Map.unionWith f)

||| Atomically combine two maps using a key-aware function.
||| The function receives the key, first value, and second value.
|||
||| Both handles must belong to the same store.
||| The second map is not modified.
export
unionWithKey :  Ord k
             => (k -> v -> v -> v)
             -> Map1 s k v
             -> Map1 s k v
             -> F1' s
unionWithKey f =
  modifyMaps (Data.Map.unionWithKey f)

||| Atomically remove entries from the first map whose keys
||| also occur in the second map.
|||
||| Both handles must belong to the same store.
||| The second map is not modified.
export
difference :  Ord k
           => Map1 s k v
           -> Map1 s k v
           -> F1' s
difference =
  modifyMaps Data.Map.difference

||| Atomically retain entries from the first map whose keys
||| also occur in the second map.
|||
||| Both handles must belong to the same store.
||| Values from the first map are preserved.
||| The second map is not modified.
export
intersection :  Eq (Map k v)
             => Ord k
             => Map1 s k v
             -> Map1 s k v
             -> F1' s
intersection =
  modifyMaps Data.Map.intersection

||| Atomically exchange the contents of two maps.
|||
||| Both handles must belong to the same store.
||| If both handles identify the same map, nothing changes.
export
swap :  Map1 s k v
     -> Map1 s k v
     -> F1' s
swap =
  swapMaps

--------------------------------------------------------------------------------
--          Submap
--------------------------------------------------------------------------------

||| Check whether every entry in the first map occurs in the second.
||| Both keys and associated values must match.
|||
||| Both handles must belong to the same store.
||| Both maps are observed through one atomic snapshot.
export
isSubmapOf :  Eq v
           => Ord k
           => Map1 s k v
           -> Map1 s k v
           -> F1 s Bool
isSubmapOf =
  queryMaps Data.Map.isSubmapOf

||| Check whether the first map is a proper submap of the second.
||| A proper submap contains strictly fewer entries.
|||
||| Both handles must belong to the same store.
||| Both maps are observed through one atomic snapshot.
export
isProperSubmapOf :  Eq v
                 => Ord k
                 => Map1 s k v
                 -> Map1 s k v
                 -> F1 s Bool
isProperSubmapOf =
  queryMaps Data.Map.isProperSubmapOf

||| Check whether the first map is a submap of the second
||| using the supplied value-comparison function.
|||
||| Both handles must belong to the same store.
||| Both maps are observed through one atomic snapshot.
export
isSubmapOfBy :  Ord k
             => (v -> v -> Bool)
             -> Map1 s k v
             -> Map1 s k v
             -> F1 s Bool
isSubmapOfBy f =
  queryMaps (Data.Map.isSubmapOfBy f)

||| Check whether the first map is a proper submap of the second
||| using the supplied value-comparison function.
|||
||| Both handles must belong to the same store.
||| Both maps are observed through one atomic snapshot.
export
isProperSubmapOfBy :  Ord k
                   => (v -> v -> Bool)
                   -> Map1 s k v
                   -> Map1 s k v
                   -> F1 s Bool
isProperSubmapOfBy f =
  queryMaps (Data.Map.isProperSubmapOfBy f)

--------------------------------------------------------------------------------
--          Filter
--------------------------------------------------------------------------------

||| Atomically retain only entries whose values satisfy a predicate.
||| O(m + log n)
export
filter :  Eq (Map k v)
       => (v -> Bool)
       -> Map1 s k v
       -> F1' s
filter p =
  modifyMap (Data.Map.filter p)

||| Atomically retain only entries satisfying a key-aware predicate.
||| O(m + log n)
export
filterWithKey :  Eq (Map k v)
              => (k -> v -> Bool)
              -> Map1 s k v
              -> F1' s
filterWithKey p =
  modifyMap (Data.Map.filterWithKey p)

--------------------------------------------------------------------------------
--          Folds
--------------------------------------------------------------------------------

||| Fold values using a left-associative binary operator.
||| Values are visited in ascending key order. O(m + log n)
export
foldl :  (a -> v -> a)
      -> a
      -> Map1 s k v
      -> F1 s a
foldl f z =
  queryMap (Data.Map.foldl f z)

||| Fold values using a right-associative binary operator.
||| Values are visited in ascending key order. O(m + log n)
export
foldr :  (v -> a -> a)
      -> a
      -> Map1 s k v
      -> F1 s a
foldr f z =
  queryMap (Data.Map.foldr f z)

||| Fold keys and values using a left-associative operator.
||| Entries are visited in ascending key order. O(m + log n)
export
foldlWithKey :  (a -> k -> v -> a)
             -> a
             -> Map1 s k v
             -> F1 s a
foldlWithKey f z =
  queryMap (Data.Map.foldlWithKey f z)

||| Fold keys and values using a right-associative operator.
||| Entries are visited in ascending key order. O(m + log n)
export
foldrWithKey :  (k -> v -> a -> a)
             -> a
             -> Map1 s k v
             -> F1 s a
foldrWithKey f z =
  queryMap (Data.Map.foldrWithKey f z)

--------------------------------------------------------------------------------
--          Lists
--------------------------------------------------------------------------------

||| Convert a Map1 to a list of key/value pairs in ascending key order.
||| O(m + log n)
export
toAscList :  Map1 s k v
          -> F1 s (List (k, v))
toAscList =
  queryMap Data.Map.toAscList

||| Convert a Map1 to a list of key/value pairs in descending key order.
||| O(m + log n)
export
toDescList :  Map1 s k v
           -> F1 s (List (k, v))
toDescList =
  queryMap Data.Map.toDescList

||| Convert a Map1 to a list of key/value pairs in ascending key order.
||| O(m + log n)
export
toList :  Map1 s k v
       -> F1 s (List (k, v))
toList =
  queryMap Data.Map.toList

--------------------------------------------------------------------------------
--          Keys
--------------------------------------------------------------------------------

||| Retrieve the keys of a Map1 in ascending order.
||| O(m + log n)
export
keys :  Map1 s k v
     -> F1 s (List k)
keys =
  queryMap Data.Map.keys

--------------------------------------------------------------------------------
--          Values
--------------------------------------------------------------------------------

||| Retrieve the values of a Map1 in ascending key order.
||| Values may contain duplicates. O(m + log n)
export
values :  Map1 s k v
       -> F1 s (List v)
values =
  queryMap Data.Map.values

--------------------------------------------------------------------------------
--          Map
--------------------------------------------------------------------------------

||| Map a function over the values of a Map1, creating a new Map1.
|||
||| Keys and their ordering are preserved.
||| The new map is allocated atomically in the destination store.
||| The original Map1 is not modified.
export
map :  MapStore1 s k b
    -> (a -> b)
    -> Map1 s k a
    -> F1 s (Map1 s k b)
map store f source t =
  let original # t := queryMap id source t
      mapped       := Data.Map.map f original
    in fromMap store mapped t

||| Map a key-aware function over the values of a Map1.
||| Creates a new Map1 in the destination store.
||| The original Map1 is not modified.
export
mapWithKey :  MapStore1 s k b
           -> (k -> a -> b)
           -> Map1 s k a
           -> F1 s (Map1 s k b)
mapWithKey store f source t =
  let original # t := queryMap id source t
      mapped       := Data.Map.mapWithKey f original
    in fromMap store mapped t

||| Map a partial function over the values of a Map1.
||| Entries producing Nothing are omitted.
||| Creates a new Map1 in the destination store.
export
mapMaybe :  MapStore1 s k b
          -> (a -> Maybe b)
          -> Map1 s k a
          -> F1 s (Map1 s k b)
mapMaybe store f source t =
  let original # t := queryMap id source t
      mapped       := Data.Map.mapMaybe f original
    in fromMap store mapped t

||| Map a key-aware partial function over a Map1.
||| Entries producing Nothing are omitted.
||| Creates a new Map1 in the destination store.
export
mapMaybeWithKey :  MapStore1 s k b
                 -> (k -> a -> Maybe b)
                 -> Map1 s k a
                 -> F1 s (Map1 s k b)
mapMaybeWithKey store f source t =
  let original # t := queryMap id source t
      mapped       := Data.Map.mapMaybeWithKey f original
    in fromMap store mapped t
