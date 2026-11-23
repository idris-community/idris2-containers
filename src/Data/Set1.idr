||| Linear Finite Sets
module Data.Set1

import public Data.Set1.Internal

import Data.Set
import Data.Set.Internal
import Data.SortedMap
import Data.Linear.Ref1

%hide Prelude.null
%hide Prelude.toList

%default total

--------------------------------------------------------------------------------
--          Internal Operations
--------------------------------------------------------------------------------

||| Apply a read-only operation to a set using one store snapshot.
||| The set is not modified.
private
querySet :  (Set a -> b)
         -> Set1 s a
         -> F1 s b
querySet f (MkSet1 (MkSetStore1 ref) i) t =
  let sets # t := read1 ref t
    in f (getAt i sets) # t

||| Atomically modify a set using a CAS loop on its shared store.
||| The operation is retried if the store changes concurrently.
private
modifySet :  (Set a -> Set a)
          -> Set1 s a
          -> F1' s
modifySet f (MkSet1 (MkSetStore1 ref) i) t =
  casmod1 ref
    (\sets =>
      replaceAt i (f (getAt i sets)) sets
    ) t

||| Atomically modify a set and return an additional result.
||| The result corresponds to the successfully committed update.
private
updateSet :  (Set a -> (Set a, b))
          -> Set1 s a
          -> F1 s b
updateSet f (MkSet1 (MkSetStore1 ref) i) t =
  casupdate1 ref
    (\sets =>
      let (set, result) = f (getAt i sets)
        in (replaceAt i set sets, result)
    ) t

||| Query two sets using a single atomic store snapshot.
|||
||| Both handles must belong to the same store.
private
querySets :  (Set a -> Set a -> b)
          -> Set1 s a
          -> Set1 s a
          -> F1 s b
querySets f (MkSet1 (MkSetStore1 ref) i) (MkSet1 _ j) t =
  let sets # t := read1 ref t
      set1     := getAt i sets
      set2     := getAt j sets
    in f set1 set2 # t

||| Atomically update the first of two sets using both sets.
|||
||| Both handles must belong to the same store.
||| Both sets are read from the same store snapshot inside the
||| CAS loop, preventing read-write conflicts between them.
|||
||| The second set is not modified.
private
modifySets :  (Set a -> Set a -> Set a)
           -> Set1 s a
           -> Set1 s a
           -> F1' s
modifySets f (MkSet1 (MkSetStore1 ref) i) (MkSet1 _ j) t =
  casmod1 ref
    (\sets =>
      let set1 = getAt i sets
          set2 = getAt j sets
        in replaceAt i (f set1 set2) sets
    ) t

||| Atomically modify two sets and return an additional result.
|||
||| Both handles must belong to the same store.
||| The callback receives both sets from one consistent snapshot.
||| The replacement values are committed through one CAS.
private
updateSets :  (Set a -> Set a -> (Set a, Set a, b))
           -> Set1 s a
           -> Set1 s a
           -> F1 s b
updateSets f (MkSet1 (MkSetStore1 ref) i) (MkSet1 _ j) t =
  casupdate1 ref
    (\sets =>
      let set1 = getAt i sets
          set2 = getAt j sets
        in case i == j of
             True =>
               let (_, _, result) = f set1 set2
                 in (sets, result)
             False =>
               let (set1', set2', result) = f set1 set2
                   sets' = replaceAt i set1' sets
                 in (replaceAt j set2' sets', result)
    ) t

--------------------------------------------------------------------------------
--          Construction
--------------------------------------------------------------------------------

||| Create an empty shared atomic store. O(1)
export
newStore : F1 s (SetStore1 s a)
newStore t =
  let ref # t := ref1 Data.SortedMap.empty t
    in MkSetStore1 ref # t

||| Create a new Set1 containing the given immutable set.
|||
||| A unique identifier is allocated atomically within the store.
||| O(log n), where n is the number of sets in the store.
export
fromSet :  SetStore1 s a
        -> Set a
        -> F1 s (Set1 s a)
fromSet store@(MkSetStore1 ref) set t =
  casupdate1 ref
    (\sets =>
      let i = nextId sets
        in ( Data.SortedMap.insert i set sets
           , MkSet1 store i
           )
    ) t

||| Create an empty Set1 within the given store.
||| O(log n), where n is the number of sets in the store.
export
empty :  SetStore1 s a
      -> F1 s (Set1 s a)
empty store t =
  fromSet store Data.Set.empty t

||| Create a Set1 containing a single element.
||| O(log n), where n is the number of sets in the store.
export
singleton :  a
          -> SetStore1 s a
          -> F1 s (Set1 s a)
singleton x store t =
  fromSet store (Data.Set.Internal.singleton x) t

||| Create a Set1 from a list of elements.
||| Duplicate elements are removed according to the ordering.
||| O(m log m + log n) in the general case, where m is the number
||| of input elements and n is the number of sets in the store.
export
fromList :  Ord a
         => List a
         -> SetStore1 s a
         -> F1 s (Set1 s a)
fromList xs store t =
  fromSet store (Data.Set.fromList xs) t

--------------------------------------------------------------------------------
--          Conversion
--------------------------------------------------------------------------------

||| Return an immutable snapshot of a Set1.
||| Subsequent updates do not modify the returned snapshot.
||| O(log n), where n is the number of sets in the store.
export
freeze :  Set1 s a
       -> F1 s (Set a)
freeze =
  querySet id

--------------------------------------------------------------------------------
--          Insertion
--------------------------------------------------------------------------------

||| Atomically insert an element into a Set1.
||| If an equivalent element already exists, it is replaced according
||| to the semantics of Data.Set.insert. O(log m + log n)
export
insert :  Ord a
       => a
       -> Set1 s a
       -> F1' s
insert x =
  modifySet (Data.Set.insert x)

--------------------------------------------------------------------------------
--          Deletion
--------------------------------------------------------------------------------

||| Atomically delete an element from a Set1.
||| If the element does not exist, the set remains unchanged.
||| O(log m + log n)
export
delete :  Ord a
       => a
       -> Set1 s a
       -> F1' s
delete x =
  modifySet (Data.Set.delete x)

||| Atomically delete the smallest element from a Set1.
||| If the set is empty, it remains unchanged. O(log m + log n)
export
deleteMin :  Set1 s a
          -> F1' s
deleteMin =
  modifySet Data.Set.deleteMin

||| Atomically delete the largest element from a Set1.
||| If the set is empty, it remains unchanged. O(log m + log n)
export
deleteMax :  Set1 s a
          -> F1' s
deleteMax =
  modifySet Data.Set.deleteMax

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Check whether an element exists in a Set1. O(log m + log n)
export
member :  Ord a
       => a
       -> Set1 s a
       -> F1 s Bool
member x =
  querySet (Data.Set.member x)

||| Check whether an element does not exist in a Set1.
||| O(log m + log n)
export
notMember :  Ord a
          => a
          -> Set1 s a
          -> F1 s Bool
notMember x =
  querySet (Data.Set.notMember x)

||| Check whether a Set1 is empty. O(log n)
export
null :  Set1 s a
     -> F1 s Bool
null =
  querySet Data.Set.null

||| Return the number of elements in a Set1. O(log n)
export
size :  Set1 s a
     -> F1 s Nat
size =
  querySet Data.Set.Internal.size

||| Find the largest element strictly smaller than the given value.
||| Returns Nothing if no such element exists. O(log m + log n)
export
lookupLT :  Ord a
         => a
         -> Set1 s a
         -> F1 s (Maybe a)
lookupLT x =
  querySet (Data.Set.lookupLT x)

||| Find the smallest element strictly greater than the given value.
||| Returns Nothing if no such element exists. O(log m + log n)
export
lookupGT :  Ord a
         => a
         -> Set1 s a
         -> F1 s (Maybe a)
lookupGT x =
  querySet (Data.Set.lookupGT x)

||| Find the largest element smaller than or equal to the given value.
||| Returns Nothing if no such element exists. O(log m + log n)
export
lookupLE :  Ord a
         => a
         -> Set1 s a
         -> F1 s (Maybe a)
lookupLE x =
  querySet (Data.Set.lookupLE x)

||| Find the smallest element greater than or equal to the given value.
||| Returns Nothing if no such element exists. O(log m + log n)
export
lookupGE :  Ord a
         => a
         -> Set1 s a
         -> F1 s (Maybe a)
lookupGE x =
  querySet (Data.Set.lookupGE x)

--------------------------------------------------------------------------------
--          Indexed
--------------------------------------------------------------------------------

||| Find the zero-based index of an element in ascending order.
||| Returns Nothing if the element does not exist. O(log m + log n)
export
lookupIndex :  Ord a
            => a
            -> Set1 s a
            -> F1 s (Maybe Nat)
lookupIndex x =
  querySet (Data.Set.lookupIndex x)

||| Find the zero-based index of an element in ascending order.
||| Calls idris_crash if the element does not exist. O(log m + log n)
export
findIndex :  Ord a
          => a
          -> Set1 s a
          -> F1 s Nat
findIndex x =
  querySet (Data.Set.findIndex x)

||| Retrieve an element at its zero-based index in ascending order.
||| Calls idris_crash if the index is out of bounds. O(log m + log n)
export
elemAt :  Nat
       -> Set1 s a
       -> F1 s a
elemAt i =
  querySet (Data.Set.elemAt i)

||| Atomically delete an element at its zero-based index.
||| Calls idris_crash if the index is out of bounds. O(log m + log n)
export
deleteAt :  Nat
         -> Set1 s a
         -> F1' s
deleteAt i =
  modifySet (Data.Set.deleteAt i)

--------------------------------------------------------------------------------
--          Min/Max
--------------------------------------------------------------------------------

||| Retrieve the smallest element in a Set1.
||| Returns Nothing if the set is empty. O(log m + log n)
export
lookupMin :  Set1 s a
          -> F1 s (Maybe a)
lookupMin =
  querySet Data.Set.lookupMin

||| Retrieve the largest element in a Set1.
||| Returns Nothing if the set is empty. O(log m + log n)
export
lookupMax :  Set1 s a
          -> F1 s (Maybe a)
lookupMax =
  querySet Data.Set.lookupMax

||| Retrieve the smallest element in a Set1.
||| Calls idris_crash if the set is empty. O(log m + log n)
export
findMin :  Set1 s a
        -> F1 s a
findMin =
  querySet Data.Set.findMin

||| Retrieve the largest element in a Set1.
||| Calls idris_crash if the set is empty. O(log m + log n)
export
findMax :  Set1 s a
        -> F1 s a
findMax =
  querySet Data.Set.findMax

--------------------------------------------------------------------------------
--          Views
--------------------------------------------------------------------------------

||| Atomically retrieve and remove the smallest element from a Set1.
||| Returns Nothing if the set is empty. O(log m + log n)
export
minView :  Set1 s a
        -> F1 s (Maybe a)
minView =
  updateSet
    (\set =>
      case Data.Set.minView set of
        Nothing        => (set, Nothing)
        Just (x, set') => (set', Just x)
    )

||| Atomically retrieve and remove the largest element from a Set1.
||| Returns Nothing if the set is empty. O(log m + log n)
export
maxView :  Set1 s a
        -> F1 s (Maybe a)
maxView =
  updateSet
    (\set =>
      case Data.Set.maxView set of
        Nothing        => (set, Nothing)
        Just (x, set') => (set', Just x)
    )

||| Atomically retrieve and remove the smallest element from a Set1.
||| Calls idris_crash if the set is empty. O(log m + log n)
export
deleteFindMin :  Set1 s a
              -> F1 s a
deleteFindMin =
  updateSet
    (\set =>
      let (x, set') = Data.Set.deleteFindMin set
        in (set', x)
    )

||| Atomically retrieve and remove the largest element from a Set1.
||| Calls idris_crash if the set is empty. O(log m + log n)
export
deleteFindMax :  Set1 s a
              -> F1 s a
deleteFindMax =
  updateSet
    (\set =>
      let (x, set') = Data.Set.deleteFindMax set
        in (set', x)
    )

--------------------------------------------------------------------------------
--          Combine
--------------------------------------------------------------------------------

||| Atomically insert all elements of the second Set1 into the first.
||| The union is left-biased, preserving elements from the first set
||| when equivalent elements exist in both sets.
|||
||| Both handles must belong to the same store.
||| Both sets are read from the same atomic snapshot.
||| The second set is not modified.
export
union :  Eq (Set a)
      => Eq a
      => Ord a
      => Set1 s a
      -> Set1 s a
      -> F1' s
union =
  modifySets Data.Set.union

||| Atomically remove all elements of the second Set1 from the first.
|||
||| Both handles must belong to the same store.
||| Both sets are read from the same atomic snapshot.
||| The second set is not modified.
export
difference :  Ord a
           => Set1 s a
           -> Set1 s a
           -> F1' s
difference =
  modifySets Data.Set.difference

||| Atomically retain elements of the first Set1 that also exist
||| in the second Set1.
|||
||| Both handles must belong to the same store.
||| Both sets are read from the same atomic snapshot.
||| The second set is not modified.
export
intersection :  Eq (Set a)
             => Ord a
             => Set1 s a
             -> Set1 s a
             -> F1' s
intersection =
  modifySets Data.Set.intersection

--------------------------------------------------------------------------------
--          Set Relations
--------------------------------------------------------------------------------

||| Check whether every element of the first Set1 exists in the second.
|||
||| Both handles must belong to the same store.
||| Both sets are observed through one atomic snapshot.
export
isSubsetOf :  Ord a
           => Set1 s a
           -> Set1 s a
           -> F1 s Bool
isSubsetOf =
  querySets Data.Set.isSubsetOf

||| Check whether the first Set1 is a proper subset of the second.
||| A proper subset contains strictly fewer elements.
|||
||| Both handles must belong to the same store.
||| Both sets are observed through one atomic snapshot.
export
isProperSubsetOf :  Ord a
                 => Set1 s a
                 -> Set1 s a
                 -> F1 s Bool
isProperSubsetOf =
  querySets
    (\set1, set2 =>
      Data.Set.Internal.size set1 < Data.Set.Internal.size set2
        && Data.Set.isSubsetOf set1 set2
    )

||| Check whether two Set1 values contain no common elements.
|||
||| Both handles must belong to the same store.
||| Both sets are observed through one atomic snapshot.
export
disjoint :  Ord a
         => Set1 s a
         -> Set1 s a
         -> F1 s Bool
disjoint =
  querySets Data.Set.disjoint

--------------------------------------------------------------------------------
--          Filter
--------------------------------------------------------------------------------

||| Atomically retain only elements satisfying the given predicate.
||| The existing Set1 is updated. O(m + log n)
export
filter :  Eq (Set a)
       => (a -> Bool)
       -> Set1 s a
       -> F1' s
filter p =
  modifySet (Data.Set.filter p)

||| Atomically retain only the first n elements in ascending order.
||| O(log m + log n)
export
take :  Nat
     -> Set1 s a
     -> F1' s
take n =
  modifySet (Data.Set.take n)

||| Atomically remove the first n elements in ascending order.
||| O(log m + log n)
export
drop :  Nat
     -> Set1 s a
     -> F1' s
drop n =
  modifySet (Data.Set.drop n)

||| Atomically retain the initial elements satisfying an antitone
||| predicate. The predicate must hold for an initial segment
||| of the elements in ascending order. O(log m + log n)
export
takeWhileAntitone :  (a -> Bool)
                  -> Set1 s a
                  -> F1' s
takeWhileAntitone p =
  modifySet (Data.Set.takeWhileAntitone p)

||| Atomically remove the initial elements satisfying an antitone
||| predicate. The predicate must hold for an initial segment
||| of the elements in ascending order. O(log m + log n)
export
dropWhileAntitone :  (a -> Bool)
                  -> Set1 s a
                  -> F1' s
dropWhileAntitone p =
  modifySet (Data.Set.dropWhileAntitone p)

--------------------------------------------------------------------------------
--          Folds
--------------------------------------------------------------------------------

||| Fold the elements of a Set1 using a left-associative
||| binary operator in ascending order. O(m + log n)
export
foldl :  (b -> a -> b)
      -> b
      -> Set1 s a
      -> F1 s b
foldl f z =
  querySet (Data.Set.foldl f z)

||| Fold the elements of a Set1 using a right-associative
||| binary operator in ascending order. O(m + log n)
export
foldr :  (a -> b -> b)
      -> b
      -> Set1 s a
      -> F1 s b
foldr f z =
  querySet (Data.Set.foldr f z)

--------------------------------------------------------------------------------
--          Creating a List from a Set1
--------------------------------------------------------------------------------

||| Convert a Set1 to a list of elements in ascending order.
||| O(m + log n)
export
toAscList :  Set1 s a
          -> F1 s (List a)
toAscList =
  querySet Data.Set.toAscList

||| Convert a Set1 to a list of elements in descending order.
||| O(m + log n)
export
toDescList :  Set1 s a
           -> F1 s (List a)
toDescList =
  querySet Data.Set.toDescList

||| Convert a Set1 to a list of elements in ascending order.
||| O(m + log n)
export
toList :  Set1 s a
       -> F1 s (List a)
toList =
  querySet Data.Set.toList

--------------------------------------------------------------------------------
--          Map
--------------------------------------------------------------------------------

||| Map a function over the elements of a Set1, creating a new Set1.
|||
||| The resulting set is rebuilt to preserve its ordering invariant.
||| Duplicate results are removed.
||| The new set is allocated atomically in the destination store.
||| The original Set1 is not modified.
export
map :  Ord b
    => SetStore1 s b
    -> (a -> b)
    -> Set1 s a
    -> F1 s (Set1 s b)
map store f set t =
  let values # t := querySet Data.Set.toList set t
      mapped     := Data.Set.fromList (Prelude.map f values)
    in fromSet store mapped t

--------------------------------------------------------------------------------
--          Transfer
--------------------------------------------------------------------------------

||| Atomically transfer an element from the first Set1 to the second.
|||
||| Both handles must belong to the same store.
||| Returns True if the element was transferred.
||| Returns False if the element does not exist in the source,
||| or if both handles identify the same set.
|||
||| Both modifications are committed through a single CAS.
export
transfer :  Ord a
         => a
         -> Set1 s a
         -> Set1 s a
         -> F1 s Bool
transfer x =
  updateSets
    (\source, destination =>
      case Data.Set.member x source of
        True  =>
          ( Data.Set.delete x source
          , Data.Set.insert x destination
          , True
          )
        False =>
          ( source
          , destination
          , False
          )
    )
