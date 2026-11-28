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
--          Construction
--------------------------------------------------------------------------------

||| Create an empty shared atomic set store. O(1)
export
newStore : F1 s (SetStore1 s a)
newStore = Data.Set1.Internal.newStore

||| Allocate a new set from an immutable value, using one CAS.
||| Returns a handle with a unique store-local identifier. O(log n)
export
fromSet :  SetStore1 s a
          -> Set a
          -> F1 s (Set1 s a)
fromSet = Data.Set1.Internal.allocateSet

||| Allocate an empty set in an existing store. O(log n)
export
empty :  SetStore1 s a
      -> F1 s (Set1 s a)
empty store t = fromSet store Data.Set.empty t

||| Allocate a singleton set in an existing store. O(log n)
export
singleton :  a -> SetStore1 s a -> F1 s (Set1 s a)
singleton x store t =
  fromSet store (Data.Set.Internal.singleton x) t

||| Allocate a set from a list, removing duplicates. O(m log m + log n)
export
fromList :  Ord a
         => List a
         -> SetStore1 s a
         -> F1 s (Set1 s a)
fromList xs store t = fromSet store (Data.Set.fromList xs) t

--------------------------------------------------------------------------------
--          Conversion
--------------------------------------------------------------------------------

||| Return an immutable snapshot; Nothing indicates an invalid handle.
export
freeze :  Set1 s a -> F1 s (Maybe (Set a))
freeze = querySet id

--------------------------------------------------------------------------------
--          Insertion
--------------------------------------------------------------------------------

||| Atomically insert an element; False means invalid handle.
export
insert :  Ord a => a -> Set1 s a -> F1 s Bool
insert =
  \x => modifySet (Data.Set.insert x)

--------------------------------------------------------------------------------
--          Deletion
--------------------------------------------------------------------------------

||| Atomically delete an element; False means invalid handle.
export
delete :  Ord a => a -> Set1 s a -> F1 s Bool
delete =
  \x => modifySet (Data.Set.delete x)

||| Atomically remove the minimum; empty sets remain unchanged.
export
deleteMin :  Set1 s a -> F1 s Bool
deleteMin =
  modifySet Data.Set.deleteMin

||| Atomically remove the maximum; empty sets remain unchanged.
export
deleteMax :  Set1 s a -> F1 s Bool
deleteMax =
  modifySet Data.Set.deleteMax

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Test membership; Nothing means invalid handle.
export
member :  Ord a => a -> Set1 s a -> F1 s (Maybe Bool)
member =
  \x => querySet (Data.Set.member x)

||| Test non-membership; Nothing means invalid handle.
export
notMember :  Ord a => a -> Set1 s a -> F1 s (Maybe Bool)
notMember =
  \x => querySet (Data.Set.notMember x)

||| Test emptiness; Nothing means invalid handle.
export
null :  Set1 s a -> F1 s (Maybe Bool)
null =
  querySet Data.Set.null

||| Get the number of elements; Nothing means invalid handle.
export
size :  Set1 s a -> F1 s (Maybe Nat)
size =
  querySet Data.Set.Internal.size

||| Find the lower strict neighbor; Nothing indicates an invalid handle.
export
lookupLT :  Ord a => a -> Set1 s a -> F1 s (Maybe (Maybe a))
lookupLT =
  \x => querySet (Data.Set.lookupLT x)

||| Find the upper strict neighbor; Nothing indicates an invalid handle.
export
lookupGT :  Ord a => a -> Set1 s a -> F1 s (Maybe (Maybe a))
lookupGT =
  \x => querySet (Data.Set.lookupGT x)

||| Find the lower inclusive neighbor; Nothing indicates invalid handle.
export
lookupLE :  Ord a => a -> Set1 s a -> F1 s (Maybe (Maybe a))
lookupLE =
  \x => querySet (Data.Set.lookupLE x)

||| Find the upper inclusive neighbor; Nothing indicates invalid handle.
export
lookupGE :  Ord a => a -> Set1 s a -> F1 s (Maybe (Maybe a))
lookupGE =
  \x => querySet (Data.Set.lookupGE x)

--------------------------------------------------------------------------------
--          Indexed
--------------------------------------------------------------------------------

||| Find the index of an element; nested Maybe distinguishes invalid handles.
export
lookupIndex :  Ord a => a -> Set1 s a -> F1 s (Maybe (Maybe Nat))
lookupIndex =
  \x => querySet (Data.Set.lookupIndex x)

||| Total alternative to immutable findIndex; missing elements return Nothing.
export
findIndex :  Ord a => a -> Set1 s a -> F1 s (Maybe (Maybe Nat))
findIndex =
  \x => querySet (Data.Set.lookupIndex x)

||| Safely index a list without partial functions.
private
atList : Nat -> List a -> Maybe a
atList Z (x :: xs) = Just x
atList (S k) (_ :: xs) = atList k xs
atList _ [] = Nothing


||| Retrieve the indexed element safely; outer Nothing means invalid handle.
export
elemAt :  Nat -> Set1 s a -> F1 s (Maybe (Maybe a))
elemAt =
  \i => querySet (atList i . Data.Set.toAscList)

||| Delete the indexed element if it exists, in a single CAS.
||| Returns Nothing for invalid handles and Just False for bad indices.
export
deleteAt : Nat -> Set1 s a -> F1 s (Maybe Bool)
deleteAt i =
  updateSet (\set =>
    case atList i (Data.Set.toAscList set) of
      Nothing => (set, False)
      Just x  => (Data.Set.deleteAt i set, True))

--------------------------------------------------------------------------------
--          Min/Max
--------------------------------------------------------------------------------

||| Return the smallest element; nested Maybe distinguishes empty sets.
export
lookupMin :  Set1 s a -> F1 s (Maybe (Maybe a))
lookupMin =
  querySet Data.Set.lookupMin

||| Return the largest element; nested Maybe distinguishes empty sets.
export
lookupMax :  Set1 s a -> F1 s (Maybe (Maybe a))
lookupMax =
  querySet Data.Set.lookupMax

||| Total findMin alternative; returns Nothing for an empty set.
export
findMin :  Set1 s a -> F1 s (Maybe (Maybe a))
findMin =
  querySet Data.Set.lookupMin

||| Total findMax alternative; returns Nothing for an empty set.
export
findMax :  Set1 s a -> F1 s (Maybe (Maybe a))
findMax =
  querySet Data.Set.lookupMax

--------------------------------------------------------------------------------
--          Views
--------------------------------------------------------------------------------

||| Atomically remove and return the smallest element.
||| Outer Nothing means invalid handle; inner Nothing means empty set.
export
minView : Set1 s a -> F1 s (Maybe (Maybe a))
minView =
  updateSet (\set =>
    case Data.Set.minView set of
      Nothing        => (set, Nothing)
      Just (x, set') => (set', Just x))

||| Atomically remove and return the largest element.
||| Outer Nothing means invalid handle; inner Nothing means empty set.
export
maxView : Set1 s a -> F1 s (Maybe (Maybe a))
maxView =
  updateSet (\set =>
    case Data.Set.maxView set of
      Nothing        => (set, Nothing)
      Just (x, set') => (set', Just x))

||| Total deleteFindMin: remove and return an endpoint, if present.
export
deleteFindMin :  Set1 s a -> F1 s (Maybe (Maybe a))
deleteFindMin =
  minView

||| Total deleteFindMax: remove and return an endpoint, if present.
export
deleteFindMax :  Set1 s a -> F1 s (Maybe (Maybe a))
deleteFindMax =
  maxView

--------------------------------------------------------------------------------
--          Combine
--------------------------------------------------------------------------------

||| Atomically compute union within one store; False means invalid handle.
export
union :  Eq (Set a) => Eq a => Ord a => Set1 s a -> Set1 s a -> F1 s Bool
union =
  modifySets Data.Set.union

||| Atomically compute difference within one store; False means invalid handle.
export
difference :  Ord a => Set1 s a -> Set1 s a -> F1 s Bool
difference =
  modifySets Data.Set.difference

||| Atomically intersect two sets in one store.
export
intersection :  Eq (Set a) => Ord a => Set1 s a -> Set1 s a -> F1 s Bool
intersection =
  modifySets Data.Set.intersection

--------------------------------------------------------------------------------
--          Set Relations
--------------------------------------------------------------------------------

||| Compare two sets in one snapshot; Nothing means invalid handle.
export
isSubsetOf :  Ord a => Set1 s a -> Set1 s a -> F1 s (Maybe Bool)
isSubsetOf =
  querySets Data.Set.isSubsetOf

||| Compare two sets in one snapshot; Nothing means invalid handle.
export
disjoint :  Ord a => Set1 s a -> Set1 s a -> F1 s (Maybe Bool)
disjoint =
  querySets Data.Set.disjoint

||| Test strict subsethood using a consistent two-set snapshot.
||| Nothing means an invalid handle.
export
isProperSubsetOf : Ord a
                 => Set1 s a
                 -> Set1 s a
                 -> F1 s (Maybe Bool)
isProperSubsetOf =
  querySets (\xs, ys =>
    Data.Set.Internal.size xs < Data.Set.Internal.size ys &&
      Data.Set.isSubsetOf xs ys)

--------------------------------------------------------------------------------
--          Filter
--------------------------------------------------------------------------------

||| Atomically apply filter; False means invalid handle.
export
filter :  Eq (Set a) => (a -> Bool) -> Set1 s a -> F1 s Bool
filter =
  \p => modifySet (Data.Set.filter p)

||| Atomically apply take; False means invalid handle.
export
take :  Nat -> Set1 s a -> F1 s Bool
take =
  \n => modifySet (Data.Set.take n)

||| Atomically apply drop; False means invalid handle.
export
drop :  Nat -> Set1 s a -> F1 s Bool
drop =
  \n => modifySet (Data.Set.drop n)

||| Atomically apply takeWhileAntitone; False means invalid handle.
export
takeWhileAntitone :  (a -> Bool) -> Set1 s a -> F1 s Bool
takeWhileAntitone =
  \p => modifySet (Data.Set.takeWhileAntitone p)

||| Atomically apply dropWhileAntitone; False means invalid handle.
export
dropWhileAntitone :  (a -> Bool) -> Set1 s a -> F1 s Bool
dropWhileAntitone =
  \p => modifySet (Data.Set.dropWhileAntitone p)

--------------------------------------------------------------------------------
--          Folds
--------------------------------------------------------------------------------

||| Fold elements via foldl; Nothing means invalid handle.
export
foldl :  (b -> a -> b) -> b -> Set1 s a -> F1 s (Maybe b)
foldl =
  \f => \z => querySet (Data.Set.foldl f z)

||| Fold elements via foldr; Nothing means invalid handle.
export
foldr :  (a -> b -> b) -> b -> Set1 s a -> F1 s (Maybe b)
foldr =
  \f => \z => querySet (Data.Set.foldr f z)

--------------------------------------------------------------------------------
--          Lists
--------------------------------------------------------------------------------

||| Convert to toAscList; Nothing means invalid handle.
export
toAscList :  Set1 s a -> F1 s (Maybe (List a))
toAscList =
  querySet Data.Set.toAscList

||| Convert to toDescList; Nothing means invalid handle.
export
toDescList :  Set1 s a -> F1 s (Maybe (List a))
toDescList =
  querySet Data.Set.toDescList

||| Convert to toList; Nothing means invalid handle.
export
toList :  Set1 s a -> F1 s (Maybe (List a))
toList =
  querySet Data.Set.toList

--------------------------------------------------------------------------------
--          Map
--------------------------------------------------------------------------------

||| Rebuild mapped elements in a destination store.
||| Returns Nothing for invalid source handles; source is not mutated.
||| Reading the source and allocating the result are separate steps.
export
map :  Ord b
    => SetStore1 s b
    -> (a -> b)
    -> Set1 s a
    -> F1 s (Maybe (Set1 s b))
map store f source t =
  let original # t := querySet id source t
    in case original of
         Nothing => Nothing # t
         Just xs =>
           let mapped = Data.Set.fromList
                          (Prelude.map f (Data.Set.toList xs))
               result # t := fromSet store mapped t
             in Just result # t

--------------------------------------------------------------------------------
--          Transfer
--------------------------------------------------------------------------------

||| Atomically transfer an element between distinct sets in one store.
||| Nothing means invalid handles or identical source/destination IDs.
||| Just False means the element was absent; Just True means transferred.
export
transfer : Ord a
        => a
        -> Set1 s a
        -> Set1 s a
        -> F1 s (Maybe Bool)
transfer x =
  updateSets (\source, destination =>
    if Data.Set.member x source
      then ( Data.Set.delete x source
           , Data.Set.insert x destination
           , True
           )
      else (source, destination, False))
