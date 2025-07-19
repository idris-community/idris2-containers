||| Least Recently Used (LRU) Cache
module Data.LRUCache

import public Data.HashPSQ
import public Data.LRUCache.Internal

import Data.List
import Data.Hashable
import Data.Maybe
import Data.Zippable

%default total

--------------------------------------------------------------------------------
--          Construction
--------------------------------------------------------------------------------

||| Create an empty LRUCache of the given size.
export
empty :  Nat
      -> LRUCache k v
empty capacity =
  case capacity < 1 of
    True  =>
      assert_total $ idris_crash "Data.LRUCache.empty: capacity < 1"
    False =>
      MkLRUCache capacity
                 0
                 0
                 empty

--------------------------------------------------------------------------------
--          Insertion
--------------------------------------------------------------------------------

private
compress :  List (k, Priority, v)
         -> List (k, Priority, v)
compress q =
  let sortedq = sortBy compareByPriority q
    in zipWith (\(k, _, v), p => (k, p, v))
               sortedq
               [1..(length sortedq)]
  where
    compareByPriority :  (k, Priority, v)
                      -> (k, Priority, v)
                      -> Ordering
    compareByPriority (_, p, _) (_, p', _) =
      compare p p'

||| Restore LRUCache invariants.
||| For performance reasons this is not snd . trim'.
private
trim :  Hashable k
     => Ord k
     => LRUCache k v
     -> LRUCache k v
trim cache@(MkLRUCache c s t q) =
  case s > c of
    True  =>
      MkLRUCache c
                 (s `minus` 1)
                 t
                 (deleteMin q)
    False =>
      cache

||| Insert an element into the LRUCache.
export
insert :  Hashable k
       => Ord k
       => k
       -> v
       -> LRUCache k v
       -> LRUCache k v
insert key val (MkLRUCache c s t q) =
  let (mboldval, queue) = HashPSQ.insertView key t val q
    in case isNothing mboldval of
         True  =>
           trim $
             MkLRUCache c
                        (s `plus` 1)
                        (t `plus` 1)
                        queue
         False =>
           trim $
             MkLRUCache c
                        s
                        (t `plus` 1)
                        queue

--------------------------------------------------------------------------------
--          Views
--------------------------------------------------------------------------------

||| Restore LRUCache invariants returning the evicted element if any.
private
trim' :  Hashable k
      => Ord k
      => LRUCache k v
      -> (Maybe (k, v), LRUCache k v)
trim' cache@(MkLRUCache c s t q) =
  case s > c of
    True  =>
      case HashPSQ.findMin q of
        Nothing        =>
          assert_total $ idris_crash "Data.LRUCache.trim': internal error"
        Just (k, _, v) =>
          let c' = MkLRUCache c
                              (s `minus` 1)
                              t
                              (HashPSQ.deleteMin q)
            in (Just (k, v), c')
    False =>
      (Nothing, cache)

||| Insert an element into the LRUCache returning the evicted element if any.
||| When the logical clock reaches its maximum value and all values are
||| evicted Nothing is returned.
export
insertView :  Hashable k
           => Ord k
           => k
           -> v
           -> LRUCache k v
           -> (Maybe (k, v), LRUCache k v)
insertView key val (MkLRUCache c s t q) =
  let (mboldval, queue) = HashPSQ.insertView key t val q
    in case isNothing mboldval of
         True  =>
           trim' $
             MkLRUCache c
                        (s `plus` 1)
                        (t `plus` 1)
                        queue
         False =>
            trim' $
              MkLRUCache c
                         s
                         (t `plus` 1)
                         queue

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Lookup an element in an LRUCache and mark it as the least recently accessed.
export
lookup :  Hashable k
       => Ord k
       => k
       -> LRUCache k v
       -> Maybe (v, LRUCache k v)
lookup k cache@(MkLRUCache c s t q) =
  case HashPSQ.alter lookupAndBump k q of
    (Nothing, _) =>
      Nothing
    (Just x, q)  =>
      let c' = trim $
                 MkLRUCache c
                            s
                            (t `plus` 1)
                            q
        in Just (x, c')
  where
    lookupAndBump :  Maybe (a, b)
                  -> (Maybe b, Maybe (Priority, b))
    lookupAndBump Nothing       =
      (Nothing, Nothing)
    lookupAndBump (Just (_, x)) =
      (Just x, Just (t, x))
