||| Linear Least Recently Used (LRU) Cache
module Data.LRUCache1

import public Data.HashPSQ
import public Data.LRUCache.Internal
import public Data.LRUCache1.Internal

import Data.List
import Data.Hashable
import Data.Maybe
import Data.So
import Data.Zippable
import Data.Linear.Ref1

%default total

--------------------------------------------------------------------------------
--          Construction
--------------------------------------------------------------------------------

||| Create an empty LRUCache1 of the given size.
export
empty :  (capacity : Nat)
      -> F1 s (LRUCache1 s k v)
empty capacity t =
  let lrucache # t := ref1 ( MkLRUCache capacity
                                        0
                                        0
                                        Data.HashPSQ.empty
                           ) t
    in (MkLRUCache1 lrucache) # t

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

||| Insert an element into the LRUCache1.
export
insert :  Hashable k
       => Ord k
       => k
       -> v
       -> LRUCache1 s k v
       -> F1 s (LRUCache1 s k v)
insert key val (MkLRUCache1 cache) t =
  casupdate1 cache
    (\(MkLRUCache c s tc q) =>
      let (mboldval, queue) := HashPSQ.insertView key tc val q
          s1                := case isNothing mboldval of
                                 True  => s `plus` 1
                                 False => s
          cache1            := MkLRUCache c s1 (tc `plus` 1) queue
        in case s1 > c of
             True  =>
               ( MkLRUCache c (s1 `minus` 1) (tc `plus` 1) (deleteMin queue)
               , MkLRUCache1 cache
               )
             False =>
               ( cache1
               , MkLRUCache1 cache
               )
    ) t

--------------------------------------------------------------------------------
--          Views
--------------------------------------------------------------------------------

||| Insert an element into the LRUCache1 returning the evicted element if any.
||| When the logical clock reaches its maximum value and all values are
||| evicted Nothing is returned.
export
insertView :  Hashable k
           => Ord k
           => k
           -> v
           -> LRUCache1 s k v
           -> F1 s (Maybe (k, v), LRUCache1 s k v)
insertView key val (MkLRUCache1 cache) t =
  casupdate1 cache
    (\(MkLRUCache c s tc q) =>
     let (mboldval, queue) := HashPSQ.insertView key tc val q
         s1                := case isNothing mboldval of
                                True  => s `plus` 1
                                False => s
       in case s1 > c of
            True =>
              case HashPSQ.findMin queue of
                Nothing =>
                  (assert_total $ idris_crash "Data.LRUCache1.insertView: internal error")
                Just (k, _, v) =>
                  ( MkLRUCache c (s1 `minus` 1) (tc `plus` 1) (deleteMin queue)
                  , (Just (k, v), MkLRUCache1 cache)
                  )
            False =>
              ( MkLRUCache c s1 (tc `plus` 1) queue
              , (Nothing, MkLRUCache1 cache)
              )
    ) t

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Lookup an element in an LRUCache1 and mark it as the least recently accessed.
export
lookup :  Hashable k
       => Ord k
       => k
       -> LRUCache1 s k v
       -> F1 s (Maybe (v, LRUCache1 s k v))
lookup k (MkLRUCache1 cache) t =
  casupdate1 cache
    (\(MkLRUCache c s tc q) =>
      case HashPSQ.alter (\x =>
                             case x of
                               Nothing        =>
                                 (Nothing, Nothing)
                               Just (_, x')   =>
                                 (Just x', Just (tc, x'))
                         ) k q of
        (Nothing, _)    =>
          ( MkLRUCache c s tc q
          , Nothing
          )
        (Just x, queue) =>
          let tc1 = tc `plus` 1
            in case s > c of
                 True  =>
                   ( MkLRUCache c (s `minus` 1) tc1 (deleteMin queue)
                   , Just (x, MkLRUCache1 cache)
                   )
                 False =>
                   ( MkLRUCache c s tc1 queue
                   , Just (x, MkLRUCache1 cache)
                   )
    ) t

--------------------------------------------------------------------------------
--          Creating a List from a LRUCache1
--------------------------------------------------------------------------------

||| Convert an LRUCache1 to a list of (key, value) pairs.
export
toList :  Hashable k
       => Ord k
       => LRUCache1 s k v
       -> F1 s (List (k, v))
toList (MkLRUCache1 cache) t =
  let (MkLRUCache _ _ _ q) # t := read1 cache t
      lst                      := map (\(k, _, v) => (k, v)) (HashPSQ.toList q)
    in lst # t
