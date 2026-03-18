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
      -> {0 prfcapacity : So (capacity >= 0)}
      -> F1 s (LRUCache1 s k v)
empty capacity {prfcapacity} t =
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

||| Restore LRUCache1 invariants.
||| For performance reasons this is not snd . trim'.
private
trim :  Hashable k
     => Ord k
     => LRUCache1 s k v
     -> F1 s (LRUCache1 s k v)
trim (MkLRUCache1 cache) t =
  let (MkLRUCache c s tc q) # t := read1 cache t
    in case s > c of
         True  =>
           let () # t := casswap1 cache (MkLRUCache c (s `minus` 1) tc (deleteMin q)) t
             in (MkLRUCache1 cache) # t
         False =>
           (MkLRUCache1 cache) # t

||| Insert an element into the LRUCache1.
export
insert :  Hashable k
       => Ord k
       => k
       -> v
       -> LRUCache1 s k v
       -> F1 s (LRUCache1 s k v)
insert key val (MkLRUCache1 cache) t =
  let (MkLRUCache c s tc q) # t := read1 cache t
      (mboldval, queue)         := HashPSQ.insertView key tc val q
    in case isNothing mboldval of
         True  =>
           let () # t := casswap1 cache (MkLRUCache c (s `plus` 1) (tc `plus` 1) queue) t
             in trim (MkLRUCache1 cache) t
         False =>
           let () # t := casswap1 cache (MkLRUCache c s (tc `plus` 1) queue) t
             in trim (MkLRUCache1 cache) t

--------------------------------------------------------------------------------
--          Views
--------------------------------------------------------------------------------

||| Restore LRUCache1 invariants returning the evicted element if any.
private
trim' :  Hashable k
      => Ord k
      => LRUCache1 s k v
      -> F1 s (Maybe (k, v), LRUCache1 s k v)
trim' (MkLRUCache1 cache) t =
  let (MkLRUCache c s tc q) # t := read1 cache t
    in case s > c of
         True  =>
           case HashPSQ.findMin q of
             Nothing        =>
               (assert_total $ idris_crash "Data.LRUCache1.trim': internal error") # t
             Just (k, _, v) =>
               let () # t := casswap1 cache (MkLRUCache c (s `minus` 1) tc (deleteMin q)) t
                 in (Just (k, v), (MkLRUCache1 cache)) # t
         False =>
           (Nothing, (MkLRUCache1 cache)) # t

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
  let (MkLRUCache c s tc q) # t := read1 cache t
      (mboldval, queue)         := HashPSQ.insertView key tc val q
    in case isNothing mboldval of
         True  =>
           let () # t := casswap1 cache (MkLRUCache c (s `plus` 1) (tc `plus` 1) queue) t
             in trim' (MkLRUCache1 cache) t
         False =>
           let () # t := casswap1 cache (MkLRUCache c s (tc `plus` 1) queue) t
             in trim' (MkLRUCache1 cache) t

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
  let (MkLRUCache c s tc q) # t := read1 cache t
    in case HashPSQ.alter (\x =>
                              case x of
                                Nothing        =>
                                  (Nothing, Nothing)
                                (Just (_, x')) =>
                                  (Just x', Just (tc, x'))
                          ) k q of
         (Nothing, _)    =>
           Nothing # t
         (Just x, queue) =>
           let ()           # t := casswap1 cache (MkLRUCache c s (tc `plus` 1) queue) t
               trimmedcache # t := trim (MkLRUCache1 cache) t
             in (Just (x, trimmedcache)) # t
