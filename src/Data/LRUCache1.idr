||| Linear Least Recently Used (LRU) Cache
module Data.LRUCache1

import public Data.HashPSQ
import public Data.LRUCache1.Internal

import Data.List
import Data.Hashable
import Data.Maybe
import Data.So
import Data.Zippable
import Data.Linear.Ref1
import Data.Linear.Token

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
  let capacity # t := ref1 capacity t
      size     # t := ref1 0 t
      tick     # t := ref1 0 t
      queue    # t := ref1 Data.HashPSQ.empty t
    in ( MkLRUCache1 capacity
                     size
                     tick
                     queue
       ) # t

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
trim cache@(MkLRUCache1 c s _ q) t =
  let c' # t := read1 c t
      s' # t := read1 s t
    in case s' > c' of
         True  =>
           let () # t := casmod1 s (`minus` 1) t
               () # t := casmod1 q deleteMin t
             in cache # t
         False =>
           cache # t

||| Insert an element into the LRUCache1.
export
insert :  Hashable k
       => Ord k
       => k
       -> v
       -> LRUCache1 s k v
       -> F1 s (LRUCache1 s k v)
insert key val cache@(MkLRUCache1 c s tc q) t =
  let tc'           # t := read1 tc t
      q'            # t := read1 q t
      (mboldval, queue) := HashPSQ.insertView key tc' val q'
    in case isNothing mboldval of
         True  =>
           let ()     # t := casmod1 s (`plus` 1) t
               ()     # t := casmod1 tc (`plus` 1) t
               queue' # t := ref1 queue t
               cache'     := MkLRUCache1 c s tc queue'
             in trim cache' t
         False =>
           let ()     # t := casmod1 tc (`plus` 1) t
               queue' # t := ref1 queue t
               cache'     := MkLRUCache1 c s tc queue'
             in trim cache' t

--------------------------------------------------------------------------------
--          Views
--------------------------------------------------------------------------------

||| Restore LRUCache1 invariants returning the evicted element if any.
private
trim' :  Hashable k
      => Ord k
      => LRUCache1 s k v
      -> F1 s (Maybe (k, v), LRUCache1 s k v)
trim' cache@(MkLRUCache1 c s _ q) t =
  let c' # t := read1 c t
      s' # t := read1 s t
      q' # t := read1 q t
    in case s' > c' of
         True  =>
           case HashPSQ.findMin q' of
             Nothing        =>
               (assert_total $ idris_crash "Data.LRUCache1.trim': internal error") # t
             Just (k, _, v) =>
               let () # t := casmod1 s (`minus` 1) t
                   () # t := casmod1 q deleteMin t
                 in (Just (k, v), cache) # t
         False =>
           (Nothing, cache) # t

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
insertView key val (MkLRUCache1 c s tc q) t =
  let tc'           # t := read1 tc t
      q'            # t := read1 q t
      (mboldval, queue) := HashPSQ.insertView key tc' val q'
    in case isNothing mboldval of
         True  =>
           let ()     # t := casmod1 s (`plus` 1) t
               ()     # t := casmod1 tc (`plus` 1) t
               queue' # t := ref1 queue t
               cache'     := MkLRUCache1 c s tc queue'
             in trim' cache' t
         False =>
           let ()     # t := casmod1 tc (`plus` 1) t
               queue' # t := ref1 queue t
               cache'     := MkLRUCache1 c s tc queue'
             in trim' cache' t

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
lookup k cache@(MkLRUCache1 c s tc q) t =
  let tc'   # t := read1 tc t
      q'    # t := read1 q t
    in case HashPSQ.alter (\x =>
                              case x of
                                Nothing        =>
                                  (Nothing, Nothing)
                                (Just (_, x')) =>
                                  (Just x', Just (tc', x'))
                          ) k q' of
         (Nothing, _)    =>
           Nothing # t
         (Just x, queue) =>
           let ()           # t := casmod1 tc (`plus` 1) t
               queue'       # t := ref1 queue t
               cache'           := MkLRUCache1 c s tc queue'
               trimmedcache # t := trim cache' t
             in (Just (x, trimmedcache)) # t
