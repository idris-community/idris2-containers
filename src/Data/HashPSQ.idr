||| Hash Priority Search Queue
module Data.HashPSQ

import public Data.HashPSQ.Internal
import public Data.NatPSQ
import public Data.NatPSQ.Internal
import public Data.OrdPSQ

import Data.List
import Data.Hashable
import Data.Maybe

%default total

--------------------------------------------------------------------------------
--          Insertion
--------------------------------------------------------------------------------

private
ins :  Eq k
    => Ord k
    => Ord p
    => k
    -> p
    -> v
    -> Maybe (p, Bucket k p v)
    -> Maybe (p, Bucket k p v)
ins k p v Nothing                        =
  Just (p, MkBucket k v (OrdPSQ.empty))
ins k p v (Just (p', MkBucket k' v' os)) =
  case k' == k of
    True  =>
      -- Tricky: p might have less priority than an item in os.
      Just (mkBucket k p v os)
    False =>
      case p' < p || (p == p' && k' < k) of
        True  =>
          Just (p', MkBucket k' v' (OrdPSQ.insert k p v os))
        False =>
          case OrdPSQ.member k os of
            True  =>
              -- This is a bit tricky: k might already be present in 'os' and we
              -- don't want to end up with duplicate keys.
              Just (p, MkBucket k v (OrdPSQ.insert k' p' v' (OrdPSQ.delete k os)))
            False =>
              Just (p, MkBucket k v (OrdPSQ.insert k' p' v' os))

||| Insert a new key, priority and value into the queue.
||| If the key is already present in the queue,
||| the associated priority and value are
||| replaced with the supplied priority and value. O(min(n, W))
export
insert :  Hashable k
       => Ord k
       => Ord p
       => k
       -> p
       -> v
       -> HashPSQ k p v
       -> HashPSQ k p v
insert k p v (MkHashPSQ npsq) =
  MkHashPSQ $
    snd     $
      NatPSQ.alter (\x => ((), ins k p v x)) (cast $ hash k) npsq

--------------------------------------------------------------------------------
--          Construction
--------------------------------------------------------------------------------

||| The empty queue. O(1)
export
empty : HashPSQ k p v
empty =
  MkHashPSQ NatPSQ.empty

||| Build a queue with one element. O(1)
export
singleton :  Hashable k
          => Ord k
          => Ord p
          => k
          -> p
          -> v
          -> HashPSQ k p v
singleton k p v =
  Data.HashPSQ.insert k p v empty

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Is the queue empty? O(1)
export
null :  HashPSQ k p v
     -> Bool
null (MkHashPSQ npsq) =
  NatPSQ.null npsq

||| The number of elements in a queue. O(n)
export
size :  HashPSQ k p v
     -> Nat
size (MkHashPSQ npsq) =
  NatPSQ.fold (\_, _, (MkBucket _ _ opsq), acc => 1 + OrdPSQ.size opsq + acc)
              0
              npsq

||| The priority and value of a given key, or Nothing if the
||| key is not bound. O(min(n ,W))
export
lookup :  Hashable k
       => Ord k
       => Ord p
       => k
       -> HashPSQ k p v
       -> Maybe (p, v)
lookup k (MkHashPSQ npsq) =
  let nsq' = NatPSQ.lookup (cast $ hash k) npsq
    in case nsq' of
         Nothing                      =>
           Nothing
         Just (p0, MkBucket k0 v0 os) =>
           case k0 == k of
             True  =>
               Just (p0, v0)
             False =>
               OrdPSQ.lookup k os

||| Check if a key is present in the queue. O(min(n, W))
export
member :  Hashable k
       => Ord k
       => Ord p
       => k
       -> HashPSQ k p v
       -> Bool
member k =
  isJust . lookup k

||| Is the key not a member of the queue? See also member. O(log n)
export
notMember :  Hashable k
          => Ord k
          => Ord p
          => k
          -> HashPSQ k p v
          -> Bool
notMember k m =
  not $
    member k m

||| The element with the lowest priority. O(1)
export
findMin :  Hashable k
        => Ord k
        => Ord p
        => HashPSQ k p v
        -> Maybe (k, p, v)
findMin (MkHashPSQ npsq) =
  case NatPSQ.findMin npsq of
    Nothing                     =>
      Nothing
    Just (_, p, MkBucket k x _) =>
      Just (k, p, x)

--------------------------------------------------------------------------------
--          Views
--------------------------------------------------------------------------------

private
deleteV :  Eq k
        => Ord k
        => Ord p
        => k
        -> Maybe (p, Bucket k p v)
        -> (Maybe (p, v), Maybe (p, Bucket k p v))
deleteV _ Nothing                         =
  (Nothing, Nothing)
deleteV k (Just (p, MkBucket bk bx opsq)) =
  case k == bk of
    True  =>
      case OrdPSQ.minView opsq of
        Nothing                  =>
          (Just (p, bx), Nothing)
        Just (k', p', x', opsq') =>
          (Just (p, bx), Just (p', MkBucket k' x' opsq'))
    False =>
      case OrdPSQ.deleteView k opsq of
        Nothing              =>
          (Nothing,       Nothing)
        Just (p', x', opsq') =>
          (Just (p', x'), Just (p, MkBucket bk bx opsq'))

||| Delete a key and its priority and value from the queue. If
||| the key was present, the associated priority and value are returned in
||| addition to the updated queue. O(min(n, W))
export
deleteView :  Hashable k
           => Ord k
           => Ord p
           => k
           -> HashPSQ k p v
           -> Maybe (p, v, HashPSQ k p v)
deleteView k (MkHashPSQ npsq) =
  case NatPSQ.alter (\x => deleteV k x) (cast $ hash k) npsq of
    (Nothing,     _    ) =>
      Nothing
    (Just (p, x), npsq') =>
      Just (p, x, MkHashPSQ npsq')

||| Insert a new key, priority and value into the queue. If the key
||| is already present in the queue, then the evicted priority and value can be
||| found the first element of the returned tuple. O(min(n, W))
export
insertView :  Hashable k
           => Ord k
           => Ord p
           => k
           -> p
           -> v
           -> HashPSQ k p v
           -> (Maybe (p, v), HashPSQ k p v)
insertView k p x t =
  case deleteView k t of
    Nothing          =>
      (Nothing,       insert k p x t)
    Just (p', x', _) =>
      (Just (p', x'), insert k p x t)

private
minV :  Ord k
     => Ord p
     => Maybe (a, b, Bucket k p v)
     -> (Maybe (k, b, v), Maybe (a, p, Bucket k p v))
minV Nothing                        =
  (Nothing, Nothing)
minV (Just (h, p, MkBucket k x os)) =
  case OrdPSQ.minView os of
    Nothing                =>
      (Just (k, p, x), Nothing)
    Just (k', p', x', os') =>
      (Just (k, p, x), Just (h, p', MkBucket k' x' os'))

||| Retrieve the binding with the least priority, and the
||| rest of the queue stripped of that binding. O(min(n, W))
export
minView :  Hashable k
        => Ord k
        => Ord p
        => HashPSQ k p v
        -> Maybe (k, p, v, HashPSQ k p v)
minView (MkHashPSQ npsq) =
  case NatPSQ.alterMin minV npsq of
    (Nothing       , _    ) =>
      Nothing
    (Just (k, p, x), npsq') =>
      Just (k, p, x, MkHashPSQ npsq')

||| Return a list of elements ordered by key whose priorities are at most pt,
||| and the rest of the queue stripped of these elements.
||| The returned list of elements can be in any order: no guarantees there.
export
atMostView :  Hashable k
           => Ord k
           => Ord p
           => p
           -> HashPSQ k p v
           -> (List (k, p, v), HashPSQ k p v)
atMostView pt (MkHashPSQ t0) =
  let -- First we use NatPSQ.atMostView to get a collection of buckets that have
      -- AT LEAST one element with a low priority.  Buckets will usually only
      -- contain a single element.
      (buckets, t1) = NatPSQ.atMostView pt t0
      -- We now need to run through the buckets.  This will give us a list of
      -- elements to return and a bunch of buckets to re-insert.
      (returns, reinserts) = go Nil Nil buckets
      -- Now we can do the re-insertion pass.
      t2 = foldl
             (\t, (p, b@(MkBucket k _ _)) => NatPSQ.unsafeInsertNew (cast $ hash k) p b t)
             t1
             reinserts

    in (returns, MkHashPSQ t2)
    where
      -- We use two accumulators, for returns and re-inserts.
      go :  List (k, p, v)
         -> List (p, Bucket k p v)
         -> List (a, p, Bucket k p v)
         -> (List (k, p, v), List (p, Bucket k p v))
      go rets reins []                                =
        (rets, reins)
      go rets reins ((_, p, MkBucket k v opsq) :: bs) =
          -- Note that 'elems' should be very small, ideally a null list.
          let (elems, opsq') = OrdPSQ.atMostView pt opsq
              rets'          = (k, p, v) :: elems ++ rets
              reins'         = case toBucket opsq' of
                                 Nothing      =>
                                   reins
                                 Just (p', b) =>
                                   ((p', b) :: reins)
            in go rets' reins' bs

--------------------------------------------------------------------------------
--          Delete
--------------------------------------------------------------------------------

||| Delete a key and its priority and value from the queue.
||| When the key is not a member of the queue, the original queue is returned. O(min(n, W))
export
delete :  Hashable k
       => Ord k
       => Ord p
       => k
       -> HashPSQ k p v
       -> HashPSQ k p v
delete k t =
  case deleteView k t of
    Nothing         =>
      t
    Just (_, _, t') =>
      t'

||| Delete the binding with the least priority, and return the
||| rest of the queue stripped of that binding.
||| In case the queue is empty, the empty queue is returned again. O(min(n, W))
export
deleteMin :  Hashable k
          => Ord k
          => Ord p
          => HashPSQ k p v
          -> HashPSQ k p v
deleteMin t =
  case minView t of
    Nothing            =>
      t
    Just (_, _, _, t') =>
      t'

--------------------------------------------------------------------------------
--          Alter
--------------------------------------------------------------------------------

||| The expression, alter f k queue, alters the value x at k, or absence thereof.
||| alter can be used to insert, delete, or update a value in a queue.
||| It also allows you to calculate an additional value b. O(min(n, w))
export
alter :  Hashable k
      => Ord k
      => Ord p
      => (Maybe (p, v) -> (b, Maybe (p, v)))
      -> k
      -> HashPSQ k p v
      -> (b, HashPSQ k p v)
alter f k (MkHashPSQ npsq) =
  let h = cast $ hash k
    in case NatPSQ.deleteView h npsq of
         Nothing =>
           case f Nothing of
             (b, Nothing)     =>
               (b, MkHashPSQ npsq)
             (b, Just (p, x)) =>
               (b, MkHashPSQ $ NatPSQ.unsafeInsertNew h p (MkBucket k x OrdPSQ.empty) npsq)
         Just (bp, MkBucket bk bx opsq, npsq') =>
           case k == bk of
             True  =>
               case f (Just (bp, bx)) of
                 (b, Nothing) =>
                   case toBucket opsq of
                     Nothing             =>
                       (b, MkHashPSQ npsq')
                     Just (bp', bucket') =>
                       (b, MkHashPSQ $ NatPSQ.unsafeInsertNew h bp' bucket' npsq')
                 (b, Just (p, x)) =>
                   let (bp', bucket') = mkBucket k p x opsq
                     in (b, MkHashPSQ $ NatPSQ.unsafeInsertNew h bp' bucket' npsq')
             False =>
               let (b, opsq')     = OrdPSQ.alter f k opsq
                   (bp', bucket') = mkBucket bk bp bx opsq'
                 in (b, MkHashPSQ $ NatPSQ.unsafeInsertNew h bp' bucket' npsq')

||| A variant of alter which works on the element with the
||| minimum priority.
||| Unlike alter, this variant also allows you to change the key of the element. O(min(n, W))
export
alterMin :  Hashable k
         => Ord k
         => Ord p
         => (Maybe (k, p, v) -> (b, Maybe (k, p, v)))
         -> HashPSQ k p v
         -> (b, HashPSQ k p v)
alterMin f t0 =
  let (t, mbx)  = case minView t0 of
                    Nothing             =>
                      (t0, Nothing)
                    Just (k, p, x, t0') =>
                      (t0', Just (k, p, x))
      (b, mbx') = f mbx
    in case mbx' of
         Nothing        =>
           (b, t)
         Just (k, p, x) =>
           (b, insert k p x t)

--------------------------------------------------------------------------------
--          Traversal
--------------------------------------------------------------------------------

||| Modify every value in the queue. O(n)
export
map :  (v -> w)
    -> HashPSQ k p v
    -> HashPSQ k p w
map f (MkHashPSQ npsq) =
  MkHashPSQ (NatPSQ.map mapBucket npsq)
  where
    mapBucket :  Bucket k p v
              -> Bucket k p w
    mapBucket (MkBucket k v opsq) =
      MkBucket k (f v) (OrdPSQ.map (\k', p', v' => f v') opsq)

--------------------------------------------------------------------------------
--          Conversion
--------------------------------------------------------------------------------

||| Build a queue from a list of (key, priority, value) tuples.
||| If the list contains more than one priority and value for the same key, the
||| last priority and value for the key is retained. O(min(n, W))
export
fromList :  Hashable k
         => Ord k
         => Ord p
         => List (k, p, v)
         -> HashPSQ k p v
fromList =
  foldl (\psq, (k, p, x) => insert k p x psq) empty

||| Convert a queue to a list of (key, priority, value) tuples. The
||| order of the list is not specified. O(n)
export
toList :  Hashable k
       => Ord k
       => Ord p
       => HashPSQ k p v
       -> List (k, p, v)
toList (MkHashPSQ npsq) =
    [ (k', p', x')
    | (_, p, (MkBucket k x opsq)) <- NatPSQ.toList npsq
    , (k', p', x')                <- (k, p, x) :: OrdPSQ.toList opsq
    ]

||| Obtain the list of present keys in the queue. O(n)
export
keys :  Hashable k
     => Ord k
     => Ord p
     => HashPSQ k p v
     -> List k
keys t =
  [k | (k, _, _) <- toList t]

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Functor (HashPSQ k p) where
  map = Data.HashPSQ.map
