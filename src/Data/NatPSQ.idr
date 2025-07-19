||| Ordered Nat Priority Search Queue
module Data.NatPSQ

import public Data.NatPSQ.Internal

import Data.List
import Data.Maybe

%default total

--------------------------------------------------------------------------------
--          Unsafe operations
--------------------------------------------------------------------------------

private
link :  Key
     -> p
     -> v
     -> Key
     -> NatPSQ p v
     -> NatPSQ p v
     -> NatPSQ p v
link k p x k' k't othertree =
  let m = branchMask k k'
    in case zero m k' of
         True  =>
           Bin k p x m k't othertree
         False =>
           Bin k p x m othertree k't

||| Internal function that merges two disjoint NatPSQ's that share the
||| same prefix mask.
private
merge :  Ord p
      => Mask
      -> NatPSQ p v
      -> NatPSQ p v
      -> NatPSQ p v
merge m l r =
  case l of
    Nil          =>
      r
    Tip lk lp lx =>
      case r of
        Nil          =>
          l
        Tip rk rp rx =>
          case (lp, lk) < (rp, rk) of
            True  =>
              Bin lk lp lx m Nil r
            False =>
              Bin rk rp rx m l Nil
        Bin rk rp rx rm rl rr =>
          case (lp, lk) < (rp, rk) of
            True  =>
              Bin lk lp lx m Nil r
            False =>
              Bin rk rp rx m l (merge rm rl rr)
    Bin lk lp lx lm ll lr =>
      case r of
        Nil          =>
          l
        Tip rk rp rx =>
          case (lp, lk) < (rp, rk) of
            True  =>
              Bin lk lp lx m (merge lm ll lr) r
            False =>
              Bin rk rp rx m l Nil
        Bin rk rp rx rm rl rr =>
          case (lp, lk) < (rp, rk) of
            True  =>
              Bin lk lp lx m (merge lm ll lr) r
            False =>
              Bin rk rp rx m l (merge rm rl rr)

||| Smart constructor for a Bin node.
private
bin :  Key
    -> p
    -> v
    -> Mask
    -> NatPSQ p v
    -> NatPSQ p v
    -> NatPSQ p v
bin k p x _ Nil Nil =
  Tip k p x
bin k p x m l   r   =
  Bin k p x m l r

||| Internal function to insert a key that is *not* present in the priority queue.
export
unsafeInsertNew :  Ord p
                => Key
                -> p
                -> v
                -> NatPSQ p v
                -> NatPSQ p v
unsafeInsertNew k p x t =
  case t of
    Nil          =>
      Tip k p x
    Tip k' p' x' =>
      case (p, k) < (p', k') of
        True  =>
          link k p x k' t Nil
        False =>
          link k' p' x' k (Tip k p x) Nil
    Bin k' p' x' m l r =>
      case noMatch k k' m of
        True  =>
          case (p, k) < (p', k') of
            True  =>
              link k p x k' t Nil
            False =>
              link k' p' x' k (Tip k p x) (merge m l r)
        False =>
          case (p, k) < (p', k') of
            True  =>
              case zero k' m of
                True  =>
                  Bin k p x m (unsafeInsertNew k' p' x' l) r
                False =>
                  Bin k p x m l (unsafeInsertNew k' p' x' r)
            False =>
              case zero k m of
                True =>
                  Bin k' p' x' m (unsafeInsertNew k p x l) r
                False =>
                  Bin k' p' x' m l (unsafeInsertNew k p x r)

--------------------------------------------------------------------------------
--          Construction
--------------------------------------------------------------------------------

||| The empty queue. O(1)
export
empty : NatPSQ p v
empty =
  Nil

||| Build a queue with one element. O(1)
export
singleton :  Ord p
          => Nat
          -> p
          -> v
          -> NatPSQ p v
singleton k p v =
  Tip k p v

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Is the queue empty? O(1)
export
null :  NatPSQ p v
     -> Bool
null Nil =
  True
null _   =
  False

||| The number of elements in a queue. O(1)
export
size :  NatPSQ p v
     -> Nat
size Nil               =
  0
size (Tip _ _ _)       =
  1
size (Bin _ _ _ _ l r) =
  1 + size l + size r

||| The priority and value of a given key, or Nothing
||| if the key is not bound. O(log n)
export
lookup :  Nat
       -> NatPSQ p v
       -> Maybe (p, v)
lookup key =
  go
  where
    go :  NatPSQ p v
       -> Maybe (p, v)
    go Nil            =
          Nothing
    go (Tip k' p' x') =
      case key == k' of
        True  =>
          Just (p', x')
        False =>
          Nothing
    go (Bin k' p' x' m l r) =
      case noMatch key k' m of
        True  =>
          Nothing
        False =>
          case key == k' of
            True  =>
              Just (p', x')
            False =>
              case zero key m of
                True  =>
                  go l
                False =>
                  go r

||| Check if a key is present in the queue. O(log n)
export
member :  Nat
       -> NatPSQ p v
       -> Bool
member k =
  isJust . lookup k

||| The element with the lowest priority. O(1)
export
findMin :  NatPSQ p v
        -> Maybe (Nat, p, v)
findMin Nil               =
  Nothing
findMin (Tip k p x)       =
  Just (k, p, x)
findMin (Bin k p x _ _ _) =
  Just (k, p, x)

--------------------------------------------------------------------------------
--          Views
--------------------------------------------------------------------------------

||| Delete a key and its priority and value from the queue. If
||| the key was present, the associated priority and value are returned in
||| addition to the updated queue. O(min(n, W))
export
deleteView :  Ord p
           => Nat
           -> NatPSQ p v
           -> Maybe (p, v, NatPSQ p v)
deleteView k t =
    case delFrom t of
      (_, Nothing)      =>
        Nothing
      (t', Just (p, x)) =>
        Just (p, x, t')
  where
    delFrom :  NatPSQ p v
            -> (NatPSQ p v, Maybe (p, v))
    delFrom Nil            =
      (Nil, Nothing)
    delFrom (Tip k' p' x') =
      case k == k' of
        True  =>
          (Nil, Just (p', x'))
        False =>
          (t, Nothing)
    delFrom (Bin k' p' x' m l r) =
      case noMatch k k' m of
        True  =>
          (t, Nothing)
        False =>
          case k == k' of
            True  =>
              let t' = merge m l r
                in (t', Just (p', x'))
            False =>
              case zero k m of
                True  =>
                  let (l', mbpx) = delFrom l
                      t'         = bin k' p' x' m l' r
                    in (t', mbpx)
                False =>
                  let (r', mbpx) = delFrom r
                      t'         = bin k' p' x' m l  r'
                    in (t', mbpx)

||| Insert a new key, priority and value into the queue. If the key
||| is already present in the queue, then the evicted priority and value can be
||| found the first element of the returned tuple. O(min(n, W))
export
insertView :  Ord p
           => Nat
           -> p
           -> v
           -> NatPSQ p v
           -> (Maybe (p, v), NatPSQ p v)
insertView k p x t =
  case deleteView k t of
    Nothing           =>
      (Nothing, unsafeInsertNew k p x t)
    Just (p', v', t') =>
      (Just (p', v'), unsafeInsertNew k p x t')

||| Retrieve the binding with the least priority, and the
||| rest of the queue stripped of that binding. O(min(n, W))
export
minView :  Ord p
        => NatPSQ p v
        -> Maybe (Nat, p, v, NatPSQ p v)
minView Nil               =
  Nothing
minView (Tip k p x)       =
  Just (k, p, x, Nil)
minView (Bin k p x m l r) =
  Just (k, p, x, merge m l r)

||| Return a list of elements ordered by key whose priorities are at most @pt@,
||| and the rest of the queue stripped of these elements.  The returned list of
||| elements can be in any order: no guarantees there.
export
atMostView :  Ord p
           => p
           -> NatPSQ p v
           -> (List (Nat, p, v), NatPSQ p v)
atMostView pt t =
  go Nil t
  where
    go :  List (Key, p, v)
       -> NatPSQ p v
       -> (List (Key, p, v), NatPSQ p v)
    go acc Nil         =
      (acc, t)
    go acc (Tip k p x) =
      case p > pt of
        True  =>
          (acc, t)
        False =>
          ((k, p, x) :: acc, Nil)
    go acc (Bin k p x m l r) =
      case p > pt of
        True  =>
          (acc, t)
        False =>
          let (acc',  l') = go acc  l
              (acc'', r') = go acc' r
            in  ((k, p, x) :: acc'', merge m l' r')

--------------------------------------------------------------------------------
--          Delete
--------------------------------------------------------------------------------

||| Delete a key and its priority and value from the queue.
||| When the key is not a member of the queue,
||| the original queue is returned. O(min(n, W))
export
delete :  Ord p
       => Nat
       -> NatPSQ p v
       -> NatPSQ p v
delete key =
  go
  where
    go :  NatPSQ p v
       -> NatPSQ p v
    go t =
      case t of
        Nil        =>
          Nil
        Tip k' _ _ =>
          case key == k' of
            True  =>
              Nil
            False =>
              t
        Bin k' p' x' m l r =>
          case noMatch key k' m of
            True  =>
              t
            False =>
              case key == k' of
                True  =>
                  merge m l r
                False =>
                  case zero key m of
                    True  =>
                      bin k' p' x' m (go l) r
                    False =>
                      bin k' p' x' m l (go r)

||| Delete the binding with the least priority, and return the
||| rest of the queue stripped of that binding.
||| In case the queue is empty, the empty queue is returned again. O(min(n, w))
export
deleteMin :  Ord p
          => NatPSQ p v
          -> NatPSQ p v
deleteMin t =
  case minView t of
    Nothing            =>
      t
    Just (_, _, _, t') =>
      t'

--------------------------------------------------------------------------------
--          Insertion
--------------------------------------------------------------------------------

||| Insert a new key, priority and value into the queue. If the key
||| is already present in the queue, the associated priority and value are
||| replaced with the supplied priority and value. O(min(n, W))
export
insert :  Ord p
       => Nat
       -> p
       -> v
       -> NatPSQ p v
       -> NatPSQ p v
insert k p x t =
  unsafeInsertNew k p x (delete k t)

--------------------------------------------------------------------------------
--          Alter
--------------------------------------------------------------------------------

||| The expression alter f k queue alters the value x at k,
||| or absence thereof.
||| alter can be used to insert, delete, or update a value
||| in a queue.
||| It also allows you to calculate an additional value b. O(min(n, W))
export
alter :  Ord p
      => (Maybe (p, v) -> (b, Maybe (p, v)))
      -> Nat
      -> NatPSQ p v
      -> (b, NatPSQ p v)
alter f k t =
  let (t', mbx) = case deleteView k t of
                    Nothing          =>
                      (t, Nothing)
                    Just (p, v, t'') =>
                      (t'', Just (p, v))
      (b, mbx') = f mbx
    in case mbx' of
         Nothing     =>
           (b, t')
         Just (p, v) =>
           let t'' = unsafeInsertNew k p v t'
             in (b, t'')

||| A variant of alter which works on the element with the
||| minimum priority. Unlike alter,
||| this variant also allows you to change the
||| key of the element. O(min(n, W))
export
alterMin :  Ord p
         => (Maybe (Nat, p, v) -> (b, Maybe (Nat, p, v)))
         -> NatPSQ p v
         -> (b, NatPSQ p v)
alterMin f Nil         =
  case f Nothing of
    (b, Nothing)           =>
      (b, Nil)
    (b, Just (k', p', x')) =>
      (b, Tip k' p' x')
alterMin f (Tip k p x) =
  case f (Just (k, p, x)) of
    (b, Nothing)           =>
      (b, Nil)
    (b, Just (k', p', x')) =>
      (b, Tip k' p' x')
alterMin f (Bin k p x m l r) =
  case f (Just (k, p, x)) of
    (b, Nothing)           =>
      (b, merge m l r)
    (b, Just (k', p', x')) =>
      case k /= k' of
        True  =>
          (b, insert k' p' x' (merge m l r))
        False =>
          case p' <= p of
            True  =>
              (b, Bin k p' x' m l r)
            False =>
              (b, unsafeInsertNew k p' x' (merge m l r))

--------------------------------------------------------------------------------
--          Traversal
--------------------------------------------------------------------------------

||| Modify every value in the queue. O(n)
export
map :  (v -> w)
    -> NatPSQ p v
    -> NatPSQ p w
map _ Nil               =
  Nil
map f (Tip k p x)       =
  Tip k p (f x)
map f (Bin k p x m l r) =
  Bin k p (f x) m (map f l) (map f r)

||| Maps a function over the values and priorities of the queue.
||| The function f must be monotonic with respect to the priorities.
||| This means that if x < y, then fst (f k x v) < fst (f k y v).
||| The precondition is not checked.
||| If f is not monotonic, then the result
||| will be invalid. O(n)
export
unsafeMapMonotonic :  (Key -> p -> v -> (q, w))
                   -> NatPSQ p v
                   -> NatPSQ q w
unsafeMapMonotonic f Nil               =
  Nil
unsafeMapMonotonic f (Tip k p x)       =
  let (p', x') = f k p x
    in Tip k p' x'
unsafeMapMonotonic f (Bin k p x m l r) =
  let (p', x') = f k p x
    in Bin k p' x' m (unsafeMapMonotonic f l) (unsafeMapMonotonic f r)

||| Fold over every key, priority and value in the queue.
||| The order in which the fold is performed is not specified. O(n)
export
fold :  (Nat -> p -> v -> a -> a)
     -> a
     -> NatPSQ p v
     -> a
fold f acc Nil                  =
  acc
fold f acc (Tip k' p' x')       =
  f k' p' x' acc
fold f acc (Bin k' p' x' m l r) =
  let acc1 = f k' p' x' acc
      acc2 = fold f acc1 l
      acc3 = fold f acc2 r
    in acc3

export
foldl :  (acc -> v -> acc)
      -> acc
      -> NatPSQ p v
      -> acc
foldl f acc Nil               =
  acc
foldl f acc (Tip _ _ v)       =
  f acc v
foldl f acc (Bin _ _ v _ l r) =
  foldl f (foldl f (f acc v) l) r

export
foldr :  (v -> acc -> acc)
      -> acc
      -> NatPSQ p v
      -> acc
foldr f acc Nil               =
  acc
foldr f acc (Tip _ _ v)       =
  f v acc
foldr f acc (Bin _ _ v _ l r) =
  foldr f (f v (foldr f acc r)) l


--------------------------------------------------------------------------------
--          Conversion
--------------------------------------------------------------------------------

||| Build a queue from a list of (key, priority, value) tuples.
||| If the list contains more than one priority and value for the same key, the
||| last priority and value for the key is retained. O(n * min(n, W))
export
fromList :  Ord p
         => List (Nat, p, v)
         -> NatPSQ p v
fromList =
  foldl (\im, (k, p, x) => insert k p x im) empty

||| Convert a queue to a list of (key, priority, value) tuples.
||| The order of the list is not specified. O(n)
export
toList :  NatPSQ p v
       -> List (Nat, p, v)
toList Nil               =
  Nil
toList (Tip k p v)       =
  [(k, p, v)]
toList (Bin k p v _ l r) =
  (k, p, v) :: toList l ++ toList r

||| Obtain the list of present keys in the queue. O(n)
export
keys :  NatPSQ p v
     -> List Nat
keys t =
  [k | (k, _, _) <- toList t]

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Functor (NatPSQ p) where
  map = Data.NatPSQ.map

export
Foldable (NatPSQ p) where
  foldl = Data.NatPSQ.foldl
  foldr = Data.NatPSQ.foldr
  null  = Data.NatPSQ.null
