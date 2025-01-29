||| Ordered Priority Search Queue
module Data.OrdPSQ

import public Data.OrdPSQ.Internal

import Data.List
import Data.Maybe
import Data.String
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Construction
--------------------------------------------------------------------------------

||| The empty queue.
export
empty : OrdPSQ k p v
empty = Void

||| Build a queue with one element.
export
singleton : k -> p -> v -> OrdPSQ k p v
singleton k p v = Winner (Elem' k p v) Start k

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Is the queue empty? O(1)
export
null : OrdPSQ k p v -> Bool
null Void           = True
null (Winner _ _ _) = False

||| The number of elements in a queue. O(1)
export
size : OrdPSQ k p v -> Nat
size Void            = 0
size (Winner _ lt _) = 1 + size' lt

||| The priority and value of a given key, or Nothing
||| if the key is not bound. O(log n)
covering
export
lookup : Ord k => k -> OrdPSQ k p v -> Maybe (p, v)
lookup key = go
  where
    go : OrdPSQ k p v -> Maybe (p, v)
    go t =
      case tourView t of
        Null                  =>
          Nothing
        Single (Elem' k' p v) =>
          case key == k' of
            True  =>
              Just (p, v)
            False =>
              Nothing
        Play tl tr            =>
          case key <= maxKey tl of
            True  =>
              go tl
            False =>
              go tr

||| Check if a key is present in the queue. O(log n)
covering
export
member : Ord k => k -> OrdPSQ k p v -> Bool
member k = isJust . lookup k

||| The element with the lowest priority. O(1)
export
findMin : OrdPSQ k p v -> Maybe (k, p, v)
findMin Void                       = Nothing
findMin (Winner (Elem' k p v) _ _) = Just (k, p, v)

--------------------------------------------------------------------------------
--          Insertion
--------------------------------------------------------------------------------

||| Insert a new key, priority and value into the queue.
||| If the key is already present in the queue, the associated
||| priority and value are replaced with the supplied priority
||| and value. O(log n)
covering
export
insert : Ord k => Ord p => k -> p -> v -> OrdPSQ k p v -> OrdPSQ k p v
insert key priority value = go
  where
    go : OrdPSQ k p v -> OrdPSQ k p v
    go t =
      case t of
        Void                              =>
          singleton key priority value
        Winner (Elem' k' p' v') Start _   =>
          case compare key k' of
            LT =>
              singleton key priority value `play` singleton k' p' v'
            EQ =>
              singleton key priority value
            GT =>
              singleton k' p' v' `play` singleton key priority value
        Winner e (RLoser _ e' tl m tr) m' =>
          case key <= m of
            True  =>
              go (Winner e tl m) `play` (Winner e' tr m')
            False =>
              (Winner e tl m) `play` go (Winner e' tr m')
        Winner e (LLoser _ e' tl m tr) m' =>
          case key <= m of
            True  =>
              go (Winner e' tl m) `play` (Winner e tr m')
            False =>
              (Winner e' tl m) `play` go (Winner e tr m')

--------------------------------------------------------------------------------
--          Traversals
--------------------------------------------------------------------------------

||| Modify every value in the queue. O(n)
export
map : (k -> p -> v -> w) -> OrdPSQ k p v -> OrdPSQ k p w
map f = goPSQ
  where
    goElem : Elem k p v -> Elem k p w
    goElem (Elem' k p x) = Elem' k p (f k p x)
    goLTree : LTree k p v -> LTree k p w
    goLTree Start              = Start
    goLTree (LLoser s e l k r) = LLoser s (goElem e) (goLTree l) k (goLTree r)
    goLTree (RLoser s e l k r) = RLoser s (goElem e) (goLTree l) k (goLTree r)
    goPSQ : OrdPSQ k p v -> OrdPSQ k p w
    goPSQ Void           = Void
    goPSQ (Winner e l k) = Winner (goElem e) (goLTree l) k

||| Maps a function over the values and priorities of the queue.
||| The function f must be monotonic with respect to the priorities.
||| I.e. if x < y, then fst (f k x v) < fst (f k y v).
||| The precondition is not checked.
||| If f is not monotonic, then the result
||| will be invalid. O(n)
export
unsafeMapMonotonic : (k -> p -> v -> (q, w)) -> OrdPSQ k p v -> OrdPSQ k q w
unsafeMapMonotonic f = goPSQ
  where
    goElem : Elem k p v -> Elem k q w
    goElem (Elem' k p x) =
      let (p', x') = f k p x
        in Elem' k p' x'
    goLTree : LTree k p v -> LTree k q w
    goLTree Start              = Start
    goLTree (LLoser s e l k r) = LLoser s (goElem e) (goLTree l) k (goLTree r)
    goLTree (RLoser s e l k r) = RLoser s (goElem e) (goLTree l) k (goLTree r)
    goPSQ : OrdPSQ k p v -> OrdPSQ k q w
    goPSQ Void           = Void
    goPSQ (Winner e l k) = Winner (goElem e) (goLTree l) k

||| Fold over every key, priority and value in the queue. O(n)
export
fold : (k -> p -> v -> a -> a) -> a -> OrdPSQ k p v -> a
fold f acc psq =
  case psq of
    Void                       =>
      acc
    (Winner (Elem' k p v) t _) =>
      let acc' = f k p v acc
        in go acc' t
  where
    go : a -> LTree k p v -> a
    go acc Start                            = acc
    go acc (LLoser _ (Elem' k p v) lt _ rt) = go (f k p v (go acc lt)) rt
    go acc (RLoser _ (Elem' k p v) lt _ rt) = go (f k p v (go acc lt)) rt

export
foldr : (a -> b -> b) -> b -> OrdPSQ k p a -> b
foldr f z Void           = z
foldr f z (Winner e l _) = Prelude.foldr f (Data.OrdPSQ.Internal.LTree.foldr f z l) e

export
foldl : (b -> a -> b) -> b -> OrdPSQ k p a -> b
foldl f z Void           = z
foldl f z (Winner e l _) = Prelude.foldl f (Data.OrdPSQ.Internal.LTree.foldl f z l) e

--------------------------------------------------------------------------------
--          Views
--------------------------------------------------------------------------------

||| Delete a key and its priority and value from the queue.
||| If the key was present, the associated priority and value are returned in addition
||| to the updated queue. O(log n)
covering
export
deleteView : Ord k => Ord p => k -> OrdPSQ k p v -> Maybe (p, v, OrdPSQ k p v)
deleteView k psq =
  case psq of
    Void                              =>
      Nothing
    Winner (Elem' k' p v) Start _     =>
      case k == k' of
        True  =>
          Just (p, v, empty)
        False =>
          Nothing
    Winner e (RLoser _ e' tl m tr) m' =>
      case k <= m of
        True  =>
          map (\(p, v, q) => (p, v,  q `play` (Winner e' tr m'))) (deleteView k (Winner e tl m))
        False =>
          map (\(p, v, q) => (p, v,  (Winner e tl m) `play` q)) (deleteView k (Winner e' tr m'))
    Winner e (LLoser _ e' tl m tr) m' =>
      case k <= m of
        True  =>
          map (\(p, v, q) => (p, v, q `play` (Winner e tr m'))) (deleteView k (Winner e' tl m))
        False =>
          map (\(p, v, q) => (p, v, (Winner e' tl m) `play` q)) (deleteView k (Winner e tr m'))

||| Insert a new key, priority and value into the queue.
||| If the key is already present in the queue,
||| then the evicted priority and value can be
||| found the first element of the returned tuple. O(log n)
covering
export
insertView : Ord k => Ord p => k -> p -> v -> OrdPSQ k p v -> (Maybe (p, v), OrdPSQ k p v)
insertView k p x t =
  case deleteView k t of
    Nothing          =>
      (Nothing,       insert k p x t)
    Just (p', x', _) =>
      (Just (p', x'), insert k p x t)

private
secondBest : Ord k => Ord p => LTree k p v -> k -> OrdPSQ k p v
secondBest Start _                 = Void
secondBest (LLoser _ e tl m tr) m' = Winner e tl m `play` secondBest tr m'
secondBest (RLoser _ e tl m tr) m' = secondBest tl m `play` Winner e tr m'

||| Retrieve the binding with the least priority, and the
||| rest of the queue stripped of that binding. O(log n)
export
minView : Ord k => Ord p => OrdPSQ k p v -> Maybe (k, p, v, OrdPSQ k p v)
minView Void                       = Nothing
minView (Winner (Elem' k p v) t m) = Just (k, p, v, secondBest t m)

--------------------------------------------------------------------------------
--          Delete/Update
--------------------------------------------------------------------------------

||| Delete a key, its priority, and its value from the queue.
||| When the key is not a member of the queue,
||| the original queue is returned. O(log n)
covering
export
delete : Ord k => Ord p => k -> OrdPSQ k p v -> OrdPSQ k p v
delete key = go
  where
    go : OrdPSQ k p v -> OrdPSQ k p v
    go t =
      case t of
        Void                              =>
          empty
        Winner (Elem' k' p v) Start _     =>
          case key == k' of
            True  =>
              empty
            False =>
              singleton k' p v
        Winner e (RLoser _ e' tl m tr) m' =>
          case key <= m of
            True  =>
              go (Winner e tl m) `play` (Winner e' tr m')
            False =>
              (Winner e tl m) `play` go (Winner e' tr m')
        Winner e (LLoser _ e' tl m tr) m' =>
          case key <= m of
            True  =>
              go (Winner e' tl m) `play` (Winner e tr m')
            False =>
              (Winner e' tl m) `play` go (Winner e tr m')

||| Delete the binding with the least priority, and return the
||| rest of the queue stripped of that binding.
||| In case the queue is empty, the empty queue is returned again. O(log n)
export
deleteMin : Ord k => Ord p => OrdPSQ k p v -> OrdPSQ k p v
deleteMin t =
  case minView t of
    Nothing            =>
      t
    Just (_, _, _, t') =>
      t'

||| The expression alter f k queue alters the value x at k, or
||| absence thereof.
||| alter can be used to insert, delete, or update a value in a queue.
||| It also allows you to calculate an additional value b. O(log n)
covering
export
alter : Ord k => Ord p => (Maybe (p, v) -> (b, Maybe (p, v))) -> k -> OrdPSQ k p v -> (b, OrdPSQ k p v)
alter f k psq =
  let (psq', mbpv) = case deleteView k psq of
                       Nothing          =>
                         (psq, Nothing)
                       Just (p, v, psq) =>
                         (psq, Just (p, v))
      (b, mbpv') = f mbpv
    in case mbpv' of
         Nothing     =>
           (b, psq')
         Just (p, v) =>
           (b, insert k p v psq')

||| A variant of alter which works on the element with the minimum priority.
||| Unlike alter, this variant also allows you to change the key of the element. O(log n)
covering
export
alterMin : Ord k => Ord p => (Maybe (k, p, v) -> (b, Maybe (k, p, v))) -> OrdPSQ k p v -> (b, OrdPSQ k p v)
alterMin f psq =
  case minView psq of
    Nothing            =>
      let (b, mbkpv) = f Nothing
        in (b, insertMay mbkpv psq)
    Just (k,p,v, psq') =>
      let (b, mbkpv) = f $ Just (k, p, v)
        in (b, insertMay mbkpv psq')
  where
    insertMay : Maybe (k, p, v) -> OrdPSQ k p v -> OrdPSQ k p v
    insertMay Nothing          psq = psq
    insertMay (Just (k, p, v)) psq = insert k p v psq

--------------------------------------------------------------------------------
--          Conversion
--------------------------------------------------------------------------------

||| Build a queue from a list of (key, priority, value) tuples.
||| If the list contains more than one priority and value for the same key, the
||| last priority and value for the key is retained. O(n * log n)
covering
export
fromList : Ord k => Ord p => List (k, p, v) -> OrdPSQ k p v
fromList = foldl (\q, (k, p, v) => insert k p v q) empty

||| Convert a queue to a list of (key, priority, value) tuples. O(n)
export
toList : OrdPSQ k p v -> List (k, p, v)
toList psq =
  case psq of
    Void                     =>
      []
    Winner (Elem' k p v) l _ =>
      (k, p, v) :: toListLTree l
  where
    toListLTree : LTree k p v -> List (k, p, v)
    toListLTree lTree =
      case lTree of
        Start                        =>
          []
        LLoser _ (Elem' k p v) l _ r =>
          (k, p, v) :: toListLTree l ++ toListLTree r
        RLoser _ (Elem' k p v) l _ r =>
          (k, p, v) :: toListLTree l ++ toListLTree r
