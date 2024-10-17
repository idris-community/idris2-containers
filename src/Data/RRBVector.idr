||| Relaxed Radix Balanced Vectors (RRB-Vectors)
module Data.RRBVector

import public Data.RRBVector.Internal

import Data.Array.Core
import Data.Array.Index
import Data.Array.Indexed
import Data.Bits
import Data.Maybe

%hide Prelude.null
%hide Prelude.toList

%default total

--------------------------------------------------------------------------------
--          Creating RRB-Vectors
--------------------------------------------------------------------------------

||| The empty vector. O(1)
export
empty : RRBVector a
empty = Empty

||| A vector with a single element. O(1)
export
singleton : a -> RRBVector a
singleton x = Root 1 0 (Leaf $ A 1 $ fill 1 x)

||| Creates a vector of length n with every element set to x. O(log n)
partial
export
replicate : Nat -> a -> RRBVector a
replicate n x =
  case compare n 0 of
    LT =>
      Empty
    EQ =>
      Empty
    GT =>
      case compare n blocksize of
        LT =>
          Root n 0 (Leaf $ A n $ fill n x)
        EQ =>
          Root n 0 (Leaf $ A n $ fill n x)
        GT =>
          let size' = the Nat (cast ((the Int (cast (minus n 1))) .&. (the Int (cast (plus blockmask 1)))))
            in iterateNodes blockshift
                            (Leaf $ A blocksize $ fill blocksize x)
                            (Leaf $ A size' $ fill size' x)
  where
    iterateNodes : Shift -> Tree a -> Tree a -> RRBVector a
    iterateNodes sh full rest =
      let subtreesm1  = shiftR (minus n 1) sh
          restsize    = the Nat (cast ((the Int (cast subtreesm1)) .&. (the Int (cast blockmask))))
          rest'       = Balanced $ A (plus restsize 1) $ append (fill restsize full) (fill 1 rest)
        in case compare subtreesm1 blocksize of
             LT =>
               Root n sh rest'
             EQ =>
               let full' = Balanced (A blocksize $ fill blocksize full)
                 in iterateNodes (up sh) full' rest'
             GT =>
               let full' = Balanced (A blocksize $ fill blocksize full)
                 in iterateNodes (up sh) full' rest'

--------------------------------------------------------------------------------
--          Indexing
--------------------------------------------------------------------------------

||| The element at the index or Nothing if the index is out of range. O (log n)
partial
export
lookup : Nat -> RRBVector a -> Maybe a
lookup _ Empty               = Nothing
lookup i (Root size sh tree) =
  case compare i 0 of
    LT =>
      Nothing -- index out of range
    GT =>
      case compare i size of
        EQ =>
          Nothing -- index out of range
        GT =>
          Nothing -- index out of range
        LT =>
          Just $ lookupTree i sh tree
    EQ =>
      case compare i size of
        EQ =>
          Nothing
        GT =>
          Nothing
        LT =>
          Just $ lookupTree i sh tree
  where
    lookupTree : Nat -> Nat -> Tree a -> a
    lookupTree i sh (Balanced arr)         =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.lookup: can't convert Nat to Fin"
        Just i' =>
          lookupTree i (down sh) (at arr.arr i')
    lookupTree i sh (Unbalanced arr sizes) =
      let (idx, subidx) = relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               assert_total $ idris_crash "Data.RRBVector.lookup: can't convert Nat to Fin"
             Just idx' =>
               lookupTree subidx (down sh) (at arr.arr idx')
    lookupTree i _ (Leaf arr)              =
      let i' = the Nat (cast ((the Int (cast i)) .&. (the Int (cast blockmask))))
        in case tryNatToFin i' of
             Nothing =>
               assert_total $ idris_crash "Data.RRBVector.lookup: can't convert Nat to Fin"
             Just i'' =>
               at arr.arr i''

||| The element at the index.
||| Calls 'idris_crash' if the index is out of range. O(log n)
partial
export
index : Nat -> RRBVector a -> a
index i = fromMaybe (assert_total $ idris_crash "index out of range") . lookup i

||| A flipped version of lookup. O(log n)
partial
export
(!?) : RRBVector a -> Nat -> Maybe a
(!?) = flip lookup

||| A flipped version of index. O(log n)
partial
export
(!!) : RRBVector a -> Nat -> a
(!!) = flip index

||| Update the element at the index with a new element.
||| If the index is out of range, the original vector is returned. O (log n)
partial
export
update : Nat -> a -> RRBVector a -> RRBVector a
update _ _ Empty                 = Empty
update i x v@(Root size sh tree) =
  case compare i 0 of
    LT =>
      v -- index out of range
    GT =>
      case compare i size of
        EQ =>
          v -- index out of range
        GT =>
          v -- index out of range
        LT =>
          Root size sh (updateTree i sh tree)
    EQ =>
      case compare i size of
        EQ =>
          v
        GT =>
          v
        LT =>
          Root size sh (updateTree i sh tree)
  where
    updateTree : Nat -> Nat -> Tree a -> Tree a
    updateTree i sh (Balanced arr)         =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.update: can't convert Nat to Fin"
        Just i' =>
          Balanced (A arr.size (updateAt i' (updateTree i (down sh)) arr.arr))
    updateTree i sh (Unbalanced arr sizes) =
      let (idx, subidx) = relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               assert_total $ idris_crash "Data.RRBVector.update: can't convert Nat to Fin"
             Just idx' =>
               Unbalanced (A arr.size (updateAt idx' (updateTree subidx (down sh)) arr.arr)) sizes
    updateTree i _ (Leaf arr)              =
      let i' = the Nat (cast ((the Int (cast i)) .&. (the Int (cast blockmask))))
        in case tryNatToFin i' of
             Nothing =>
               assert_total $ idris_crash "Data.RRBVector.update: can't convert Nat to Fin"
             Just i'' =>
               Leaf (A arr.size (setAt i'' x arr.arr))

||| Adjust the element at the index by applying the function to it.
||| If the index is out of range, the original vector is returned. O(log n)
partial
export
adjust : Nat -> (a -> a) -> RRBVector a -> RRBVector a
adjust _ _ Empty                 = Empty
adjust i f v@(Root size sh tree) =
  case compare i 0 of
    LT =>
      v -- index out of range
    GT =>
      case compare i size of
        EQ =>
          v -- index out of range
        GT =>
          v -- index out of range
        LT =>
          Root size sh (adjustTree i sh tree)
    EQ =>
      case compare i size of
        EQ =>
          v
        GT =>
          v
        LT =>
          Root size sh (adjustTree i sh tree)
  where
    adjustTree : Nat -> Nat -> Tree a -> Tree a
    adjustTree i sh (Balanced arr)         =
      case tryNatToFin (radixIndex i sh) of
        Nothing =>
          assert_total $ idris_crash "Data.RRBVector.adjust: can't convert Nat to Fin"
        Just i' =>
          Balanced (A arr.size (updateAt i' (adjustTree i (down sh)) arr.arr))
    adjustTree i sh (Unbalanced arr sizes) =
      let (idx, subidx) = relaxedRadixIndex sizes i sh
        in case tryNatToFin idx of
             Nothing   =>
               assert_total $ idris_crash "Data.RRBVector.adjust: can't convert Nat to Fin"
             Just idx' =>
               Unbalanced (A arr.size (updateAt idx' (adjustTree subidx (down sh)) arr.arr)) sizes
    adjustTree i _ (Leaf arr)              =
      let i' = the Nat (cast ((the Int (cast i)) .&. (the Int (cast blockmask))))
        in case tryNatToFin i' of
             Nothing =>
               assert_total $ idris_crash "Data.RRBVector.adjust: can't convert Nat to Fin"
             Just i'' =>
               Leaf (A arr.size (updateAt i'' f arr.arr))








{-
--------------------------------------------------------------------------------
--          Folds
--------------------------------------------------------------------------------

||| Fold the values in the map using the given left-associative binary operator. O(n)
export
foldl : (v -> w -> v) -> v -> Map k w -> v
foldl f z Tip             = z
foldl f z (Bin _ _ x l r) = foldl f (f (foldl f z l) x) r

||| Fold the values in the map using the given right-associative binary operator. O(n)
export
foldr : (v -> w -> w) -> w -> Map k v -> w
foldr f z Tip             = z
foldr f z (Bin _ _ x l r) = foldr f (f x (foldr f z r)) l

||| Fold the keys and values in the map using the given left-associative binary operator. O(n)
export
foldlWithKey : (v -> k -> w -> v) -> v -> Map k w -> v
foldlWithKey f z Tip              = z
foldlWithKey f z (Bin _ kx x l r) = foldlWithKey f (f (foldlWithKey f z l) kx x) r

||| Fold the keys and values in the map using the given right-associative binary operator. O(n)
export
foldrWithKey : (k -> v -> w -> w) -> w -> Map k v -> w
foldrWithKey f z Tip              = z
foldrWithKey f z (Bin _ kx x l r) = foldrWithKey f (f kx x (foldrWithKey f z r)) l

--------------------------------------------------------------------------------
--          Insertion
--------------------------------------------------------------------------------

||| Insert a new key and value in the map.
||| If the key is already present in the map, the associated value is
||| replaced with the supplied value. O(log n)
export
insert : Eq (Map k v) => Eq v => Ord k => k -> v -> Map k v -> Map k v
insert kx0 vx0 m = go kx0 kx0 vx0 m
  where
    go : k -> k -> v -> Map k v -> Map k v
    go orig _  x Tip                 = singleton orig x
    go orig kx x t@(Bin sz ky y l r) =
      case compare kx ky of
        LT =>
          let l' = go orig kx x l
            in case l' == l of
                 True  =>
                   t
                 False =>
                   balanceL ky y l' r
        GT =>
          let r' = go orig kx x r
            in case r' == r of
                 True  =>
                   t
                 False =>
                   balanceR ky y l r'
        EQ =>
          case (x == y && orig == ky) of
            True  =>
              t
            False =>
              Bin sz orig x l r

private
insertR : Eq (Map k v) => Eq v => Ord k => k -> v -> Map k v -> Map k v
insertR kx0 = go kx0 kx0
  where
    go : k -> k -> v -> Map k v -> Map k v
    go orig _  x Tip                = singleton orig x
    go orig kx x t@(Bin _ ky y l r) =
      case compare kx ky of
        LT =>
          let l' = go orig kx x l
            in case l' == l of
                 True  =>
                   t
                 False =>
                   balanceL ky y l' r
        GT =>
          let r' = go orig kx x r
            in case r' == r of
                 True  =>
                   t
                 False =>
                   balanceR ky y l r'
        EQ =>
          t

||| Insert with a function, combining new value and old value.
||| insertWith f key value mp
||| will insert the pair (key, value) into mp if key does
||| not exist in the map. If the key does exist, the function will
||| insert the pair (key, f new_value old_value). O(log n)
export
insertWith : Ord k => (v -> v -> v) -> k -> v -> Map k v -> Map k v
insertWith = go
  where
    go : (a -> a -> a) -> k -> a -> Map k a -> Map k a
    go _ kx x Tip               = singleton kx x
    go f kx x (Bin sy ky y l r) =
      case compare kx ky of
        LT =>
          balanceL ky y (go f kx x l) r
        GT =>
          balanceR ky y l (go f kx x r)
        EQ =>
          Bin sy kx (f x y) l r

private
insertWithR : Ord k => (v -> v -> v) -> k -> v -> Map k v -> Map k v
insertWithR = go
  where
    go : (v -> v -> v) -> k -> v -> Map k v -> Map k v
    go _ kx x Tip               = singleton kx x
    go f kx x (Bin sy ky y l r) =
      case compare kx ky of
        LT =>
          balanceL ky y (go f kx x l) r
        GT =>
          balanceR ky y l (go f kx x r)
        EQ =>
          Bin sy ky (f y x) l r

private
insertWithKeyR : Ord k => (k -> v -> v -> v) -> k -> v -> Map k v -> Map k v
insertWithKeyR = go
  where
    go : (k -> v -> v -> v) -> k -> v -> Map k v -> Map k v
    go _ kx x Tip               = singleton kx x
    go f kx x (Bin sy ky y l r) =
      case compare kx ky of
        LT => balanceL ky y (go f kx x l) r
        GT => balanceR ky y l (go f kx x r)
        EQ => Bin sy ky (f ky y x) l r

||| Insert with a function, combining key, new value and old value.
||| insertWithKey f key value mp
||| will insert the pair (key, value) into mp if key does
||| not exist in the map. If the key does exist, the function will
||| insert the pair (key,f key new_value old_value). O(log n)
export
insertWithKey : Ord k => (k -> v -> v -> v) -> k -> v -> Map k v -> Map k v
insertWithKey = go
  where
    go : (k -> v -> v -> v) -> k -> v -> Map k v -> Map k v
    go _ kx x Tip               = singleton kx x
    go f kx x (Bin sy ky y l r) =
      case compare kx ky of
        LT => balanceL ky y (go f kx x l) r
        GT => balanceR ky y l (go f kx x r)
        EQ => Bin sy kx (f kx x y) l r

||| Combines insert operation with old value retrieval.
||| The expression (insertLookupWithKey f k x map)
||| is a pair where the first element is equal to (lookup k map)
||| and the second element equal to (insertWithKey f k x map). O(log n)
export
insertLookupWithKey : Ord k => (k -> v -> v -> v) -> k -> v -> Map k v -> (Maybe v,Map k v)
insertLookupWithKey f0 k0 x0 = go f0 k0 x0
  where
    go : (k -> a -> a -> a) -> k -> a -> Map k a -> (Maybe a,Map k a)
    go _ kx x Tip               = (Nothing,singleton kx x)
    go f kx x (Bin sy ky y l r) =
      case compare kx ky of
        LT => let (found,l') = go f kx x l
                  t'         = balanceL ky y l' r
                in (found,t')
        GT => let (found,r') = go f kx x r
                  t'         = balanceR ky y l r'
                in (found,t')
        EQ => (Just y,Bin sy kx (f kx x y) l r)

--------------------------------------------------------------------------------
--          Deletion/Update
--------------------------------------------------------------------------------

||| Delete a key and its value from the map. When the key is not
||| a member of the map, the original map is returned. O(log n)
export
delete : Eq (Map k v) => Eq k => Ord k => k -> Map k v -> Map k v
delete = go
  where
    go : k -> Map k v -> Map k v
    go _ Tip                = Tip
    go k t@(Bin _ kx x l r) =
      case compare k kx of
        LT =>
          let l' = go k l
            in case l' == l of
                 True  =>
                   t
                 False =>
                   balanceR kx x l' r
        GT =>
          let r' = go k r
            in case r' == r of
                 True  =>
                   t
                 False =>
                   balanceL kx x l r'
        EQ =>
          glue l r

||| Adjust a value at a specific key. When the key is not
||| a member of the map, the original map is returned. O(log n)
export
adjustWithKey : Ord k => (k -> v -> v) -> k -> Map k v -> Map k v
adjustWithKey = go
  where
    go : (k -> v -> v) -> k -> Map k v -> Map k v
    go _ _ Tip               = Tip
    go f k (Bin sx kx x l r) =
      case compare k kx of
        LT =>
          Bin sx kx x (go f k l) r
        GT =>
          Bin sx kx x l (go f k r)
        EQ =>
          Bin sx kx (f kx x) l r

||| Update a value at a specific key with the result of the provided function.
||| When the key is not a member of the map, the original map is returned. O(log n)
export
adjust : Ord k => (v -> v) -> k -> Map k v -> Map k v
adjust f = adjustWithKey (\_, x => f x)

||| The expression (updateWithKey f k map) updates the
||| value x at k (if it is in the map). If (f k x) is Nothing,
||| the element is deleted. If it is (Just y), the key k is bound
||| to the new value y. O(log n)
export
updateWithKey : Ord k => (k -> v -> Maybe v) -> k -> Map k v -> Map k v
updateWithKey = go
  where
    go : (k -> v -> Maybe v) -> k -> Map k v -> Map k v
    go _ _ Tip               = Tip
    go f k (Bin sx kx x l r) =
      case compare k kx of
        LT =>
          balanceR kx x (go f k l) r
        GT =>
          balanceL kx x l (go f k r)
        EQ =>
          case f kx x of
            Just x' =>
              Bin sx kx x' l r
            Nothing =>
              glue l r

||| The expression (update f k map) updates the value x
||| at k (if it is in the map). If (f x) is Nothing, the element is
||| deleted. If it is (Just y), the key k is bound to the new value y. O(log n)
export
update : Ord k => (v -> Maybe v) -> k -> Map k v -> Map k v
update f = updateWithKey (\_, x => f x)

||| Lookup and update. See also updateWithKey.
||| The function returns changed value, if it is updated.
||| Returns the original key value if the map entry is deleted. O(log n)
export
updateLookupWithKey : Ord k => (k -> v -> Maybe v) -> k -> Map k v -> (Maybe v,Map k v)
updateLookupWithKey f0 k0 = go f0 k0
 where
   go : (k -> v -> Maybe v) -> k -> Map k v -> (Maybe v,Map k v)
   go _ _ Tip               = (Nothing,Tip)
   go f k (Bin sx kx x l r) =
     case compare k kx of
       LT =>
         let (found,l') = go f k l
             t'         = balanceR kx x l' r
           in (found,t')
       GT =>
         let (found,r') = go f k r
             t'         = balanceL kx x l r'
           in (found,t')
       EQ =>
         case f kx x of
           Just x' =>
             (Just x',Bin sx kx x' l r)
           Nothing =>
             let glued = glue l r
               in (Just x,glued)

||| The expression (alter f k map) alters the value x at k, or absence thereof.
||| alter can be used to insert, delete, or update a value in a Map. O(log n)
export
alter : Ord k => (Maybe v -> Maybe v) -> k -> Map k v -> Map k v
alter = go
  where
    go : (Maybe v -> Maybe v) -> k -> Map k v -> Map k v
    go f k Tip               =
      case f Nothing of
        Nothing => Tip
        Just x  => singleton k x
    go f k (Bin sx kx x l r) =
      case compare k kx of
        LT =>
          balance kx x (go f k l) r
        GT =>
          balance kx x l (go f k r)
        EQ =>
          case f (Just x) of
            Just x' => Bin sx kx x' l r
            Nothing => glue l r

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Lookup the value at a key in the map.
||| The function will return the corresponding value as (Just value),
||| or Nothing if the key isn't in the map. O(log n)
export
lookup : Ord k => k -> Map k v -> Maybe v
lookup = go
  where
    go : k -> Map k v -> Maybe v
    go _ Tip              =
      Nothing
    go k (Bin _ kx x l r) =
      case compare k kx of
        LT => go k l
        GT => go k r
        EQ => Just x

||| Find the value at a key.
||| Returns Nothing when the element can not be found. O(log n)
export
(!?) : Ord k => Map k v -> k -> Maybe v
(!?) m k = lookup k m

||| Is the key a member of the map? See also notMember. O(log n)
export
member : Ord k => k -> Map k v -> Bool
member _ Tip              = False
member k (Bin _ kx _ l r) =
  case compare k kx of
    LT => member k l
    GT => member k r
    EQ => True

||| Is the key not a member of the map? See also member. O(log n)
export
notMember : Ord k => k -> Map k v -> Bool
notMember k m = not $ member k m

||| Find the value at a key.
||| Calls idris_crash when the element can not be found. O(log n)
export
partial
find : Ord k => k -> Map k v -> v
find _ Tip              = assert_total $ idris_crash "Map.!: given key is not an element in the map"
find k (Bin _ kx x l r) =
  case compare k kx of
    LT => find k l
    GT => find k r
    EQ => x

||| Find the value at a key.
||| Calls idris_crash when the element can not be found. O(log n)
export
partial
(!!) : Ord k => Map k v -> k -> v
(!!) m k = find k m

||| The expression (findWithDefault def k map) returns
||| the value at key k or returns default value def
||| when the key is not in the map. O(log n)
export
findWithDefault : Ord k => v -> k -> Map k v -> v
findWithDefault def _ Tip              = def
findWithDefault def k (Bin _ kx x l r) =
  case compare k kx of
    LT => findWithDefault def k l
    GT => findWithDefault def k r
    EQ => x

||| Find largest key smaller than the given one and return the
||| corresponding (key, value) pair. O(log n)
export
lookupLT : Ord k => k -> Map k v -> Maybe (k,v)
lookupLT = goNothing
  where
    goJust : k -> k -> v -> Map k v -> Maybe (k,v)
    goJust _ kx' x' Tip              = Just (kx',x')
    goJust k kx' x' (Bin _ kx x l r) =
      case k <= kx of
        True  => goJust k kx' x' l
        False => goJust k kx x r
    goNothing : k -> Map k v -> Maybe (k,v)
    goNothing _ Tip              = Nothing
    goNothing k (Bin _ kx x l r) =
      case k <= kx of
        True  => goNothing k l
        False => goJust k kx x r

||| Find smallest key greater than the given one and return the
||| corresponding (key, value) pair. O(log n)
export
lookupGT : Ord k => k -> Map k v -> Maybe (k,v)
lookupGT = goNothing
  where
    goJust : k -> k -> v -> Map k v -> Maybe (k,v)
    goJust _ kx' x' Tip              = Just (kx',x')
    goJust k kx' x' (Bin _ kx x l r) =
      case k < kx of
        True  => goJust k kx x l
        False => goJust k kx' x' r
    goNothing : k -> Map k v -> Maybe (k,v)
    goNothing _ Tip              = Nothing
    goNothing k (Bin _ kx x l r) =
      case k < kx of
        True  => goJust k kx x l
        False => goNothing k r

||| Find largest key smaller or equal to the given one and return
||| the corresponding (key, value) pair. O(log n)
export
lookupLE : Ord k => k -> Map k v -> Maybe (k,v)
lookupLE = goNothing
  where
    goJust : k -> k -> v -> Map k v -> Maybe (k,v)
    goJust _ kx' x' Tip              = Just (kx',x')
    goJust k kx' x' (Bin _ kx x l r) =
      case compare k kx of
        LT => goJust k kx' x' l
        EQ => Just (kx,x)
        GT => goJust k kx x r
    goNothing : k -> Map k v -> Maybe (k,v)
    goNothing _ Tip              = Nothing
    goNothing k (Bin _ kx x l r) =
      case compare k kx of
        LT => goNothing k l
        EQ => Just (kx,x)
        GT => goJust k kx x r

||| Find smallest key greater or equal to the given one and return
||| the corresponding (key, value) pair. O(log n)
export
lookupGE : Ord k => k -> Map k v -> Maybe (k,v)
lookupGE = goNothing
  where
    goJust : k -> k -> v -> Map k v -> Maybe (k,v)
    goJust _ kx' x' Tip              = Just (kx',x')
    goJust k kx' x' (Bin _ kx x l r) =
      case compare k kx of
        LT => goJust k kx x l
        EQ => Just (kx,x)
        GT => goJust k kx' x' r
    goNothing : k -> Map k v -> Maybe (k,v)
    goNothing _ Tip              = Nothing
    goNothing k (Bin _ kx x l r) =
      case compare k kx of
        LT => goJust k kx x l
        EQ => Just (kx,x)
        GT => goNothing k r

--------------------------------------------------------------------------------
--          Size
--------------------------------------------------------------------------------

||| Is the map empty? O(1)
export
null : Map k v -> Bool
null Tip = True
null _   = False

--------------------------------------------------------------------------------
--          Filter
--------------------------------------------------------------------------------

private
splitMember : Ord k => k -> Map k v -> (Map k v,Bool,Map k v)
splitMember k0 m = go k0 m
  where
    go : k -> Map k v -> (Map k v,Bool,Map k v)
    go k t =
      case t of
        Tip            =>
          (Tip,False,Tip)
        Bin _ kx x l r =>
          case compare k kx of
            LT => let (lt,z,gt) = go k l
                    in (lt,z,link kx x gt r)
            GT => let (lt,z,gt) = go k r
                    in (link kx x l lt,z,gt)
            EQ => (l,True,r)

||| Decompose a map into pieces based on the structure of the underlying tree.
||| This function is useful for consuming a map in parallel. O(1)
export
splitRoot : Map k v -> List (Map k v)
splitRoot orig =
  case orig of
    Tip           =>
      []
    Bin _ k v l r =>
      [l,singleton k v,r]

||| The expression (splitLookup k map) splits a map just
||| like split but also returns lookup k map. O(log n)
export
splitLookup : Ord k => k -> Map k v -> (Map k v,Maybe v,Map k v)
splitLookup k0 m = go k0 m
  where
    go : k -> Map k v -> (Map k v,Maybe v,Map k v)
    go k t =
      case t of
        Tip            =>
          (Tip,Nothing,Tip)
        Bin _ kx x l r =>
          case compare k kx of
          LT => let (lt,z,gt) = go k l
                  in (lt,z,link kx x gt r)
          GT => let (lt,z,gt) = go k r
                  in (link kx x l lt,z,gt)
          EQ => (l,Just x,r)

||| The expression (split k map) is a pair (map1,map2) where
||| the keys in map1 are smaller than k and the keys in map2 larger than k.
||| Any key equal to k is found in neither map1 nor map2. O(log n)
export
split : Ord k => k -> Map k v -> (Map k v,Map k v)
split k0 t0 = go k0 t0
  where
    go : k -> Map k v -> (Map k v,Map k v)
    go k t =
      case t of
        Tip            =>
          (Tip,Tip)
        Bin _ kx x l r =>
          case compare k kx of
            LT => let (lt,gt) = go k l
                    in (lt,link kx x gt r)
            GT => let (lt,gt) = go k r
                    in (link kx x l lt,gt)
            EQ => (l,r)

||| Filter all keys/values that satisfy the predicate. O(n)
export
filterWithKey : Eq (Map k v) => (k -> v -> Bool) -> Map k v -> Map k v
filterWithKey _ Tip                = Tip
filterWithKey p t@(Bin _ kx x l r) =
  case p kx x of
    True  =>
      case (filterWithKey p l) == l && (filterWithKey p r) == r of
        True  =>
          t
        False =>
          link kx x (filterWithKey p l) (filterWithKey p r)
    False =>
      link2 (filterWithKey p l) (filterWithKey p r)

||| Filter all values that satisfy the predicate. O(n)
export
filter : Eq (Map k v) => (v -> Bool) -> Map k v -> Map k v
filter p m = filterWithKey (\_, x => p x) m

||| Partition the map according to a predicate. The first
||| map contains all elements that satisfy the predicate, the second all
||| elements that fail the predicate. See also split. O(n)
export
partitionWithKey : Eq (Map k v) => (k -> v -> Bool) -> Map k v -> (Map k v,Map k v)
partitionWithKey p0 t0 = go p0 t0
  where
    go : (k -> v -> Bool) -> Map k v -> (Map k v,Map k v)
    go _ Tip                = (Tip,Tip)
    go p t@(Bin _ kx x l r) =
      case p kx x of
        True  =>
          ( case (fst $ go p l) == l && (fst $ go p r) == r of
             True  =>
               t
             False =>
               link kx x (fst $ go p l) (fst $ go p r)
          , link2 (snd $ go p l) (snd $ go p r)
          )
        False =>
          ( link2 (fst $ go p l) (fst $ go p r)
          , case (snd $ go p l) == l && (snd $ go p r) == r of
              True  =>
                t
              False =>
                link kx x (snd $ go p l) (snd $ go p r)
          )

||| Take while a predicate on the keys holds.
||| The user is responsible for ensuring that for all keys j and k in the map,
||| j < k ==> p j >= p k. See note at spanAntitone. O(log n)
export
takeWhileAntitone : (k -> Bool) -> Map k v -> Map k v
takeWhileAntitone _ Tip              = Tip
takeWhileAntitone p (Bin _ kx x l r) =
  case p kx of
    True  =>
      link kx x l (takeWhileAntitone p r)
    False =>
      takeWhileAntitone p l

||| Drop while a predicate on the keys holds.
||| The user is responsible for ensuring that for all keys j and k in the map,
||| j < k ==> p j >= p k. See note at spanAntitone. O(log n)
export
dropWhileAntitone : (k -> Bool) -> Map k v -> Map k v
dropWhileAntitone _ Tip              = Tip
dropWhileAntitone p (Bin _ kx x l r) =
  case p kx of
    True  =>
      dropWhileAntitone p r
    False =>
      link kx x (dropWhileAntitone p l) r

||| Divide a map at the point where a predicate on the keys stops holding.
||| The user is responsible for ensuring that for all keys j and k in the map,
||| j < k ==> p j>= p k. O(log n)
export
spanAntitone : (k -> Bool) -> Map k v -> (Map k v, Map k v)
spanAntitone p0 m = go p0 m
  where
    go : (k -> Bool) -> Map k v -> (Map k v,Map k v)
    go _ Tip              = (Tip,Tip)
    go p (Bin _ kx x l r) =
      case p kx of
        True  =>
          let (u,v) = go p r
            in (link kx x l u,v)
        False =>
          let (u,v) = go p l
            in (u,link kx x v r)

||| Map keys/values and collect the Just results. O(n)
export
mapMaybeWithKey : (k -> a -> Maybe b) -> Map k a -> Map k b
mapMaybeWithKey _ Tip              = Tip
mapMaybeWithKey f (Bin _ kx x l r) =
  case f kx x of
    Just y  =>
      link kx y (mapMaybeWithKey f l) (mapMaybeWithKey f r)
    Nothing =>
      link2 (mapMaybeWithKey f l) (mapMaybeWithKey f r)

||| Map values and collect the Just results. O(n)
export
mapMaybe : (a -> Maybe b) -> Map k a -> Map k b
mapMaybe f = mapMaybeWithKey (\_, x => f x)

||| Map keys/values and separate the Left and Right results. O(n)
export
mapEitherWithKey : (k -> a -> Either b c) -> Map k a -> (Map k b, Map k c)
mapEitherWithKey f0 t0 = go f0 t0
  where
    go : (k -> a -> Either b c) -> Map k a -> (Map k b,Map k c)
    go _ Tip              = (Tip,Tip)
    go f (Bin _ kx x l r) =
      case f kx x of
        Left  y => (link kx y (fst $ go f l) (fst $ go f r),link2 (snd $ go f l) (snd $ go f r))
        Right z => (link2 (fst $ go f l) (fst $ go f r),link kx z (snd $ go f l) (snd $ go f r))

||| Map values and separate the Left and Right results. O(n)
export
mapEither : (a -> Either b c) -> Map k a -> (Map k b, Map k c)
mapEither f m = mapEitherWithKey (\_, x => f x) m

--------------------------------------------------------------------------------
--          Submap
--------------------------------------------------------------------------------

private
submap' : Ord a => (b -> c -> Bool) -> Map a b -> Map a c -> Bool
submap' _ Tip _              = True
submap' _ _   Tip            = False
submap' f (Bin 1 kx x _ _) t =
  case lookup kx t of
    Just y  =>
      f x y
    Nothing =>
      False
submap' f (Bin _ kx x l r) t =
  let (lt,found,gt) = splitLookup kx t
    in case found of
         Nothing =>
           False
         Just y  =>
           f x y && size l <= size lt
                 && size r <= size gt
                 && submap' f l lt
                 && submap' f r gt

||| The expression (isSubmapOfBy f t1 t2) returns True if
||| all keys in t1 are in tree t2, and when f returns True when
||| applied to their respective values.
export
isSubmapOfBy : Ord k => (a -> b -> Bool) -> Map k a -> Map k b -> Bool
isSubmapOfBy f t1 t2 = size t1 <= size t2 && submap' f t1 t2

||| This function is defined as (isSubmapOf = isSubmapOfBy (==)).
export
isSubmapOf : Eq v => Ord k => Map k v -> Map k v -> Bool
isSubmapOf m1 m2 = isSubmapOfBy (==) m1 m2

||| Is this a proper submap? (ie. a submap but not equal).
||| The expression (isProperSubmapOfBy f m1 m2) returns True when
||| keys m1 and keys m2 are not equal,
||| all keys in m1 are in m2, and when f returns True when
||| applied to their respective values.
export
isProperSubmapOfBy : Ord k => (a -> b -> Bool) -> Map k a -> Map k b -> Bool
isProperSubmapOfBy f t1 t2 = size t1 < size t2 && submap' f t1 t2

||| Is this a proper submap? (ie. a submap but not equal).
||| Defined as (isProperSubmapOf = isProperSubmapOfBy (==)).
export
isProperSubmapOf : Eq v => Ord k => Map k v -> Map k v -> Bool
isProperSubmapOf m1 m2 = isProperSubmapOfBy (==) m1 m2

--------------------------------------------------------------------------------
--          Indexed
--------------------------------------------------------------------------------

||| Lookup the index of a key, which is its zero-based index in
||| the sequence sorted by keys. The index is a number from 0 up to, but not
||| including, the size of the map. O(log n)
export
lookupIndex : Ord k => k -> Map k v -> Maybe Nat
lookupIndex = go 0
  where
    go : Nat -> k -> Map k a -> Maybe Nat
    go _  _ Tip               = Nothing
    go idx k (Bin _ kx _ l r) =
      case compare k kx of
        LT =>
          go idx k l
        GT =>
          go (idx + size l + 1) k r
        EQ =>
          Just $ idx + size l

||| Return the index of a key, which is its zero-based index in
||| the sequence sorted by keys. The index is a number from 0 up to, but not
||| including, the size of the map. Calls idris_crash when the key is not
||| a member of the map. O(log n)
export
partial
findIndex : Ord k => k -> Map k v -> Nat
findIndex = go 0
  where
    go : Nat -> k -> Map k a -> Nat
    go _   _ Tip              = assert_total $ idris_crash "Map.findIndex: element is not in the map"
    go idx k (Bin _ kx _ l r) =
      case compare k kx of
        LT =>
          go idx k l
        GT =>
          go (idx + size l + 1) k r
        EQ =>
          idx + size l

||| Retrieve an element by its index, i.e. by its zero-based
||| index in the sequence sorted by keys. If the index is out of range (less
||| than zero, greater or equal to size of the map), idris_crash is called. O(log n)
export
partial
elemAt : Nat -> Map k v -> (k,v)
elemAt _ Tip              = assert_total $ idris_crash "Map.elemAt: index out of range"
elemAt i (Bin _ kx x l r) =
  case compare i (size l) of
     LT =>
       elemAt i l
     GT =>
       elemAt ((i `minus` (size l)) `minus` 1) r
     EQ =>
       (kx,x)

||| Update the element at index, i.e. by its zero-based index in
||| the sequence sorted by keys. If the index is out of range (less than zero,
||| greater or equal to size of the map), idris_crash is called. O(log n)
export
partial
updateAt : (k -> v -> Maybe v) -> Nat -> Map k v -> Map k v
updateAt f i t =
  case t of
    Tip             => assert_total $ idris_crash "Map.updateAt: index out of range"
    Bin sx kx x l r =>
      case compare i (size l) of
        LT =>
          balanceR kx x (updateAt f i l) r
        GT =>
          balanceL kx x l (updateAt f ((i `minus` (size l)) `minus` 1) r)
        EQ =>
          case f kx x of
            Just x' =>
              Bin sx kx x' l r
            Nothing =>
              glue l r

||| Delete the element at index, i.e. by its zero-based index in
||| the sequence sorted by keys. If the index is out of range (less than zero,
||| greater or equal to size of the map), idris_crash is called. O(log n)
export
partial
deleteAt : Nat -> Map k v -> Map k v
deleteAt i t =
  case t of
    Tip            => assert_total $ idris_crash "Map.deleteAt: index out of range"
    Bin _ kx x l r =>
      case compare i (size l) of
        LT =>
          balanceR kx x (deleteAt i l) r
        GT =>
          balanceL kx x l (deleteAt ((i `minus` (size l)) `minus` 1) r)
        EQ =>
          glue l r

||| Take a given number of entries in key order, beginning
||| with the smallest keys. O(log n)
export
take : Nat -> Map k v -> Map k v
take i m =
  case i >= size m of
    True  =>
      m
    False =>
      go i m
  where
    go : Nat -> Map k v -> Map k v
    go _ Tip              = Tip
    go i (Bin _ kx x l r) =
      case i <= 0 of
        True  =>
          Tip
        False =>
          case compare i (size l) of
            LT =>
              go i l
            GT =>
              link kx x l (go ((i `minus` (size l)) `minus` 1) r)
            EQ =>
              l

||| Drop a given number of entries in key order, beginning
||| with the smallest keys. O(log n)
export
drop : Nat -> Map k v -> Map k v
drop i m =
  case i >= size m of
    True  =>
      Tip
    False =>
      go i m
  where
    go : Nat -> Map k v -> Map k v
    go _ Tip              = Tip
    go i (Bin _ kx x l r) =
      case i <= 0 of
        True  =>
          m
        False =>
          case compare i (size l) of
            LT =>
              link kx x (go i l) r
            GT =>
              go ((i `minus` (size l)) `minus` 1) r
            EQ =>
              insertMin kx x r

||| Split a map at a particular index. O(log n)
export
splitAt : Nat -> Map k v -> (Map k v, Map k v)
splitAt i m =
  case i >= size m of
    True  =>
      (m,Tip)
    False =>
      go i m
  where
    go : Nat -> Map k v -> (Map k v,Map k v)
    go _ Tip              = (Tip,Tip)
    go i (Bin _ kx x l r) =
      case i <= 0 of
        True  =>
          (Tip,m)
        False =>
          case compare i (size l) of
            LT =>
              case go i l of
                (ll,lr) =>
                  (ll,link kx x lr r)
            GT =>
              case go ((i `minus` (size l)) `minus` 1) r of
                (rl,rr) =>
                  (link kx x l rl,rr)
            EQ =>
              (l,insertMin kx x r)

--------------------------------------------------------------------------------
--          Min/Max
--------------------------------------------------------------------------------

private
lookupMinSure : k -> v -> Map k v -> (k,v)
lookupMinSure k v Tip             = (k,v)
lookupMinSure _ _ (Bin _ k v l _) = lookupMinSure k v l

||| The minimal key of the map. Returns Nothing if the map is empty. O(log n)
export
lookupMin : Map k v -> Maybe (k,v)
lookupMin Tip             = Nothing
lookupMin (Bin _ k v l _) = Just $ lookupMinSure k v l

private
lookupMaxSure : k -> v -> Map k v -> (k,v)
lookupMaxSure k v Tip             = (k,v)
lookupMaxSure _ _ (Bin _ k v _ r) = lookupMaxSure k v r

||| The maximal key of the map. Returns Nothing if the map is empty. O(log n)
export
lookupMax : Map k v -> Maybe (k,v)
lookupMax Tip             = Nothing
lookupMax (Bin _ k v _ r) = Just $ lookupMaxSure k v r

||| The minimal key of the map. Calls idris_crash if the map is empty. O(log n)
export
partial
findMin : Map k v -> (k,v)
findMin t =
  case lookupMin t of
    Just r  => r
    Nothing => assert_total $ idris_crash "Map.findMin: empty map has no minimal element"

||| The maximal key of the map. Calls idris_crash if the map is empty. O(log n)
export
partial
findMax : Map k v -> (k,v)
findMax t =
  case lookupMax t of
    Just r  => r
    Nothing => assert_total $ idris_crash "Map.findMax: empty map has no maximal element"

||| Delete the minimal key. Returns an empty map if the map is empty. O(log n)
export
deleteMin : Map k v -> Map k v
deleteMin Tip                 = Tip
deleteMin (Bin _ _  _ Tip r)  = r
deleteMin (Bin _ kx x l   r)  = balanceR kx x (deleteMin l) r

||| Delete the maximal key. Returns an empty map if the map is empty. O(log n)
export
deleteMax : Map k v -> Map k v
deleteMax Tip                 = Tip
deleteMax (Bin _ _  _ l Tip)  = l
deleteMax (Bin _ kx x l r)    = balanceL kx x l (deleteMax r)

||| Retrieves the minimal (key,value) pair of the map, and
||| the map stripped of that element, or Nothing if passed an empty map. O(log n)
export
minViewWithKey : Map k v -> Maybe ((k,v),Map k v)
minViewWithKey Tip             = Nothing
minViewWithKey (Bin _ k x l r) =
  Just $
    case minViewSure k x l r of
      MinView' km xm t =>
        ((km,xm),t)

||| Delete and find the minimal element. O(log n)
export
partial
deleteFindMin : Map k v -> ((k,v),Map k v)
deleteFindMin t =
  case minViewWithKey t of
    Just res => res
    Nothing  => (assert_total $ idris_crash "Map.deleteFindMin: can not return the minimal element of an empty map",Tip)

||| Retrieves the maximal (key,value) pair of the map, and
||| the map stripped of that element, or Nothing if passed an empty map. O(log n)
export
maxViewWithKey : Map k v -> Maybe ((k,v),Map k v)
maxViewWithKey Tip             = Nothing
maxViewWithKey (Bin _ k x l r) =
  Just $
    case maxViewSure k x l r of
      MaxView' km xm t =>
        ((km,xm),t)

||| Delete and find the maximal element. O(log n)
export
partial
deleteFindMax : Map k v -> ((k,v),Map k v)
deleteFindMax t =
  case maxViewWithKey t of
    Just res => res
    Nothing  => (assert_total $ idris_crash "Map.deleteFindMax: can not return the maximal element of an empty map",Tip)

||| Update the value at the minimal key. O(log n)
export
updateMinWithKey : (k -> v -> Maybe v) -> Map k v -> Map k v
updateMinWithKey _ Tip                 = Tip
updateMinWithKey f (Bin sx kx x Tip r) =
  case f kx x of
    Nothing => r
    Just x' => Bin sx kx x' Tip r
updateMinWithKey f (Bin _ kx x l r)    =
  balanceR kx x (updateMinWithKey f l) r

||| Update the value at the minimal key. O(log n)
export
updateMin : (v -> Maybe v) -> Map k v -> Map k v
updateMin f m = updateMinWithKey (\_, x => f x) m

||| Update the value at the maximal key. O(log n)
export
updateMaxWithKey : (k -> v -> Maybe v) -> Map k v -> Map k v
updateMaxWithKey _ Tip                 = Tip
updateMaxWithKey f (Bin sx kx x l Tip) =
  case f kx x of
    Nothing => l
    Just x' => Bin sx kx x' l Tip
updateMaxWithKey f (Bin _ kx x l r)    =
  balanceL kx x l (updateMaxWithKey f r)

||| Update the value at the maximal key. O(log n)
export
updateMax : (v -> Maybe v) -> Map k v -> Map k v
updateMax f m = updateMaxWithKey (\_, x => f x) m

||| Retrieves the value associated with minimal key of the
||| map, and the map stripped of that element, or Nothing if passed an empty map. O(log n)
export
minView : Map k v -> Maybe (v,Map k v)
minView t =
  case minViewWithKey t of
    Nothing         => Nothing
    Just ((_,x),t') => Just (x,t')

||| Retrieves the value associated with maximal key of the
||| map, and the map stripped of that element, or Nothing if passed an empty map. O(log n)
export
maxView : Map k v -> Maybe (v,Map k v)
maxView t =
  case maxViewWithKey t of
    Nothing         => Nothing
    Just ((_,x),t') => Just (x,t')

--------------------------------------------------------------------------------
--          Combine
--------------------------------------------------------------------------------

||| The expression (union t1 t2) takes the left-biased union of t1 and t2.
||| It prefers t1 when duplicate keys are encountered.
export
union : Eq (Map k v) => Eq v => Ord k => Map k v -> Map k v -> Map k v
union t1                     Tip                 = t1
union t1                     (Bin _ k x Tip Tip) = insertR k x t1
union (Bin _ k x Tip Tip)    t2                  = insert k x t2
union Tip                    t2                  = t2
union t1@(Bin _ k1 x1 l1 r1) t2                  =
  case split k1 t2 of
    (l2,r2) =>
      case (union l1 l2) == l1 && (union r1 r2) == r1 of
        True  =>
          t1
        False =>
          link k1 x1 (union l1 l2) (union r1 r2)

||| Union with a combining function.
export
unionWith : Ord k => (v -> v -> v) -> Map k v -> Map k v -> Map k v
unionWith _ t1                  Tip                 = t1
unionWith f t1                  (Bin _ k x Tip Tip) = insertWithR f k x t1
unionWith f (Bin _ k x Tip Tip) t2                  = insertWith f k x t2
unionWith _ Tip                 t2                  = t2
unionWith f (Bin _ k1 x1 l1 r1) t2                  =
  case splitLookup k1 t2 of
    (l2,mb,r2) =>
      case mb of
        Nothing => link k1 x1 (unionWith f l1 l2) (unionWith f r1 r2)
        Just x2 => link k1 (f x1 x2) (unionWith f l1 l2) (unionWith f r1 r2)

||| Union with a combining function.
export
unionWithKey : Ord k => (k -> v -> v -> v) -> Map k v -> Map k v -> Map k v
unionWithKey _ t1                  Tip                 = t1
unionWithKey f t1                  (Bin _ k x Tip Tip) = insertWithKeyR f k x t1
unionWithKey f (Bin _ k x Tip Tip) t2                  = insertWithKey f k x t2
unionWithKey _ Tip                 t2                  = t2
unionWithKey f (Bin _ k1 x1 l1 r1) t2                  =
  case splitLookup k1 t2 of
    (l2,mb,r2) =>
      case mb of
        Nothing => link k1 x1 (unionWithKey f l1 l2) (unionWithKey f r1 r2)
        Just x2 => link k1 (f k1 x1 x2) (unionWithKey f l1 l2) (unionWithKey f r1 r2)

||| The union of a list of maps.
export
unions : Eq (Map k v) => Eq v => Foldable f => Ord k => f (Map k v) -> Map k v
unions ts = foldl union empty ts

||| The union of a list of maps, with a combining operation.
export
unionsWith : Foldable f => Ord k => (v -> v -> v) -> f (Map k v) -> Map k v
unionsWith f ts = foldl (unionWith f) empty ts

--------------------------------------------------------------------------------
--          Difference
--------------------------------------------------------------------------------

||| Difference of two maps.
||| Return elements of the first map not existing in the second map.
export
difference : Ord k => Map k a -> Map k b -> Map k a
difference Tip _                = Tip
difference t1 Tip               = t1
difference t1 (Bin _ k _ l2 r2) =
  case split k t1 of
    (l1,r1) =>
      case size (difference l1 l2) + size (difference r1 r2) == size t1 of
        True  =>
          t1
        False =>
          link2 (difference l1 l2) (difference r1 r2)

||| Same as difference.
export
(\\) : Ord k => Map k a -> Map k b -> Map k a
m1 \\ m2 = difference m1 m2

--------------------------------------------------------------------------------
--          Intersection
--------------------------------------------------------------------------------

||| Intersection of two maps.
||| Return data in the first map for the keys existing in both maps.
export
intersection : Eq (Map k a) => Ord k => Map k a -> Map k b -> Map k a
intersection Tip                  _   = Tip
intersection _                    Tip = Tip
intersection t1@(Bin _ k x l1 r1) t2  =
  case splitMember k t2 of
    (l2,True,r2) =>
      case (intersection l1 l2) == l1 && (intersection r1 r2) == r1 of
        True  =>
          t1
        False =>
          link k x (intersection l1 l2) (intersection r1 r2)
    (l2,False,r2) =>
      link2 (intersection l1 l2) (intersection r1 r2)

||| Intersection with a combining function.
export
intersectionWith : Ord k => (a -> b -> c) -> Map k a -> Map k b -> Map k c
intersectionWith f Tip                _   = Tip
intersectionWith f _                  Tip = Tip
intersectionWith f (Bin _ k x1 l1 r1) t2  =
  case splitLookup k t2 of
    (l2,Just x2,r2) =>
      link k (f x1 x2) (intersectionWith f l1 l2) (intersectionWith f r1 r2)
    (l2,Nothing,r2) =>
      link2 (intersectionWith f l1 l2) (intersectionWith f r1 r2)

||| Intersection with a combining function.
export
intersectionWithKey : Ord k => (k -> a -> b -> c) -> Map k a -> Map k b -> Map k c
intersectionWithKey f Tip                _   = Tip
intersectionWithKey f _                  Tip = Tip
intersectionWithKey f (Bin _ k x1 l1 r1) t2  =
  case splitLookup k t2 of
    (l2,Just x2,r2) =>
      link k (f k x1 x2) (intersectionWithKey f l1 l2) (intersectionWithKey f r1 r2)
    (l2,Nothing,r2) =>
      link2 (intersectionWithKey f l1 l2) (intersectionWithKey f r1 r2)

--------------------------------------------------------------------------------
--          Disjoint
--------------------------------------------------------------------------------

||| Check whether the key sets of two
||| maps are disjoint (i.e., their intersection is empty).
export
disjoint : Ord k => Map k a -> Map k b -> Bool
disjoint Tip             _   = True
disjoint _               Tip = True
disjoint (Bin 1 k _ _ _) t   = k `notMember` t
disjoint (Bin _ k _ l r) t   =
  let (lt,found,gt) = splitMember k t
    in not found && disjoint l lt && disjoint r gt

--------------------------------------------------------------------------------
--          Compose
--------------------------------------------------------------------------------

||| Relate the keys of one map to the values of
||| the other, by using the values of the former as keys for lookups in the latter.
||| O(n * log(m)), where m is the size of the first argument.
export
compose : Ord b => Map b c -> Map a b -> Map a c
compose bc ab =
  case null bc of
    True  =>
      empty
    False =>
      mapMaybe ((!?) bc) ab

--------------------------------------------------------------------------------
--          Traversal
--------------------------------------------------------------------------------

||| Map a function over all values in the map. O(n)
export
map : (v -> w) -> Map k v -> Map k w
map _ Tip               = Tip
map f (Bin sx kx x l r) = Bin sx kx (f x) (map f l) (map f r)

||| Map a function over all values in the map. O(n)
export
mapWithKey : (k -> v -> w) -> Map k v -> Map k w
mapWithKey _ Tip               = Tip
mapWithKey f (Bin sx kx x l r) = Bin sx kx (f kx x) (mapWithKey f l) (mapWithKey f r)

||| The function mapAccumL threads an accumulating
||| argument through the map in ascending order of keys. O(n)
export
mapAccumL : (v -> k -> w -> (v,c)) -> v -> Map k w -> (v,Map k c)
mapAccumL _ a Tip               = (a,Tip)
mapAccumL f a (Bin sx kx x l r) =
  let (a1,l') = mapAccumL f a l
      (a2,x') = f a1 kx x
      (a3,r') = mapAccumL f a2 r
  in (a3,Bin sx kx x' l' r')

||| The function mapAccumRWithKey threads an accumulating
||| argument through the map in descending order of keys. O(n)
export
mapAccumRWithKey : (v -> k -> w -> (v,c)) -> v -> Map k w -> (v,Map k c)
mapAccumRWithKey _ a Tip               = (a,Tip)
mapAccumRWithKey f a (Bin sx kx x l r) =
  let (a1,r') = mapAccumRWithKey f a r
      (a2,x') = f a1 kx x
      (a3,l') = mapAccumRWithKey f a2 l
  in (a3,Bin sx kx x' l' r')

||| The function mapAccumWithKey threads an accumulating
||| argument through the map in ascending order of keys. O(n)
export
mapAccumWithKey : (v -> k -> w -> (v,c)) -> v -> Map k w -> (v,Map k c)
mapAccumWithKey f a t = mapAccumL f a t

||| The function mapAccum threads an accumulating
||| argument through the map in ascending order of keys. O(n)
export
mapAccum : (v -> w -> (v,c)) -> v -> Map k w -> (v,Map k c)
mapAccum f a m = mapAccumWithKey (\a', _, x' => f a' x') a m

--------------------------------------------------------------------------------
--          Lists
--------------------------------------------------------------------------------

||| Convert the map to a list of key/value pairs where the keys are in descending order. O(n)
export
toDescList : Map k v -> List (k,v)
toDescList Tip               = []
toDescList t@(Bin _ _ _ _ _) = foldlWithKey (\xs, k, x => (k,x) :: xs) [] t

||| Convert the map to a list of key/value pairs where the keys are in ascending order. O(n)
export
toAscList : Map k v -> List (k,v)
toAscList Tip               = []
toAscList t@(Bin _ _ _ _ _) = foldrWithKey (\k, x, xs => (k,x) :: xs) [] t

||| Convert the map to a list of key/value pairs.
export
toList : Map k v -> List (k,v)
toList = toAscList

||| Build a map from a list of key/value pairs.
||| If the list contains more than one value for the same key, the last value
||| for the key is retained.
||| If the keys of the list are ordered, a linear-time implementation is used. O(n * log(n))
export
partial
fromList : Ord (k, v) => Ord k => List (k, v) -> Map k v
fromList [] = Tip
fromList xs =
  case sorted xs of
    True  =>
      buildBalancedTree (convertToList1 xs) (length xs)
    False =>
      buildBalancedTree (convertToList1 (sort xs)) (length xs)
  where
    -- Calculate the size of a tree
    sizeTree : Map k v -> Nat
    sizeTree Tip              = 0
    sizeTree (Bin sz _ _ _ _) = sz
    -- Convert a list to a List1, which requires the list to be non-empty
    convertToList1 : List (k, v) -> List1 (k, v)
    convertToList1 []        = assert_total $ idris_crash "Unexpected empty list"
    convertToList1 (x :: xs) = x ::: xs
    -- Link a root node with two subtrees
    linkRootWithSubtrees : (k, v) -> Map k v -> Map k v -> Nat -> Map k v
    linkRootWithSubtrees (kx, x) left right newSize =
      Bin newSize kx x left right
    -- Split a non-empty list into left, middle, and right parts
    splitList : List1 (k, v) -> Nat -> (List (k, v), (k, v), List (k, v), Nat)
    splitList l len =
      let half         = len `div` 2
          (left, rest) = splitAt half (forget l)
        in case rest of
             []                =>
               assert_total $ idris_crash "Unexpected empty list"
             (middle :: right) =>
               (left, middle, right, len)
    -- Build a balanced tree from a non-empty list
    buildBalancedTree : List1 (k, v) -> Nat -> Map k v
    buildBalancedTree ((kx, x) ::: []) _   = Bin 1 kx x Tip Tip
    buildBalancedTree xs               len =
      let (left, root, right, totalSize) = splitList xs len
          leftTree = case left of
                       [] =>
                         Tip
                       _  =>
                         assert_total $ buildBalancedTree (convertToList1 left) (length left)
          rightTree = case right of
                        [] =>
                          Tip
                        _  =>
                          assert_total $ buildBalancedTree (convertToList1 right) (length right)
        in linkRootWithSubtrees root leftTree rightTree totalSize

--------------------------------------------------------------------------------
--          Keys
--------------------------------------------------------------------------------

||| Gets the keys of the map.
export
keys : Map k v -> List k
keys = map fst . toList

--------------------------------------------------------------------------------
--          Values
--------------------------------------------------------------------------------

||| Gets the values of the map.
||| Could contain duplicates.
export
values : Map k v -> List v
values = map snd . toList

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Functor (Map k) where
  map f m = map f m

export
Foldable (Map k) where
  foldl f z = foldl f z . values
  foldr f z = foldr f z . values
  null      = null

private
Show k => Show v => Show (List (k, v)) where
  show xs = "[" ++ show' xs ++ "]"
    where
      show'' : (k, v) -> String
      show'' (k, v) = "(" ++ show k ++ ", " ++ show v ++ ")"
      show' : List (k, v) -> String
      show' Nil        = ""
      show' (x :: Nil) = show'' x
      show' (x :: xs)  = show'' x ++ ", " ++ show' xs

export
Show (List (k, v)) => Show (Map k v) where
  show m = "fromList " ++ (show $ toList m)

-}
