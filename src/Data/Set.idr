||| Finite Sets
module Data.Set

import public Data.Set.Internal

import Data.Bits
import Data.List
import Data.List1

%hide Prelude.foldl
%hide Prelude.null
%hide Prelude.toList

%default total

--------------------------------------------------------------------------------
--          Creating Sets
--------------------------------------------------------------------------------

||| The empty set. (O)1
export
empty : Set a
empty = Tip

--------------------------------------------------------------------------------
--          Folds
--------------------------------------------------------------------------------

||| Fold the values in the set using the given left-associative binary operator. O(n)
export
foldl : (a -> b -> a) -> a -> Set b -> a
foldl f z Tip           = z
foldl f z (Bin _ x l r) = foldl f (f (foldl f z l) x) r

||| Fold the values in the set using the given right-associative binary operator. O(n)
export
foldr : (a -> b -> b) -> b -> Set a -> b
foldr f z Tip             = z
foldr f z (Bin _ x l r) = foldr f (f x (foldr f z r)) l

--------------------------------------------------------------------------------
--          Insertion
--------------------------------------------------------------------------------

||| Insert an element in a set.
||| If the set already contains an element equal to the given value,
||| it is replaced with the new value. O(log n)
export
insert : Eq (Set a) => Eq a => Ord a => a -> Set a -> Set a
insert x0 s = go x0 x0 s
  where
    go : a -> a -> Set a -> Set a
    go orig _ Tip              = singleton orig
    go orig x t@(Bin sz y l r) =
      case compare x y of
        LT =>
          case (go orig x l) == l of
            True  =>
              t
            False =>
              balanceL y (go orig x l) r
        GT =>
          case (go orig x r) == r of
            True  =>
              t
            False =>
              balanceR y l (go orig x r)
        EQ =>
          case orig == y of
            True  =>
              t
            False =>
              Bin sz orig l r

private
insertR : Eq (Set a) => Eq a => Ord a => a -> Set a -> Set a
insertR x0 s = go x0 x0 s
  where
    go : a -> a -> Set a -> Set a
    go orig _ Tip             = singleton orig
    go orig x t@(Bin _ y l r) =
      case compare x y of
        LT =>
          case (go orig x l) == l of
            True  =>
              t
            False =>
              balanceL y (go orig x l) r
        GT =>
          case (go orig x r) == r of
            True  =>
              t
            False =>
              balanceR y l (go orig x r)
        EQ =>
          t

--------------------------------------------------------------------------------
--          Deletion
--------------------------------------------------------------------------------

||| Delete an element from a set. When the element is not
||| a member of the set, the original set is returned. O(log n)
export
delete : Eq (Set a) => Eq a => Ord a => a -> Set a -> Set a
delete = go
  where
    go : a -> Set a -> Set a
    go _ Tip                = Tip
    go x t@(Bin _ y l r) =
      case compare x y of
        LT =>
          case (go x l) == l of
            True  =>
              t
            False =>
              balanceR y (go x l) r
        GT =>
          case (go x r) == r of
            True  =>
              t
            False =>
              balanceL y l (go x r)
        EQ =>
          glue l r

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Is the element in the set? O(log n)
export
member : Ord a => a -> Set a -> Bool
member _ Tip           = False
member x (Bin _ y l r) =
  case compare x y of
    LT => member x l
    GT => member x r
    EQ => True

||| Is the element not in the set? O(log n)
export
notMember : Ord a => a -> Set a -> Bool
notMember k m = not $ member k m

||| Find largest element smaller than the given one. O(log n)
export
lookupLT : Ord a => a -> Set a -> Maybe a
lookupLT = goNothing
  where
    goJust : a -> a -> Set a -> Maybe a
    goJust _ best Tip           = Just best
    goJust x best (Bin _ y l r) =
      case x <= y of
        True  => goJust x best l
        False => goJust x y r
    goNothing : a -> Set a -> Maybe a
    goNothing _ Tip           = Nothing
    goNothing x (Bin _ y l r) =
      case x <= y of
        True  => goNothing x l
        False => goJust x y r

||| Find smallest element greater than the given one. O(log n)
export
lookupGT : Ord a => a -> Set a -> Maybe a
lookupGT = goNothing
  where
    goJust : a -> a -> Set a -> Maybe a
    goJust _ best Tip           = Just best
    goJust x best (Bin _ y l r) =
      case x < y of
        True  => goJust x y l
        False => goJust x best r
    goNothing : a -> Set a -> Maybe a
    goNothing _ Tip              = Nothing
    goNothing x (Bin _ y l r) =
      case x < y of
        True  => goJust x y l
        False => goNothing x r

||| Find the largest element smaller or equal to the given one. O(log n)
export
lookupLE : Ord a => a -> Set a -> Maybe a
lookupLE = goNothing
  where
    goJust : a -> a -> Set a -> Maybe a
    goJust _ best Tip           = Just best
    goJust x best (Bin _ y l r) =
      case compare x y of
        LT => goJust x best l
        EQ => Just y
        GT => goJust x y r
    goNothing : a -> Set a -> Maybe a
    goNothing _ Tip           = Nothing
    goNothing x (Bin _ y l r) =
      case compare x y of
        LT => goNothing x l
        EQ => Just y
        GT => goJust x y r

||| Find the smallest element greater or equal to the given one. O(log n)
export
lookupGE : Ord a => a -> Set a -> Maybe a
lookupGE = goNothing
  where
    goJust : a -> a -> Set a -> Maybe a
    goJust _ best Tip           = Just best
    goJust x best (Bin _ y l r) =
      case compare x y of
        LT => goJust x y l
        EQ => Just y
        GT => goJust x best r
    goNothing : a -> Set a -> Maybe a
    goNothing _ Tip           = Nothing
    goNothing x (Bin _ y l r) =
      case compare x y of
        LT => goJust x y l
        EQ => Just y
        GT => goNothing x r

||| Is the set empty? O(1)
export
null : Set a -> Bool
null Tip = True
null _   = False

||| Performs a split but also returns whether
||| the pivot element was found in the original set. O(log n)
export
splitMember : Ord a => a -> Set a -> (Set a,Bool,Set a)
splitMember _ Tip           = (Tip, False, Tip)
splitMember x (Bin _ y l r) =
  case compare x y of
    LT => let (lt, found, gt) = splitMember x l
              gt'             = link y gt r
            in (lt, found, gt')
    GT => let (lt, found, gt) = splitMember x r
              lt'             = link y l lt
            in (lt', found, gt)
    EQ => (l, True, r)

||| Decompose a set into pieces based on the structure of the underlying tree.
||| This function is useful for consuming a set in parallel. O(1)
export
splitRoot : Set a -> List (Set a)
splitRoot orig =
  case orig of
    Tip         =>
      []
    Bin _ v l r =>
      [l, singleton v, r]

||| The expression (split x set) is a pair (set1,set2) where
||| set1 comprises the elements of set less than x and
||| set2 comprises the elements of set greater than x. O(log n)
export
split : Ord a => a -> Set a -> (Set a,Set a)
split _ Tip          = (Tip, Tip)
split x (Bin _ y l r) =
  case compare x y of
    LT => let (lt, gt) = split x l
            in (lt, link y gt r)
    GT => let (lt, gt) = split x r
            in (link y l lt, gt)
    EQ => (l, r)

private
isSubsetOfX : Ord a => Set a -> Set a -> Bool
isSubsetOfX Tip           _   = True
isSubsetOfX _             Tip = False
isSubsetOfX (Bin 1 x _ _) t   = member x t
isSubsetOfX (Bin _ x l r) t   =
  let (lt, found, gt) = splitMember x t
    in found             &&
       size l <= size lt &&
       size r <= size gt &&
       isSubsetOfX l lt  &&
       isSubsetOfX r gt

||| Indicates whether s1 is a subset of s2.
export
isSubsetOf : Ord a => Set a -> Set a -> Bool
isSubsetOf t1 t2 =
  size t1 <= size t2 && isSubsetOfX t1 t2

||| Indicates whether s1 is a proper subset of s2.
export
isProperSubsetOf : Ord a => Set a -> Set a -> Bool
isProperSubsetOf s1 s2 =
  size s1 <= size s2 && isSubsetOfX s1 s2

||| Check whether two sets are disjoint (i.e. their intersection is empty).
export
disjoint : Ord a => Set a -> Set a -> Bool
disjoint Tip           _   = True
disjoint _             Tip = True
disjoint (Bin 1 x _ _) t   = notMember x t
disjoint (Bin _ x l r) t   =
  let (lt, found, gt) = splitMember x t
    in not found     &&
       disjoint l lt &&
       disjoint r gt

--------------------------------------------------------------------------------
--          Merge
--------------------------------------------------------------------------------

private
||| Merges two trees.
merge : Set a -> Set a -> Set a
merge Tip                   r                     = r
merge l                     Tip                   = l
merge l@(Bin sizeL x lx rx) r@(Bin sizeR y ly ry) =
  case delta * sizeL < sizeR of
    True  =>
      balanceL y (merge l ly) ry
    False =>
      case delta*sizeR < sizeL of
        True  =>
          balanceR x lx (merge rx r)
        False =>
          glue l r

--------------------------------------------------------------------------------
--          Filter
--------------------------------------------------------------------------------

||| Filter all elements that satisfy the predicate. O(n)
export
filter : Eq (Set a) => (a -> Bool) -> Set a -> Set a
filter _ Tip             = Tip
filter p t@(Bin _ x l r) =
  case p x of
    True  =>
      case l == (filter p l) && r == (filter p r) of
        True  =>
          t
        False =>
          link x (filter p l) (filter p r)
    False =>
      merge (filter p l) (filter p r)

||| Partition the set into two sets, one with all elements
||| that satisfy the predicate and one with all elements
||| that don't satisfy the predicate.
||| See also split.
partition : Eq (Set a) => (a -> Bool) -> Set a -> (Set a,Set a)
partition _ Tip             = (Tip, Tip)
partition p t@(Bin _ x l r) =
  case (partition p l, partition p r) of
    ((l1, l2), (r1, r2)) =>
      case p x of
        True  =>
          case l1 == l && r1 == r of
            True  =>
              (t, merge l2 r2)
            False =>
              (link x l1 r1, merge l2 r2)
        False =>
          case l2 == l && r2 == r of
            True  =>
              (merge l1 r1, t)
            False =>
              (merge l1 r1, link x l2 r2)

||| Take while a predicate on the keys holds.
||| The user is responsible for ensuring that for all elements j and k in the set,
||| j < k ==> p j >= p k. See note at spanAntitone. O(log n)
export
takeWhileAntitone : (a -> Bool) -> Set a -> Set a
takeWhileAntitone _ Tip           = Tip
takeWhileAntitone p (Bin _ x l r) =
  case p x of
    True  =>
      link x l (takeWhileAntitone p r)
    False =>
      takeWhileAntitone p l

||| Drop while a predicate on the keys holds.
||| The user is responsible for ensuring that for all elements j and k in the map,
||| j < k ==> p j >= p k. See note at spanAntitone. O(log n)
export
dropWhileAntitone : (a -> Bool) -> Set a -> Set a
dropWhileAntitone _ Tip           = Tip
dropWhileAntitone p (Bin _ x l r) =
  case p x of
    True  =>
      dropWhileAntitone p r
    False =>
      link x (dropWhileAntitone p l) r

||| Divide a map at the point where a predicate on the keys stops holding.
||| The user is responsible for ensuring that for all keys j and k in the map,
||| j < k ==> p j>= p k. O(log n)
export
spanAntitone : (a -> Bool) -> Set a -> (Set a,Set a)
spanAntitone p0 s = go p0 s
  where
    go : (a -> Bool) -> Set a -> (Set a,Set a)
    go _ Tip           = (Tip,Tip)
    go p (Bin _ x l r) =
      case p x of
        True  =>
          let (u,v) = go p r
            in (link x l u,v)
        False =>
          let (u,v) = go p l
            in (u,link x v r)

--------------------------------------------------------------------------------
--          Indexed
--------------------------------------------------------------------------------

||| Lookup the index of a element, which is its zero-based index in
||| the sorted sequence of elements. The index is a number from 0 up to, but not
||| including, the size of the set. O(log n)
export
lookupIndex : Ord a => a -> Set a -> Maybe Nat
lookupIndex = go 0
  where
    go : Nat -> a -> Set a -> Maybe Nat
    go _  _ Tip             = Nothing
    go idx x (Bin _ kx l r) =
      case compare x kx of
        LT =>
          go idx x l
        GT =>
          go (idx + size l + 1) x r
        EQ =>
          Just $ idx + size l

||| Return the index of an element, which is its zero-based index in
||| the sorted sequence of elements. The index is a number from 0 up to, but not
||| including, the size of the set. Calls idris_crash when the element is not
||| a member of the set. O(log n)
export
findIndex : Ord a => a -> Set a -> Nat
findIndex = go 0
  where
    go : Nat -> a -> Set a -> Nat
    go _   _ Tip            = assert_total $ idris_crash "Set.findIndex: element is not in the set"
    go idx x (Bin _ kx l r) =
      case compare x kx of
        LT =>
          go idx x l
        GT =>
          go (idx + size l + 1) x r
        EQ =>
          idx + size l

||| Retrieve an element by its index, i.e. by its zero-based
||| index in the sorted sequence of elements. If the index is out of range (less
||| than zero, greater or equal to size of the set), idris_crash is called. O(log n)
export
elemAt : Nat -> Set a -> a
elemAt _ Tip           = assert_total $ idris_crash "Set.elemAt: index out of range"
elemAt i (Bin _ x l r) =
  case compare i (size l) of
     LT =>
       elemAt i l
     GT =>
       elemAt ((i `minus` (size l)) `minus` 1) r
     EQ =>
       x

||| Delete the element at index, i.e. by its zero-based index in
||| the sorted sequence of elements. If the index is out of range (less than zero,
||| greater or equal to size of the set), idris_crash is called. O(log n)
export
deleteAt : Nat -> Set a -> Set a
deleteAt i t =
  case t of
    Tip         => assert_total $ idris_crash "Set.deleteAt: index out of range"
    Bin _ x l r =>
      case compare i (size l) of
        LT =>
          balanceR x (deleteAt i l) r
        GT =>
          balanceL x l (deleteAt ((i `minus` (size l)) `minus` 1) r)
        EQ =>
          glue l r

||| Take a given number of elements in order, beginning
||| with the smallest keys. O(log n)
export
take : Nat -> Set a -> Set a
take i s =
  case i >= size s of
    True  =>
      s
    False =>
      go i s
  where
    go : Nat -> Set a -> Set a
    go _ Tip           = Tip
    go i (Bin _ x l r) =
      case i <= 0 of
        True  =>
          Tip
        False =>
          case compare i (size l) of
            LT =>
              go i l
            GT =>
              link x l (go ((i `minus` (size l)) `minus` 1) r)
            EQ =>
              l

||| Drop a given number of elements in order, beginning
||| with the smallest ones. O(log n)
export
drop : Nat -> Set a -> Set a
drop i s =
  case i >= size s of
    True  =>
      Tip
    False =>
      go i s
  where
    go : Nat -> Set a -> Set a
    go _ Tip             = Tip
    go i s@(Bin _ x l r) =
      case i <= 0 of
        True  =>
          s
        False =>
          case compare i (size l) of
            LT =>
              link x (go i l) r
            GT =>
              go ((i `minus` (size l)) `minus` 1) r
            EQ =>
              insertMin x r

||| Split a set at a particular index. O(log n)
export
splitAt : Nat -> Set a -> (Set a, Set a)
splitAt i s =
  case i >= size s of
    True  =>
      (s,Tip)
    False =>
      go i s
  where
    go : Nat -> Set a -> (Set a,Set a)
    go _ Tip             = (Tip,Tip)
    go i s@(Bin _ x l r) =
      case i <= 0 of
        True  =>
          (Tip,s)
        False =>
          case compare i (size l) of
            LT =>
              case go i l of
                (ll,lr) =>
                  (ll,link x lr r)
            GT =>
              case go ((i `minus` (size l)) `minus` 1) r of
                (rl,rr) =>
                  (link x l rl,rr)
            EQ =>
              (l,insertMin x r)

--------------------------------------------------------------------------------
--          Min/Max
--------------------------------------------------------------------------------

private
lookupMinSure : a -> Set a -> a
lookupMinSure x Tip           = x
lookupMinSure _ (Bin _ x l _) = lookupMinSure x l

||| The minimal element of the set. Returns Nothing if the set is empty. O(log n)
export
lookupMin : Set a -> Maybe a
lookupMin Tip           = Nothing
lookupMin (Bin _ x l _) = Just $ lookupMinSure x l

private
lookupMaxSure : a -> Set a -> a
lookupMaxSure x Tip           = x
lookupMaxSure _ (Bin _ x _ r) = lookupMaxSure x r

||| The maximal element of the set. Returns Nothing if the set is empty. O(log n)
export
lookupMax : Set a -> Maybe a
lookupMax Tip           = Nothing
lookupMax (Bin _ x _ r) = Just $ lookupMaxSure x r

||| The minimal element of the set. Calls idris_crash if the set is empty. O(log n)
export
findMin : Set a -> a
findMin t =
  case lookupMin t of
    Just r  => r
    Nothing => assert_total $ idris_crash "Set.findMin: empty set has no minimal element"

||| The maximal element of the set. Calls idris_crash if the set is empty. O(log n)
export
findMax : Set a -> a
findMax t =
  case lookupMax t of
    Just r  => r
    Nothing => assert_total $ idris_crash "Set.findMax: empty set has no maximal element"

||| Delete the minimal element. Returns an empty set if the set is empty. O(log n)
export
deleteMin : Set a -> Set a
deleteMin Tip              = Tip
deleteMin (Bin _ _ Tip r)  = r
deleteMin (Bin _ x l   r)  = balanceR x (deleteMin l) r

||| Delete the maximal element. Returns an empty set if the set is empty. O(log n)
export
deleteMax : Set a -> Set a
deleteMax Tip             = Tip
deleteMax (Bin _ _ l Tip) = l
deleteMax (Bin _ x l r)   = balanceL x l (deleteMax r)

||| Retrieves the minimal element of the set, and
||| the set stripped of that element, or Nothing if passed an empty set. O(log n)
export
minView : Set a -> Maybe (a,Set a)
minView Tip           = Nothing
minView (Bin _ x l r) =
  Just $ minViewSure x l r

||| Delete and find the minimal element. O(log n)
export
deleteFindMin : Set a -> (a,Set a)
deleteFindMin t =
  case minView t of
    Just res => res
    Nothing  => (assert_total $ idris_crash "Set.deleteFindMin: can not return the minimal element of an empty set",Tip)

||| Retrieves the maximal element of the set, and
||| the set stripped of that element, or Nothing if passed an empty set. O(log n)
export
maxView : Set a -> Maybe (a,Set a)
maxView Tip           = Nothing
maxView (Bin _ x l r) =
  Just $ maxViewSure x l r

||| Delete and find the maximal element. O(log n)
export
deleteFindMax : Set a -> (a,Set a)
deleteFindMax t =
  case maxView t of
    Just res => res
    Nothing  => (assert_total $ idris_crash "Set.deleteFindMax: can not return the maximal element of an empty set",Tip)

--------------------------------------------------------------------------------
--          Combine
--------------------------------------------------------------------------------

||| The expression (union t1 t2) takes the left-biased union of t1 and t2.
||| It prefers t1 when duplicate keys are encountered.
export
union : Eq (Set a) => Eq a => Ord a => Set a -> Set a -> Set a
union t1                 Tip           = t1
union t1                 (Bin 1 x _ _) = insertR x t1
union (Bin 1 x _ _)      t2            = insert x t2
union Tip                t2            = t2
union t1@(Bin _ x l1 r1) t2            =
  case split x t2 of
    (l2,r2) =>
      case (union l1 l2) == l1 && (union r1 r2) == r1 of
        True  =>
          t1
        False =>
          link x (union l1 l2) (union r1 r2)

--------------------------------------------------------------------------------
--          Difference
--------------------------------------------------------------------------------

||| Difference of two sets.
||| Return elements of the first set not existing in the second set.
export
difference : Ord a => Set a -> Set a -> Set a
difference Tip _               = Tip
difference t1  Tip             = t1
difference t1  (Bin _ x l2 r2) =
  case split x t1 of
    (l1,r1) =>
      case size (difference l1 l2) + size (difference r1 r2) == size t1 of
        True  =>
          t1
        False =>
          merge (difference l1 l2) (difference r1 r2)

||| Same as difference.
export
(\\) : Ord a => Set a -> Set a -> Set a
s1 \\ s2 = difference s1 s2

--------------------------------------------------------------------------------
--          Intersection
--------------------------------------------------------------------------------

||| Intersection of two sets.
||| Return data in the first set for elements existing in both sets.
export
intersection : Eq (Set a) => Ord a => Set a -> Set a -> Set a
intersection Tip                _   = Tip
intersection _                  Tip = Tip
intersection t1@(Bin _ x l1 r1) t2  =
  case splitMember x t2 of
    (l2,True,r2) =>
      case (intersection l1 l2) == l1 && (intersection r1 r2) == r1 of
        True  =>
          t1
        False =>
          link x (intersection l1 l2) (intersection r1 r2)
    (l2,False,r2) =>
      merge (intersection l1 l2) (intersection r1 r2)

--------------------------------------------------------------------------------
--          Lists
--------------------------------------------------------------------------------

||| Convert the set to a list of elements where the elements are in descending order. O(n)
export
toDescList : Set a -> List a
toDescList Tip             = []
toDescList t@(Bin _ _ _ _) = foldl (\xs, x => x :: xs) [] t

||| Convert the set to a list of elements where the elements are in ascending order. O(n)
export
toAscList : Set a -> List a
toAscList Tip             = []
toAscList t@(Bin _ _ _ _) = foldr (\x, xs => x :: xs) [] t

||| Convert the set to a list of elements.
export
toList : Set a -> List a
toList = toAscList

||| Build a set from a list of elements.
||| If the list contains identical element(s),
||| the last of each identical elemen is retained.
||| If the elements of the list are ordered, a linear-time implementation is used. O(n * log(n))
export
fromList : Ord a => List a -> Set a
fromList [] = Tip
fromList xs =
  case sorted xs of
    True  =>
      buildBalancedTree (convertToList1 xs) (length xs)
    False =>
      buildBalancedTree (convertToList1 (sort xs)) (length xs)
  where
    -- Calculate the size of a tree
    sizeTree : Set a -> Nat
    sizeTree Tip            = 0
    sizeTree (Bin sz _ _ _) = sz
    -- Convert a list to a List1, which requires the list to be non-empty
    convertToList1 : List a -> List1 a
    convertToList1 []        = assert_total $ idris_crash "Unexpected empty list"
    convertToList1 (x :: xs) = x ::: xs
    -- Link a root node with two subtrees
    linkRootWithSubtrees : a -> Set a -> Set a -> Nat -> Set a
    linkRootWithSubtrees x left right newSize =
      Bin newSize x left right
    -- Split a non-empty list into left, middle, and right parts
    splitList : List1 a -> Nat -> (List a, a, List a, Nat)
    splitList l len =
      let half         = len `div` 2
          (left, rest) = splitAt half (forget l)
        in case rest of
             []                =>
               assert_total $ idris_crash "Unexpected empty list"
             (middle :: right) => 
               (left, middle, right, len)
    -- Build a balanced tree from a non-empty list
    buildBalancedTree : List1 a -> Nat -> Set a
    buildBalancedTree (x ::: []) _   = Bin 1 x Tip Tip
    buildBalancedTree xs         len =
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
--          Map
--------------------------------------------------------------------------------

||| Map a function over all elements in the set. O(n)
export
map : (a -> b) -> Set a -> Set b
map _ Tip            = Tip
map f (Bin sz x l r) = Bin sz (f x) (map f l) (map f r)

--------------------------------------------------------------------------------
--          Disjoint Union
--------------------------------------------------------------------------------

||| Calculate the disjoint union of two sets. O(n + m)
export
disjointUnion : Set a -> Set b -> Set (Either a b)
disjointUnion as bs = merge (map Left as) (map Right bs)

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Functor Set where
  map f s = map f s

export
Show (List a) => Show (Set a) where
  show s = "fromList " ++ (show $ toList s)