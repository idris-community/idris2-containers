||| Ordered Priority Search Queue Internals
module Data.OrdPSQ.Internal

import Data.List
import Data.String

%default total

--------------------------------------------------------------------------------
--          Elem
--------------------------------------------------------------------------------

public export
Size : Type
Size = Nat

||| Elem k p v binds the key k to the value v with priority p.
public export
data Elem k p v = MkElem k p v

public export
Show k => Show p => Show v => Show (Elem k p v) where
  show (MkElem k p v) = "Elem "  ++
                        "("      ++
                        (show k) ++
                        " "      ++
                        (show p) ++
                        " "      ++
                        (show v) ++
                        ")"

namespace Elem
  export
  foldr : (a -> b -> b) -> b -> Elem k p a -> b
  foldr f z (MkElem _ _ v) = f v z

  export
  foldl : (b -> a -> b) -> b -> Elem k p a -> b
  foldl f z (MkElem _ _ v) = f z v

  export
  map : (a -> b) -> Elem k p a -> Elem k p b
  map f (MkElem k p v) = MkElem k p (f v)

export
Functor (Elem k p) where
  map f v = map f v

export
Foldable (Elem k p) where
  foldr f z = Data.OrdPSQ.Internal.Elem.foldr f z
  foldl f z = Data.OrdPSQ.Internal.Elem.foldl f z

--------------------------------------------------------------------------------
--          LTree
--------------------------------------------------------------------------------

public export
data LTree k p v = Start
                 | LLoser Size
                          (Elem k p v)
                          (LTree k p v)
                          k             -- split key
                          (LTree k p v)
                 | RLoser Size
                          (Elem k p v)
                          (LTree k p v)
                          k             -- split key
                          (LTree k p v)

public export
Show k => Show p => Show v => Show (LTree k p v) where
  show Start              = "Start"
  show (LLoser s e l m r) = "LLoser " ++
                            "("       ++
                            (show s)  ++
                            " "       ++
                            (show e)  ++
                            " "       ++
                            (show l)  ++
                            " "       ++
                            (show m)  ++
                            " "       ++
                            (show r)  ++
                            ")"
  show (RLoser s e l m r) = "RLoser " ++
                            "("       ++
                            (show s)  ++
                            " "       ++
                            (show e)  ++
                            " "       ++
                            (show l)  ++
                            " "       ++
                            (show m)  ++
                            " "       ++
                            (show r)  ++
                            ")"

namespace LTree
  export
  foldr : (a -> b -> b) -> b -> LTree k p a -> b
  foldr f z Start              = z
  foldr f z (LLoser _ e l _ r) =
    foldr f (Prelude.foldr f (foldr f z r) e) l
  foldr f z (RLoser _ e l _ r) =
    foldr f (Prelude.foldr f (foldr f z r) e) l

  export
  foldl : (b -> a -> b) -> b -> LTree k p a -> b
  foldl f z Start              = z
  foldl f z (LLoser _ e l _ r) =
    foldl f (Prelude.foldl f (foldl f z l) e) r
  foldl f z (RLoser _ e l _ r) =
    foldl f (Prelude.foldl f (foldl f z l) e) r

  export
  map : (a -> b) -> LTree k p a -> LTree k p b
  map _ Start              = Start
  map f (LLoser s e l k r) = LLoser s (map f e) (map f l) k (map f r)
  map f (RLoser s e l k r) = RLoser s (map f e) (map f l) k (map f r)

export
Functor (LTree k p) where
  map f v = map f v

export
Foldable (LTree k p) where
  foldr f z = Data.OrdPSQ.Internal.LTree.foldr f z
  foldl f z = Data.OrdPSQ.Internal.LTree.foldl f z

--------------------------------------------------------------------------------
--          OrdPSQ
--------------------------------------------------------------------------------

||| An OrdPSQ uses the Ord instance of the key type to build a priority search queue.
||| It is a mapping from keys k to priorities p and values v.
public export
data OrdPSQ k p v = Void
                  | Winner (Elem k p v)
                           (LTree k p v)
                           k

public export
Show (Elem k p v) => Show (LTree k p v) => Show (OrdPSQ k p v) where
  show xs = show' xs  where
    show' : OrdPSQ k p v -> String
    show' Void           = "Void"
    show' (Winner e l m) = "Winner " ++
                           "("       ++
                           (show e)  ++
                           " "       ++
                           (show l)  ++
                           ")"

--------------------------------------------------------------------------------
--          Balancing Internals
--------------------------------------------------------------------------------

||| Balance factor
||| Has to be greater than 3.75 (see Hinze's paper).
private
omega : Nat
omega = 4

||| When priorities are equal, the tree with the lowest key wins. This is
||| important to have a deterministic `==`, which requires on `minView` pulling
||| out the elements in the right order.
private
beats : Ord k => Ord p => (p, k) -> (p, k) -> Bool
beats (p, k) (p', k') = p < p' || (p == p' && k < k')

export
size' : LTree p k v -> Size
size' Start              = 0
size' (LLoser s _ _ _ _) = s
size' (RLoser s _ _ _ _) = s

private
left : LTree k p v -> LTree k p v
left Start               = assert_total $ idris_crash "Data.OrdPSQ.Internal.left: empty loser tree"
left (LLoser _ _ tl _ _) = tl
left (RLoser _ _ tl _ _) = tl

private
right : LTree k p v -> LTree k p v
right Start               = assert_total $ idris_crash "Data.OrdPSQ.Internal.right: empty loser tree"
right (LLoser _ _ _ _ tr) = tr
right (RLoser _ _ _ _ tr) = tr

export
maxKey : OrdPSQ k p v -> k
maxKey Void           = assert_total $ idris_crash "Data.OrdPSQ.Internal.maxKey: empty queue"
maxKey (Winner _ _ m) = m

private
lLoser : k -> p -> v -> LTree k p v -> k -> LTree k p v -> LTree k p v
lLoser k p v tl m tr = LLoser (1 + size' tl + size' tr) (MkElem k p v) tl m tr

private
rLoser : k -> p -> v -> LTree k p v -> k -> LTree k p v -> LTree k p v
rLoser k p v tl m tr = RLoser (1 + size' tl + size' tr) (MkElem k p v) tl m tr

private
lSingleLeft : Ord k => Ord p => k -> p -> v -> LTree k p v -> k -> LTree k p v -> LTree k p v
lSingleLeft k1 p1 v1 t1 m1 (LLoser _ (MkElem k2 p2 v2) t2 m2 t3) =
  case (p1, k1) `beats` (p2, k2) of
    True  =>
      lLoser k1 p1 v1 (rLoser k2 p2 v2 t1 m1 t2) m2 t3
    False =>
      lLoser k2 p2 v2 (lLoser k1 p1 v1 t1 m1 t2) m2 t3
lSingleLeft k1 p1 v1 t1 m1 (RLoser _ (MkElem k2 p2 v2) t2 m2 t3) =
  rLoser k2 p2 v2 (lLoser k1 p1 v1 t1 m1 t2) m2 t3
lSingleLeft _  _  _  _  _  _                                     =
  assert_total $ idris_crash "Data.OrdPSQ.Internal.lSingleLeft: malformed tree"

private
rSingleLeft : k -> p -> v -> LTree k p v -> k -> LTree k p v -> LTree k p v
rSingleLeft k1 p1 v1 t1 m1 (LLoser _ (MkElem k2 p2 v2) t2 m2 t3) =
    rLoser k1 p1 v1 (rLoser k2 p2 v2 t1 m1 t2) m2 t3
rSingleLeft k1 p1 v1 t1 m1 (RLoser _ (MkElem k2 p2 v2) t2 m2 t3) =
    rLoser k2 p2 v2 (rLoser k1 p1 v1 t1 m1 t2) m2 t3
rSingleLeft _  _  _  _  _  _                                     =
  assert_total $ idris_crash "Data.OrdPSQ.Internal.rSingleLeft: malformed tree"

private
lSingleRight : k -> p -> v -> LTree k p v -> k -> LTree k p v -> LTree k p v
lSingleRight k1 p1 v1 (LLoser _ (MkElem k2 p2 v2) t1 m1 t2) m2 t3 =
    lLoser k2 p2 v2 t1 m1 (lLoser k1 p1 v1 t2 m2 t3)
lSingleRight k1 p1 v1 (RLoser _ (MkElem k2 p2 v2) t1 m1 t2) m2 t3 =
    lLoser k1 p1 v1 t1 m1 (lLoser k2 p2 v2 t2 m2 t3)
lSingleRight _  _  _  _                                     _  _  =
  assert_total $ idris_crash "Data.OrdPSQ.Internal.lSingleRight: malformed tree"

private
rSingleRight : Ord k => Ord p => k -> p -> v -> LTree k p v -> k -> LTree k p v -> LTree k p v
rSingleRight k1 p1 v1 (LLoser _ (MkElem k2 p2 v2) t1 m1 t2) m2 t3 =
    lLoser k2 p2 v2 t1 m1 (rLoser k1 p1 v1 t2 m2 t3)
rSingleRight k1 p1 v1 (RLoser _ (MkElem k2 p2 v2) t1 m1 t2) m2 t3 =
  case (p1, k1) `beats` (p2, k2) of
    True  =>
      rLoser k1 p1 v1 t1 m1 (lLoser k2 p2 v2 t2 m2 t3)
    False =>
      rLoser k2 p2 v2 t1 m1 (rLoser k1 p1 v1 t2 m2 t3)
rSingleRight _  _  _  _                                     _  _  =
  assert_total $ idris_crash "Data.OrdPSQ.Internal.rSingleRight: malformed tree"

private
lDoubleLeft : Ord k => Ord p => k -> p -> v -> LTree k p v -> k -> LTree k p v -> LTree k p v
lDoubleLeft k1 p1 v1 t1 m1 (LLoser _ (MkElem k2 p2 v2) t2 m2 t3) =
  lSingleLeft k1 p1 v1 t1 m1 (lSingleRight k2 p2 v2 t2 m2 t3)
lDoubleLeft k1 p1 v1 t1 m1 (RLoser _ (MkElem k2 p2 v2) t2 m2 t3) =
  lSingleLeft k1 p1 v1 t1 m1 (rSingleRight k2 p2 v2 t2 m2 t3)
lDoubleLeft _  _  _  _  _  _                                     =
  assert_total $ idris_crash "Data.OrdPSQ.Internal.lDoubleLeft: malformed tree"

private
lDoubleRight : Ord k => Ord p => k -> p -> v -> LTree k p v -> k -> LTree k p v -> LTree k p v
lDoubleRight k1 p1 v1 (LLoser _ (MkElem k2 p2 v2) t1 m1 t2) m2 t3 =
  lSingleRight k1 p1 v1 (lSingleLeft k2 p2 v2 t1 m1 t2) m2 t3
lDoubleRight k1 p1 v1 (RLoser _ (MkElem k2 p2 v2) t1 m1 t2) m2 t3 =
  lSingleRight k1 p1 v1 (rSingleLeft k2 p2 v2 t1 m1 t2) m2 t3
lDoubleRight _  _  _  _                                     _  _  =
  assert_total $ idris_crash "Data.OrdPSQ.Internal.lDoubleRight: malformed tree"

private
rDoubleLeft : Ord k => Ord p => k -> p -> v -> LTree k p v -> k -> LTree k p v -> LTree k p v
rDoubleLeft k1 p1 v1 t1 m1 (LLoser _ (MkElem k2 p2 v2) t2 m2 t3) =
  rSingleLeft k1 p1 v1 t1 m1 (lSingleRight k2 p2 v2 t2 m2 t3)
rDoubleLeft k1 p1 v1 t1 m1 (RLoser _ (MkElem k2 p2 v2) t2 m2 t3) =
  rSingleLeft k1 p1 v1 t1 m1 (rSingleRight k2 p2 v2 t2 m2 t3)
rDoubleLeft _  _  _  _  _  _                                     =
  assert_total $ idris_crash "Data.OrdPSQ.Internal.rDoubleLeft: malformed tree"

private
rDoubleRight : Ord k => Ord p => k -> p -> v -> LTree k p v -> k -> LTree k p v -> LTree k p v
rDoubleRight k1 p1 v1 (LLoser _ (MkElem k2 p2 v2) t1 m1 t2) m2 t3 =
  rSingleRight k1 p1 v1 (lSingleLeft k2 p2 v2 t1 m1 t2) m2 t3
rDoubleRight k1 p1 v1 (RLoser _ (MkElem k2 p2 v2) t1 m1 t2) m2 t3 =
  rSingleRight k1 p1 v1 (rSingleLeft k2 p2 v2 t1 m1 t2) m2 t3
rDoubleRight _  _  _  _                                     _  _  =
  assert_total $ idris_crash "Data.OrdPSQ.Internal.rDoubleRight: malformed tree"

private
lBalanceLeft : Ord k => Ord p => k -> p -> v -> LTree k p v -> k -> LTree k p v -> LTree k p v
lBalanceLeft  k p v l m r =
  case size' (left r) < size' (right r) of
    True  =>
      lSingleLeft k p v l m r
    False =>
      lDoubleLeft k p v l m r

private
lBalanceRight : Ord k => Ord p => k -> p -> v -> LTree k p v -> k -> LTree k p v -> LTree k p v
lBalanceRight k p v l m r =
  case size' (left l) > size' (right l) of
    True  =>
      lSingleRight k p v l m r
    False =>
      lDoubleRight k p v l m r

private
rBalanceLeft : Ord k => Ord p => k -> p -> v -> LTree k p v -> k -> LTree k p v -> LTree k p v
rBalanceLeft  k p v l m r =
  case size' (left r) < size' (right r) of
    True  =>
      rSingleLeft k p v l m r
    False =>
      rDoubleLeft k p v l m r

private
rBalanceRight : Ord k => Ord p => k -> p -> v -> LTree k p v -> k -> LTree k p v -> LTree k p v
rBalanceRight k p v l m r =
  case size' (left l) > size' (right l) of
    True  =>
      rSingleRight k p v l m r
    False =>
      rDoubleRight k p v l m r

private
lBalance : Ord k => Ord p => k -> p -> v -> LTree k p v -> k -> LTree k p v -> LTree k p v
lBalance k p v Start m r     = lLoser k p v Start m r
lBalance k p v l     m Start = lLoser k p v l m Start
lBalance k p v l     m r     =
  case size' r > omega * size' l of
    True  =>
      lBalanceLeft k p v l m r
    False =>
      case size' l > omega * size' r of
        True  =>
          lBalanceRight k p v l m r
        False =>
          lLoser k p v l m r

private
rBalance : Ord k => Ord p => k -> p -> v -> LTree k p v -> k -> LTree k p v -> LTree k p v
rBalance k p v Start m r     = rLoser k p v Start m r
rBalance k p v l     m Start = rLoser k p v l m Start
rBalance k p v l     m r     =
  case size' r > omega * size' l of
    True  =>
      rBalanceLeft k p v l m r
    False =>
      case size' l > omega * size' r of
        True  =>
          rBalanceRight k p v l m r
        False =>
          rLoser k p v l m r

--------------------------------------------------------------------------------
--          Tournament View
--------------------------------------------------------------------------------

public export
data TourView k p v = Null
                    | Single (Elem k p v)
                    | Play (OrdPSQ k p v) (OrdPSQ k p v)

export
tourView : OrdPSQ k p v -> TourView k p v
tourView Void                                = Null
tourView (Winner e Start _)                  = Single e
tourView (Winner e (RLoser _ e' tl m tr) m') = Winner e tl m `Play` Winner e' tr m'
tourView (Winner e (LLoser _ e' tl m tr) m') = Winner e' tl m `Play` Winner e tr m'

||| Take two pennants and returns a new pennant that is the union of
||| the two with the precondition that the keys in the first tree are
||| strictly smaller than the keys in the second tree.
export
play : Ord k => Ord p => OrdPSQ k p v -> OrdPSQ k p v -> OrdPSQ k p v
Void                          `play` t'                                  = t'
t                             `play` Void                                = t
(Winner e@(MkElem k p v) t m) `play` (Winner e'@(MkElem k' p' v') t' m') =
  case (p, k) `beats` (p', k') of
    True  =>
      Winner e (rBalance k' p' v' t m t') m'
    False =>
      Winner e' (lBalance k p v t m t') m'
