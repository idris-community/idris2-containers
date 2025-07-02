||| Map Internals
module Data.Map.Internal

import Data.List
import Data.String
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Maps
--------------------------------------------------------------------------------

public export
Size : Type
Size = Nat

||| A finite map from keys k to values v.
public export
data Map : (k : Type) -> (v : Type) -> Type where
  Bin :  Size
      -> k
      -> v
      -> Map k v
      -> Map k v
      -> Map k v
  Tip : Map k v

%runElab derive "Map" [Eq,Ord,Show]

public export
data MinView k a = MinView' k a (Map k a)

%runElab derive "MinView" [Eq,Ord,Show]

public export
data MaxView k a = MaxView' k a (Map k a)

%runElab derive "MaxView" [Eq,Ord,Show]

--------------------------------------------------------------------------------
--          Creating Maps
--------------------------------------------------------------------------------

||| Wrap a single value in a map.
export
singleton : k -> a -> Map k a
singleton k x = Bin 1 k x Tip Tip

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| The number of elements in the map. O(1)
export
size : Map k v -> Nat
size Tip             = 0
size (Bin _ _ _ l r) = 1 + size l + size r

--------------------------------------------------------------------------------
--          Map Internals
--------------------------------------------------------------------------------

{-
  [balance l x r] balances two trees with value x.
  The sizes of the trees should balance after decreasing the
  size of one of them. (a rotation).

  [delta] is the maximal relative difference between the sizes of
          two trees, it corresponds with the [w] in Adams' paper.
  [ratio] is the ratio between an outer and inner sibling of the
          heavier subtree in an unbalanced setting. It determines
          whether a double or single rotation should be performed
          to restore balance. It is corresponds with the inverse
          of $\alpha$ in Adam's article.

  Note that according to the Adam's paper:
  - [delta] should be larger than 4.646 with a [ratio] of 2.
  - [delta] should be larger than 3.745 with a [ratio] of 1.534.

  But the Adam's paper is erroneous:
  - It can be proved that for delta=2 and delta>=5 there does
    not exist any ratio that would work.
  - Delta=4.5 and ratio=2 does not work.

  That leaves two reasonable variants, delta=3 and delta=4,
  both with ratio=2.

  - A lower [delta] leads to a more 'perfectly' balanced tree.
  - A higher [delta] performs less rebalancing.

  In the benchmarks, delta=3 is faster on insert operations,
  and delta=4 has slightly better deletes. As the insert speedup
  is larger, we currently use delta=3.
-}

delta : Nat
delta = 3

ratio : Nat
ratio = 2

||| The bin constructor maintains the size of the tree.
bin : k -> v -> Map k v -> Map k v -> Map k v
bin k x l r = Bin (size l + size r + 1) k x l r

||| Balances a map after the addition, deletion, or updating of a map via a new key and value.
export
balance : k -> v -> Map k v -> Map k v -> Map k v
balance k x l r =
  case l of
    Tip                  =>
      case r of
        Tip                                                              =>
          Bin 1 k x Tip Tip
        (Bin _  _  _  Tip                          Tip)                  =>
          Bin 2 k x Tip r
        (Bin _  rk rx Tip                          rr@(Bin _ _ _ _ _))   =>
          Bin 3 rk rx (Bin 1 k x Tip Tip) rr
        (Bin _  rk rx (Bin _ rlk rlx _ _)          Tip)                  =>
          Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
        (Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _)) =>
          case rls < ratio * rrs of
            True  =>
              Bin (1+rs) rk rx (Bin (1+rls) k x Tip rl) rr
            False =>
              Bin (1+rs) rlk rlx (Bin (1+size rll) k x Tip rll) (Bin (1+rrs+size rlr) rk rx rlr rr)
    (Bin ls lk lx ll lr) =>
      case r of
        Tip                  =>
          case (ll,lr) of
            (Tip,               Tip)                       =>
              Bin 2 k x l Tip
            (Tip,               (Bin _ lrk lrx _ _))       =>
              Bin 3 lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)
            ((Bin _ _ _ _ _),   Tip)                       =>
              Bin 3 lk lx ll (Bin 1 k x Tip Tip)
            ((Bin lls _ _ _ _), (Bin lrs lrk lrx lrl lrr)) =>
              case lrs < ratio * lls of
                True  =>
                  Bin (1+ls) lk lx ll (Bin (1+lrs) k x lr Tip)
                False =>
                  Bin (1+ls) lrk lrx (Bin (1+lls+size lrl) lk lx ll lrl) (Bin (1+size lrr) k x lrr Tip)
        (Bin rs rk rx rl rr) =>
          case rs > delta * ls of
            True  =>
              case (rl,rr) of
                (Bin rls rlk rlx rll rlr, Bin rrs _ _ _ _) =>
                  case rls < ratio * rrs of
                    True  =>
                      Bin (1+ls+rs) rk rx (Bin (1+ls+rls) k x l rl) rr
                    False =>
                      Bin (1+ls+rs) rlk rlx (Bin (1+ls+size rll) k x l rll) (Bin (1+rrs+size rlr) rk rx rlr rr)
                (_,_)                                      =>
                  assert_total $ idris_crash "Failure in Data.Map.Internal.balance"
            False =>
              case ls > delta * rs of
                True  =>
                  case (ll,lr) of
                    (Bin lls _ _ _ _, Bin lrs lrk lrx lrl lrr) =>
                      case lrs < ratio * lls of
                        True  =>
                          Bin (1+ls+rs) lk lx ll (Bin (1+rs+lrs) k x lr r)
                        False =>
                          Bin (1+ls+rs) lrk lrx (Bin (1+lls+size lrl) lk lx ll lrl) (Bin (1+rs+size lrr) k x lrr r)
                    (_,_)                                      =>
                      assert_total $ idris_crash "Failure in Data.Map.Internal.balance"
                False =>
                  Bin (1+ls+rs) k x l r

||| A specialized version of balance.
||| balanceL is called when left subtree might have been inserted to or when
||| right subtree might have been deleted from.
export
balanceL : k -> v -> Map k v -> Map k v -> Map k v
balanceL k x l r =
  case r of
    Tip              =>
      case l of
        Tip                                                              =>
          Bin 1 k x Tip Tip
        (Bin _  _  _  Tip                  Tip)                          =>
          Bin 2 k x l Tip
        (Bin _  lk lx Tip                  (Bin _ lrk lrx _ _))          =>
          Bin 3 lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)
        (Bin _  lk lx ll@(Bin _ _ _ _ _)   Tip)                          =>
          Bin 3 lk lx ll (Bin 1 k x Tip Tip)
        (Bin ls lk lx ll@(Bin lls _ _ _ _) lr@(Bin lrs lrk lrx lrl lrr)) =>
          case lrs < ratio * lls of
            True  =>
              Bin (1+ls) lk lx ll (Bin (1+lrs) k x lr Tip)
            False =>
              Bin (1+ls) lrk lrx (Bin (1+lls+size lrl) lk lx ll lrl) (Bin (1+size lrr) k x lrr Tip)
    (Bin rs _ _ _ _) =>
      case l of
        Tip                  =>
          Bin (1+rs) k x Tip r
        (Bin ls lk lx ll lr) =>
          case ls > delta * rs of
            True  =>
              case (ll,lr) of
                (Bin lls _ _ _ _, Bin lrs lrk lrx lrl lrr) =>
                  case lrs < ratio * lls of
                    True  =>
                      Bin (1+ls+rs) lk lx ll (Bin (1+rs+lrs) k x lr r)
                    False =>
                      Bin (1+ls+rs) lrk lrx (Bin (1+lls+size lrl) lk lx ll lrl) (Bin (1+rs+size lrr) k x lrr r)
                (_,_)                                      =>
                  assert_total $ idris_crash "Failure in Data.Map.Internal.balanceL"
            False =>
              Bin (1+ls+rs) k x l r

||| A specialized version of balance.
||| balanceR is called when right subtree might have been inserted to or when
||| left subtree might have been deleted from.
export
balanceR : k -> v -> Map k v -> Map k v -> Map k v
balanceR k x l r =
  case l of
    Tip              =>
      case r of
        Tip                                                              =>
          Bin 1 k x Tip Tip
        (Bin _  _  _  Tip                          Tip               )   =>
          Bin 2 k x Tip r
        (Bin _  rk rx Tip                          rr@(Bin _ _ _ _ _))   =>
          Bin 3 rk rx (Bin 1 k x Tip Tip) rr
        (Bin _  rk rx (Bin _ rlk rlx _ _)          Tip)                  =>
          Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
        (Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _)) =>
          case rls < ratio * rrs of
            True  =>
              Bin (1+rs) rk rx (Bin (1+rls) k x Tip rl) rr
            False =>
              Bin (1+rs) rlk rlx (Bin (1+size rll) k x Tip rll) (Bin (1+rrs+size rlr) rk rx rlr rr)
    (Bin ls _ _ _ _) =>
      case r of
        Tip                  =>
          Bin (1+ls) k x l Tip
        (Bin rs rk rx rl rr) =>
          case rs > delta * ls of
            True  =>
              case (rl,rr) of
                (Bin rls rlk rlx rll rlr, Bin rrs _ _ _ _) =>
                  case rls < ratio * rrs of
                    True  =>
                      Bin (1+ls+rs) rk rx (Bin (1+ls+rls) k x l rl) rr
                    False =>
                      Bin (1+ls+rs) rlk rlx (Bin (1+ls+size rll) k x l rll) (Bin (1+rrs+size rlr) rk rx rlr rr)
                (_,_)                                      =>
                  assert_total $ idris_crash "Failure in Data.Map.Internal.balanceR"
            False =>
              Bin (1+ls+rs) k x l r

export
insertMax : k -> v -> Map k v -> Map k v
insertMax kx x t =
  case t of
    Tip            =>
      singleton kx x
    Bin _ ky y l r =>
      balanceR ky y l (insertMax kx x r)

export
insertMin : k -> v -> Map k v -> Map k v
insertMin kx x t =
  case t of
    Tip            =>
      singleton kx x
    Bin _ ky y l r =>
      balanceL ky y (insertMin kx x l) r

export
minViewSure : k -> v -> Map k v -> Map k v -> MinView k v
minViewSure k x Tip                 r = MinView' k x r
minViewSure k x (Bin _ kl xl ll lr) r =
  case minViewSure kl xl ll lr of
    MinView' km xm l' => MinView' km xm (balanceR k x l' r)

export
maxViewSure : k -> v -> Map k v -> Map k v -> MaxView k v
maxViewSure k x l Tip                 = MaxView' k x l
maxViewSure k x l (Bin _ kr xr rl rr) =
  case maxViewSure kr xr rl rr of
    MaxView' km xm r' => MaxView' km xm (balanceL k x l r')

||| Glues two maps together (assumes that both maps are already balanced with respect to each other).
export
glue : Map k v -> Map k v -> Map k v
glue Tip                    r                      = r
glue l                      Tip                    = l
glue l@(Bin sl kl xl ll lr) r@(Bin sr kr xr rl rr) =
  case sl > sr of
    True  =>
      let (MaxView' km m l') = maxViewSure kl xl ll lr
        in balanceR km m l' r
    False =>
      let (MinView' km m r') = minViewSure kr xr rl rr
        in balanceL km m l r'

||| Utility function that maintains the balance properties of the tree.
export
link2 : Map k v -> Map k v -> Map k v
link2 Tip                      r                        = r
link2 l                        Tip                      = l
link2 l@(Bin sizeL kx x lx rx) r@(Bin sizeR ky y ly ry) =
  case delta * sizeL < sizeR of
    True  =>
      balanceL ky y (link2 l ly) ry
    False =>
      case delta * sizeR < sizeL of
        True  =>
          balanceR kx x lx (link2 rx r)
        False =>
          glue l r

||| Utility function that maintains the balance properties of the tree.
export
link : k -> v -> Map k v -> Map k v -> Map k v
link kx x Tip                      r                        = insertMin kx x r
link kx x l                        Tip                      = insertMax kx x l
link kx x l@(Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz) =
  case delta * sizeL < sizeR of
    True  =>
      balanceL kz z (link kx x l lz) rz
    False =>
      case delta * sizeR < sizeL of
        True  =>
          balanceR ky y ly (link kx x ry r)
        False =>
          bin kx x l r
