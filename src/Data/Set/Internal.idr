||| Set Internals
module Data.Set.Internal

import Data.List
import Data.String
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Sets
--------------------------------------------------------------------------------

public export
Size : Type
Size = Nat

||| A finite set of values.
public export
data Set : (a : Type) -> Type where
  Bin :  Size
      -> a
      -> Set a
      -> Set a
      -> Set a
  Tip : Set a

%runElab derive "Set" [Eq,Ord,Show]

--------------------------------------------------------------------------------
--          Creating Sets
--------------------------------------------------------------------------------

||| Wrap a single value in a set.
export
singleton :  a
          -> Set a
singleton x =
  Bin 1 x Tip Tip

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| The number of elements in the set. O(1)
export
size :  Set a
     -> Nat
size Tip           =
  0
size (Bin _ _ l r) =
  1 + size l + size r

--------------------------------------------------------------------------------
--          Set Internals
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

export
delta : Nat
delta = 3

ratio : Nat
ratio = 2

||| The bin constructor maintains the size of the tree.
bin :  a
    -> Set a
    -> Set a
    -> Set a
bin x l r =
  Bin (size l + size r + 1) x l r

||| A specialized version of balance.
||| balanceL is called when left subtree might have been inserted to or when
||| right subtree might have been deleted from.
export
balanceL :  a
         -> Set a
         -> Set a
         -> Set a
balanceL x l r =
  case r of
    Tip              =>
      case l of
        Tip                                                     =>
          Bin 1 x Tip Tip
        (Bin _  _  Tip                Tip)                      =>
          Bin 2 x l Tip
        (Bin _  lx Tip                (Bin _ lrx _ _))          =>
          Bin 3 lrx (Bin 1 lx Tip Tip) (Bin 1 x Tip Tip)
        (Bin _  lx ll@(Bin _ _ _ _)   Tip)                      =>
          Bin 3 lx ll (Bin 1 x Tip Tip)
        (Bin ls lx ll@(Bin lls _ _ _) lr@(Bin lrs lrx lrl lrr)) =>
          case lrs < ratio * lls of
            True  =>
              Bin (1+ls) lx ll (Bin (1+lrs) x lr Tip)
            False =>
              Bin (1+ls) lrx (Bin (1+lls+size lrl) lx ll lrl) (Bin (1+size lrr) x lrr Tip)
    (Bin rs _ _ _) =>
      case l of
        Tip               =>
          Bin (1+rs) x Tip r
        (Bin ls lx ll lr) =>
          case ls > delta * rs of
            True  =>
              case (ll,lr) of
                (Bin lls _ _ _, Bin lrs lrx lrl lrr) =>
                  case lrs < ratio * lls of
                    True  =>
                      Bin (1+ls+rs) lx ll (Bin (1+rs+lrs) x lr r)
                    False =>
                      Bin (1+ls+rs) lrx (Bin (1+lls+size lrl) lx ll lrl) (Bin (1+rs+size lrr) x lrr r)
                (_,_)                                      =>
                  assert_total $ idris_crash "Failure in Data.Set.Internal.balanceL"
            False =>
              Bin (1+ls+rs) x l r

||| A specialized version of balance.
||| balanceR is called when right subtree might have been inserted to or when
||| left subtree might have been deleted from.
export
balanceR :  a
         -> Set a
         -> Set a
         -> Set a
balanceR x l r =
  case l of
    Tip            =>
      case r of
        Tip                                                     =>
          Bin 1 x Tip Tip
        (Bin _  _  Tip                      Tip)                =>
          Bin 2 x Tip r
        (Bin _  rx Tip                      rr@(Bin _ _ _ _))   =>
          Bin 3 rx (Bin 1 x Tip Tip) rr
        (Bin _  rx (Bin _ rlx _ _)          Tip)                =>
          Bin 3 rlx (Bin 1 x Tip Tip) (Bin 1 rx Tip Tip)
        (Bin rs rx rl@(Bin rls rlx rll rlr) rr@(Bin rrs _ _ _)) =>
          case rls < ratio * rrs of
            True  =>
              Bin (1+rs) rx (Bin (1+rls) x Tip rl) rr
            False =>
              Bin (1+rs) rlx (Bin (1+size rll) x Tip rll) (Bin (1+rrs+size rlr) rx rlr rr)
    (Bin ls _ _ _) =>
      case r of
        Tip                  =>
          Bin (1+ls) x l Tip
        (Bin rs rx rl rr) =>
          case rs > delta * ls of
            True  =>
              case (rl,rr) of
                (Bin rls rlx rll rlr, Bin rrs _ _ _) =>
                  case rls < ratio * rrs of
                    True  =>
                      Bin (1+ls+rs) rx (Bin (1+ls+rls) x l rl) rr
                    False =>
                      Bin (1+ls+rs) rlx (Bin (1+ls+size rll) x l rll) (Bin (1+rrs+size rlr) rx rlr rr)
                (_,_)                                      =>
                  assert_total $ idris_crash "Failure in Data.Set.Internal.balanceR"
            False =>
              Bin (1+ls+rs) x l r

export
insertMax :  a
          -> Set a
          -> Set a
insertMax x t =
  case t of
    Tip            =>
      singleton x
    Bin _ y l r =>
      balanceR y l (insertMax x r)

export
insertMin :  a
          -> Set a
          -> Set a
insertMin x t =
  case t of
    Tip            =>
      singleton x
    Bin _ y l r =>
      balanceL y (insertMin x l) r

export
minViewSure :  a
            -> Set a
            -> Set a
            -> (a, Set a)
minViewSure x Tip              r =
  (x, r)
minViewSure x (Bin _ xl ll lr) r =
  case minViewSure xl ll lr of
    (xm, l') =>
      (xm, balanceR x l' r)

export
maxViewSure :  a
            -> Set a
            -> Set a
            -> (a, Set a)
maxViewSure x l Tip              =
  (x, l)
maxViewSure x l (Bin _ xr rl rr) =
  case maxViewSure xr rl rr of
    (xm, r') =>
      (xm, balanceL x l r')

||| Glues two sets together (assumes that both sets are already balanced with respect to each other).
export
glue :  Set a
     -> Set a
     -> Set a
glue Tip                    r                =
  r
glue l                      Tip              =
  l
glue l@(Bin sl xl ll lr) r@(Bin sr xr rl rr) =
  case sl > sr of
    True  =>
      let (m, l') = maxViewSure xl ll lr
        in balanceR m l' r
    False =>
      let (m, r') = minViewSure xr rl rr
        in balanceL m l r'

||| Utility function that maintains the balance properties of the tree.
export
link :  a
     -> Set a
     -> Set a
     -> Set a
link x Tip                      r                  =
  insertMin x r
link x l                        Tip                =
  insertMax x l
link x l@(Bin sizeL y ly ry) r@(Bin sizeR z lz rz) =
  case delta * sizeL < sizeR of
    True  =>
      balanceL z (link x l lz) rz
    False =>
      case delta * sizeR < sizeL of
        True  =>
          balanceR y ly (link x ry r)
        False =>
          bin x l r
