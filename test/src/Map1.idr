module Map1

import Hedgehog
import Data.List
import Data.Map1
import Data.Map
import Data.Linear.Ref1
import Data.Linear.Token

%hide Prelude.toList
%hide Prelude.Stream.(::)
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixr.(<|)

||| Check from to list against the immutable model.
prop_from_to_list : Property
prop_from_to_list = property $ do
  ks <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll (list (linear 0 20) anyBits8)
  let xs = zip ks vs
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList xs store t
        in Data.Map1.toList x t) === Data.Map.toList (Data.Map.fromList xs)

||| Check eq refl.
prop_eq_refl : Property
prop_eq_refl = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.freeze x t) === Data.Map.fromList [(5, 0), (3, 1)]

||| Check from list.
prop_from_list : Property
prop_from_list = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1), (5, 2)] store t
        in Data.Map1.toList x t) === [(3, 1), (5, 2)]

||| Check to list.
prop_to_list : Property
prop_to_list = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.toList x t) === [(3, 1), (5, 0)]

||| Check to asc list.
prop_to_asc_list : Property
prop_to_asc_list = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.toAscList x t) === [(3, 1), (5, 0)]

||| Check to desc list.
prop_to_desc_list : Property
prop_to_desc_list = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.toDescList x t) === [(5, 0), (3, 1)]

||| Check null.
prop_null : Property
prop_null = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.null x t) === False

||| Check member.
prop_member : Property
prop_member = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.member 5 x t) === True

||| Check notMember.
prop_notMember : Property
prop_notMember = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.notMember 5 x t) === False

||| Check singleton.
prop_singleton : Property
prop_singleton = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          y     # t := Data.Map1.singleton 5 1 store t
        in Data.Map1.toList y t) === [(5, 1)]

||| Check empty.
prop_empty : Property
prop_empty = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList (the (List (Nat, Nat)) [(5, 0), (3, 1)]) store t
          y     # t := Data.Map1.empty store t
        in Data.Map1.toList y t) === the (List (Nat, Nat)) []

||| Check insert.
prop_insert : Property
prop_insert = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.insert 5 1 x t
        in Data.Map1.toList x t) === [(3, 1), (5, 1)]

||| Check delete.
prop_delete : Property
prop_delete = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.delete 5 x t
        in Data.Map1.toList x t) === [(3, 1)]

||| Check adjust.
prop_adjust : Property
prop_adjust = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.adjust (\v => v + 3) 5 x t
        in Data.Map1.toList x t) === [(3, 1), (5, 3)]

||| Check update.
prop_update : Property
prop_update = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.update (\v => Just (v + 4)) 5 x t
        in Data.Map1.toList x t) === [(3, 1), (5, 4)]

||| Check alterF.
prop_alterF : Property
prop_alterF = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.alter (\_ => Nothing) 5 x t
        in Data.Map1.toList x t) === [(3, 1)]

||| Check alterG.
prop_alterG : Property
prop_alterG = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.alter (\_ => Just 4) 5 x t
        in Data.Map1.toList x t) === [(3, 1), (5, 4)]

||| Check insertWith.
prop_insertWith : Property
prop_insertWith = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.insertWith (+) 5 2 x t
        in Data.Map1.toList x t) === [(3, 1), (5, 2)]

||| Check insertWithKey.
prop_insertWithKey : Property
prop_insertWithKey = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.insertWithKey (\k, n, old => k + n + old) 5 2 x t
        in Data.Map1.toList x t) === [(3, 1), (5, 7)]

||| Check insertLookupWithKey.
prop_insertLookupWithKey : Property
prop_insertLookupWithKey = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          old   # t := Data.Map1.insertLookupWithKey
                         (\_, n, old => n + old) 5 2 x t
          ys    # t := Data.Map1.toList x t
        in (old, ys) # t) === (Just 0, [(3, 1), (5, 2)])

||| Check updateWithKey.
prop_updateWithKey : Property
prop_updateWithKey = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.updateWithKey (\k, v => Just (k + v)) 5 x t
        in Data.Map1.toList x t) === [(3, 1), (5, 5)]

||| Check updateLookupWithKey.
prop_updateLookupWithKey : Property
prop_updateLookupWithKey = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          old   # t := Data.Map1.updateLookupWithKey (\_, v => Just (v + 3)) 3 x t
          ys    # t := Data.Map1.toList x t
        in (old, ys) # t) === (Just 4, [(3, 4), (5, 0)])

||| Check union.
prop_union : Property
prop_union = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          y     # t := Data.Map1.fromList [(5, 2), (7, 1)] store t
          _     # t := Data.Map1.union x y t
        in Data.Map1.toList x t) === [(3, 1), (5, 0), (7, 1)]

||| Check difference.
prop_difference : Property
prop_difference = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          y     # t := Data.Map1.fromList [(5, 2), (7, 1)] store t
          _     # t := Data.Map1.difference x y t
        in Data.Map1.toList x t) === [(3, 1)]

||| Check intersection.
prop_intersection : Property
prop_intersection = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          y     # t := Data.Map1.fromList [(5, 2), (7, 1)] store t
          _     # t := Data.Map1.intersection x y t
        in Data.Map1.toList x t) === [(5, 0)]

||| Check unionWith.
prop_unionWith : Property
prop_unionWith = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          y # t := Data.Map1.fromList [(5, 2)] store t
          _ # t := Data.Map1.unionWith (+) x y t
        in Data.Map1.toList x t) === [(3, 1), (5, 2)]

||| Check unionWithKey.
prop_unionWithKey : Property
prop_unionWithKey = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          y     # t := Data.Map1.fromList [(5, 2)] store t
          _     # t := Data.Map1.unionWithKey (\k, a, b => k + a + b) x y t
        in Data.Map1.toList x t) === [(3, 1), (5, 7)]

||| Check isSubmapOf.
prop_isSubmapOf : Property
prop_isSubmapOf = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          y     # t := Data.Map1.fromList [(3, 1)] store t
        in Data.Map1.isSubmapOf y x t) === True

||| Check isProperSubmapOf.
prop_isProperSubmapOf : Property
prop_isProperSubmapOf = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          y     # t := Data.Map1.fromList [(3, 1)] store t
        in Data.Map1.isProperSubmapOf y x t) === True

||| Check lookupIndex.
prop_lookupIndex : Property
prop_lookupIndex = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.lookupIndex 2 x t) === Nothing

||| Check lookupLT.
prop_lookupLT : Property
prop_lookupLT = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.lookupLT 3 x t) === Nothing

||| Check lookupGT.
prop_lookupGT : Property
prop_lookupGT = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.lookupGT 4 x t) === Just (5, 0)

||| Check lookupLE.
prop_lookupLE : Property
prop_lookupLE = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.lookupLE 2 x t) === Nothing

||| Check lookupGE.
prop_lookupGE : Property
prop_lookupGE = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.lookupGE 3 x t) === Just (3, 1)

||| Check findIndex.
prop_findIndex : Property
prop_findIndex = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.findIndex 3 x t) === 0

||| Check elemAt.
prop_elemAt : Property
prop_elemAt = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.elemAt 0 x t) === (3, 1)

||| Check updateAt.
prop_updateAt : Property
prop_updateAt = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _ # t := Data.Map1.updateAt (\_, _ => Just 4) 0 x t
        in Data.Map1.toList x t) === [(3, 4), (5, 0)]

||| Check findMin.
prop_findMin : Property
prop_findMin = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.findMin x t) === (3, 1)

||| Check findMax.
prop_findMax : Property
prop_findMax = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.findMax x t) === (5, 0)

||| Check lookupMin.
prop_lookupMin : Property
prop_lookupMin = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.lookupMin x t) === Just (3, 1)

||| Check lookupMax.
prop_lookupMax : Property
prop_lookupMax = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.lookupMax x t) === Just (5, 0)

||| Check deleteMin.
prop_deleteMin : Property
prop_deleteMin = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.deleteMin x t
        in Data.Map1.toList x t) === [(5, 0)]

||| Check deleteMax.
prop_deleteMax : Property
prop_deleteMax = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.deleteMax x t
        in Data.Map1.toList x t) === [(3, 1)]

||| Check deleteFindMin.
prop_deleteFindMin : Property
prop_deleteFindMin = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          item  # t := Data.Map1.deleteFindMin x t
          ys    # t := Data.Map1.toList x t
        in (item, ys) # t) === ((3, 1), [(5, 0)])

||| Check deleteFindMax.
prop_deleteFindMax : Property
prop_deleteFindMax = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          item  # t := Data.Map1.deleteFindMax x t
          ys    # t := Data.Map1.toList x t
        in (item, ys) # t) === ((5, 0), [(3, 1)])

||| Check minView.
prop_minView : Property
prop_minView = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          item  # t := Data.Map1.minView x t
          ys    # t := Data.Map1.toList x t
        in (item, ys) # t) === (Just 1, [(5, 0)])

||| Check maxView.
prop_maxView : Property
prop_maxView = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          item  # t := Data.Map1.maxView x t
          ys    # t := Data.Map1.toList x t
        in (item, ys) # t) === (Just 0, [(3, 1)])

||| Check minViewWithKey.
prop_minViewWithKey : Property
prop_minViewWithKey = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          item # t := Data.Map1.minViewWithKey x t
          ys   # t := Data.Map1.toList x t
        in (item, ys) # t) === (Just (3, 1), [(5, 0)])

||| Check maxViewWithKey.
prop_maxViewWithKey : Property
prop_maxViewWithKey = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          item # t := Data.Map1.maxViewWithKey x t
          ys   # t := Data.Map1.toList x t
        in (item, ys) # t) === (Just (5, 0), [(3, 1)])

||| Check updateMin.
prop_updateMin : Property
prop_updateMin = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.updateMin (\_ => Just 4) x t
        in Data.Map1.toList x t) === [(3, 4), (5, 0)]

||| Check updateMax.
prop_updateMax : Property
prop_updateMax = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.updateMax (\_ => Just 4) x t
        in Data.Map1.toList x t) === [(3, 1), (5, 4)]

||| Check updateMinWithKey.
prop_updateMinWithKey : Property
prop_updateMinWithKey = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.updateMinWithKey (\_, _ => Just 4) x t
        in Data.Map1.toList x t) === [(3, 4), (5, 0)]

||| Check updateMaxWithKey.
prop_updateMaxWithKey : Property
prop_updateMaxWithKey = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.updateMaxWithKey (\_, _ => Just 4) x t
        in Data.Map1.toList x t) === [(3, 1), (5, 4)]

||| Check map.
prop_map : Property
prop_map = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          dest  # t := Data.Map1.newStore t
          y     # t := Data.Map1.map dest (\v => v + 4) x t
        in Data.Map1.toList y t) === [(3, 5), (5, 4)]

||| Check map id.
prop_map_id : Property
prop_map_id = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          dest  # t := Data.Map1.newStore t
          y     # t := Data.Map1.map dest id x t
        in Data.Map1.toList y t) === [(3, 1), (5, 0)]

||| Check mapWithKey.
prop_mapWithKey : Property
prop_mapWithKey = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          dest  # t := Data.Map1.newStore t
          y     # t := Data.Map1.mapWithKey dest (\k, v => k + v) x t
        in Data.Map1.toList y t) === [(3, 4), (5, 5)]

||| Check mapMaybe.
prop_mapMaybe : Property
prop_mapMaybe = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          dest  # t := Data.Map1.newStore t
          y     # t := Data.Map1.mapMaybe dest
                        (\v => if v == 0 then Nothing else Just v) x t
        in Data.Map1.toList y t) === [(3, 1)]

||| Check mapMaybeWithKey.
prop_mapMaybeWithKey : Property
prop_mapMaybeWithKey = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          dest  # t := Data.Map1.newStore t
          y     # t := Data.Map1.mapMaybeWithKey dest
                        (\k, v => if k == 3 then Just v else Nothing) x t
        in Data.Map1.toList y t) === [(3, 1)]

||| Check filter.
prop_filter : Property
prop_filter = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.filter (== 1) x t
        in Data.Map1.toList x t) === [(3, 1)]

||| Check filterWithKey.
prop_filterWithKey : Property
prop_filterWithKey = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.filterWithKey (\k, _ => k == 5) x t
        in Data.Map1.toList x t) === [(5, 0)]

||| Check keys.
prop_keys : Property
prop_keys = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.keys x t) === [3, 5]

||| Check values.
prop_values : Property
prop_values = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.values x t) === [1, 0]

||| Check foldl.
prop_foldl : Property
prop_foldl = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.foldl (+) 0 x t) === 1

||| Check foldr.
prop_foldr : Property
prop_foldr = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.foldr (+) 0 x t) === 1

||| Check foldlWithKey.
prop_foldlWithKey : Property
prop_foldlWithKey = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.foldlWithKey (\acc, k, v => acc + k + v) 0 x t) === 9

||| Check foldrWithKey.
prop_foldrWithKey : Property
prop_foldrWithKey = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
        in Data.Map1.foldrWithKey (\k, v, acc => acc + k + v) 0 x t) === 9

||| Check swap.
prop_swap : Property
prop_swap = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          y     # t := Data.Map1.fromList [(8, 2)] store t
          _     # t := Data.Map1.swap x y t
          xs    # t := Data.Map1.toList x t
          ys    # t := Data.Map1.toList y t
        in (xs, ys) # t) === ([(8, 2)], [(3, 1), (5, 0)])

||| Check swap self.
prop_swap_self : Property
prop_swap_self = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          _     # t := Data.Map1.swap x x t
        in Data.Map1.toList x t) === [(3, 1), (5, 0)]

||| Check store isolation.
prop_store_isolation : Property
prop_store_isolation = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          y     # t := Data.Map1.fromList [(8, 2)] store t
          _     # t := Data.Map1.insert 9 4 x t
          ys    # t := Data.Map1.toList y t
        in ys # t) === [(8, 2)]

||| Check freeze snapshot.
prop_freeze_snapshot : Property
prop_freeze_snapshot = property1 $
  (run1 $ \t =>
      let store # t := Data.Map1.newStore t
          x     # t := Data.Map1.fromList [(5, 0), (3, 1)] store t
          old   # t := Data.Map1.freeze x t
          _     # t := Data.Map1.insert 8 2 x t
        in Data.Map.toList old # t) === [(3, 1), (5, 0)]

export
props : Group
props = MkGroup "Map1"
  [ ("prop_from_to_list", prop_from_to_list)
  , ("prop_eq_refl", prop_eq_refl)
  , ("prop_from_list", prop_from_list)
  , ("prop_to_list", prop_to_list)
  , ("prop_to_asc_list", prop_to_asc_list)
  , ("prop_to_desc_list", prop_to_desc_list)
  , ("prop_null", prop_null)
  , ("prop_member", prop_member)
  , ("prop_notMember", prop_notMember)
  , ("prop_singleton", prop_singleton)
  , ("prop_empty", prop_empty)
  , ("prop_insert", prop_insert)
  , ("prop_delete", prop_delete)
  , ("prop_adjust", prop_adjust)
  , ("prop_update", prop_update)
  , ("prop_alterF", prop_alterF)
  , ("prop_alterG", prop_alterG)
  , ("prop_insertWith", prop_insertWith)
  , ("prop_insertWithKey", prop_insertWithKey)
  , ("prop_insertLookupWithKey", prop_insertLookupWithKey)
  , ("prop_updateWithKey", prop_updateWithKey)
  , ("prop_updateLookupWithKey", prop_updateLookupWithKey)
  , ("prop_union", prop_union)
  , ("prop_difference", prop_difference)
  , ("prop_intersection", prop_intersection)
  , ("prop_unionWith", prop_unionWith)
  , ("prop_unionWithKey", prop_unionWithKey)
  , ("prop_isSubmapOf", prop_isSubmapOf)
  , ("prop_isProperSubmapOf", prop_isProperSubmapOf)
  , ("prop_lookupIndex", prop_lookupIndex)
  , ("prop_lookupLT", prop_lookupLT)
  , ("prop_lookupGT", prop_lookupGT)
  , ("prop_lookupLE", prop_lookupLE)
  , ("prop_lookupGE", prop_lookupGE)
  , ("prop_findIndex", prop_findIndex)
  , ("prop_elemAt", prop_elemAt)
  , ("prop_updateAt", prop_updateAt)
  , ("prop_findMin", prop_findMin)
  , ("prop_findMax", prop_findMax)
  , ("prop_lookupMin", prop_lookupMin)
  , ("prop_lookupMax", prop_lookupMax)
  , ("prop_deleteMin", prop_deleteMin)
  , ("prop_deleteMax", prop_deleteMax)
  , ("prop_deleteFindMin", prop_deleteFindMin)
  , ("prop_deleteFindMax", prop_deleteFindMax)
  , ("prop_minView", prop_minView)
  , ("prop_maxView", prop_maxView)
  , ("prop_minViewWithKey", prop_minViewWithKey)
  , ("prop_maxViewWithKey", prop_maxViewWithKey)
  , ("prop_updateMin", prop_updateMin)
  , ("prop_updateMax", prop_updateMax)
  , ("prop_updateMinWithKey", prop_updateMinWithKey)
  , ("prop_updateMaxWithKey", prop_updateMaxWithKey)
  , ("prop_map", prop_map)
  , ("prop_map_id", prop_map_id)
  , ("prop_mapWithKey", prop_mapWithKey)
  , ("prop_mapMaybe", prop_mapMaybe)
  , ("prop_mapMaybeWithKey", prop_mapMaybeWithKey)
  , ("prop_filter", prop_filter)
  , ("prop_filterWithKey", prop_filterWithKey)
  , ("prop_keys", prop_keys)
  , ("prop_values", prop_values)
  , ("prop_foldl", prop_foldl)
  , ("prop_foldr", prop_foldr)
  , ("prop_foldlWithKey", prop_foldlWithKey)
  , ("prop_foldrWithKey", prop_foldrWithKey)
  , ("prop_swap", prop_swap)
  , ("prop_swap_self", prop_swap_self)
  , ("prop_store_isolation", prop_store_isolation)
  , ("prop_freeze_snapshot", prop_freeze_snapshot)
  ]
