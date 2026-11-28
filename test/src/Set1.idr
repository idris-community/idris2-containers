module Set1

import Hedgehog
import Data.List
import Data.Set1
import Data.Set
import Data.Linear.Ref1
import Data.Linear.Token

%hide Prelude.toList
%hide Prelude.Stream.(::)
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixr.(<|)

||| Check from to list against the immutable model.
prop_from_to_list : Property
prop_from_to_list = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList xs store t
        in Data.Set1.toList x t)
    === Just (Data.Set.toList (Data.Set.fromList xs))

||| Check eq refl.
prop_eq_refl : Property
prop_eq_refl = property1 $
  (run1 $ \t =>
      let store    # t := Data.Set1.newStore t
          x        # t := Data.Set1.fromList [5, 3] store t
          snapshot # t := Data.Set1.freeze x t
        in (Data.Set.toList <$> snapshot) # t) === Just ([3, 5])

||| Check from list.
prop_from_list : Property
prop_from_list = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3, 5] store t
        in Data.Set1.toList x t) === Just ([3, 5])

||| Check to list.
prop_to_list : Property
prop_to_list = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.toList x t) === Just ([3, 5])

||| Check to asc list.
prop_to_asc_list : Property
prop_to_asc_list = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.toAscList x t) === Just ([3, 5])

||| Check to desc list.
prop_to_desc_list : Property
prop_to_desc_list = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.toDescList x t) === Just ([5, 3])

||| Check null.
prop_null : Property
prop_null = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.null x t) === Just (False)

||| Check member.
prop_member : Property
prop_member = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.member 5 x t) === Just (True)

||| Check notMember.
prop_notMember : Property
prop_notMember = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.notMember 5 x t) === Just (False)

||| Check singleton.
prop_singleton : Property
prop_singleton = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          y     # t := Data.Set1.singleton 5 store t
        in Data.Set1.toList y t) === Just ([5])

||| Check empty.
prop_empty : Property
prop_empty = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList (the (List Nat) [5, 3]) store t
          y     # t := Data.Set1.empty store t
        in Data.Set1.toList y t) === Just (the (List Nat) [])

||| Check insert.
prop_insert : Property
prop_insert = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          _     # t := Data.Set1.insert 6 x t
        in Data.Set1.toList x t) === Just ([3, 5, 6])

||| Check delete.
prop_delete : Property
prop_delete = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          _     # t := Data.Set1.delete 5 x t
        in Data.Set1.toList x t) === Just ([3])

||| Check union.
prop_union : Property
prop_union = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          y     # t := Data.Set1.fromList [5, 7] store t
          _     # t := Data.Set1.union x y t
        in Data.Set1.toList x t) === Just ([3, 5, 7])

||| Check difference.
prop_difference : Property
prop_difference = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          y     # t := Data.Set1.fromList [5, 7] store t
          _     # t := Data.Set1.difference x y t
        in Data.Set1.toList x t) === Just ([3])

||| Check intersection.
prop_intersection : Property
prop_intersection = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          y     # t := Data.Set1.fromList [5, 7] store t
          _     # t := Data.Set1.intersection x y t
        in Data.Set1.toList x t) === Just ([5])

||| Check map.
prop_map : Property
prop_map = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          dest  # t := Data.Set1.newStore t
          y     # t := Data.Set1.map dest (\v => v * 4) x t
        in case y of
             Nothing => Nothing # t
             Just result => Data.Set1.toList result t) === Just ([12, 20])

||| Check map id.
prop_map_id : Property
prop_map_id = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          dest  # t := Data.Set1.newStore t
          y     # t := Data.Set1.map dest id x t
        in case y of
             Nothing => Nothing # t
             Just result => Data.Set1.toList result t) === Just ([3, 5])

||| Check isSubsetOf.
prop_isSubsetOf : Property
prop_isSubsetOf = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          y     # t := Data.Set1.fromList [3] store t
        in Data.Set1.isSubsetOf y x t) === Just (True)

||| Check isProperSubsetOf.
prop_isProperSubsetOf : Property
prop_isProperSubsetOf = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          y     # t := Data.Set1.fromList [3] store t
        in Data.Set1.isProperSubsetOf y x t) === Just (True)

||| Check proper subset equal.
prop_proper_subset_equal : Property
prop_proper_subset_equal = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.isProperSubsetOf x x t) === Just (False)

||| Check disjoint.
prop_disjoint : Property
prop_disjoint = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          y     # t := Data.Set1.fromList [7] store t
        in Data.Set1.disjoint x y t) === Just (True)

||| Check lookupIndex.
prop_lookupIndex : Property
prop_lookupIndex = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.lookupIndex 2 x t) === Just (Nothing)

||| Check findIndex.
prop_findIndex : Property
prop_findIndex = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.findIndex 3 x t) === Just (Just (0))

||| Check elemAt.
prop_elemAt : Property
prop_elemAt = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.elemAt 0 x t) === Just (Just (3))

||| Check deleteAt.
prop_deleteAt : Property
prop_deleteAt = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          _     # t := Data.Set1.deleteAt 0 x t
        in Data.Set1.toList x t) === Just ([5])

||| Check findMin.
prop_findMin : Property
prop_findMin = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.findMin x t) === Just (Just (3))

||| Check findMax.
prop_findMax : Property
prop_findMax = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.findMax x t) === Just (Just (5))

||| Check lookupMin.
prop_lookupMin : Property
prop_lookupMin = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.lookupMin x t) === Just (Just 3)

||| Check lookupMax.
prop_lookupMax : Property
prop_lookupMax = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.lookupMax x t) === Just (Just 5)

||| Check deleteMin.
prop_deleteMin : Property
prop_deleteMin = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          _     # t := Data.Set1.deleteMin x t
        in Data.Set1.toList x t) === Just ([5])

||| Check deleteMax.
prop_deleteMax : Property
prop_deleteMax = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          _     # t := Data.Set1.deleteMax x t
        in Data.Set1.toList x t) === Just ([3])

||| Check deleteFindMin.
prop_deleteFindMin : Property
prop_deleteFindMin = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          item  # t := Data.Set1.deleteFindMin x t
          ys    # t := Data.Set1.toList x t
        in (item, ys) # t) === (Just (Just 3), Just [5])

||| Check deleteFindMax.
prop_deleteFindMax : Property
prop_deleteFindMax = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          item  # t := Data.Set1.deleteFindMax x t
          ys    # t := Data.Set1.toList x t
        in (item, ys) # t) === (Just (Just 5), Just [3])

||| Check minView.
prop_minView : Property
prop_minView = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          item  # t := Data.Set1.minView x t
          ys    # t := Data.Set1.toList x t
        in (item, ys) # t) === (Just (Just 3), Just ([5]))

||| Check maxView.
prop_maxView : Property
prop_maxView = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          item  # t := Data.Set1.maxView x t
          ys    # t := Data.Set1.toList x t
        in (item, ys) # t) === (Just (Just 5), Just ([3]))

||| Check lookupLT.
prop_lookupLT : Property
prop_lookupLT = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.lookupLT 3 x t) === Just (Nothing)

||| Check lookupGT.
prop_lookupGT : Property
prop_lookupGT = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.lookupGT 4 x t) === Just (Just 5)

||| Check lookupLE.
prop_lookupLE : Property
prop_lookupLE = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.lookupLE 2 x t) === Just (Nothing)

||| Check lookupGE.
prop_lookupGE : Property
prop_lookupGE = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.lookupGE 3 x t) === Just (Just 3)

||| Check filter.
prop_filter : Property
prop_filter = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          _     # t := Data.Set1.filter (> 3) x t
        in Data.Set1.toList x t) === Just ([5])

||| Check take.
prop_take : Property
prop_take = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          _     # t := Data.Set1.take 1 x t
        in Data.Set1.toList x t) === Just ([3])

||| Check drop.
prop_drop : Property
prop_drop = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          _     # t := Data.Set1.drop 1 x t
        in Data.Set1.toList x t) === Just ([5])

||| Check takeWhileAntitone.
prop_takeWhileAntitone : Property
prop_takeWhileAntitone = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          _     # t := Data.Set1.takeWhileAntitone (< 5) x t
        in Data.Set1.toList x t) === Just ([3])

||| Check dropWhileAntitone.
prop_dropWhileAntitone : Property
prop_dropWhileAntitone = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          _     # t := Data.Set1.dropWhileAntitone (< 5) x t
        in Data.Set1.toList x t) === Just ([5])

||| Check foldl.
prop_foldl : Property
prop_foldl = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.foldl (+) 0 x t) === Just (8)

||| Check foldr.
prop_foldr : Property
prop_foldr = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.foldr (+) 0 x t) === Just (8)

||| Check size.
prop_size : Property
prop_size = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
        in Data.Set1.size x t) === Just (2)

||| Check transfer.
prop_transfer : Property
prop_transfer = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          y     # t := Data.Set1.fromList [7] store t
          moved # t := Data.Set1.transfer 3 x y t
          xs    # t := Data.Set1.toList x t
          ys    # t := Data.Set1.toList y t
        in (moved, xs, ys) # t) === (Just (True), Just ([5]), Just ([3, 7]))

||| Check transfer missing.
prop_transfer_missing : Property
prop_transfer_missing = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          y     # t := Data.Set1.fromList [7] store t
          moved # t := Data.Set1.transfer 9 x y t
          xs    # t := Data.Set1.toList x t
          ys    # t := Data.Set1.toList y t
        in (moved, xs, ys) # t) === (Just (False), Just ([3, 5]), Just ([7]))

||| Check store isolation.
prop_store_isolation : Property
prop_store_isolation = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          y     # t := Data.Set1.fromList [7] store t
          _     # t := Data.Set1.insert 9 x t
          ys    # t := Data.Set1.toList y t
        in ys # t) === Just ([7])

||| Check freeze snapshot.
prop_freeze_snapshot : Property
prop_freeze_snapshot = property1 $
  (run1 $ \t =>
      let store # t := Data.Set1.newStore t
          x     # t := Data.Set1.fromList [5, 3] store t
          old   # t := Data.Set1.freeze x t
          _     # t := Data.Set1.insert 9 x t
        in (Data.Set.toList <$> old) # t) === Just ([3, 5])

||| Check that allocated handles have distinct, stable store entries.
||| An update to one set must not affect independently allocated sets.
prop_allocation_isolation : Property
prop_allocation_isolation = property1 $
  (run1 $ \t =>
      let store  # t := Data.Set1.newStore t
          first  # t := Data.Set1.fromList [1] store t
          second # t := Data.Set1.fromList [2] store t
          third  # t := Data.Set1.fromList [3] store t
          ok     # t := Data.Set1.insert 4 second t
          xs     # t := Data.Set1.toList first t
          ys     # t := Data.Set1.toList second t
          zs     # t := Data.Set1.toList third t
        in (ok, xs, ys, zs) # t)
    === ( True
        , Just [1]
        , Just [2, 4]
        , Just [3]
        )

export
props : Group
props = MkGroup "Set1"
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
  , ("prop_union", prop_union)
  , ("prop_difference", prop_difference)
  , ("prop_intersection", prop_intersection)
  , ("prop_map", prop_map)
  , ("prop_map_id", prop_map_id)
  , ("prop_isSubsetOf", prop_isSubsetOf)
  , ("prop_isProperSubsetOf", prop_isProperSubsetOf)
  , ("prop_proper_subset_equal", prop_proper_subset_equal)
  , ("prop_disjoint", prop_disjoint)
  , ("prop_lookupIndex", prop_lookupIndex)
  , ("prop_findIndex", prop_findIndex)
  , ("prop_elemAt", prop_elemAt)
  , ("prop_deleteAt", prop_deleteAt)
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
  , ("prop_lookupLT", prop_lookupLT)
  , ("prop_lookupGT", prop_lookupGT)
  , ("prop_lookupLE", prop_lookupLE)
  , ("prop_lookupGE", prop_lookupGE)
  , ("prop_filter", prop_filter)
  , ("prop_take", prop_take)
  , ("prop_drop", prop_drop)
  , ("prop_takeWhileAntitone", prop_takeWhileAntitone)
  , ("prop_dropWhileAntitone", prop_dropWhileAntitone)
  , ("prop_foldl", prop_foldl)
  , ("prop_foldr", prop_foldr)
  , ("prop_size", prop_size)
  , ("prop_transfer", prop_transfer)
  , ("prop_transfer_missing", prop_transfer_missing)
  , ("prop_store_isolation", prop_store_isolation)
  , ("prop_freeze_snapshot", prop_freeze_snapshot)
  , ("prop_allocation_isolation", prop_allocation_isolation)
  ]
