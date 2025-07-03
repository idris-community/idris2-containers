module Set

import Hedgehog
import Data.List
import Data.Set

%hide Prelude.toList
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Stream.(::)

setBits : Gen (Set Bits8)
setBits = do
  x <- list (linear 0 20) anyBits8
  pure $ fromList x

setBits' : Gen (Set Bits8)
setBits' = do
  x <- list (linear 1 20) anyBits8
  pure $ fromList x

prop_eq_refl : Property
prop_eq_refl = property $ do
  vs <- forAll setBits
  vs === vs

prop_map_id : Property
prop_map_id = property $ do
  vs <- forAll setBits
  vs === map id vs

prop_null : Property
prop_null = property $ do
  vs <- forAll setBits
  Data.Set.null vs === null (toList vs)

prop_to_list : Property
prop_to_list = property1 $
  (toList $ fromList [5, 3]) === [3, 5]

prop_to_asc_list : Property
prop_to_asc_list = property1 $
  (toAscList $ fromList [5, 3]) === [3, 5]

prop_to_desc_list : Property
prop_to_desc_list = property1 $
  (toDescList $ fromList [5, 3]) === [5, 3]

prop_from_list : Property
prop_from_list = property1 $
  (fromList [5, 3, 5]) === (fromList [5, 3])

prop_member : Property
prop_member = property1 $
  (member 5 (fromList [3, 5])) === True

prop_notMember : Property
prop_notMember = property1 $
  (notMember 5 (fromList [3, 5])) === False

prop_singleton : Property
prop_singleton = property1 $
  (singleton 5) === (fromList [5])

prop_insert : Property
prop_insert = property1 $
  (insert 6 (fromList [3, 5])) === (fromList [3, 5, 6])

prop_delete : Property
prop_delete = property1 $
  (delete 5 (fromList [3, 5])) === (singleton 3)

prop_union : Property
prop_union = property1 $
  (union (fromList [5, 3]) (fromList [5, 7])) === (fromList [5, 3, 7])

prop_difference : Property
prop_difference = property1 $
  (difference (fromList [5, 3]) (fromList [5, 7])) === (fromList [3])

prop_intersection : Property
prop_intersection = property1 $
  (intersection (fromList [5, 3]) (fromList [5, 7])) === (fromList [5])

prop_map : Property
prop_map = property1 $
  (map (\x => x `shiftL` (the Nat 2)) (fromList [5, 3])) === (fromList [20, 12])

prop_isSubsetOf : Property
prop_isSubsetOf = property1 $
  (isSubsetOf (fromList [3]) (fromList [5, 3])) === True

prop_lookupIndex : Property
prop_lookupIndex = property1 $
  (isJust (lookupIndex 2 (fromList [5, 3]))) === False

prop_findIndex : Property
prop_findIndex = property1 $
  (findIndex 3 (fromList [5, 3])) === 0

prop_deleteAt : Property
prop_deleteAt = property1 $
  (deleteAt 0 (fromList [5, 3])) === (fromList [5])

prop_findMin : Property
prop_findMin = property1 $
  (findMin (fromList [5, 3])) === 3

prop_findMax : Property
prop_findMax = property1 $
  (findMax (fromList [5, 3])) === 5

prop_deleteMin : Property
prop_deleteMin = property1 $
  (deleteMin (fromList [5, 3, 7])) === (fromList [5, 7])

prop_deleteMax : Property
prop_deleteMax = property1 $
  (deleteMax (fromList [5, 3, 7])) === (fromList [5, 3])

prop_deleteFindMin : Property
prop_deleteFindMin = property1 $
  (deleteFindMin (fromList [5, 3, 10])) === (3, fromList [5, 10])

prop_deleteFindMax : Property
prop_deleteFindMax = property1 $
  (deleteFindMax (fromList [5, 3, 10])) === (10, fromList [5, 3])

prop_minView : Property
prop_minView = property1 $
  (minView (fromList [5, 3])) === (Just (3, fromList [5]))

prop_maxView : Property
prop_maxView = property1 $
  (maxView (fromList [5, 3])) === (Just (5, fromList [3]))

export
props : Group
props = MkGroup "Set"
  [ ("prop_eq_refl", prop_eq_refl)
  , ("prop_map_id", prop_map_id)
  , ("prop_null", prop_null)
  , ("prop_from_list", prop_from_list)
  , ("prop_to_list", prop_to_list)
  , ("prop_to_asc_list", prop_to_asc_list)
  , ("prop_to_desc_list", prop_to_desc_list)
  , ("prop_member", prop_member)
  , ("prop_notMember", prop_notMember)
  , ("prop_singleton", prop_singleton)
  , ("prop_insert", prop_insert)
  , ("prop_delete", prop_delete)
  , ("prop_union", prop_union)
  , ("prop_difference", prop_difference)
  , ("prop_intersection", prop_intersection)
  , ("prop_map", prop_map)
  , ("prop_isSubsetOf", prop_isSubsetOf)
  , ("prop_lookupIndex", prop_lookupIndex)
  , ("prop_findIndex", prop_findIndex)
  , ("prop_deleteAt", prop_deleteAt)
  , ("prop_findMin", prop_findMin)
  , ("prop_findMax", prop_findMax)
  , ("prop_deleteMin", prop_deleteMin)
  , ("prop_deleteMax", prop_deleteMax)
  , ("prop_deleteFindMin", prop_deleteFindMin)
  , ("prop_deleteFindMax", prop_deleteFindMax)
  , ("prop_minView", prop_minView)
  , ("prop_maxView", prop_maxView)
  ]
