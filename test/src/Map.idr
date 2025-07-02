module Map

import Hedgehog
import Data.List
import Data.Map

%hide Prelude.toList
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Stream.(::)

mapBits : Gen (Map Bits8 Bits8)
mapBits = do
  x <- list (linear 0 20) anyBits8
  y <- list (linear 0 20) anyBits8
  pure $ fromList $ zip x y

mapBits' : Gen (Map Bits8 Bits8)
mapBits' = do
  x <- list (linear 1 20) anyBits8
  y <- list (linear 1 20) anyBits8
  pure $ fromList $ zip x y

prop_eq_refl : Property
prop_eq_refl = property $ do
  vs <- forAll mapBits
  vs === vs

prop_map_id : Property
prop_map_id = property $ do
  vs <- forAll mapBits
  vs === map id vs

prop_null : Property
prop_null = property $ do
  vs <- forAll mapBits
  Data.Map.null vs === null (toList vs)

prop_to_list : Property
prop_to_list = property1 $
  (toList $ fromList [(5, 0), (3, 1)]) === [(3, 1), (5, 0)]

prop_to_asc_list : Property
prop_to_asc_list = property1 $
  (toAscList $ fromList [(5, 0), (3, 1)]) === [(3, 1), (5, 0)]

prop_to_desc_list : Property
prop_to_desc_list = property1 $
  (toDescList $ fromList [(5, 0), (3, 1)]) === [(5, 0), (3, 1)]

prop_from_list : Property
prop_from_list = property1 $
  (fromList [(5, 0), (3, 1), (5, 2)]) === (fromList [(5, 2), (3, 1)])

prop_member : Property
prop_member = property1 $
  (member 5 (fromList [(3, 1), (5, 1)])) === True

prop_notMember : Property
prop_notMember = property1 $
  (notMember 5 (fromList [(3, 1), (5, 1)])) === False

prop_singleton : Property
prop_singleton = property1 $
  (singleton 5 1) === (fromList [(5, 1)])

prop_insert : Property
prop_insert = property1 $
  (insert 5 1 (fromList [(3, 1), (5, 0)])) === (fromList [(3, 1), (5, 1)])

prop_delete : Property
prop_delete = property1 $
  (delete 5 (fromList [(3, 1), (5, 0)])) === (singleton 3 1)

prop_adjust : Property
prop_adjust = property1 $
  (adjust (\a => a `shiftL` (the Nat 2)) 5 (fromList [(3, 1), (5, 1)])) === (fromList [(3, 1), (5, 4)])

prop_update : Property
prop_update = property1 $
  ( update (\a => case a == 1 of
                    True  =>
                      Just $ a `shiftL` (the Nat 2)
                    False =>
                      Nothing
           )
           5
           (fromList [(3, 1), (5, 1)])
  ) === (fromList [(3, 1), (5, 4)])

prop_alterF : Property
prop_alterF = property1 $
  (alter (\_ => Nothing) 5 (fromList [(3, 1), (5, 1)])) === (fromList [(3, 1)])

prop_alterG : Property
prop_alterG = property1 $
  (alter (\_ => Just 4) 5 (fromList [(3, 1), (5, 1)])) === (fromList [(3, 1), (5, 4)])

prop_union : Property
prop_union = property1 $
  (union (fromList [(5, 1), (3, 1)]) (fromList [(5, 2), (7, 1)])) === (fromList [(5, 1), (3, 1), (7, 1)])

prop_difference : Property
prop_difference = property1 $
  (difference (fromList [(5, 1), (3, 1)]) (fromList [(5, 2), (7, 1)])) === (fromList [(3, 1)])

prop_intersection : Property
prop_intersection = property1 $
  (intersection (fromList [(5, 1), (3, 1)]) (fromList [(5, 2), (7, 1)])) === (fromList [(5, 1)])

prop_map : Property
prop_map = property1 $
  (map (\x => x `shiftL` (the Nat 2)) (fromList [(5, 1), (3, 1)])) === (fromList [(5, 4), (3, 4)])

prop_isSubmapOf : Property
prop_isSubmapOf = property1 $
  (isSubmapOf (fromList [(3, 1)]) (fromList [(5, 1), (3, 1)])) === True

prop_lookupIndex : Property
prop_lookupIndex = property1 $
  (isJust (lookupIndex 2 (fromList [(5, 1), (3, 1)]))) === False

prop_lookupLT : Property
prop_lookupLT = property1 $
  (lookupLT 3 (fromList [(3, 1), (5, 1)])) === Nothing

prop_lookupGT : Property
prop_lookupGT = property1 $
  (lookupGT 4 (fromList [(3, 1), (5, 1)])) === (Just (5, 1))

prop_lookupLE : Property
prop_lookupLE = property1 $
  (lookupLE 2 (fromList [(3, 1), (5, 1)])) === Nothing

prop_lookupGE : Property
prop_lookupGE = property1 $
  (lookupGE 3 (fromList [(3, 1), (5, 1)])) === (Just (3, 1))

prop_findIndex : Property
prop_findIndex = property1 $
  (findIndex 3 (fromList [(5, 1), (3, 1)])) === 0

prop_updateAt : Property
prop_updateAt = property1 $
  (updateAt (\ _, _ => Just 4) 0 (fromList [(5, 1), (3, 1)])) === (fromList [(5, 1), (3, 4)])

prop_deleteAt : Property
prop_deleteAt = property1 $
  (deleteAt 0 (fromList [(5, 1), (3, 1)])) === (fromList [(5, 1)])

prop_findMin : Property
prop_findMin = property1 $
  (findMin (fromList [(5, 1), (3, 1)])) === (3, 1)

prop_findMax : Property
prop_findMax = property1 $
  (findMax (fromList [(5, 1), (3, 1)])) === (5, 1)

prop_deleteMin : Property
prop_deleteMin = property1 $
  (deleteMin (fromList [(5, 1), (3, 1), (7, 1)])) === (fromList [(5, 1), (7, 1)])

prop_deleteMax : Property
prop_deleteMax = property1 $
  (deleteMax (fromList [(5, 1), (3, 1), (7, 1)])) === (fromList [(5, 1), (3, 1)])

prop_deleteFindMin : Property
prop_deleteFindMin = property1 $
  (deleteFindMin (fromList [(5, 1), (3, 1), (10, 1)])) === ((3, 1), fromList [(5, 1), (10, 1)])

prop_deleteFindMax : Property
prop_deleteFindMax = property1 $
  (deleteFindMax (fromList [(5, 1), (3, 1), (10, 1)])) === ((10, 1), fromList [(5, 1), (3, 1)])

prop_updateMin : Property
prop_updateMin = property1 $
  (updateMin (\a => Just $ a `shiftL` (the Nat 2)) (fromList [(5, 1), (3, 1)])) === (fromList [(5, 1), (3, 4)])

prop_updateMax : Property
prop_updateMax = property1 $
  (updateMax (\a => Just $ a `shiftL` (the Nat 2)) (fromList [(5, 1), (3, 1)])) === (fromList [(5, 4), (3, 1)])

prop_updateMinWithKey : Property
prop_updateMinWithKey = property1 $
  (updateMinWithKey (\k, a => Just $ (a `shiftL` (the Nat 2)) `shiftL` (the Nat k)) (fromList [(5, 1), (3, 1)])) === (fromList [(5, 1), (3, 32)])

prop_updateMaxWithKey : Property
prop_updateMaxWithKey = property1 $
  (updateMaxWithKey (\k, a => Just $ (a `shiftL` (the Nat 2)) `shiftL` (the Nat k)) (fromList [(5, 1), (3, 1)])) === (fromList [(5, 128), (3, 1)])

prop_minView : Property
prop_minView = property1 $
  (minView (fromList [(5, 1), (3, 1)])) === (Just (1, fromList [(5, 1)]))

prop_maxView : Property
prop_maxView = property1 $
  (maxView (fromList [(5, 1), (3, 1)])) === (Just (1, fromList [(3, 1)]))

prop_minViewWithKey : Property
prop_minViewWithKey = property1 $
  (minViewWithKey (fromList [(5, 1), (3, 1)])) === (Just ((3, 1), fromList [(5, 1)]))

prop_maxViewWithKey : Property
prop_maxViewWithKey = property1 $
  (maxViewWithKey (fromList [(5, 1), (3, 1)])) === (Just ((5, 1), fromList [(3, 1)]))

export
props : Group
props = MkGroup "Map"
  [ ("prop_eq_refl", prop_eq_refl)
  , ("prop_map_id", prop_map_id)
  , ("prop_from_list", prop_from_list)
  , ("prop_to_list", prop_to_list)
  , ("prop_to_asc_list", prop_to_asc_list)
  , ("prop_to_desc_list", prop_to_desc_list)
  , ("prop_null", prop_null)
  , ("prop_member", prop_member)
  , ("prop_notMember", prop_notMember)
  , ("prop_singleton", prop_singleton)
  , ("prop_insert", prop_insert)
  , ("prop_delete", prop_delete)
  , ("prop_adjust", prop_adjust)
  , ("prop_update", prop_update)
  , ("prop_alterF", prop_alterF)
  , ("prop_alterG", prop_alterG)
  , ("prop_union", prop_union)
  , ("prop_difference", prop_difference)
  , ("prop_intersection", prop_intersection)
  , ("prop_map", prop_map)
  , ("prop_isSubmapOf", prop_isSubmapOf)
  , ("prop_lookupIndex", prop_lookupIndex)
  , ("prop_lookupLT", prop_lookupLT)
  , ("prop_lookupGT", prop_lookupGT)
  , ("prop_lookupLE", prop_lookupLE)
  , ("prop_lookupGE", prop_lookupGE)
  , ("prop_findIndex", prop_findIndex)
  , ("prop_updateAt", prop_updateAt)
  , ("prop_deleteAt", prop_deleteAt)
  , ("prop_findMin", prop_findMin)
  , ("prop_findMax", prop_findMax)
  , ("prop_deleteMin", prop_deleteMin)
  , ("prop_deleteMax", prop_deleteMax)
  , ("prop_deleteFindMin", prop_deleteFindMin)
  , ("prop_deleteFindMax", prop_deleteFindMax)
  , ("prop_updateMin", prop_updateMin)
  , ("prop_updateMax", prop_updateMax)
  , ("prop_updateMinWithKey", prop_updateMinWithKey)
  , ("prop_updateMaxWithKey", prop_updateMaxWithKey)
  , ("prop_minView", prop_minView)
  , ("prop_maxView", prop_maxView)
  , ("prop_minViewWithKey", prop_minViewWithKey)
  , ("prop_maxViewWithKey", prop_maxViewWithKey)
  ]
