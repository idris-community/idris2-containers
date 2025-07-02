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

prop_findIndex : Property
prop_findIndex = property1 $
  (findIndex 3 (fromList [(5, 1), (3, 1)])) === 0

prop_updateAt : Property
prop_updateAt 

--  x       <- forAll $ list (linear 0 20) anyBits8
--  y       <- forAll $ list (linear 0 20) anyBits8
--  let xy  = zip x y
--  let xy' = fromList xy
--  toList xy' === xy

{-
prop_size : Property
prop_size = property $ do
  vs <- forAll mapBits
  length vs === length (toList vs)

prop_replicate : Property
prop_replicate = property1 $
  toList (Data.RRBVector.replicate 5 1) === [1,1,1,1,1]

prop_take : Property
prop_take = property $ do
  vs <- forAll mapBits
  toList (take 1 vs) === take 1 (toList vs)

prop_drop : Property
prop_drop = property $ do
  vs <- forAll mapBits
  toList (drop ((length vs) `minus` 1) vs) === drop ((length vs) `minus` 1) (toList vs)

prop_cons : Property
prop_cons = property $ do
  vs <- forAll mapBits
  (1 :: (toList vs)) === toList (1 <| vs)

prop_snoc : Property
prop_snoc = property $ do
  vs <- forAll mapBits
  (toList vs) ++ [1] === toList (vs |> 1)

prop_concat : Property
prop_concat = property $ do
  x <- forAll mapBits
  y <- forAll mapBits
  (toList x) ++ (toList y) === toList ((><) x y)

prop_insertAt : Property
prop_insertAt = property $ do
  vs <- forAll mapBits
  case isLTE 0 (length (toList vs)) of
    No  _   =>
      assert_total $ idris_crash "index not within bounds of list"
    Yes prf =>
      insertAt 0 0 @{prf} (toList vs) === toList (insertAt 0 0 vs)

prop_deleteAt : Property
prop_deleteAt = property $ do
  vs <- forAll mapBits'
  case inBounds 0 (toList vs) of
    No  _   =>
      assert_total $ idris_crash "index not within bounds of list"
    Yes prf =>
      deleteAt 0 (toList vs) @{prf} === toList (deleteAt 0 vs)
-}

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
  , ("prop_findIndex", prop_findIndex)
--  , ("prop_size", prop_size)
--  , ("prop_replicate", prop_replicate)
--  , ("prop_take", prop_take)
--  , ("prop_drop", prop_drop)
--  , ("prop_cons", prop_cons)
--  , ("prop_snoc", prop_snoc)
--  , ("prop_concat", prop_concat)
--  , ("prop_insertAt", prop_insertAt)
--  , ("prop_deleteAt", prop_deleteAt)
  ]
