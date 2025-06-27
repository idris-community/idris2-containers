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

mapOf' : Gen (Map Bits8 Bits8)
mapOf' = do
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

prop_to_list : Property
prop_to_list = property1 $
  (toList $ fromList [(5, 0), (3, 0)]) === [(3, 0), (5, 0)]

prop_from_list : Property
prop_from_list = property1 $
  (toList $ fromList [(5, 0), (3, 1), (5, 2)]) === (toList $ fromList [(5, 2), (3, 1)])
   
--  x       <- forAll $ list (linear 0 20) anyBits8
--  y       <- forAll $ list (linear 0 20) anyBits8
--  let xy  = zip x y
--  let xy' = fromList xy
--  toList xy' === xy

prop_null : Property
prop_null = property $ do
  vs <- forAll mapBits
  Data.Map.null vs === null (toList vs)

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
  , ("prop_null", prop_null)
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
