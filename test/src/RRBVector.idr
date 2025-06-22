module RRBVector

import Hedgehog
import Data.List
import Data.RRBVector

%hide Prelude.toList
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Stream.(::)

rrbvectorOf : Gen a -> Gen (RRBVector a)
rrbvectorOf g = fromList <$> list (linear 0 20) g

rrbvectorOf' : Gen a -> Gen (RRBVector a)
rrbvectorOf' g = fromList <$> list (linear 1 20) g

rrbvectorBits : Gen (RRBVector Bits8)
rrbvectorBits = rrbvectorOf anyBits8

rrbvectorBits' : Gen (RRBVector Bits8)
rrbvectorBits' = rrbvectorOf' anyBits8

prop_eq_refl : Property
prop_eq_refl = property $ do
  vs <- forAll rrbvectorBits
  vs === vs

prop_map_id : Property
prop_map_id = property $ do
  vs <- forAll rrbvectorBits
  vs === map id vs

prop_from_to_list : Property
prop_from_to_list = property $ do
  vs <- forAll (list (linear 0 10) anyBits8)
  toList (fromList vs) === vs

prop_null : Property
prop_null = property $ do
  vs <- forAll rrbvectorBits
  Data.RRBVector.null vs === null (toList vs)

prop_size : Property
prop_size = property $ do
  vs <- forAll rrbvectorBits
  length vs === length (toList vs)

prop_replicate : Property
prop_replicate = property1 $
  toList (Data.RRBVector.replicate 5 1) === [1,1,1,1,1]

prop_drop : Property
prop_drop = property $ do
  vs <- forAll rrbvectorBits
  toList (drop ((length vs) `minus` 1) vs) === drop ((length vs) `minus` 1) (toList vs)

prop_cons : Property
prop_cons = property $ do
  vs <- forAll rrbvectorBits
  (1 :: (toList vs)) === toList (1 <| vs)

prop_snoc : Property
prop_snoc = property $ do
  vs <- forAll rrbvectorBits
  (toList vs) ++ [1] === toList (vs |> 1)

prop_concat : Property
prop_concat = property $ do
  x <- forAll rrbvectorBits
  y <- forAll rrbvectorBits
  (toList x) ++ (toList y) === toList ((><) x y)

prop_insertAt : Property
prop_insertAt = property $ do
  vs <- forAll rrbvectorBits
  case isLTE 0 (length (toList vs)) of
    No  _   =>
      assert_total $ idris_crash "index not within bounds of list"
    Yes prf =>
      insertAt 0 0 @{prf} (toList vs) === toList (insertAt 0 0 vs)

prop_deleteAt : Property
prop_deleteAt = property $ do
  vs <- forAll rrbvectorBits'
  case inBounds 0 (toList vs) of
    No  _   =>
      assert_total $ idris_crash "index not within bounds of list"
    Yes prf =>
      deleteAt 0 (toList vs) @{prf} === toList (deleteAt 0 vs)

export
props : Group
props = MkGroup "RRBVector"
  [ ("prop_eq_refl", prop_eq_refl)
  , ("prop_map_id", prop_map_id)
  , ("prop_from_to_list", prop_from_to_list)
  , ("prop_null", prop_null)
  , ("prop_size", prop_size)
  , ("prop_replicate", prop_replicate)
  , ("prop_drop", prop_drop)
  , ("prop_cons", prop_cons)
  , ("prop_snoc", prop_snoc)
  , ("prop_concat", prop_concat)
  , ("prop_insertAt", prop_insertAt)
  , ("prop_deleteAt", prop_deleteAt)
  ]
