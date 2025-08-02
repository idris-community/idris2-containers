module Seq.Unsized

import Hedgehog
import Data.List
import Data.Seq.Unsized

%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Stream.(::)

seqOf : Gen a -> Gen (Seq a)
seqOf g = fromList <$> list (linear 0 20) g

seqOf' : Gen a -> Gen (Seq a)
seqOf' g = fromList <$> list (linear 1 20) g

seqBits : Gen (Seq Bits8)
seqBits = seqOf anyBits8

seqBits' : Gen (Seq Bits8)
seqBits' = seqOf' anyBits8

prop_eq_refl : Property
prop_eq_refl = property $ do
  vs <- forAll seqBits
  vs === vs

prop_map_id : Property
prop_map_id = property $ do
  vs <- forAll seqBits
  vs === map id vs

prop_from_to_list : Property
prop_from_to_list = property $ do
  vs <- forAll (list (linear 0 10) anyBits8)
  toList (fromList vs) === vs

prop_null : Property
prop_null = property $ do
  vs <- forAll seqBits
  null vs === null (toList vs)

prop_size : Property
prop_size = property $ do
  vs <- forAll seqBits
  length vs === length (toList vs)

prop_replicate : Property
prop_replicate = property $ do
  vs <- forAll seqBits
  toList (Data.Seq.Unsized.replicate 5 1) === replicate 5 1

prop_take : Property
prop_take = property $ do
  vs <- forAll seqBits
  toList (take 1 vs) === take 1 (toList vs)

prop_drop : Property
prop_drop = property $ do
  vs <- forAll seqBits
  toList (drop ((length vs) `minus` 1) vs) === drop ((length vs) `minus` 1) (toList vs)

prop_cons : Property
prop_cons = property $ do
  vs <- forAll seqBits
  (1 :: (toList vs)) === toList (1 `cons` vs)

prop_snoc : Property
prop_snoc = property $ do
  vs <- forAll seqBits
  (toList vs) ++ [1] === toList (vs `snoc` 1)

prop_concat : Property
prop_concat = property $ do
  x <- forAll seqBits
  y <- forAll seqBits
  (toList x) ++ (toList y) === toList ((++) x y)

export
props : Group
props = MkGroup "Seq (Unsized)"
  [ ("prop_eq_refl", prop_eq_refl)
  , ("prop_map_id", prop_map_id)
  , ("prop_from_to_list", prop_from_to_list)
  , ("prop_null", prop_null)
  , ("prop_size", prop_size)
  , ("prop_replicate", prop_replicate)
  , ("prop_take", prop_take)
  , ("prop_drop", prop_drop)
  , ("prop_cons", prop_cons)
  , ("prop_snoc", prop_snoc)
  , ("prop_concat", prop_concat)
  ]
