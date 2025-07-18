module OrdPSQ

import Hedgehog
import Data.List
import Data.OrdPSQ

%hide Prelude.Interfaces.toList
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Stream.(::)

ordpsqOf : Ord a => Gen a -> Gen (OrdPSQ a a a)
ordpsqOf g = do
  k <- list (linear 0 20) g
  p <- list (linear 0 20) g
  v <- list (linear 0 20) g
  pure $ fromList $ zip3 k p v

ordpsqOf' : Ord a => Gen a -> Gen (OrdPSQ a a a)
ordpsqOf' g = do
  k <- list (linear 1 20) g
  p <- list (linear 1 20) g
  v <- list (linear 1 20) g
  pure $ fromList $ zip3 k p v

ordpsqBits : Gen (OrdPSQ Bits8 Bits8 Bits8)
ordpsqBits = ordpsqOf anyBits8

ordpsqBits' : Gen (OrdPSQ Bits8 Bits8 Bits8)
ordpsqBits' = ordpsqOf' anyBits8

prop_eq_refl : Property
prop_eq_refl = property $ do
  vs <- forAll ordpsqBits
  vs === vs

prop_map_id : Property
prop_map_id = property $ do
  vs <- forAll ordpsqBits
  vs === map id vs

prop_from_to_list : Property
prop_from_to_list = property $ do
  vs <- forAll ordpsqBits
  fromList (toList vs) === vs

{-
prop_null : Property
prop_null = property $ do
  vs <- forAll boundedqueueBits
  null vs === null (Data.BoundedQueue.toList vs)

prop_size : Property
prop_size = property $ do
  vs <- forAll boundedqueueBits
  length vs === length (toList vs)

prop_enqueue : Property
prop_enqueue = property $ do
  vs <- forAll boundedqueueBits
  (toList vs) ++ [1] === toList (enqueue vs 1)

prop_prepend : Property
prop_prepend = property $ do
  vs <- forAll boundedqueueBits
  (1 :: (toList vs)) === (toList (prepend 1 vs))
  -}

export
props : Group
props = MkGroup "OrdPSQ"
  [ ("prop_eq_refl", prop_eq_refl)
  , ("prop_map_id", prop_map_id)
  , ("prop_from_to_list", prop_from_to_list)
--  , ("prop_null", prop_null)
--  , ("prop_size", prop_size)
--  , ("prop_enqueue", prop_enqueue)
--  , ("prop_prepend", prop_prepend)
  ]
