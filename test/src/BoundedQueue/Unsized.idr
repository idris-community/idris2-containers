module BoundedQueue.Unsized

import Hedgehog
import Data.List
import Data.BoundedQueue.Unsized

%hide Prelude.Interfaces.toList
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Stream.(::)

boundedqueueOf : Gen a -> Gen (BoundedQueue a)
boundedqueueOf g = do
  l <- list (linear 0 20) g
  pure $ fromList 20 l

boundedqueueOf' : Gen a -> Gen (BoundedQueue a)
boundedqueueOf' g = do
  l <- list (linear 1 20) g
  pure $ fromList 20 l

boundedqueueBits : Gen (BoundedQueue Bits8)
boundedqueueBits = boundedqueueOf anyBits8

boundedqueueBits' : Gen (BoundedQueue Bits8)
boundedqueueBits' = boundedqueueOf' anyBits8

prop_eq_refl : Property
prop_eq_refl = property $ do
  vs <- forAll boundedqueueBits
  vs === vs

prop_map_id : Property
prop_map_id = property $ do
  vs <- forAll boundedqueueBits
  vs === map id vs

prop_from_to_list : Property
prop_from_to_list = property $ do
  vs <- forAll (list (linear 0 10) anyBits8)
  toList (fromList 10 vs) === vs

prop_null : Property
prop_null = property $ do
  vs <- forAll boundedqueueBits
  null vs === null (Data.BoundedQueue.Unsized.toList vs)

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

export
props : Group
props = MkGroup "BoundedQueue (Unsized)"
  [ ("prop_eq_refl", prop_eq_refl)
  , ("prop_map_id", prop_map_id)
  , ("prop_from_to_list", prop_from_to_list)
  , ("prop_null", prop_null)
  , ("prop_size", prop_size)
  , ("prop_enqueue", prop_enqueue)
  , ("prop_prepend", prop_prepend)
  ]
