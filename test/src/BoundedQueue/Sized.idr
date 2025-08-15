module BoundedQueue.Sized

import Hedgehog
import Data.List
import Data.BoundedQueue.Sized

%hide Prelude.Interfaces.toList
%hide Prelude.Stream.(::)

boundedqueueOf : (xs : List a) -> Gen (BoundedQueue (length xs) (length $ take (length xs) xs) a)
boundedqueueOf xs = pure $ fromList (Prelude.Types.List.length xs) xs

boundedqueueBits : (xs : List Bits8) -> Gen (BoundedQueue (length xs) (length $ take (length xs) xs) Bits8)
boundedqueueBits xs = pure $ fromList (Prelude.Types.List.length xs) xs

prop_eq_refl : Property
prop_eq_refl = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ boundedqueueBits xs
  vs === vs

prop_map_id : Property
prop_map_id = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ boundedqueueBits xs
  vs === map id vs

prop_from_to_list : Property
prop_from_to_list = property $ do
  vs <- forAll (list (linear 0 10) anyBits8)
  toList (fromList (length vs) vs) === vs

prop_null : Property
prop_null = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ boundedqueueBits xs
  Data.BoundedQueue.Sized.null vs === null (toList vs)

prop_size : Property
prop_size = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ boundedqueueBits xs
  length vs === length (toList vs)

prop_enqueue : Property
prop_enqueue = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ boundedqueueBits xs
  let (_ ** vs') = enqueue vs 1
  (toList vs) ++ [1] === toList vs'

prop_prepend : Property
prop_prepend = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ boundedqueueBits xs
  let (_ ** vs') = prepend 1 vs
  (1 :: (toList vs)) === (toList vs')

export
props : Group
props = MkGroup "BoundedQueue (Sized)"
  [ ("prop_eq_refl", prop_eq_refl)
  , ("prop_map_id", prop_map_id)
  , ("prop_from_to_list", prop_from_to_list)
  , ("prop_null", prop_null)
  , ("prop_size", prop_size)
  , ("prop_enqueue", prop_enqueue)
  , ("prop_prepend", prop_prepend)
  ]
