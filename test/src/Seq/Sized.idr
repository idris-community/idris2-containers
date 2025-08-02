module Seq.Sized

import Hedgehog
import Data.List
import Data.Seq.Sized
import Data.Vect

%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Stream.(::)

seqOf : (xs : List a) -> Gen (Seq (length xs) a)
seqOf xs = pure $ fromList xs

seqBits : (xs : List Bits8) -> Gen (Seq (length xs) Bits8)
seqBits xs = pure $ fromList xs

prop_eq_refl : Property
prop_eq_refl = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ seqBits xs
  vs === vs

prop_map_id : Property
prop_map_id = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ seqBits xs
  vs === map id vs

prop_from_to_list : Property
prop_from_to_list = property $ do
  vs <- forAll (list (linear 0 10) anyBits8)
  toVect (fromList vs) === fromList vs

prop_null : Property
prop_null = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ seqBits xs
  null vs === null (toList vs)

prop_size : Property
prop_size = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ seqBits xs
  length vs === length (toList vs)

prop_replicate : Property
prop_replicate = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ seqBits xs
  toVect (Data.Seq.Sized.replicate 5 1) === replicate 5 1

prop_take : Property
prop_take = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ seqBits xs
  let vs' = take Z vs
  toList vs' === take Z (toList vs)

prop_drop : Property
prop_drop = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ seqBits xs
  let vs' = drop Z vs
  toList vs' === drop Z (toList vs)

prop_cons : Property
prop_cons = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ seqBits xs
  let vs' = cons 1 vs
  (1 :: (toList vs)) === toList vs'

prop_snoc : Property
prop_snoc = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ seqBits xs
  let vs' = snoc vs 1
  snoc (toList vs) 1 === toList vs'

prop_concat : Property
prop_concat = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  ys <- forAll (list (linear 0 20) anyBits8)
  x <- forAll $ seqBits xs
  y <- forAll $ seqBits ys
  let xsys = (++) x y
  (toList x) ++ (toList y) === toList xsys

export
props : Group
props = MkGroup "Seq (Sized)"
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
