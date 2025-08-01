module RRBVector

import Hedgehog
import Data.List
import Data.RRBVector

%hide Prelude.toList
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Stream.(::)

rrbvectorOf : (xs : List a) -> Gen (RRBVector (length xs) a)
rrbvectorOf xs = pure $ fromList xs

rrbvectorBits : (xs : List Bits8) -> Gen (RRBVector (length xs) Bits8)
rrbvectorBits xs = pure $ fromList xs

prop_eq_refl : Property
prop_eq_refl = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ rrbvectorBits xs
  vs === vs

prop_map_id : Property
prop_map_id = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ rrbvectorBits xs
  vs === map id vs

prop_from_to_list : Property
prop_from_to_list = property $ do
  vs <- forAll (list (linear 0 10) anyBits8)
  toList (fromList vs) === vs

prop_null : Property
prop_null = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ rrbvectorBits xs
  Data.RRBVector.null vs === null (toList vs)

prop_size : Property
prop_size = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ rrbvectorBits xs
  length vs === length (toList vs)

prop_replicate : Property
prop_replicate = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ rrbvectorBits xs
  toList (Data.RRBVector.replicate 5 1) === replicate 5 1

prop_take : Property
prop_take = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ rrbvectorBits xs
  toList (take 1 vs) === take 1 (toList vs)

prop_drop : Property
prop_drop = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ rrbvectorBits xs
  toList (drop ((length vs) `minus` 1) vs) === drop ((length vs) `minus` 1) (toList vs)

prop_cons : Property
prop_cons = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ rrbvectorBits xs
  let (_ ** vs') = 1 <| vs
  (1 :: (toList vs)) === toList vs'

prop_snoc : Property
prop_snoc = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ rrbvectorBits xs
  let (_ ** vs') = vs |> 1
  (toList vs) ++ [1] === toList vs'

prop_concat : Property
prop_concat = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  ys <- forAll (list (linear 0 20) anyBits8)
  x <- forAll $ rrbvectorBits xs
  y <- forAll $ rrbvectorBits ys
  let (_ ** xsys) = (><) x y
  (toList x) ++ (toList y) === toList xsys

prop_insertAt : Property
prop_insertAt = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  vs <- forAll $ rrbvectorBits xs
  case isLTE 0 (length (toList vs)) of
    No  _   =>
      assert_total $ idris_crash "index not within bounds of list"
    Yes prf =>
      let (_ ** vs') = insertAt 0 0 vs
        in insertAt 0 0 @{prf} (toList vs) === toList vs'

prop_deleteAt : Property
prop_deleteAt = property $ do
  xs <- forAll (list (linear 1 20) anyBits8)
  vs <- forAll $ rrbvectorBits xs
  case inBounds 0 (toList vs) of
    No  _   =>
      assert_total $ idris_crash "index not within bounds of list"
    Yes prf =>
      let (_ ** vs') = deleteAt 0 vs
        in deleteAt 0 (toList vs) @{prf} === toList vs'

export
props : Group
props = MkGroup "RRBVector"
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
  , ("prop_insertAt", prop_insertAt)
  , ("prop_deleteAt", prop_deleteAt)
  ]
