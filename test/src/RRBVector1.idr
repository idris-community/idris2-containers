module RRBVector1

import Hedgehog
import Data.Linear.Ref1
import Data.Linear.Token
import Data.List
import Data.RRBVector1

%hide Prelude.toList
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Stream.(::)

listOf : Gen a -> Gen (List a)
listOf g = list (linear 0 20) g

listOf' : Gen a -> Gen (List a)
listOf' g = list (linear 1 20) g

listBits : Gen (List Bits8)
listBits = listOf anyBits8

listBits' : Gen (List Bits8)
listBits' = listOf' anyBits8

prop_eq_refl : Property
prop_eq_refl = property $ do
  vs <- forAll listBits
  ( run1 $ \t =>
      let vs' # t := fromList vs t
        in toList vs' t ) ===
  ( run1 $ \t =>
      let vs' # t := fromList vs t
        in toList vs' t )

prop_map_id : Property
prop_map_id = property $ do
  vs <- forAll listBits
  ( run1 $ \t =>
      let vs'  # t := fromList vs t
          vs'' # t := Data.RRBVector1.map id vs' t
        in toList vs'' t ) === map id vs

prop_from_to_list : Property
prop_from_to_list = property $ do
  vs <- forAll listBits
  ( run1 $ \t =>
      let vs' # t := fromList vs t
        in toList vs' t ) === vs

prop_null : Property
prop_null = property $ do
  vs <- forAll listBits
  ( run1 $ \t =>
      let vs' # t := fromList vs t
        in Data.RRBVector1.null vs' t ) === null vs

prop_size : Property
prop_size = property $ do
  vs <- forAll listBits
  ( run1 $ \t =>
      let vs' # t := fromList vs t
        in Data.RRBVector1.length vs' t ) === length vs

prop_replicate : Property
prop_replicate = property1 $
  ( run1 $ \t =>
      let vs' # t := Data.RRBVector1.replicate 5 1 t
        in toList vs' t ) === [1,1,1,1,1]

prop_take : Property
prop_take = property $ do
  vs <- forAll listBits
  ( run1 $ \t =>
      let vs'  # t := fromList vs t
          vs'' # t := Data.RRBVector1.take 1 vs' t
        in toList vs'' t ) === take 1 vs

prop_drop : Property
prop_drop = property $ do
  vs <- forAll listBits
  ( run1 $ \t =>
      let vs'  # t := fromList vs t
          vs'' # t := Data.RRBVector1.drop ((length vs) `minus` 1) vs' t
        in toList vs'' t ) === drop ((length vs) `minus` 1) vs

prop_cons : Property
prop_cons = property $ do
  vs <- forAll listBits
  ( run1 $ \t =>
      let vs'  # t := fromList vs t
          vs'' # t := (Data.RRBVector1.(<|)) 1 vs' t
        in toList vs'' t ) === 1 :: vs

prop_snoc : Property
prop_snoc = property $ do
  vs <- forAll listBits
  ( run1 $ \t =>
      let vs'  # t := fromList vs t
          vs'' # t := Data.RRBVector1.(|>) vs' 1 t
        in toList vs'' t ) === vs ++ [1]

prop_concat : Property
prop_concat = property $ do
  x <- forAll listBits
  y <- forAll listBits
  ( run1 $ \t =>
      let x'  # t := fromList x t
          y'  # t := fromList y t
          xy' # t := (><) x' y' t
        in toList xy' t ) === x ++ y

prop_insertAt : Property
prop_insertAt = property $ do
  vs <- forAll listBits
  case isLTE 0 (length vs) of
    No  _   =>
      assert_total $ idris_crash "index not within bounds of list"
    Yes prf =>
      ( run1 $ \t =>
          let vs'  # t := fromList vs t
              vs'' # t := Data.RRBVector1.insertAt 0 0 vs' t
            in toList vs'' t ) === insertAt 0 0 @{prf} vs

prop_deleteAt : Property
prop_deleteAt = property $ do
  vs <- forAll listBits'
  case inBounds 0 vs of
    No  _   =>
      assert_total $ idris_crash "index not within bounds of list"
    Yes prf =>
      ( run1 $ \t =>
          let vs'  # t := fromList vs t
              vs'' # t := Data.RRBVector1.deleteAt 0 vs' t
            in toList vs'' t ) === deleteAt 0 vs @{prf}

export
props : Group
props = MkGroup "RRBVector1"
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
