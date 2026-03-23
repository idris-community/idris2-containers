module Seq1.Unsized

import Data.List
import Data.Linear.Ref1
import Data.Linear.Token
import Data.Seq1.Unsized
import Hedgehog

%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Stream.(::)

prop_eq_refl : Property
prop_eq_refl = property $ do
  vs <- forAll (list (linear 0 20) anyBits8)
  ( run1 $ \t =>
      let vs' # t := Data.Seq1.Unsized.fromList vs t
        in Data.Seq1.Unsized.toList vs' t ) === vs

prop_size : Property
prop_size = property $ do
  vs <- forAll (list (linear 0 20) anyBits8)
  ( run1 $ \t =>
      let vs' # t := Data.Seq1.Unsized.fromList vs t
        in Data.Seq1.Unsized.length vs' t ) === length vs

prop_replicate : Property
prop_replicate = property $ do
  vs <- forAll (list (linear 0 20) anyBits8)
  ( run1 $ \t =>
      let vs' # t := Data.Seq1.Unsized.replicate 5 1 t
        in Data.Seq1.Unsized.toList vs' t ) === replicate 5 1

prop_cons : Property
prop_cons = property $ do
  vs <- forAll (list (linear 0 20) anyBits8)
  ( run1 $ \t =>
      let vs' # t := Data.Seq1.Unsized.fromList vs t
          _   # t := Data.Seq1.Unsized.cons 1 vs' t
        in Data.Seq1.Unsized.toList vs' t ) === 1 :: vs

prop_snoc : Property
prop_snoc = property $ do
  vs <- forAll (list (linear 0 20) anyBits8)
  ( run1 $ \t =>
      let vs' # t := Data.Seq1.Unsized.fromList vs t
          _   # t := Data.Seq1.Unsized.snoc vs' 1 t
        in Data.Seq1.Unsized.toList vs' t ) === vs ++ [1]

prop_concat : Property
prop_concat = property $ do
  xs <- forAll (list (linear 0 20) anyBits8)
  ys <- forAll (list (linear 0 20) anyBits8)
  ( run1 $ \t =>
      let xs'  # t := Data.Seq1.Unsized.fromList xs t
          ys'  # t := Data.Seq1.Unsized.fromList ys t
          xsys # t := Data.Seq1.Unsized.(++) xs' ys' t
        in Data.Seq1.Unsized.toList xsys t ) === xs ++ ys

export
props : Group
props = MkGroup "Seq1 (Unsized)"
  [ ("prop_eq_refl", prop_eq_refl)
  , ("prop_size", prop_size)
  , ("prop_replicate", prop_replicate)
  , ("prop_cons", prop_cons)
  , ("prop_snoc", prop_snoc)
  , ("prop_concat", prop_concat)
  ]
