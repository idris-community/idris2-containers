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

prop_null : Property
prop_null = property $ do
  vs <- forAll ordpsqBits
  Prelude.null vs === null (Data.OrdPSQ.toList vs)

prop_size : Property
prop_size = property $ do
  vs <- forAll ordpsqBits
  size vs === length (toList vs)

prop_member : Property
prop_member = property1 $
  (member 5 (fromList [(3, 0, 1), (5, 1, the Nat 2)])) === True

prop_notMember : Property
prop_notMember = property1 $
  (notMember 5 (fromList [(3, 0, 1), (5, 1, the Nat 2)])) === False

prop_singleton : Property
prop_singleton = property1 $
  (singleton 3 0 1) === (fromList [(3, 0, 1)])

prop_insert : Property
prop_insert = property1 $
  (insert 5 1 2 (fromList [(3, 0, 1), (5, 0, 2)])) === (fromList [(3, 0, 1), (5, 1, 2)])

prop_delete : Property
prop_delete = property1 $
  (delete 5 (fromList [(3, 0, 1), (5, 1, 2)])) === (singleton 3 0 1)

prop_alterF : Property
prop_alterF = property1 $
  (alter (\_ => (6, Nothing)) 5 (fromList [(3, 0, 1), (5, 1, 2)])) === (6, (fromList [(3, 0, 1)]))

prop_alterG : Property
prop_alterG = property1 $
  (alter (\_ => (6, Just (1, 4))) 5 (fromList [(3, 0, 1), (5, 1, 2)])) === (6, (fromList [(3, 0, 1), (5, 1, 4)]))

export
props : Group
props = MkGroup "OrdPSQ"
  [ ("prop_eq_refl", prop_eq_refl)
  , ("prop_map_id", prop_map_id)
  , ("prop_null", prop_null)
  , ("prop_size", prop_size)
  , ("prop_member", prop_member)
  , ("prop_notMember", prop_notMember)
  , ("prop_singleton", prop_singleton)
  , ("prop_insert", prop_insert)
  , ("prop_delete", prop_delete)
  , ("prop_alterF", prop_alterF)
  , ("prop_alterG", prop_alterG)
  ]
