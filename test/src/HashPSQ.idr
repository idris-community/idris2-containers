module HashPSQ

import Hedgehog
import Data.List
import Data.Hashable
import Data.HashPSQ

%hide Prelude.Interfaces.toList
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Stream.(::)
%hide Data.NatPSQ.member
%hide Data.OrdPSQ.member
%hide Data.NatPSQ.notMember
%hide Data.OrdPSQ.notMember
%hide Data.NatPSQ.insert
%hide Data.OrdPSQ.insert
%hide Data.NatPSQ.delete
%hide Data.OrdPSQ.delete
%hide Data.NatPSQ.alter
%hide Data.OrdPSQ.alter
%hide Data.NatPSQ.alterMin
%hide Data.OrdPSQ.alterMin
%hide Data.NatPSQ.findMin
%hide Data.OrdPSQ.findMin
%hide Data.NatPSQ.minView
%hide Data.OrdPSQ.minView

hashpsqOf : Hashable a => Ord a => Gen a -> Gen (HashPSQ a a a)
hashpsqOf g = do
  k <- list (linear 0 20) g
  p <- list (linear 0 20) g
  v <- list (linear 0 20) g
  pure $ fromList $ zip3 k p v

hashpsqOf' : Hashable a => Ord a => Gen a -> Gen (HashPSQ a a a)
hashpsqOf' g = do
  k <- list (linear 1 20) g
  p <- list (linear 1 20) g
  v <- list (linear 1 20) g
  pure $ fromList $ zip3 k p v

hashpsqBits : Gen (HashPSQ Bits8 Bits8 Bits8)
hashpsqBits = hashpsqOf anyBits8

hashpsqBits' : Gen (HashPSQ Bits8 Bits8 Bits8)
hashpsqBits' = hashpsqOf' anyBits8

prop_eq_refl : Property
prop_eq_refl = property $ do
  vs <- forAll hashpsqBits
  vs === vs

prop_map_id : Property
prop_map_id = property $ do
  vs <- forAll hashpsqBits
  vs === map id vs

prop_null : Property
prop_null = property $ do
  vs <- forAll hashpsqBits
  null vs === null (Data.HashPSQ.toList vs)

prop_size : Property
prop_size = property $ do
  vs <- forAll hashpsqBits
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

prop_alterMin : Property
prop_alterMin = property1 $
  (alterMin (\_ => (6, Just (3, 0, 4))) (fromList [(3, 0, 1), (5, 1, 2)])) === (6, (fromList [(3, 0, 4), (5, 1, 2)]))

prop_findMin : Property
prop_findMin = property1 $
  (findMin (fromList [(3, 0, 1), (5, 1, 2)])) === (Just (3 ,0 ,1))

prop_deleteView : Property
prop_deleteView = property1 $
  (deleteView 5 (fromList [(3, the Nat 0, 1), (5, the Nat 1, 2)])) === (Just (1, 2, singleton 3 0 1))

prop_insertView : Property
prop_insertView = property1 $
  (insertView 5 (the Nat 1) 2 (fromList [(3, 0, 1), (5, 0, 2)])) === (Just (0, 2), fromList [(3, 0, 1), (5, 1, 2)])

prop_minView : Property
prop_minView = property1 $
  (minView (fromList [(3, 0, 1), (5, 1, 2)])) === (Just (3, 0, 1, fromList [(5, 1, 2)]))

prop_deleteMin : Property
prop_deleteMin = property1 $
  (deleteMin (fromList [(3, the Nat 0, 1), (5, 1, 2)])) === (singleton 5 1 2)

export
props : Group
props = MkGroup "HashPSQ"
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
  , ("prop_alterMin", prop_alterMin)
  , ("prop_findMin", prop_findMin)
  , ("prop_deleteView", prop_deleteView)
  , ("prop_insertView", prop_insertView)
  , ("prop_minView", prop_minView)
  , ("prop_deleteMin", prop_deleteMin)
  ]
