module BoundedQueue1.Sized

import Hedgehog
import Data.BoundedQueue1.Sized
import Data.BoundedQueue1.Sized.Internal
import Data.Linear.Ref1
import Data.Linear.Token
import Data.List

%hide Prelude.Interfaces.toList
%hide Prelude.Stream.(::)

prop_eq_refl : Property
prop_eq_refl = property $ do
  vs <- forAll (list (linear 0 20) anyBits8)
  ( run1 $ \t =>
      let vs' # t := fromList (length vs) vs t
        in toList vs' t ) ===
  ( run1 $ \t =>
      let vs' # t := fromList (length vs) vs t
        in toList vs' t )

prop_from_to_list : Property
prop_from_to_list = property $ do
  vs <- forAll (list (linear 0 10) anyBits8)
  ( run1 $ \t =>
      let vs' # t := fromList (length vs) vs t
        in toList vs' t ) === vs

prop_null : Property
prop_null = property $ do
  vs <- forAll (list (linear 0 20) anyBits8)
  ( run1 $ \t =>
      let vs' # t := fromList (length vs) vs t
        in Data.BoundedQueue1.Sized.null vs' t ) === null vs

prop_size : Property
prop_size = property $ do
  vs <- forAll (list (linear 0 20) anyBits8)
  ( run1 $ \t =>
      let vs' # t := fromList (length vs) vs t
        in Data.BoundedQueue1.Sized.length vs' t ) === length vs

prop_enqueue : Property
prop_enqueue = property $ do
  vs <- forAll (list (linear 0 20) anyBits8)
  ( run1 $ \t =>
      let vs'         # t := fromList (S (length vs)) vs t
          (_ ** vs'') # t := enqueue vs' 1 t
        in Data.BoundedQueue1.Sized.toList vs'' t ) === (vs ++ [1])

prop_prepend : Property
prop_prepend = property $ do
  vs <- forAll (list (linear 0 20) anyBits8)
  ( run1 $ \t =>
      let vs'         # t := fromList (S (length vs)) vs t
          (_ ** vs'') # t := prepend 1 vs' t
        in Data.BoundedQueue1.Sized.toList vs'' t ) === (1 :: vs)

export
props : Group
props = MkGroup "BoundedQueue1 (Sized)"
  [ ("prop_eq_refl", prop_eq_refl)
  , ("prop_from_to_list", prop_from_to_list)
  , ("prop_null", prop_null)
  , ("prop_size", prop_size)
  , ("prop_enqueue", prop_enqueue)
  , ("prop_prepend", prop_prepend)
  ]
