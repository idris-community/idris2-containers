module LRUCache1

import Hedgehog
import Data.Hashable
import Data.LRUCache1
import Data.Linear.Ref1
import Data.Linear.Token
import Data.So

prop_eviction : Property
prop_eviction = property1 $
  case decSo (1 >= 0) of
    No _    =>
      failure
    Yes prf =>
      ( run1 $ \t =>
          let c                     # t := Data.LRUCache1.empty (S Z) {prfcapacity=prf} t
              c'                    # t := Data.LRUCache1.insert Z Z c t
              (MkLRUCache1 _ s _ _) # t := Data.LRUCache1.insert (S Z) (S Z) c' t
            in read1 s t ) === 1

export
props : Group
props = MkGroup "LRUCache1"
  [ ("prop_eviction", prop_eviction)
  ]
