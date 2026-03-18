module LRUCache1

import Hedgehog
import Data.Hashable
import Data.LRUCache1
import Data.Linear.Ref1
import Data.Linear.Token
import Data.So

prop_eviction : Property
prop_eviction = property1 $
  case decSo ((S Z) >= Z) of
    No _    =>
      failure
    Yes prf =>
      ( run1 $ \t =>
          let cache                 # t := Data.LRUCache1.empty (S Z) {prfcapacity=prf} t
              cache'                # t := Data.LRUCache1.insert Z Z cache t
              (MkLRUCache1 cache'') # t := Data.LRUCache1.insert (S Z) (S Z) cache' t
              (MkLRUCache _ s _ _)  # t := read1 cache'' t
            in s # t ) === 1

export
props : Group
props = MkGroup "LRUCache1"
  [ ("prop_eviction", prop_eviction)
  ]
