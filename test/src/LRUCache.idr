module LRUCache

import Hedgehog
import Data.Hashable
import Data.LRUCache

prop_eviction : Property
prop_eviction = property1 $
  let c   = empty 1
      c'  = insert 0 0 c
      c'' = insert 1 1 c'
    in c'' === ( MkLRUCache 1
                            1
                            2
                            (singleton 1 1 1)
               )

export
props : Group
props = MkGroup "LRUCache"
  [ ("prop_eviction", prop_eviction)
  ]
