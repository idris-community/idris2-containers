module Main

import BoundedQueue.Unsized
import BoundedQueue1.Unsized
import Concurrent.BoundedQueue1
import Concurrent.LRUCache1
import Concurrent.Map1
import Concurrent.Seq1
import Concurrent.Set1
import HashPSQ
import Hedgehog
import LRUCache
import LRUCache1
import Map
import Map1
import NatPSQ
import OrdPSQ
import Seq.Sized
import Seq.Unsized
import Seq1.Unsized
import Set
import Set1

%default total

main : IO ()
main = do
  Concurrent.BoundedQueue1.main
  Concurrent.LRUCache1.main
  Concurrent.Map1.main
  Concurrent.Seq1.main
  Concurrent.Set1.main
  test
    [ BoundedQueue.Unsized.props
    , BoundedQueue1.Unsized.props
    , HashPSQ.props
    , LRUCache.props
    , LRUCache1.props
    , Map.props
    , Map1.props
    , NatPSQ.props
    , OrdPSQ.props
    , Seq.Sized.props
    , Seq.Unsized.props
    , Seq1.Unsized.props
    , Set.props
    , Set1.props
    ]
