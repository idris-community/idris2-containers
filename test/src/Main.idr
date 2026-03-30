module Main

import BoundedQueue.Unsized
import BoundedQueue1.Unsized
import HashPSQ
import Hedgehog
import LRUCache
import LRUCache1
import Map
import NatPSQ
import OrdPSQ
import RRBVector.Unsized
import RRBVector1.Unsized
import Seq.Sized
import Seq.Unsized
import Seq1.Unsized
import Set

%default total

main : IO ()
main = test
  [ BoundedQueue.Unsized.props
  , BoundedQueue1.Unsized.props
  , HashPSQ.props
  , LRUCache.props
  , LRUCache1.props
  , Map.props
  , NatPSQ.props
  , OrdPSQ.props
  , RRBVector.Unsized.props
  , RRBVector1.Unsized.props
  , Seq.Sized.props
  , Seq.Unsized.props
  , Seq1.Unsized.props
  , Set.props
  ]
