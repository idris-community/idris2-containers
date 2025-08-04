module Main

import BoundedQueue
import HashPSQ
import Hedgehog
import LRUCache
import Map
import NatPSQ
import OrdPSQ
import RRBVector.Sized
import RRBVector.Unsized
import RRBVector1.Sized
import RRBVector1.Unsized
import Seq.Sized
import Seq.Unsized
import Set

%default total

main : IO ()
main = test
  [ BoundedQueue.props
  , HashPSQ.props
  , LRUCache.props
  , Map.props
  , NatPSQ.props
  , OrdPSQ.props
  , RRBVector.Sized.props
  , RRBVector.Unsized.props
  , RRBVector1.Sized.props
  , RRBVector1.Unsized.props
  , Seq.Sized.props
  , Seq.Unsized.props
  , Set.props
  ]
