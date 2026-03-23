module Main

import BoundedQueue.Sized
import BoundedQueue.Unsized
import BoundedQueue1.Sized
import BoundedQueue1.Unsized
import HashPSQ
import Hedgehog
import LRUCache
import LRUCache1
import Map
import NatPSQ
import OrdPSQ
import RRBVector.Sized
import RRBVector.Unsized
import RRBVector1.Sized
import RRBVector1.Unsized
import Seq.Sized
import Seq.Unsized
import Seq1.Sized
import Seq1.Unsized
import Set

%default total

main : IO ()
main = test
  [ BoundedQueue.Sized.props
  , BoundedQueue.Unsized.props
  , BoundedQueue1.Sized.props
  , BoundedQueue1.Unsized.props
  , HashPSQ.props
  , LRUCache.props
  , LRUCache1.props
  , Map.props
  , NatPSQ.props
  , OrdPSQ.props
  , RRBVector.Sized.props
  , RRBVector.Unsized.props
  , RRBVector1.Sized.props
  , RRBVector1.Unsized.props
  , Seq.Sized.props
  , Seq.Unsized.props
  , Seq1.Sized.props
  , Seq1.Unsized.props
  , Set.props
  ]
