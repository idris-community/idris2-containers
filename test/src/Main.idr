module Main

import BoundedQueue
import HashPSQ
import Hedgehog
import Map
import NatPSQ
import OrdPSQ
import RRBVector
import RRBVector1
import Seq.Unsized
import Set

%default total

main : IO ()
main = test
  [ BoundedQueue.props
  , HashPSQ.props
  , Map.props
  , NatPSQ.props
  , OrdPSQ.props
  , RRBVector.props
  , RRBVector1.props
  , Seq.Unsized.props
  , Set.props
  ]
