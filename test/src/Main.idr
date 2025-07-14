module Main

import BoundedQueue
import Hedgehog
import Map
import OrdPSQ
import RRBVector
import RRBVector1
import Seq.Unsized
import Set

%default total

main : IO ()
main = test
  [ BoundedQueue.props
  , Map.props
  , OrdPSQ.props
  , RRBVector.props
  , RRBVector1.props
  , Seq.Unsized.props
  , Set.props
  ]
