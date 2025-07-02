module Main

import Hedgehog
import Map
import RRBVector
import RRBVector1

%default total

main : IO ()
main = test
  [ Map.props
  , RRBVector.props
  , RRBVector1.props
  ]
