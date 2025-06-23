module Main

import Hedgehog
import RRBVector
import RRBVector1

%default total

main : IO ()
main = test
  [ RRBVector.props
  , RRBVector1.props
  ]
