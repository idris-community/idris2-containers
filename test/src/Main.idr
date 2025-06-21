module Main

import Hedgehog
import RRBVector

%default total

main : IO ()
main = test
  [ RRBVector.props
  ]
