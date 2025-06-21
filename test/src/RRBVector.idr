module RRBVector

import Hedgehog
import Data.RRBVector

rrbvectorOf : Gen a -> Gen (RRBVector a)
rrbvectorOf g = fromList <$> list (linear 0 20) g

rrbvectorBits : Gen (RRBVector Bits8)
rrbvectorBits = rrbvectorOf anyBits8

prop_eq_refl : Property
prop_eq_refl = property $ do
  vs <- forAll rrbvectorBits
  vs === vs

props : Group
props = MkGroup "RRBVector"
  [ ("prop_eq_refl", prop_eq_refl)
  ]
