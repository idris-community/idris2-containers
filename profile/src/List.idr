module List

import Data.List

export
createList : Nat -> List (Nat,Nat)
createList n = map (\x => (x,plus x 1)) [0..n]
