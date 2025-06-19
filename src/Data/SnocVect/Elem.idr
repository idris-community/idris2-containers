module Data.SnocVect.Elem

import Data.SnocVect
import Decidable.Equality

%default total

public export
data Elem : SnocVect k a -> a -> Type where
  Here  : Elem (sx :< x) x
  There : Elem sx x -> Elem (sx :< y) x

export
{sx : SnocVect 0 a} -> Uninhabited (Elem sx x) where
  uninhabited Here impossible
  uninhabited (There x) impossible

neitherHereNorThere : DecEq a => {0 x,y : a} ->
                      Not (x = y) ->
                      Not (Elem sy x) ->
                      Not (Elem (sy :< y) x)
neitherHereNorThere _ notThere (There z) = notThere z
neitherHereNorThere notHere _ Here = notHere Refl

export
isElem : DecEq a => (x : a) -> (sx : SnocVect k a) -> Dec (Elem sx x)
isElem x [<] = No absurd
isElem x (sx :< y) with (decEq x y)
  isElem y (sx :< y) | (Yes Refl) = Yes Here
  isElem x (sx :< y) | (No contra) with (isElem x sx)
    isElem x (sx :< y) | (No _) | (Yes prf) = Yes (There prf)
    isElem x (sx :< y) | (No yNotX) | (No xNotInSx) =
      No (neitherHereNorThere yNotX xNotInSx)

