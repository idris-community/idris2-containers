module Data.FVect.Capacity

import Data.FVect
import Data.Nat
import Decidable.Equality

finPrf : {n : Nat}
      -> (x : Fin (S n))
      -> Either (finToNat x `LT` n) (finToNat x = n)
finPrf {n = 0} FZ = Right Refl
finPrf {n = (S k)} FZ = Left (LTESucc LTEZero)
finPrf {n = (S k)} (FS x) = bimap LTESucc (\p => cong S p) $ finPrf x

||| A representation of the remaining capacity an FVect has for storage.
||| A `Full` value has proof that there are `n` values in a vect with
||| capacity `n`.
||| A `NotFull` value has exactly what you need to cons an additional
||| value onto an FVect.
public export
data Capacity : Type -> Type where
  Full : (0 eqPrf : finToNat l = c)
      -> Capacity (FVect c l e)
  NotFull : {0 n : Nat}
         -> {0 len : Fin (S (S n))}
         -> (0 ltPrf : (finToNat len) `LT` (S n))
         -> Capacity (FVect (S n) len e)

||| Determine if the given FVect has more capacity for storage or not.
export
capacity : {c : Nat}
        -> {l : Fin (S c)}
        -> (0 _ : FVect c l e)
        -> Capacity (FVect c l e)
capacity {c} _ with (finPrf l)
  capacity {c}         _ | (Right eq) = Full eq
  capacity {c = (S k)} _ | (Left lte) = NotFull lte

||| Calculate if the given FVect has more capacity for storage or not.
export
capacity' : {c : Nat}
         -> {0 l : Fin (S c)}
         -> FVect c l e
         -> Capacity (FVect c l e)
capacity' {c = 0} [] = Full Refl
capacity' {c = (S k)} [] = NotFull (LTESucc LTEZero)
capacity' {c = (S k)} (x :: xs) with (capacity' xs)
  capacity' {c = (S k)} (x :: xs) | (Full eqPrf) =
    Full (rewrite eqPrf in Refl)
  capacity' {c = (S (S n))} (x :: xs) | (NotFull ltPrf) =
    NotFull (LTESucc ltPrf)

