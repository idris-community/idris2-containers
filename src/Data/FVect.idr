||| Fin-based vects encode not just their current size but also their
||| largest size. See also Data.FVect.Capacity for a view that is
||| useful when determining if you want to add to an FVect depending
||| on whether or not it is full.
module Data.FVect

import Data.Vect
import public Data.Fin
import Data.Nat
import Decidable.Equality

%hide Prelude.Types.elem

%default total

||| A Fin-based Vect. Can be thought of as a Vect with both a length
||| and a maximum capacity. Operations like filtering can reduce the
||| length without affecting maximum capacity which provides proof
||| that a Vect's length has not increased over the course of a series
||| of operations.
public export
data FVect : (capacity : Nat) -> (len : Fin (S capacity)) -> (elem : Type) -> Type where
  Nil : FVect capacity FZ elem

  ||| Cons an element to the FVect, increasing its capacity.
  ||| See (:::) for an operator that conses an element without
  ||| increasing capacity.
  (::) : (x : elem)
      -> (xs : FVect capacity len elem)
      -> FVect (S capacity) (FS len) elem

%name FVect xs, ys, zs

Uninhabited (FVect 0 (FS l) e) where
  uninhabited [] impossible
  uninhabited (x :: xs) impossible

||| Cons an element without increasing the capacity of the FVect. You
||| must make sure the capacity and length of the FVect being consed
||| onto are accessible in the context where you call this.
|||
||| The function signature is a bit tricky because it needs to ensure
||| you are going from length of type Fin n to length of type Fin n
||| but calling Fin's FS constructor increments n. To increment the
||| value stored without weakening the bounds of the Fin, we go from
||| (weaken (Fin (S n))) to (FS (Fin (S n))).
|||
||| In other words, we go from a weaker input Fin to the succesor of a
||| stronger bounded Fin.
public export
consWeaker : {n : Nat}
          -> {len' : Fin (S n)}
          -> (v : elem)
          -> FVect (S n) (weaken len') elem
          -> FVect (S n) (FS len') elem
consWeaker {n = n}     {len' = FZ}      v _ = [v]
consWeaker {n = 0}     {len' = (FS l')} _ _ = absurd l'
consWeaker {n = (S k)} {len' = (FS l')} v (x :: xs) = v :: (x
           `consWeaker` xs)

public export
strengthenLT : {0 n : _}
            -> (j : Fin (S n))
            -> (0 prf : (finToNat j) `LT` n) =>
               Fin n
strengthenLT FZ @{(LTESucc _)} = FZ
strengthenLT (FS x) @{(LTESucc _)} = FS (strengthenLT x)

weakenStrengthenCancel : {0 n : _}
                      -> (x : Fin (S n))
                      -> (0 prf : (finToNat x) `LT` n) =>
                         (weaken (strengthenLT x)) = x
weakenStrengthenCancel FZ @{(LTESucc y)} = Refl
weakenStrengthenCancel (FS x) @{(LTESucc y)} =
  cong FS (weakenStrengthenCancel x)

||| Like `consWeaker`, cons an element onto an FVect without changing
||| its capacity.
|||
||| You need only know that the existing FVect is not at capacity to
||| know that an element can be consed onto it without increasing the
||| capacity.
public export
consLT : {n : Nat}
      -> {len : Fin (S (S n))}
      -> (0 ltPrf : (finToNat len) `LT` (S n)) =>
         (v : elem)
      -> FVect (S n) len elem
      -> FVect (S n) (FS (strengthenLT len)) elem
consLT v xs with (weakenStrengthenCancel len)
  consLT v xs | cancelPrf = v `consWeaker` (rewrite cancelPrf in xs)

||| Like `consWeaker`, cons an element onto an FVect without changing
||| its capacity.
|||
||| You need only know that the existing FVect is not at capacity to
||| know that an element can be consed onto it without increasing the
||| capacity.
public export
(:::) : {n : Nat}
     -> {len : Fin (S (S n))}
     -> (0 ltPrf : (finToNat len) `LT` (S n)) =>
        (v : elem)
     -> FVect (S n) len elem
     -> FVect (S n) (FS (strengthenLT len)) elem
(:::) = consLT


||| Create an empty FVect with the given capacity.
export
empty : (capacity : Nat) -> FVect capacity FZ elem
empty _ = []

||| Create an FVect by replicating the given element enough to fill
||| the needed length.
export
replicate : {capacity : Nat}
         -> (l : Fin (S capacity))
         -> elem
         -> FVect capacity l elem
replicate {capacity} FZ x = []
replicate {capacity = (S k)} (FS y) x = x :: replicate y x

||| Allow FVect to hold one more element.
||| Do not change the elements currently in the FVect.
public export
addCapacity : FVect c l a -> (FVect (S c) (weaken l) a)
addCapacity [] = []
addCapacity (x :: xs) = x :: (addCapacity xs)

||| Allow FVect to hold n more elements.
||| Do not change the elements currently in the FVect.
public export
addCapacityN : (n : Nat)
            -> FVect capacity l a
            -> (FVect (capacity + n) (weakenN n l) a)
addCapacityN n [] = Nil
addCapacityN n (x :: xs) = x :: (addCapacityN n xs)

||| Reduce the FVect's capacity to hold elements.
public export
removeCapacity : {n : Nat}
              -> {len' : Fin (S n)}
              -> FVect (S n) (weaken len') a
              -> FVect n len' a
removeCapacity {n = n}     {len' = FZ}      [] = []
removeCapacity {n = 0}     {len' = (FS l')} (x :: xs) = absurd l'
removeCapacity {n = (S k)} {len' = (FS l')} (x :: xs) =
  x :: (removeCapacity xs)

||| Calculate the length of the FVect.
export
length : FVect capacity l a
      -> Nat
length [] = 0
length (x :: xs) = S (length xs)

--
-- to/from List and Vect
--

||| Get the smallest FVect that can contain the given Vect.
export
fromVect : Vect l a -> FVect l (last {n=l}) a
fromVect [] = []
fromVect (x :: xs) = x :: fromVect xs

export
toVect : FVect c l elem -> Vect (finToNat l) elem
toVect [] = []
toVect (x :: xs) = x :: (toVect xs)

-- toList provided by Foldable/Data.List

--
-- Accessors
--

||| All but the first element of the FVect.
||| This operation does not change capacity. This means you can carry
||| out this operation and retain proof that the new FVect length is
||| less than or equal to the original FVect (although in this case
||| the length is exactly one less than before the call to tail).
public export
tail : FVect c (FS l) elem -> FVect c (weaken l) elem
tail (x :: xs) = addCapacity xs

||| Like tail but reduces the capacity by 1 in addition
||| to dropping the first element.
public export
dropFirst : FVect (S c) (FS l) elem -> FVect c l elem
dropFirst (x :: xs) = xs

public export
head : FVect c (FS l) elem -> elem
head (x :: _) = x

public export
last : FVect c (FS l) elem -> elem
last [x] = x
last (x :: (y :: xs)) = last $ y :: xs

||| All but the last element of the FVect.
||| This operation does not change capacity. This means you can carry
||| out this operation and retain proof that the new FVect length is
||| less than or equal to the original FVect (although in this case
||| the length is exactly one less than before the call to tail).
public export
init : FVect c (FS l) elem -> FVect c (weaken l) elem
init [_] = []
init (x :: (y :: xs)) = x :: (init $ y :: xs)

||| Like init but reduces the capacity by 1 in addition to removing
||| the last element.
public export
dropLast : FVect (S c) (FS l) elem -> FVect c l elem
dropLast [_] = []
dropLast (x :: (y :: xs)) = x :: (dropLast $ y :: xs)

--
-- Properties
--

||| If two FVects are equal, their heads and tails are equal.
export
fVectInjective : {0 xs : FVect c l elem}
              -> {0 ys : FVect c l elem}
              -> x :: xs = y :: ys
              -> (x = y, xs = ys)
fVectInjective Refl = (Refl, Refl)

||| If you add and then remove capacity, you are left with the
||| original capacity.
||| In fact, you are left with exactly the original FVect.
export
addRemoveCapacityInverse : (xs : FVect c l elem)
                        -> (removeCapacity (addCapacity xs)) = xs
addRemoveCapacityInverse [] = Refl
addRemoveCapacityInverse (x :: xs) =
  cong (x ::) (addRemoveCapacityInverse xs)

||| The calculated length of an FVect reifies the erased length of the
||| FVect.
export
lengthReifies : (v : FVect c l elem) -> length v = finToNat l
lengthReifies [] = Refl
lengthReifies (x :: xs) = cong S (lengthReifies xs)

--
-- Functor
--

export
Functor (FVect c l) where
  map f [] = []
  map f (x :: xs) = f x :: map f xs

--
-- Applicative
--

export
{capacity : Nat} -> {l : Fin (S capacity)} -> Applicative (FVect capacity l) where
  pure = replicate _

  [] <*> [] = []
  (f :: fs) <*> (x :: xs) = f x :: (fs <*> xs)

--
-- Foldable
--

export
Foldable (FVect c l) where
  foldr _ acc [] = acc
  foldr f acc (x :: xs) = f x $ foldr f acc xs

--
-- Eq/DecEq
--

export
Eq elem => Eq (FVect c l elem) where
  [] == [] = True
  (x :: xs) == (y :: ys) = if x == y
                              then xs == ys
                              else False

export
DecEq elem => DecEq (FVect c l elem) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) with (decEq x y, decEq xs ys)
    decEq (y :: ys) (y :: ys) | (Yes Refl, Yes Refl)  = Yes Refl
    decEq (x :: xs) (y :: ys) | (_,        No contra) = No $ contra . snd . fVectInjective
    decEq (x :: xs) (y :: ys) | (No contra, _)        = No $ contra . fst . fVectInjective

--
-- Utility
--

||| Remove all Nothings from the FVect.
||| This operation does not change capacity. That means you can carry
||| out this operation and retain proof that the new FVect length is
||| less than or equal to that of the original FVect.
export
catMaybes : {len : Fin (S capacity)}
         -> FVect capacity len (Maybe elem)
         -> (len' : Fin (S capacity) ** FVect capacity len' elem)
catMaybes {len = FZ} [] = (FZ ** [])
catMaybes {len = (FS k)} (Nothing  :: xs) = let (l' ** rest) = catMaybes xs in
                                              (weaken l' ** addCapacity rest)
catMaybes {len = (FS k)} ((Just x) :: xs) = let (l' ** rest) = catMaybes xs in
                                              (FS l' ** x :: rest)

||| Map all elements, removing any Nothings along the way.
||| This operation does not change capacity. That means you can carry
||| out this operation and retain proof that the new FVect length is
||| less than or equal to that of the original FVect.
export
mapMaybes : {len : Fin (S capacity)}
         -> (f : elem -> Maybe elem')
         -> FVect capacity len elem
         -> (len' : Fin (S capacity) ** FVect capacity len' elem')
mapMaybes {len = FZ} f [] = (FZ ** [])
mapMaybes {len = (FS k)} f (x :: xs) = case (f x) of
                                            Nothing => let (l' ** rest) = mapMaybes f xs in
                                                           (weaken l' ** addCapacity rest)
                                            (Just y) => let (l' ** rest) = mapMaybes f xs in
                                                            (FS l' ** y :: rest)

||| Filter down to only elements matching the predicate.
||| This operation does not change capacity. That means you can carry
||| out this operation and retain proof that the new FVect length is
||| less than or equal to that of the original FVect.
export
filter : (elem -> Bool)
      -> FVect capacity len elem
      -> (len' : Fin (S capacity) ** FVect capacity len' elem)
filter p [] = (FZ ** [])
filter p (x :: xs) = let (l' ** rest) = filter p xs in
                         if p x
                            then (FS l' ** x :: rest)
                            else (weaken l' ** addCapacity rest)

