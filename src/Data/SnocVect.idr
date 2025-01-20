module Data.SnocVect

import Data.Vect

%hide Prelude.Types.elem

%default total

||| A Backwards Vect
public export
data SnocVect : Nat -> Type -> Type where
  ||| Empty snoc-vect
  Lin : SnocVect 0 a

  ||| A non-empty snoc-vect, consisting of the rest of the snoc-vect and the final element.
  (:<) : (SnocVect n a) -> a -> SnocVect (S n) a

%name SnocVect sx, sy, sz

export infixl 7 <><
export infixr 6 <>>

||| 'fish': Action of lists on snoc-lists
public export
(<><) : SnocVect n a -> Vect m a -> SnocVect (n + m) a
sx <>< [] = rewrite plusZeroRightNeutral n in sx
sx <>< ((::) x xs {len}) =
  rewrite sym $ plusSuccRightSucc n len in
          sx :< x <>< xs

||| 'chips': Action of snoc-lists on lists
public export
(<>>) : SnocVect j a -> Vect k a -> Vect (j + k) a
Lin       <>> xs = xs
((:<) sx x {n}) <>> xs =
  rewrite plusSuccRightSucc n k in
          sx <>> x :: xs

export
Cast (SnocVect n a) (Vect n a) where
  cast sx = rewrite sym $ plusZeroRightNeutral n in
                    sx <>> []

export
Cast (Vect n a) (SnocVect n a) where
  cast xs = Lin <>< xs

||| Transform to a vect but keeping the contents in the spine order (term depth).
public export
asVect : SnocVect n type -> Vect n type
asVect = (reverse . cast)

public export
Eq a => Eq (SnocVect n a) where
  (==) Lin Lin = True
  (==) (sx :< x) (sy :< y) = x == y && sx == sy
  (==) _ _ = False

public export
Ord a => Ord (SnocVect n a) where
  compare Lin Lin = EQ
  compare (sx :< x) (sy :< y)
    = case compare sx sy of
        EQ => compare x y
        c  => c

||| True iff input is Lin
public export
isLin : SnocVect n a -> Bool
isLin Lin = True
isLin (sx :< x) = False

||| True iff input is (:<)
public export
isSnoc : SnocVect n a -> Bool
isSnoc Lin     = False
isSnoc (sx :< x) = True

public export
(++) : (sx : SnocVect j a) ->  (sy : SnocVect k a) -> SnocVect (j + k) a
(++) sx Lin = rewrite plusZeroRightNeutral j in sx
(++) sx ((:<) sy y {n}) =
  rewrite sym $ plusSuccRightSucc j n in
          (sx ++ sy) :< y

public export
length : SnocVect n a -> Nat
length Lin = Z
length (sx :< x) = S $ length sx

export
lengthCorrect : (sx : SnocVect n a) -> length sx = n
lengthCorrect [<]       = Refl
lengthCorrect (sx :< x) = cong S (lengthCorrect sx)

public export
replicate : (k : Nat) -> a -> SnocVect k a
replicate 0 x = [<]
replicate (S k) x = replicate k x :< x

||| The "head" of the snoc-vect
public export
deah : SnocVect (S n) a -> a
deah (sx :< x) = x

||| The "tail" of the snoc-vect
public export
liat : SnocVect (S n) a -> SnocVect n a
liat (sx :< x) = sx

export
Show a => Show (SnocVect n a) where
  show sx = concat ("[< " :: intersperse ", " (show' [] sx) ++ ["]"])
    where
      show' : Vect j String -> SnocVect k a -> Vect (j + k) String
      show' acc Lin       = rewrite plusZeroRightNeutral j in acc
      show' acc ((:<) xs x {n}) =
        rewrite sym $ plusSuccRightSucc j n in
                show' (show x :: acc) xs

public export
Functor (SnocVect n) where
  map f Lin = Lin
  map f (sx :< x) = (map f sx) :< (f x)

public export
Zippable (SnocVect k) where
  zipWith _ [<] [<] = [<]
  zipWith f (sx :< x) (sy :< y) = zipWith f sx sy :< f x y

  zipWith3 _ [<] [<] [<] = [<]
  zipWith3 f (sx :< x) (sy :< y) (sz :< z) = zipWith3 f sx sy sz :< f x y z

  unzipWith f [<] = ([<], [<])
  unzipWith f (sx :< x) = let (b, c) = f x
                              (sb, sc) = unzipWith f sx in
                              (sb :< b, sc :< c)

  unzipWith3 f [<] = ([<], [<], [<])
  unzipWith3 f (sx :< x) = let (b, c, d) = f x
                               (sb, sc, sd) = unzipWith3 f sx in
                               (sb :< b, sc :< c, sd :< d)

public export
Semigroup a => Semigroup (SnocVect n a) where
  (<+>) = zipWith (<+>)

public export
{k : Nat} -> Monoid a => Monoid (SnocVect k a) where
  neutral = replicate k neutral

public export
Foldable (SnocVect n) where
  foldr f z = foldr f z . (<>> [])

  foldl f z xs = h xs where
    h : SnocVect k elem -> acc
    h Lin = z
    h (xs :< x) = f (h xs) x

  null Lin      = True
  null (_ :< _) = False

  toList = toList . (<>> [])

  foldMap f = foldl (\xs, x => xs <+> f x) neutral

public export
{k : Nat} -> Applicative (SnocVect k) where
  pure = replicate _
  fs <*> sx = zipWith apply fs sx

||| Get diagonal elements
public export
diag : SnocVect len (SnocVect len elem) -> SnocVect len elem
diag [<]             = [<]
diag (ssx :< (sx :< x)) = diag (map liat ssx) :< x

||| This monad is different from the List monad, (>>=)
||| uses the diagonal.
public export
{k : Nat} -> Monad (SnocVect k) where
  sx >>= f = diag (map f sx)

public export
Traversable (SnocVect k) where
  traverse _ Lin = pure Lin
  traverse f (xs :< x) = [| traverse f xs :< f x |]

||| Check if something is a member of a snoc-vect using the default Boolean equality.
public export
elem : Eq a => a -> SnocVect k a -> Bool
elem x Lin = False
elem x (sx :< y) = x == y || elem x sx

||| Find the first element of the snoc-vect that satisfies the predicate.
public export
find : (a -> Bool) -> SnocVect k a -> Maybe a
find p Lin = Nothing
find p (xs :< x) = if p x then Just x else find p xs

||| Satisfiable if `k` is a valid index into `xs`.
|||
||| @ k  the potential index
||| @ xs the snoc-list into which k may be an index
public export
data InBounds : (k : Nat) -> (xs : SnocVect j a) -> Type where
    ||| Z is a valid index into any cons cell
    InFirst : InBounds Z (xs :< x)
    ||| Valid indices can be extended
    InLater : InBounds k xs -> InBounds (S k) (xs :< x)

||| Find the index and proof of InBounds of the first element (if exists) of a
||| snoc-list that satisfies the given test, else `Nothing`.
public export
findIndex : (a -> Bool) -> (sx : SnocVect k a) -> Maybe $ Fin (length sx)
findIndex _ Lin = Nothing
findIndex p (xs :< x) = if p x
  then Just FZ
  else FS <$> findIndex p xs
