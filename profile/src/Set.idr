module Set

import Data.Fin
import Data.Set as S

export
createSet : Nat -> Set Nat
createSet n = S.fromList [0..n]

export
insertSet : Nat -> Set Nat
insertSet n = do
  let s = S.fromList [0..n]
      s = S.insert 10 s
      s = S.insert 11 s
      s = S.insert 12 s
      s = S.insert 13 s
      s = S.insert 14 s
      s = S.insert 15 s
      s = S.insert 16 s
      s = S.insert 17 s
      s = S.insert 18 s
  S.insert 19 s

export
deleteSet : Nat -> Set Nat
deleteSet n = do
  let m = S.fromList [0..n]
      m = S.delete 9 m
      m = S.delete 8 m
      m = S.delete 7 m
      m = S.delete 6 m
      m = S.delete 5 m
      m = S.delete 4 m
      m = S.delete 3 m
      m = S.delete 2 m
      m = S.delete 1 m
  S.delete 0 m

export
memberSet : Nat -> Set Nat
memberSet n = do
  let s = S.fromList [0..n]
      v = S.member 0 s
      v = S.member 1 s
      v = S.member 2 s
      v = S.member 3 s
      v = S.member 4 s
      v = S.member 5 s
      v = S.member 6 s
      v = S.member 0 s
      v = S.member 8 s
      v = S.member 9 s
  s

export
unionSet : Nat -> Set Nat
unionSet n = do
  let s  = S.fromList [0..n]
      s' = S.fromList [(n `div` 2)..n]
  union s s'

export
differenceSet : Nat -> Set Nat
differenceSet n = do
  let s  = S.fromList [0..n]
      s' = S.fromList [(n `div` 2)..n]
  difference s s'

export
intersectionSet : Nat -> Set Nat
intersectionSet n = do
  let s  = S.fromList [0..n]
      s' = S.fromList [(n `div` 2)..n]
  intersection s s'
