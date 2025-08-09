module SortedSet

import Data.Fin
import Data.SortedSet as SS

export
createSortedSet : Nat -> SortedSet Nat
createSortedSet n = SS.fromList [0..n]

export
insertSortedSet : Nat -> SortedSet Nat
insertSortedSet n = do
  let s = SS.fromList [0..n]
      s = SS.insert 10 s
      s = SS.insert 11 s
      s = SS.insert 12 s
      s = SS.insert 13 s
      s = SS.insert 14 s
      s = SS.insert 15 s
      s = SS.insert 16 s
      s = SS.insert 17 s
      s = SS.insert 18 s
  SS.insert 19 s

export
deleteSortedSet : Nat -> SortedSet Nat
deleteSortedSet n = do
  let m = SS.fromList [0..n]
      m = SS.delete 9 m
      m = SS.delete 8 m
      m = SS.delete 7 m
      m = SS.delete 6 m
      m = SS.delete 5 m
      m = SS.delete 4 m
      m = SS.delete 3 m
      m = SS.delete 2 m
      m = SS.delete 1 m
  SS.delete 0 m

export
containsSortedSet : Nat -> SortedSet Nat
containsSortedSet n = do
  let s = SS.fromList [0..n]
      v = SS.contains 0 s
      v = SS.contains 1 s
      v = SS.contains 2 s
      v = SS.contains 3 s
      v = SS.contains 4 s
      v = SS.contains 5 s
      v = SS.contains 6 s
      v = SS.contains 0 s
      v = SS.contains 8 s
      v = SS.contains 9 s
  s

export
unionSortedSet : Nat -> SortedSet Nat
unionSortedSet n = do
  let s  = SS.fromList [0..n]
      s' = SS.fromList [(n `div` 2)..n]
  union s s'

export
differenceSortedSet : Nat -> SortedSet Nat
differenceSortedSet n = do
  let s  = SS.fromList [0..n]
      s' = SS.fromList [(n `div` 2)..n]
  difference s s'

export
intersectionSortedSet : Nat -> SortedSet Nat
intersectionSortedSet n = do
  let s  = SS.fromList [0..n]
      s' = SS.fromList [(n `div` 2)..n]
  intersection s s'
