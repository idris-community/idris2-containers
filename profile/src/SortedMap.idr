module SortedMap

import Data.Fin
import Data.SortedMap as SM

export
createSortedMap : Nat -> SortedMap Nat Nat
createSortedMap n = SM.fromList $ map (\x => (x,plus x 1)) [0..n]

export
insertSortedMap : Nat -> SortedMap Nat Nat
insertSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
      m = SM.insert 0 2 m
      m = SM.insert 1 3 m
      m = SM.insert 2 4 m
      m = SM.insert 3 5 m
      m = SM.insert 4 6 m
      m = SM.insert 5 7 m
      m = SM.insert 6 8 m
      m = SM.insert 7 9 m
      m = SM.insert 8 10 m
  SM.insert 9 11 m

export
deleteSortedMap : Nat -> SortedMap Nat Nat
deleteSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
      m = SM.delete 9 m
      m = SM.delete 8 m
      m = SM.delete 7 m
      m = SM.delete 6 m
      m = SM.delete 5 m
      m = SM.delete 4 m
      m = SM.delete 3 m
      m = SM.delete 2 m
      m = SM.delete 1 m
  SM.delete 0 m

export
updateSortedMap : Nat -> SortedMap Nat Nat
updateSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
      m = SM.update f 0 m
      m = SM.update f 1 m
      m = SM.update f 2 m
      m = SM.update f 3 m
      m = SM.update f 4 m
      m = SM.update f 5 m
      m = SM.update f 6 m
      m = SM.update f 7 m
      m = SM.update f 8 m
  SM.update f 9 m
  where
    f : (Maybe Nat -> Maybe Nat)
    f Nothing  = Nothing
    f (Just x) =
      case x `mod` 2  == 0 of
        True  =>
          Nothing
        False =>
          Just $ x * x

export
lookupSortedMap : Nat -> SortedMap Nat Nat
lookupSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
      v = SM.lookup 0 m
      v = SM.lookup 1 m
      v = SM.lookup 2 m
      v = SM.lookup 3 m
      v = SM.lookup 4 m
      v = SM.lookup 5 m
      v = SM.lookup 6 m
      v = SM.lookup 0 m
      v = SM.lookup 8 m
      v = SM.lookup 9 m
  m

export
keysSortedMap : Nat -> List Nat
keysSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
  SM.keys m

export
valuesSortedMap : Nat -> List Nat
valuesSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
  SM.values m
