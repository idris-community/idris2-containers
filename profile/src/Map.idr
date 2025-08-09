module Map

import Data.Map as M

import Profile

export
createMap : Nat -> Map Nat Nat
createMap n = M.fromList $ map (\x => (x,plus x 1)) [0..n]

export
insertMap : Nat -> Map Nat Nat
insertMap n = do
  let m = M.fromList $ map (\x => (x,plus x 1)) [0..n]
      m = M.insert 0 2 m
      m = M.insert 1 3 m
      m = M.insert 2 4 m
      m = M.insert 3 5 m
      m = M.insert 4 6 m
      m = M.insert 5 7 m
      m = M.insert 6 8 m
      m = M.insert 7 9 m
      m = M.insert 8 10 m
  M.insert 9 11 m

export
deleteMap : Nat -> Map Nat Nat
deleteMap n = do
  let m = M.fromList $ map (\x => (x,plus x 1)) [0..n]
      m = M.delete 9 m
      m = M.delete 8 m
      m = M.delete 7 m
      m = M.delete 6 m
      m = M.delete 5 m
      m = M.delete 4 m
      m = M.delete 3 m
      m = M.delete 2 m
      m = M.delete 1 m
  M.delete 0 m

export
updateMap : Nat -> Map Nat Nat
updateMap n = do
  let m = M.fromList $ map (\x => (x,plus x 1)) [0..n]
      m = M.update f 0 m
      m = M.update f 1 m
      m = M.update f 2 m
      m = M.update f 3 m
      m = M.update f 4 m
      m = M.update f 5 m
      m = M.update f 6 m
      m = M.update f 7 m
      m = M.update f 8 m
  M.update f 9 m
  where
    f : (Nat -> Maybe Nat)
    f x = case x `mod` 2  == 0 of
            True  =>
              Nothing
            False =>
              Just $ x * x

export
lookupMap : Nat -> Map Nat Nat
lookupMap n = do
  let m = M.fromList $ map (\x => (x,plus x 1)) [0..n]
      v = M.lookup 0 m
      v = M.lookup 1 m
      v = M.lookup 2 m
      v = M.lookup 3 m
      v = M.lookup 4 m
      v = M.lookup 5 m
      v = M.lookup 6 m
      v = M.lookup 0 m
      v = M.lookup 8 m
      v = M.lookup 9 m
  m

export
keysMap : Nat -> List Nat
keysMap n = do
  let m = M.fromList $ map (\x => (x,plus x 1)) [0..n]
  M.keys m

export
valuesMap : Nat -> List Nat
valuesMap n = do
  let m = M.fromList $ map (\x => (x,plus x 1)) [0..n]
  M.values m
