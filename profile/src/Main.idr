module Main

import Data.Linear.Ref1
import Data.Linear.Token
import Data.List
import Data.Map as M
import Data.RRBVector as V
import Data.RRBVector.Internal
import Data.RRBVector1.Internal
import Data.SortedMap as SM
import Data.Set as S
import Data.Seq.Unsized as SU
import Data.SortedSet as SS
import Profile

%hide Data.Fin.fromInteger
%hide Profile.Types.fromInteger
%hide Profile.Types.Scalar.fromInteger
%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.(<|)
%hide Prelude.(|>)

createList : Nat -> List (Nat,Nat)
createList n = map (\x => (x,plus x 1)) [0..n]

createMap : Nat -> Map Nat Nat
createMap n = M.fromList $ map (\x => (x,plus x 1)) [0..n]

createRRBVector : (xs : List Nat) -> RRBVector (length xs) Nat
createRRBVector xs = V.fromList xs

createSeqUnsized : Nat -> Seq Nat
createSeqUnsized n = SU.fromList [0..n]

createSortedMap : Nat -> SortedMap Nat Nat
createSortedMap n = SM.fromList $ map (\x => (x,plus x 1)) [0..n]

createSet : Nat -> Set Nat
createSet n = S.fromList [0..n]

createSortedSet : Nat -> SortedSet Nat
createSortedSet n = SS.fromList [0..n]

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

keysMap : Nat -> List Nat
keysMap n = do
  let m = M.fromList $ map (\x => (x,plus x 1)) [0..n]
  M.keys m

keysSortedMap : Nat -> List Nat
keysSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
  SM.keys m

valuesMap : Nat -> List Nat
valuesMap n = do
  let m = M.fromList $ map (\x => (x,plus x 1)) [0..n]
  M.values m

valuesSortedMap : Nat -> List Nat
valuesSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
  SM.values m

unionSet : Nat -> Set Nat
unionSet n = do
  let s  = S.fromList [0..n]
      s' = S.fromList [(n `div` 2)..n]
  union s s'

unionSortedSet : Nat -> SortedSet Nat
unionSortedSet n = do
  let s  = SS.fromList [0..n]
      s' = SS.fromList [(n `div` 2)..n]
  union s s'

differenceSet : Nat -> Set Nat
differenceSet n = do
  let s  = S.fromList [0..n]
      s' = S.fromList [(n `div` 2)..n]
  difference s s'

differenceSortedSet : Nat -> SortedSet Nat
differenceSortedSet n = do
  let s  = SS.fromList [0..n]
      s' = SS.fromList [(n `div` 2)..n]
  difference s s'

intersectionSet : Nat -> Set Nat
intersectionSet n = do
  let s  = S.fromList [0..n]
      s' = S.fromList [(n `div` 2)..n]
  intersection s s'

intersectionSortedSet : Nat -> SortedSet Nat
intersectionSortedSet n = do
  let s  = SS.fromList [0..n]
      s' = SS.fromList [(n `div` 2)..n]
  intersection s s'

consRRBVector : (n : Nat) -> (n' ** RRBVector n' Nat)
consRRBVector n = do
  let v          = V.fromList [0..n]
      (_ ** v)   = 10 <| v
      (_ ** v)   = 11 <| v
      (_ ** v)   = 12 <| v
      (_ ** v)   = 13 <| v
      (_ ** v)   = 14 <| v
      (_ ** v)   = 15 <| v
      (_ ** v)   = 16 <| v
      (_ ** v)   = 17 <| v
      (_ ** v)   = 18 <| v
      (n' ** v') = 19 <| v
  (n' ** v')

consSeqUnsized : Nat -> Seq Nat
consSeqUnsized n = do
  let s = SU.fromList [0..n]
  let s = cons 10 s
  let s = cons 11 s
  let s = cons 12 s
  let s = cons 13 s
  let s = cons 14 s
  let s = cons 15 s
  let s = cons 16 s
  let s = cons 17 s
  let s = cons 18 s
  cons 19 s

snocRRBVector : (n : Nat) -> (n' ** RRBVector n' Nat)
snocRRBVector n = do
  let v          = V.fromList [0..n]
      (_ ** v)   = v |> 10
      (_ ** v)   = v |> 11
      (_ ** v)   = v |> 12
      (_ ** v)   = v |> 13
      (_ ** v)   = v |> 14
      (_ ** v)   = v |> 15
      (_ ** v)   = v |> 16
      (_ ** v)   = v |> 17
      (_ ** v)   = v |> 18
      (n' ** v') = v |> 19
  (n' ** v')

snocSeqUnsized : Nat -> Seq Nat
snocSeqUnsized n = do
  let s = SU.fromList [0..n]
  let s = snoc s 10
  let s = snoc s 11
  let s = snoc s 12
  let s = snoc s 13
  let s = snoc s 14
  let s = snoc s 15
  let s = snoc s 16
  let s = snoc s 17
  let s = snoc s 18
  snoc s 19

appendRRBVector : (n : Nat) -> (n' ** RRBVector n' Nat)
appendRRBVector n = do
  let v          = V.fromList [0..n]
      (n' ** v') = v >< v
  (n' ** v')

appendSeqUnsized : Nat -> Seq Nat
appendSeqUnsized n = do
  let s = SU.fromList [0..n]
  s ++ s

indexRRBVector : Nat -> Maybe ()
indexRRBVector n = do
  let v = V.fromList [0..n]
  for_ (Prelude.id v) $ \v' =>
    V.lookup v' v

indexSeqUnsized : Nat -> Maybe ()
indexSeqUnsized n = do
  let s = SU.fromList [0..n]
  for_ (Prelude.id s) $ \s' =>
    SU.index s' s

mapRRBVector : (n : Nat) -> RRBVector (length [0..n]) Nat
mapRRBVector n = do
  let v = V.fromList [0..n]
  map (\x => plus x 1) v

mapSeqUnsized : Nat -> Seq Nat
mapSeqUnsized n = do
  let s = SU.fromList [0..n]
  map (\x => plus x 1) s

replicateRRBVector : (n : Nat) -> RRBVector n Nat
replicateRRBVector n = do
  V.replicate n 0

replicateSeqUnsized : Nat -> Seq Nat
replicateSeqUnsized n = do
  SU.replicate n 0

splitAtRRBVector : (n : Nat) -> (RRBVector (length [0..n]) Nat, RRBVector (length [0..n]) Nat)
splitAtRRBVector n = do
  let v = V.fromList [0..n]
  V.splitAt (n `div` 2) v

splitAtSeqUnsized : Nat -> (Seq Nat, Seq Nat)
splitAtSeqUnsized n = do
  let s = SU.fromList [0..n]
  SU.splitAt (n `div` 2) s

reverseRRBVector : (n : Nat) -> (n ** RRBVector n Nat)
reverseRRBVector n = do
  let v = V.fromList [0..n]
  V.reverse v

reverseSeqUnsized : Nat -> Seq Nat
reverseSeqUnsized n = do
  let s = SU.fromList [0..n]
  SU.reverse s

partial
bench : Benchmark Void
bench = Group "containers"
  [ Group "List"
     [ Single "1"       (basic createList 0)
     , Single "100"     (basic createList 99)
     , Single "1000"    (basic createList 999)
     ]
  , Group "fromListMap"
      [ Single "1"       (basic createMap 0)
      , Single "100"     (basic createMap 99)
      , Single "1000"    (basic createMap 999)
      ]
  , Group "fromListSortedMap"
      [ Single "1"      (basic createSortedMap 0)
      , Single "100"    (basic createSortedMap 99)
      , Single "1000"   (basic createSortedMap 999)
      ]
  , Group "fromListSet"
      [ Single "1"       (basic createSet 0)
      , Single "100"     (basic createSet 99)
      , Single "1000"    (basic createSet 999)
      ]
  , Group "fromListSortedSet"
      [ Single "1"      (basic createSortedSet 0)
      , Single "100"    (basic createSortedSet 99)
      , Single "1000"   (basic createSortedSet 999)
      ]
  , Group "insertMap"
      [ Single "10"      (basic insertMap 0)
      ]
  , Group "insertSortedMap"
      [ Single "10"      (basic insertSortedMap 0)
      ]
  , Group "insertSet"
      [ Single "10"      (basic insertSet 0)
      ]
  , Group "insertSortedSet"
      [ Single "10"      (basic insertSortedSet 0)
      ]
  , Group "deleteMap"
      [ Single "10"      (basic deleteMap 9)
      ]
  , Group "deleteSortedMap"
      [ Single "10"      (basic deleteSortedMap 9)
      ]
  , Group "deleteSet"
      [ Single "10"      (basic deleteSet 9)
      ]
  , Group "deleteSortedSet"
      [ Single "10"      (basic deleteSortedSet 9)
      ]
  , Group "updateMap"
      [ Single "10"      (basic updateMap 9)
      ]
  , Group "updateSortedMap"
      [ Single "10"      (basic updateSortedMap 9)
      ]
  , Group "lookupMap"
      [ Single "10"      (basic lookupMap 9)
      ]
  , Group "lookupSortedMap"
      [ Single "10"      (basic lookupSortedMap 9)
      ]
  , Group "memberSet"
      [ Single "10"      (basic memberSet 9)
      ]
  , Group "containsSortedSet"
      [ Single "10"      (basic containsSortedSet 9)
      ]
  , Group "keysMap"
      [ Single "1000000" (basic keysMap 999999)
      ]
  , Group "keysSortedMap"
      [ Single "1000000" (basic keysSortedMap 999999)
      ]
  , Group "valuesMap"
      [ Single "1000000" (basic valuesMap 999999)
      ]
  , Group "valuesSortedMap"
      [ Single "1000000" (basic valuesSortedMap 999999)
      ]
  , Group "unionSet"
      [ Single "1000000" (basic unionSet 999999)
      ]
  , Group "unionSortedSet"
      [ Single "1000000" (basic unionSortedSet 999999)
      ]
  , Group "differenceSet"
      [ Single "1000" (basic differenceSet 999)
      ]
  , Group "differenceSortedSet"
      [ Single "1000" (basic differenceSortedSet 999)
      ]
  , Group "intersectionSet"
      [ Single "1000" (basic intersectionSet 999)
      ]
  , Group "intersectionSortedSet"
      [ Single "1000" (basic intersectionSortedSet 999)
      ]
  , Group "fromListRRBVector"
      [ Single "1"      (basic createRRBVector [0..0])
      , Single "100"    (basic createRRBVector [0..99])
      , Single "1000"   (basic createRRBVector [0..999])
      ]
  , Group "fromListSeqUnsized"
      [ Single "1"      (basic createSeqUnsized 0)
      , Single "100"    (basic createSeqUnsized 99)
      , Single "1000"   (basic createSeqUnsized 999)
      ]
  , Group "consRRBVector"
      [ Single "10"      (basic consRRBVector 9)
      ]
  , Group "consSeqUnsized"
      [ Single "10"      (basic consSeqUnsized 9)
      ]
  , Group "snocRRBVector"
      [ Single "10"      (basic snocRRBVector 9)
      ]
  , Group "snocSeqUnsized"
      [ Single "10"      (basic snocSeqUnsized 9)
      ]
  , Group "appendRRBVector"
      [ Single "10"      (basic appendRRBVector 9)
      ]
  , Group "appendSeqUnsized"
      [ Single "10"      (basic appendSeqUnsized 9)
      ]
  , Group "indexRRBVector"
      [ Single "1"      (basic indexRRBVector 0)
      , Single "100"    (basic indexRRBVector 99)
      , Single "1000"   (basic indexRRBVector 999)
      , Single "10000"  (basic indexRRBVector 9999)
      ]
  , Group "indexSeqUnsized"
      [ Single "1"      (basic indexSeqUnsized 0)
      , Single "100"    (basic indexSeqUnsized 99)
      , Single "1000"   (basic indexSeqUnsized 999)
      , Single "10000"  (basic indexSeqUnsized 9999)
      ]
--  , Group "mapRRBVector"
--      [ Single "1"       (basic mapRRBVector 0)
--      , Single "100"     (basic mapRRBVector 99)
--      , Single "1000"    (basic mapRRBVector 999)
--      , Single "10000"   (basic mapRRBVector 9999)
--      ]
  , Group "mapSeqUnsized"
      [ Single "1"       (basic mapSeqUnsized 0)
      , Single "100"     (basic mapSeqUnsized 99)
      , Single "1000"    (basic mapSeqUnsized 999)
      , Single "10000"   (basic mapSeqUnsized 9999)
      ]
--  , Group "replicateRRBVector"
--      [ Single "1"       (basic replicateRRBVector 0)
--      , Single "100"     (basic replicateRRBVector 99)
--      , Single "1000"    (basic replicateRRBVector 999)
--      , Single "10000"   (basic replicateRRBVector 9999)
--      ]
  , Group "replicateSeqUnsized"
      [ Single "1"       (basic replicateSeqUnsized 0)
      , Single "100"     (basic replicateSeqUnsized 99)
      , Single "1000"    (basic replicateSeqUnsized 999)
      , Single "10000"   (basic replicateSeqUnsized 9999)
      ]
  , Group "reverseRRBVector"
      [ Single "1"       (basic reverseRRBVector 0)
      , Single "100"     (basic reverseRRBVector 99)
      , Single "1000"    (basic reverseRRBVector 999)
      , Single "10000"   (basic reverseRRBVector 9999)
      ]
  , Group "reverseSeqUnsized"
      [ Single "1"       (basic reverseSeqUnsized 0)
      , Single "100"     (basic reverseSeqUnsized 99)
      , Single "1000"    (basic reverseSeqUnsized 999)
      , Single "10000"   (basic reverseSeqUnsized 9999)
      ]
--  , Group "splitAtRRBVector"
--      [ Single "1"       (basic splitAtRRBVector 0)
--      , Single "100"     (basic splitAtRRBVector 99)
--      , Single "1000"    (basic splitAtRRBVector 999)
--      , Single "10000"   (basic splitAtRRBVector 9999)
--      ]
  , Group "splitAtSeqUnsized"
      [ Single "1"       (basic splitAtSeqUnsized 0)
      , Single "100"     (basic splitAtSeqUnsized 99)
      , Single "1000"    (basic splitAtSeqUnsized 999)
      , Single "10000"   (basic splitAtSeqUnsized 9999)
      ]
  ]


partial
main : IO ()
main = runDefault (const True) Details show bench
