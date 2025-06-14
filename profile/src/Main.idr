module Main

import Data.Linear.Ref1
import Data.Linear.Token
import Data.List
import Data.Map as M
import Data.RRBVector as V
import Data.RRBVector1 as V1
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

createList : Nat -> List (Nat,Nat)
createList n = map (\x => (x,plus x 1)) [0..n]

createMap : Nat -> Map Nat Nat
createMap n = M.fromList $ map (\x => (x,plus x 1)) [0..n]

createRRBVector : Nat -> RRBVector Nat
createRRBVector n = V.fromList [0..n]

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
  let m = M.insert 0 2 m
  let m = M.insert 1 3 m
  let m = M.insert 2 4 m
  let m = M.insert 3 5 m
  let m = M.insert 4 6 m
  let m = M.insert 5 7 m
  let m = M.insert 6 8 m
  let m = M.insert 7 9 m
  let m = M.insert 8 10 m
  M.insert 9 11 m

insertSortedMap : Nat -> SortedMap Nat Nat
insertSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
  let m = SM.insert 0 2 m
  let m = SM.insert 1 3 m
  let m = SM.insert 2 4 m
  let m = SM.insert 3 5 m
  let m = SM.insert 4 6 m
  let m = SM.insert 5 7 m
  let m = SM.insert 6 8 m
  let m = SM.insert 7 9 m
  let m = SM.insert 8 10 m
  SM.insert 9 11 m

insertSet : Nat -> Set Nat
insertSet n = do
  let s = S.fromList [0..n]
  let s = S.insert 10 s
  let s = S.insert 11 s
  let s = S.insert 12 s
  let s = S.insert 13 s
  let s = S.insert 14 s
  let s = S.insert 15 s
  let s = S.insert 16 s
  let s = S.insert 17 s
  let s = S.insert 18 s
  S.insert 19 s

insertSortedSet : Nat -> SortedSet Nat
insertSortedSet n = do
  let s = SS.fromList [0..n]
  let s = SS.insert 10 s
  let s = SS.insert 11 s
  let s = SS.insert 12 s
  let s = SS.insert 13 s
  let s = SS.insert 14 s
  let s = SS.insert 15 s
  let s = SS.insert 16 s
  let s = SS.insert 17 s
  let s = SS.insert 18 s
  SS.insert 19 s

deleteMap : Nat -> Map Nat Nat
deleteMap n = do
  let m = M.fromList $ map (\x => (x,plus x 1)) [0..n]
  let m = M.delete 9 m
  let m = M.delete 8 m
  let m = M.delete 7 m
  let m = M.delete 6 m
  let m = M.delete 5 m
  let m = M.delete 4 m
  let m = M.delete 3 m
  let m = M.delete 2 m
  let m = M.delete 1 m
  M.delete 0 m

deleteSortedMap : Nat -> SortedMap Nat Nat
deleteSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
  let m = SM.delete 9 m
  let m = SM.delete 8 m
  let m = SM.delete 7 m
  let m = SM.delete 6 m
  let m = SM.delete 5 m
  let m = SM.delete 4 m
  let m = SM.delete 3 m
  let m = SM.delete 2 m
  let m = SM.delete 1 m
  SM.delete 0 m


deleteSet : Nat -> Set Nat
deleteSet n = do
  let m = S.fromList [0..n]
  let m = S.delete 9 m
  let m = S.delete 8 m
  let m = S.delete 7 m
  let m = S.delete 6 m
  let m = S.delete 5 m
  let m = S.delete 4 m
  let m = S.delete 3 m
  let m = S.delete 2 m
  let m = S.delete 1 m
  S.delete 0 m

deleteSortedSet : Nat -> SortedSet Nat
deleteSortedSet n = do
  let m = SS.fromList [0..n]
  let m = SS.delete 9 m
  let m = SS.delete 8 m
  let m = SS.delete 7 m
  let m = SS.delete 6 m
  let m = SS.delete 5 m
  let m = SS.delete 4 m
  let m = SS.delete 3 m
  let m = SS.delete 2 m
  let m = SS.delete 1 m
  SS.delete 0 m

updateMap : Nat -> Map Nat Nat
updateMap n = do
  let m = M.fromList $ map (\x => (x,plus x 1)) [0..n]
  let m = M.update f 0 m
  let m = M.update f 1 m
  let m = M.update f 2 m
  let m = M.update f 3 m
  let m = M.update f 4 m
  let m = M.update f 5 m
  let m = M.update f 6 m
  let m = M.update f 7 m
  let m = M.update f 8 m
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
  let m = SM.update f 0 m
  let m = SM.update f 1 m
  let m = SM.update f 2 m
  let m = SM.update f 3 m
  let m = SM.update f 4 m
  let m = SM.update f 5 m
  let m = SM.update f 6 m
  let m = SM.update f 7 m
  let m = SM.update f 8 m
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
  let v = M.lookup 0 m
  let v = M.lookup 1 m
  let v = M.lookup 2 m
  let v = M.lookup 3 m
  let v = M.lookup 4 m
  let v = M.lookup 5 m
  let v = M.lookup 6 m
  let v = M.lookup 0 m
  let v = M.lookup 8 m
  let v = M.lookup 9 m
  m

lookupSortedMap : Nat -> SortedMap Nat Nat
lookupSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
  let v = SM.lookup 0 m
  let v = SM.lookup 1 m
  let v = SM.lookup 2 m
  let v = SM.lookup 3 m
  let v = SM.lookup 4 m
  let v = SM.lookup 5 m
  let v = SM.lookup 6 m
  let v = SM.lookup 0 m
  let v = SM.lookup 8 m
  let v = SM.lookup 9 m
  m

memberSet : Nat -> Set Nat
memberSet n = do
  let s = S.fromList [0..n]
  let v = S.member 0 s
  let v = S.member 1 s
  let v = S.member 2 s
  let v = S.member 3 s
  let v = S.member 4 s
  let v = S.member 5 s
  let v = S.member 6 s
  let v = S.member 0 s
  let v = S.member 8 s
  let v = S.member 9 s
  s

containsSortedSet : Nat -> SortedSet Nat
containsSortedSet n = do
  let s = SS.fromList [0..n]
  let v = SS.contains 0 s
  let v = SS.contains 1 s
  let v = SS.contains 2 s
  let v = SS.contains 3 s
  let v = SS.contains 4 s
  let v = SS.contains 5 s
  let v = SS.contains 6 s
  let v = SS.contains 0 s
  let v = SS.contains 8 s
  let v = SS.contains 9 s
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
  let s' = S.fromList [(n `div` 2)..n]
  union s s'

unionSortedSet : Nat -> SortedSet Nat
unionSortedSet n = do
  let s  = SS.fromList [0..n]
  let s' = SS.fromList [(n `div` 2)..n]
  union s s'

differenceSet : Nat -> Set Nat
differenceSet n = do
  let s  = S.fromList [0..n]
  let s' = S.fromList [(n `div` 2)..n]
  difference s s'

differenceSortedSet : Nat -> SortedSet Nat
differenceSortedSet n = do
  let s  = SS.fromList [0..n]
  let s' = SS.fromList [(n `div` 2)..n]
  difference s s'

intersectionSet : Nat -> Set Nat
intersectionSet n = do
  let s  = S.fromList [0..n]
  let s' = S.fromList [(n `div` 2)..n]
  intersection s s'

intersectionSortedSet : Nat -> SortedSet Nat
intersectionSortedSet n = do
  let s  = SS.fromList [0..n]
  let s' = SS.fromList [(n `div` 2)..n]
  intersection s s'

consRRBVector : Nat -> RRBVector Nat
consRRBVector n = do
  let v = V.fromList [0..n]
  let v = 10 <| v
  let v = 11 <| v
  let v = 12 <| v
  let v = 13 <| v
  let v = 14 <| v
  let v = 15 <| v
  let v = 16 <| v
  let v = 17 <| v
  let v = 18 <| v
  19 <| v

consRRBVector1 : Nat -> F1 s (RRBVector1 s Nat)
consRRBVector1 n t =
  let v # t := V1.fromList [0..n] t
      v # t := (V1.(<|) 10 v) t
      v # t := (V1.(<|) 11 v) t
      v # t := (V1.(<|) 12 v) t
      v # t := (V1.(<|) 13 v) t
      v # t := (V1.(<|) 14 v) t
      v # t := (V1.(<|) 15 v) t
      v # t := (V1.(<|) 16 v) t
      v # t := (V1.(<|) 17 v) t
      v # t := (V1.(<|) 18 v) t
      v # t := (V1.(<|) 19 v) t
    in v # t

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

snocRRBVector : Nat -> RRBVector Nat
snocRRBVector n = do
  let v = V.fromList [0..n]
  let v = v |> 10
  let v = v |> 11
  let v = v |> 12
  let v = v |> 13
  let v = v |> 14
  let v = v |> 15
  let v = v |> 16
  let v = v |> 17
  let v = v |> 18
  v |> 19

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

partial
appendRRBVector : Nat -> RRBVector Nat
appendRRBVector n = do
  let v = V.fromList [0..n]
  v >< v

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

mapRRBVector : Nat -> RRBVector Nat
mapRRBVector n = do
  let v = V.fromList [0..n]
  map (\x => plus x 1) v

mapSeqUnsized : Nat -> Seq Nat
mapSeqUnsized n = do
  let s = SU.fromList [0..n]
  map (\x => plus x 1) s

replicateRRBVector : Nat -> RRBVector Nat
replicateRRBVector n = do
  V.replicate n 0

replicateSeqUnsized : Nat -> Seq Nat
replicateSeqUnsized n = do
  SU.replicate n 0

splitAtRRBVector : Nat -> (RRBVector Nat, RRBVector Nat)
splitAtRRBVector n = do
  let v = V.fromList [0..n]
  V.splitAt (n `div` 2) v

splitAtSeqUnsized : Nat -> (Seq Nat, Seq Nat)
splitAtSeqUnsized n = do
  let s = SU.fromList [0..n]
  SU.splitAt (n `div` 2) s

reverseRRBVector : Nat -> RRBVector Nat
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
      [ Single "1"      (basic createRRBVector 0)
      , Single "100"    (basic createRRBVector 99)
      , Single "1000"   (basic createRRBVector 999)
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
  , Group "mapRRBVector"
      [ Single "1"       (basic mapRRBVector 0)
      , Single "100"     (basic mapRRBVector 99)
      , Single "1000"    (basic mapRRBVector 999)
      , Single "10000"   (basic mapRRBVector 9999)
      ]
  , Group "mapSeqUnsized"
      [ Single "1"       (basic mapSeqUnsized 0)
      , Single "100"     (basic mapSeqUnsized 99)
      , Single "1000"    (basic mapSeqUnsized 999)
      , Single "10000"   (basic mapSeqUnsized 9999)
      ]
  , Group "replicateRRBVector"
      [ Single "1"       (basic replicateRRBVector 0)
      , Single "100"     (basic replicateRRBVector 99)
      , Single "1000"    (basic replicateRRBVector 999)
      , Single "10000"   (basic replicateRRBVector 9999)
      ]
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
  , Group "splitAtRRBVector"
      [ Single "1"       (basic splitAtRRBVector 0)
      , Single "100"     (basic splitAtRRBVector 99)
      , Single "1000"    (basic splitAtRRBVector 999)
      , Single "10000"   (basic splitAtRRBVector 9999)
      ]
  , Group "splitAtSeqUnsized"
      [ Single "1"       (basic splitAtSeqUnsized 0)
      , Single "100"     (basic splitAtSeqUnsized 99)
      , Single "1000"    (basic splitAtSeqUnsized 999)
      , Single "10000"   (basic splitAtSeqUnsized 9999)
      ]
  ]

covering
main' : IO ()
main' = do
  let v = V.fromList [0..9]
      v = V.(<|) 10 v
      v = V.(<|) 11 v
      v = V.(<|) 12 v
      v = V.(<|) 13 v
      v = V.(<|) 14 v
      v = V.(<|) 15 v
      v = V.(<|) 16 v
      v = V.(<|) 17 v
      v = V.(<|) 18 v 
      v = V.(<|) 19 v
      v = V.(<|) 20 v
      v = V.(<|) 21 v
      v = V.(<|) 22 v
      v = V.(<|) 23 v
      v = V.(<|) 24 v
      v = V.(<|) 25 v
      v = V.(<|) 26 v
      v = V.(<|) 27 v
      v = V.(<|) 28 v
      v = V.(<|) 29 v
      v = V.(<|) 30 v
      v = V.(<|) 31 v
      v = V.(|>) v 10
      v = V.(|>) v 11
      v = V.(|>) v 12
      v = V.(|>) v 13
      v = V.(|>) v 14
      v = V.(|>) v 15
      v = V.(|>) v 16
      v = V.(|>) v 17
      v = V.(|>) v 18
      v = V.(|>) v 19
      v = V.(|>) v 20
      v = V.(|>) v 21
      v = V.(|>) v 22
      v = V.(|>) v 23
      v = V.(|>) v 24
      v = V.(|>) v 25
      v = V.(|>) v 26
      v = V.(|>) v 26
      v = V.(|>) v 27
      v = V.(|>) v 28
      v = V.(|>) v 29
      v = V.(|>) v 30
      v = V.(|>) v 31
      v = V.(><) v v
--  pure ()
      v = V.toList v
  putStrLn $ show v

covering
main1 : F1' World
main1 t =
  let v # t := V1.fromList [0..9] t
      v # t := (V1.(<|) 10 v) t
      v # t := (V1.(<|) 11 v) t
      v # t := (V1.(|>) v 10) t
      v # t := (V1.(|>) v 11) t
      v # t := (V1.(<|) 12 v) t
      v # t := (V1.(|>) v 12) t
      v # t := (V1.(<|) 13 v) t
      v # t := (V1.(<|) 14 v) t
      v # t := (V1.(|>) v 13) t
      v # t := (V1.(|>) v 14) t
      v # t := (V1.(><) v v) t
      {-
      v # t := (V1.(<|) 12 v) t
      v # t := (V1.(<|) 13 v) t
      v # t := (V1.(<|) 14 v) t
      v # t := (V1.(<|) 15 v) t
      v # t := (V1.(<|) 16 v) t
      v # t := (V1.(<|) 17 v) t
      v # t := (V1.(<|) 18 v) t
      v # t := (V1.(<|) 19 v) t
      v # t := (V1.(<|) 20 v) t
      v # t := (V1.(<|) 21 v) t
      v # t := (V1.(<|) 22 v) t
      v # t := (V1.(<|) 23 v) t
      v # t := (V1.(<|) 24 v) t
      v # t := (V1.(<|) 25 v) t
      v # t := (V1.(<|) 26 v) t
      v # t := (V1.(<|) 27 v) t
      v # t := (V1.(<|) 28 v) t
      v # t := (V1.(<|) 29 v) t
      v # t := (V1.(<|) 30 v) t
      v # t := (V1.(<|) 31 v) t
      v # t := (V1.(<|) 32 v) t
      v # t := (V1.(<|) 33 v) t
      v # t := (V1.(<|) 34 v) t
      v # t := (V1.(<|) 35 v) t
      v # t := (V1.(<|) 36 v) t
      v # t := (V1.(|>) v 11) t
      v # t := (V1.(|>) v 11) t
      v # t := (V1.(|>) v 12) t
      v # t := (V1.(|>) v 13) t
      v # t := (V1.(|>) v 14) t
      v # t := (V1.(|>) v 15) t
      v # t := (V1.(|>) v 16) t
      v # t := (V1.(|>) v 17) t
      v # t := (V1.(|>) v 18) t
      v # t := (V1.(|>) v 19) t
      v # t := (V1.(|>) v 20) t
      v # t := (V1.(|>) v 21) t
      v # t := (V1.(|>) v 22) t
      v # t := (V1.(|>) v 23) t
      v # t := (V1.(|>) v 24) t
      v # t := (V1.(|>) v 25) t
      v # t := (V1.(|>) v 26) t
      v # t := (V1.(|>) v 27) t
      v # t := (V1.(|>) v 28) t
      v # t := (V1.(|>) v 29) t
      v # t := (V1.(|>) v 30) t
      v # t := (V1.(|>) v 31) t
      v # t := (V1.(|>) v 32) t
      v # t := (V1.(|>) v 33) t
      v # t := (V1.(|>) v 34) t
      v # t := (V1.(|>) v 35) t
      v # t := (V1.(|>) v 36) t
      v # t := (V1.(<|) 37 v) t
      v # t := (V1.(<|) 38 v) t
      v # t := (V1.(<|) 39 v) t
      v # t := (V1.(<|) 40 v) t
      v # t := (V1.(<|) 41 v) t
      v # t := (V1.(|>) v 37) t
      v # t := (V1.(|>) v 38) t
      v # t := (V1.(|>) v 39) t
      v # t := (V1.(|>) v 40) t
      v # t := (V1.(|>) v 41) t
      v # t := (V1.(<|) 1000 v) t
      v # t := (V1.(|>) v 1000) t
      v # t := (V1.(|>) v 10000) t
--      v # t := V1.take 2 v t
--      v # t := V1.drop 2 v t
--      (v'', v''') # t := V1.splitAt 3 v' t
      v # t := (V1.(><) v v) t
--      v # t := V1.insertAt 1 1000 v t
--      v # t := V1.deleteAt 0 v t
      -}
      v'''' # t := V1.toList v t
    in ioToF1 (putStrLn $ show v'''') t

partial
main : IO ()
main = runIO main1 --main' --runIO main1 

--runDefault (const True) Details show bench
