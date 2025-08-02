module Main

import Data.Linear.Ref1
import Data.Linear.Token
import Data.List
import Data.Map as M
import Data.RRBVector.Sized as VS
import Data.RRBVector.Unsized as VU
import Data.RRBVector.Sized.Internal
import Data.RRBVector.Unsized.Internal
import Data.RRBVector1.Internal
import Data.SortedMap as SM
import Data.Set as S
import Data.Seq.Sized as SS
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

createRRBVectorSized : (xs : List Nat) -> RRBVector (length xs) Nat
createRRBVectorSized xs = VS.fromList xs

createRRBVectorUnsized : Nat -> RRBVector Nat
createRRBVectorUnsized n = VU.fromList [0..n]

createSeqSized : (xs : List Nat) -> Seq (length xs) Nat
createSeqSized xs = SS.fromList xs

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

consRRBVectorSized : (n : Nat) -> (n' ** RRBVector n' Nat)
consRRBVectorSized n = do
  let v          = VS.fromList [0..n]
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

consRRBVectorUnsized : Nat -> RRBVector Nat
consRRBVectorUnsized n = do
  let v = VU.fromList [0..n]
      v = 10 <| v
      v = 11 <| v
      v = 12 <| v
      v = 13 <| v
      v = 14 <| v
      v = 15 <| v
      v = 16 <| v
      v = 17 <| v
      v = 18 <| v
  19 <| v

consSeqSized : (xs : List Nat) -> Seq (S (S (S (S (S (S (S (S (S (S (length xs))))))))))) Nat
consSeqSized xs = do
  let s = SS.fromList xs
      s = cons 10 s
      s = cons 11 s
      s = cons 12 s
      s = cons 13 s
      s = cons 14 s
      s = cons 15 s
      s = cons 16 s
      s = cons 17 s
      s = cons 18 s
  cons 19 s

consSeqUnsized : Nat -> Seq Nat
consSeqUnsized n = do
  let s = SU.fromList [0..n]
      s = cons 10 s
      s = cons 11 s
      s = cons 12 s
      s = cons 13 s
      s = cons 14 s
      s = cons 15 s
      s = cons 16 s
      s = cons 17 s
      s = cons 18 s
  cons 19 s

snocRRBVectorSized : (n : Nat) -> (n' ** RRBVector n' Nat)
snocRRBVectorSized n = do
  let v          = VS.fromList [0..n]
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

snocRRBVectorUnsized : Nat -> RRBVector Nat
snocRRBVectorUnsized n = do
  let v = VU.fromList [0..n]
      v = v |> 10
      v = v |> 11
      v = v |> 12
      v = v |> 13
      v = v |> 14
      v = v |> 15
      v = v |> 16
      v = v |> 17
      v = v |> 18
  v |> 19

snocSeqSized : (n : Nat) -> Seq (S (S (S (S (S (S (S (S (S (S (length [0..n]))))))))))) Nat
snocSeqSized n = do
  let s = SS.fromList [0..n]
      s = snoc s 10
      s = snoc s 11
      s = snoc s 12
      s = snoc s 13
      s = snoc s 14
      s = snoc s 15
      s = snoc s 16
      s = snoc s 17
      s = snoc s 18
  snoc s 19

snocSeqUnsized : Nat -> Seq Nat
snocSeqUnsized n = do
  let s = SU.fromList [0..n]
      s = snoc s 10
      s = snoc s 11
      s = snoc s 12
      s = snoc s 13
      s = snoc s 14
      s = snoc s 15
      s = snoc s 16
      s = snoc s 17
      s = snoc s 18
  snoc s 19

appendRRBVectorSized : (n : Nat) -> (n' ** RRBVector n' Nat)
appendRRBVectorSized n = do
  let v          = VS.fromList [0..n]
      (n' ** v') = v >< v
  (n' ** v')

appendRRBVectorUnsized : Nat -> RRBVector Nat
appendRRBVectorUnsized n = do
  let v = VU.fromList [0..n]
  v >< v

appendSeqSized : (xs : List Nat) -> Seq (length xs + length xs) Nat
appendSeqSized xs = do
  let s = SS.fromList xs
  s ++ s

appendSeqUnsized : Nat -> Seq Nat
appendSeqUnsized n = do
  let s = SU.fromList [0..n]
  s ++ s

indexRRBVectorSized : Nat -> Maybe ()
indexRRBVectorSized n = do
  let v = VS.fromList [0..n]
  for_ (Prelude.id v) $ \v' =>
    VS.lookup v' v

indexRRBVectorUnsized : Nat -> Maybe ()
indexRRBVectorUnsized n = do
  let v = VU.fromList [0..n]
  for_ (Prelude.id v) $ \v' =>
    VU.lookup v' v

indexSeqUnsized : Nat -> Maybe ()
indexSeqUnsized n = do
  let s = SU.fromList [0..n]
  for_ (Prelude.id s) $ \s' =>
    SU.index s' s

mapRRBVectorSized : (n : Nat) -> RRBVector (length [0..n]) Nat
mapRRBVectorSized n = do
  let v = VS.fromList [0..n]
  map (\x => plus x 1) v

mapRRBVectorUnsized : Nat -> RRBVector Nat
mapRRBVectorUnsized n = do
  let v = VU.fromList [0..n]
  map (\x => plus x 1) v

mapSeqSized : (xs : List Nat) -> Seq (length xs) Nat
mapSeqSized xs = do
  let v = SS.fromList xs
  map (\x => plus x 1) v

mapSeqUnsized : Nat -> Seq Nat
mapSeqUnsized n = do
  let s = SU.fromList [0..n]
  map (\x => plus x 1) s

replicateRRBVectorSized : (n : Nat) -> RRBVector n Nat
replicateRRBVectorSized n = do
  VS.replicate n 0

replicateRRBVectorUnsized : Nat -> RRBVector Nat
replicateRRBVectorUnsized n = do
  VU.replicate n 0

replicateSeqSized : (n : Nat) -> Seq n Nat
replicateSeqSized n = do
  SS.replicate n 0

replicateSeqUnsized : Nat -> Seq Nat
replicateSeqUnsized n = do
  SU.replicate n 0

splitAtRRBVectorSized : (n : Nat) -> ((n' ** RRBVector n' Nat), (n'' ** RRBVector n'' Nat))
splitAtRRBVectorSized n = do
  let v = VS.fromList [0..n]
  VS.splitAt (n `div` 2) v

splitAtRRBVectorUnsized : Nat -> (RRBVector Nat, RRBVector Nat)
splitAtRRBVectorUnsized n = do
  let v = VU.fromList [0..n]
  VU.splitAt (n `div` 2) v

splitAtSeqSized : (xs : List Nat) -> Seq (length xs) Nat
splitAtSeqSized xs = do
  let v         = SS.fromList xs
      (v', v'') = SS.splitAt Z v
  v''

splitAtSeqUnsized : Nat -> (Seq Nat, Seq Nat)
splitAtSeqUnsized n = do
  let s = SU.fromList [0..n]
  SU.splitAt (n `div` 2) s

reverseRRBVectorSized : (n : Nat) -> (n ** RRBVector n Nat)
reverseRRBVectorSized n = do
  let v = VS.fromList [0..n]
  VS.reverse v

reverseRRBVectorUnsized : Nat -> RRBVector Nat
reverseRRBVectorUnsized n = do
  let v = VU.fromList [0..n]
  VU.reverse v

reverseSeqSized : (xs : List Nat) -> Seq (length xs) Nat
reverseSeqSized xs = do
  let v = SS.fromList xs
  SS.reverse v

reverseSeqUnsized : Nat -> Seq Nat
reverseSeqUnsized n = do
  let v = SU.fromList [0..n]
  SU.reverse v

partial
bench : Benchmark Void
bench = Group "containers"
  [ Group "List"
     [ Single "1"    (basic createList 0)
     , Single "100"  (basic createList 99)
     , Single "1000" (basic createList 999)
     ]
  , Group "fromListMap"
      [ Single "1"    (basic createMap 0)
      , Single "100"  (basic createMap 99)
      , Single "1000" (basic createMap 999)
      ]
  , Group "fromListSortedMap"
      [ Single "1"    (basic createSortedMap 0)
      , Single "100"  (basic createSortedMap 99)
      , Single "1000" (basic createSortedMap 999)
      ]
  , Group "fromListSet"
      [ Single "1"    (basic createSet 0)
      , Single "100"  (basic createSet 99)
      , Single "1000" (basic createSet 999)
      ]
  , Group "fromListSortedSet"
      [ Single "1"    (basic createSortedSet 0)
      , Single "100"  (basic createSortedSet 99)
      , Single "1000" (basic createSortedSet 999)
      ]
  , Group "insertMap"
      [ Single "10" (basic insertMap 0)
      ]
  , Group "insertSortedMap"
      [ Single "10" (basic insertSortedMap 0)
      ]
  , Group "insertSet"
      [ Single "10" (basic insertSet 0)
      ]
  , Group "insertSortedSet"
      [ Single "10" (basic insertSortedSet 0)
      ]
  , Group "deleteMap"
      [ Single "10" (basic deleteMap 9)
      ]
  , Group "deleteSortedMap"
      [ Single "10" (basic deleteSortedMap 9)
      ]
  , Group "deleteSet"
      [ Single "10" (basic deleteSet 9)
      ]
  , Group "deleteSortedSet"
      [ Single "10" (basic deleteSortedSet 9)
      ]
  , Group "updateMap"
      [ Single "10" (basic updateMap 9)
      ]
  , Group "updateSortedMap"
      [ Single "10" (basic updateSortedMap 9)
      ]
  , Group "lookupMap"
      [ Single "10" (basic lookupMap 9)
      ]
  , Group "lookupSortedMap"
      [ Single "10" (basic lookupSortedMap 9)
      ]
  , Group "memberSet"
      [ Single "10" (basic memberSet 9)
      ]
  , Group "containsSortedSet"
      [ Single "10" (basic containsSortedSet 9)
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
  , Group "fromListRRBVectorUnsized"
      [ Single "1"    (basic createRRBVectorUnsized 0)
      , Single "100"  (basic createRRBVectorUnsized 99)
      , Single "1000" (basic createRRBVectorUnsized 999)
      ]
  , Group "fromListSeqUnsized"
      [ Single "1"    (basic createSeqUnsized 0)
      , Single "100"  (basic createSeqUnsized 99)
      , Single "1000" (basic createSeqUnsized 999)
      ]
  , Group "consRRBVectorSized"
      [ Single "10" (basic consRRBVectorSized 9)
      ]
  , Group "consRRBVectorUnsized"
      [ Single "10" (basic consRRBVectorUnsized 9)
      ]
  , Group "consSeqUnsized"
      [ Single "10" (basic consSeqUnsized 9)
      ]
  , Group "snocRRBVectorSized"
      [ Single "10" (basic snocRRBVectorSized 9)
      ]
  , Group "snocRRBVectorUnsized"
      [ Single "10" (basic snocRRBVectorUnsized 9)
      ]
  , Group "snocSeqUnsized"
      [ Single "10" (basic snocSeqUnsized 9)
      ]
  , Group "appendRRBVectorSized"
      [ Single "10" (basic appendRRBVectorSized 9)
      ]
  , Group "appendRRBVectorUnsized"
      [ Single "10" (basic appendRRBVectorUnsized 9)
      ]
  , Group "appendSeqUnsized"
      [ Single "10" (basic appendSeqUnsized 9)
      ]
  , Group "indexRRBVectorSized"
      [ Single "1"     (basic indexRRBVectorSized 0)
      , Single "100"   (basic indexRRBVectorSized 99)
      , Single "1000"  (basic indexRRBVectorSized 999)
      , Single "10000" (basic indexRRBVectorSized 9999)
      ]
  , Group "indexRRBVectorUnsized"
      [ Single "1"     (basic indexRRBVectorUnsized 0)
      , Single "100"   (basic indexRRBVectorUnsized 99)
      , Single "1000"  (basic indexRRBVectorUnsized 999)
      , Single "10000" (basic indexRRBVectorUnsized 9999)
      ]
  , Group "indexSeqUnsized"
      [ Single "1"     (basic indexSeqUnsized 0)
      , Single "100"   (basic indexSeqUnsized 99)
      , Single "1000"  (basic indexSeqUnsized 999)
      , Single "10000" (basic indexSeqUnsized 9999)
      ]
  , Group "mapRRBVectorUnsized"
      [ Single "1"     (basic mapRRBVectorUnsized 0)
      , Single "100"   (basic mapRRBVectorUnsized 99)
      , Single "1000"  (basic mapRRBVectorUnsized 999)
      , Single "10000" (basic mapRRBVectorUnsized 9999)
      ]
  , Group "mapSeqUnsized"
      [ Single "1"     (basic mapSeqUnsized 0)
      , Single "100"   (basic mapSeqUnsized 99)
      , Single "1000"  (basic mapSeqUnsized 999)
      , Single "10000" (basic mapSeqUnsized 9999)
      ]
  , Group "replicateRRBVectorUnsized"
      [ Single "1"     (basic replicateRRBVectorUnsized 0)
      , Single "100"   (basic replicateRRBVectorUnsized 99)
      , Single "1000"  (basic replicateRRBVectorUnsized 999)
      , Single "10000" (basic replicateRRBVectorUnsized 9999)
      ]
  , Group "replicateSeqUnsized"
      [ Single "1"     (basic replicateSeqUnsized 0)
      , Single "100"   (basic replicateSeqUnsized 99)
      , Single "1000"  (basic replicateSeqUnsized 999)
      , Single "10000" (basic replicateSeqUnsized 9999)
      ]
  , Group "reverseRRBVectorSized"
      [ Single "1"     (basic reverseRRBVectorSized 0)
      , Single "100"   (basic reverseRRBVectorSized 99)
      , Single "1000"  (basic reverseRRBVectorSized 999)
      , Single "10000" (basic reverseRRBVectorSized 9999)
      ]
  , Group "reverseRRBVectorUnsized"
      [ Single "1"     (basic reverseRRBVectorUnsized 0)
      , Single "100"   (basic reverseRRBVectorUnsized 99)
      , Single "1000"  (basic reverseRRBVectorUnsized 999)
      , Single "10000" (basic reverseRRBVectorUnsized 9999)
      ]
  , Group "reverseSeqUnsized"
      [ Single "1"     (basic reverseSeqUnsized 0)
      , Single "100"   (basic reverseSeqUnsized 99)
      , Single "1000"  (basic reverseSeqUnsized 999)
      , Single "10000" (basic reverseSeqUnsized 9999)
      ]
  , Group "splitAtRRBVectorUnsized"
      [ Single "1"     (basic splitAtRRBVectorUnsized 0)
      , Single "100"   (basic splitAtRRBVectorUnsized 99)
      , Single "1000"  (basic splitAtRRBVectorUnsized 999)
      , Single "10000" (basic splitAtRRBVectorUnsized 9999)
      ]
  , Group "splitAtSeqUnsized"
      [ Single "1"     (basic splitAtSeqUnsized 0)
      , Single "100"   (basic splitAtSeqUnsized 99)
      , Single "1000"  (basic splitAtSeqUnsized 999)
      , Single "10000" (basic splitAtSeqUnsized 9999)
      ]
  ]

partial
main : IO ()
main = runDefault (const True) Details show bench
