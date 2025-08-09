module Main

import List
import Map
import RRBVector.Sized
import RRBVector.Unsized
import RRBVector1.Sized
import RRBVector1.Unsized
import Seq.Sized
import Seq.Unsized
import Set
import SortedMap
import SortedSet

import Data.Map
import Data.RRBVector.Sized
import Data.RRBVector.Unsized
import Data.Seq.Unsized
import Data.Set
import Data.SortedMap
import Data.SortedSet
import Profile

bench : Benchmark Void
bench =
  Group "Containers"
    [ Group "Sequences"
        [ Group "List"
            [ Single "1"    (basic createList 0)
            , Single "100"  (basic createList 99)
            , Single "1000" (basic createList 999)
            ]
        , Group "fromListRRBVectorUnsized"
            [ Single "1"    (basic createRRBVectorUnsized 0)
            , Single "100"  (basic createRRBVectorUnsized 99)
            , Single "1000" (basic createRRBVectorUnsized 999)
            ]
        , Group "fromListRRBVector1Sized"
            [ Single "1"    (basic createRRBVector1Sized 0)
            , Single "100"  (basic createRRBVector1Sized 100)
            , Single "1000" (basic createRRBVector1Sized 1000)
            ]
        , Group "fromListRRBVector1Unsized"
            [ Single "1"    (basic createRRBVector1Unsized 0)
            , Single "100"  (basic createRRBVector1Unsized 100)
            , Single "1000" (basic createRRBVector1Unsized 1000)
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
        , Group "consRRBVector1Sized"
            [ Single "10" (basic consRRBVector1Sized 9)
            ]
        , Group "consRRBVector1Unsized"
            [ Single "10" (basic consRRBVector1Unsized 9)
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
        , Group "snocRRBVector1Sized"
            [ Single "10" (basic snocRRBVector1Sized 9)
            ]
        , Group "snocRRBVector1Unsized"
            [ Single "10" (basic snocRRBVector1Unsized 9)
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
        , Group "appendRRBVector1Sized"
            [ Single "10" (basic appendRRBVector1Sized 9)
            ]
        , Group "appendRRBVector1Unsized"
            [ Single "10" (basic appendRRBVector1Unsized 9)
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
        , Group "mapRRBVector1Sized"
            [ Single "1"     (basic mapRRBVector1Sized 0)
            , Single "100"   (basic mapRRBVector1Sized 99)
            , Single "1000"  (basic mapRRBVector1Sized 999)
            , Single "10000" (basic mapRRBVector1Sized 9999)
            ]
        , Group "mapRRBVector1Sized"
            [ Single "1"     (basic mapRRBVector1Unsized 0)
            , Single "100"   (basic mapRRBVector1Unsized 99)
            , Single "1000"  (basic mapRRBVector1Unsized 999)
            , Single "10000" (basic mapRRBVector1Unsized 9999)
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
    , Group "Dictionaries"
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
        ]
    ]

main : IO ()
main = runDefault (const True) Details show bench
