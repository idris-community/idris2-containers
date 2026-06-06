module Main

import List
import Map
import Seq.Sized
import Seq.Unsized
import Set
import SortedMap
import SortedSet

import Data.Map
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
        , Group "fromListSeqUnsized"
            [ Single "1"    (basic createSeqUnsized 0)
            , Single "100"  (basic createSeqUnsized 99)
            , Single "1000" (basic createSeqUnsized 999)
            ]
        , Group "consSeqUnsized"
            [ Single "10" (basic consSeqUnsized 9)
            ]
        , Group "snocSeqUnsized"
            [ Single "10" (basic snocSeqUnsized 9)
            ]
        , Group "appendSeqUnsized"
            [ Single "10" (basic appendSeqUnsized 9)
            ]
        , Group "indexSeqUnsized"
            [ Single "1"     (basic indexSeqUnsized 0)
            , Single "100"   (basic indexSeqUnsized 99)
            , Single "1000"  (basic indexSeqUnsized 999)
            , Single "10000" (basic indexSeqUnsized 9999)
            ]
        , Group "mapSeqUnsized"
            [ Single "1"     (basic mapSeqUnsized 0)
            , Single "100"   (basic mapSeqUnsized 99)
            , Single "1000"  (basic mapSeqUnsized 999)
            , Single "10000" (basic mapSeqUnsized 9999)
            ]
        , Group "replicateSeqUnsized"
            [ Single "1"     (basic replicateSeqUnsized 0)
            , Single "100"   (basic replicateSeqUnsized 99)
            , Single "1000"  (basic replicateSeqUnsized 999)
            , Single "10000" (basic replicateSeqUnsized 9999)
            ]
        , Group "reverseSeqUnsized"
            [ Single "1"     (basic reverseSeqUnsized 0)
            , Single "100"   (basic reverseSeqUnsized 99)
            , Single "1000"  (basic reverseSeqUnsized 999)
            , Single "10000" (basic reverseSeqUnsized 9999)
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
