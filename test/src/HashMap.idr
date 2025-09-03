module HashMap

import Hedgehog
import Data.Vect
import Data.HashMap
import Data.HashMap.Internal
import Data.Hashable
import Data.List
import Data.SortedMap

%default total

record BadHash where
    constructor MkBadHash
    inner : Int

Hashable BadHash where
    hash x = cast $ x.inner `div` 100
    hashWithSalt _ x = hash x

Show BadHash where
    show x = "MkBadHash \{show x.inner}"

Eq BadHash where
    x == y = x.inner == y.inner

data Act : key -> val -> Type where
    Insert : key -> val -> Act key val
    Delete : key -> Act key val

Show key => Show val => Show (Act key val) where
    show (Insert k v) = "insert \{show k} \{show v}"
    show (Delete k) = "delete \{show k}"

runAct : Hashable key => Eq key => HashMap key val -> Act key val -> HashMap key val
runAct hm (Insert key val) = insert key val hm
runAct hm (Delete key) = delete key hm

runActSorted : Ord key => SortedMap key val -> Act key val -> SortedMap key val
runActSorted sm (Insert key val) = insert key val sm
runActSorted sm (Delete key) = delete key sm

genAct : Gen key -> Gen val -> Gen (Act key val)
genAct k v = frequency
    [ (10, [| Insert k v |])
    , (3, [| Delete k |])
    ]

genHashmap : Hashable key => Eq key => Gen key -> Gen val -> Gen (HashMap key val)
genHashmap k v = foldl runAct empty <$> list (exponential 1 1000) (genAct k v)

testInsertDelete :
    Hashable a =>
    Eq a => Eq b =>
    Show a => Show b =>
    (testCount : TestLimit) ->
    (key : Gen a) -> (val : Gen b) ->
    Property
testInsertDelete testCount k v = withTests testCount $ property $ do
    hm <- forAll $ genHashmap k v
    key <- forAll k
    val <- forAll v
    lookup key (insert key val hm) === Just val
    lookup key (delete key hm) === Nothing

testKeys :
    Hashable a =>
    Ord a =>
    (Show a, Show b) =>
    (testCount : TestLimit) ->
    (key : Gen a) -> (val : Gen b) ->
    Property
testKeys testCount k v = withTests testCount $ property $ do
    acts <- forAll $ list (exponential 0 1000) (genAct k v)
    let hm = foldl runAct HashMap.empty acts
    let sm = foldl runActSorted SortedMap.empty acts
    sort (keys hm) === keys sm

defaultString : Gen String
defaultString = string (exponential 0 100) printableUnicode

export
props : Group
props = MkGroup "HashMap"
  [ ("lookup/insert,delete Int32", testInsertDelete 1000 anyInt32 anyInt32)
  , ("lookup/insert,delete BadHash", testInsertDelete 100 (MkBadHash . cast <$> anyInt32) anyInt32)
  , ("lookup/insert,delete String", testInsertDelete 100 defaultString anyInt64)
  , ("keys Int32", testKeys 1000 anyInt32 anyInt32)
  , ("keys String", testKeys 100 defaultString anyInt32)
  ]
