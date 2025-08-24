||| HashMap Internals (HAMT)
module Data.HashMap.Internal.HAMT

import Data.HashMap.Internal.SparseArray

import Data.Array
import Data.Array.Core
import Data.Array.Index
import Data.Array.Indexed
import Data.Bits
import Data.Fin
import Data.Hashable
import Data.List
import Data.Nat
import Data.String
import Derive.Prelude
import Syntax.T1 as T1

%hide Data.List.drop
%hide Data.List.take
%hide Data.List.Quantifiers.All.drop
%hide Data.List.Quantifiers.All.take
%hide Data.Vect.drop
%hide Data.Vect.take
%hide Data.Vect.Quantifiers.All.drop
%hide Data.Vect.Stream.take
%hide Prelude.take

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          HAMT
--------------------------------------------------------------------------------

||| A non-empty dependently-typed hash-array mapped trie.
public export
data HAMT : (key : Type) -> (val : key -> Type) -> Type where
  Leaf      : (hash : Bits64) -> (k : key) -> (v : val k) -> HAMT key val
  Node      : SparseArray (HAMT key val) -> HAMT key val
  Collision : (hash : Bits64) -> Array (k ** val k) -> HAMT key val

--------------------------------------------------------------------------------
--          HAMT internals
--------------------------------------------------------------------------------

||| The HAMT chunk size.
chunksize : Bits64
chunksize = 6

||| The max depth of a HAMT. (10 * 6 + 4)
maxdepth : Bits64
maxdepth = 10

||| Get the mask based on the depth.
getMask :  (depth : Bits64)
        -> Bits64
getMask depth =
  let basemask        = 0b111111
      depthchunksize  = depth * chunksize
      depthchunksize' = cast {to=Nat} depthchunksize
    in case tryNatToFin depthchunksize' of 
         Nothing               =>
           assert_total $ idris_crash "Data.HashMap.Internal.HAMT.getMask: couldn't convert Nat to Fin"
         Just depthchunksize'' =>
           basemask `shiftL` depthchunksize''

||| Get the index based on the depth and hash.
export
getIndex :  (depth : Bits64)
         -> (hash : Bits64)
         -> Bits32
getIndex depth hash =
  let depthchunksize  = depth * chunksize
      depthchunksize' = cast {to=Nat} depthchunksize
    in case tryNatToFin depthchunksize' of
         Nothing              =>
           assert_total $ idris_crash "Data.HashMap.Internal.HAMT.getMask: couldn't convert Nat to Fin"
         Just depthchunksize'' =>
           let mask = getMask depth
             in cast {to=Bits32} $ (mask .&. hash) `shiftR` depthchunksize''

--------------------------------------------------------------------------------
--          Creating HAMTs
--------------------------------------------------------------------------------

||| An HAMT with a single element. 
export
singletonWithHash :  (hash : Bits64)
                  -> (k : key)
                  -> (v : val k)
                  -> HAMT key val
singletonWithHash hash k v =
  Leaf hash k v

||| An HAMT with a single element.
export
singleton :  Hashable key
          => (k : key)
          -> (v : val k)
          -> HAMT key val
singleton k v =
  singletonWithHash (hash k) k v

--------------------------------------------------------------------------------
--          Lookups
--------------------------------------------------------------------------------

||| Lookup a value in a list based on a key, index and a key equality function.
lookupEntry :  {0 key : Type}
            -> {0 val : key -> Type}
            -> (k : key)
            -> (idx : Bits32)
            -> (keyeq : (x : key) -> (y : key) -> Bool)
            -> List (k ** val k)
            -> Maybe (Bits32, (k ** val k))
lookupEntry k idx _     []                    =
  Nothing
lookupEntry k idx keyeq ((k' ** entry) :: xs) =
  case keyeq k k' of
    True  =>
      Just (idx, (k' ** entry))
    False =>
      lookupEntry k
                  (idx + 1)
                  keyeq
                  xs

||| Lookup a value in a HAMT based on a key, hash and depth.
export
lookupWithHash :  (k : key)
               -> (hash : Bits64)
               -> (depth : Bits64)
               -> (keyeq : (x : key) -> (y : key) -> Bool)
               -> HAMT key val
               -> Maybe (k ** val k)
lookupWithHash k0 hash0 depth keyeq (Leaf hash1 k1 val)   =
  case hash0 == hash1 of
    True  =>
      case keyeq k0 k1 of
        True  =>
          Just (k1 ** val)
        False =>
          Nothing
    False =>
      Nothing
lookupWithHash k0 hash0 depth keyeq (Node arr)            =
  let idx  = getIndex depth hash0
      idx' = index idx arr
    in case idx' of
         Nothing    =>
           Nothing
         Just idx'' =>
           lookupWithHash k0
                          hash0
                          (assert_smaller depth $ depth + 1)
                          keyeq
                          idx''
lookupWithHash k0 hash0 depth keyeq (Collision hash1 arr) =
  case hash0 == hash1 of
    True  =>
      let arrl  = toList arr
          arrl' = lookupEntry k0
                              0
                              keyeq
                              arrl
        in snd <$> arrl'
    False =>
      Nothing

||| Lookup a value in a HAMT based on a key.
export
lookup :  Hashable key
       => (k : key)
       -> HAMT key val
       -> (keyeq : (x : key) -> (y : key) -> Bool)
       -> Maybe (k ** val k)
lookup k hamt keyeq =
  lookupWithHash k
                 (hash k)
                 0
                 keyeq
                 hamt

export
node2 :  (tree0 : HAMT key val)
      -> (hash0 : Bits64)
      -> (tree1 : HAMT key val)
      -> (hash1 : Bits64)
      -> (depth : Bits64)
      -> HAMT key val
node2 hamt0 hash0 hamt1 hash1 depth =
  let idx0 = getIndex depth hash0
      idx1 = getIndex depth hash1
    in case idx0 == idx1 of
         True  =>
           Node $ singleton (idx0, (node2 hamt0 hash0 hamt1 hash1 (assert_smaller depth $ depth + 1)))
         False =>
           Node $ doubleton (idx0, hamt0)
                            (idx1, hamt1)

export
insertWithHash :  (k : key)
               -> val k
               -> (hash : Bits64)
               -> (depth : Bits64)
               -> (keyEq : (x : key) -> (y : key) -> Bool)
               -> HAMT key val
               -> HAMT key val
insertWithHash k0 val0 hash0 depth keyeq hamt@(Leaf hash1 k1 val1)  =
  case hash0 /= hash1 of
    True  =>
      node2 (singletonWithHash hash0 k0 val0) hash0 hamt hash1 depth
    False =>
      case keyeq k0 k1 of
        True  =>
          Leaf hash0 k0 val0 
        False =>
          Collision hash0 (fromList [(k0 ** val0), (k1 ** val1)])
insertWithHash k val hash0 depth keyeq   (Node array)               =
  let idx = getIndex depth hash0
    in case index idx array of
         Just hamt =>
           Node $
             set idx
                 (insertWithHash k val hash0 (assert_smaller depth $ depth + 1) keyeq hamt)
                 array
         Nothing =>
           Node $ set idx (singletonWithHash hash0 k val) array
insertWithHash k val hash0 depth keyeq   hamt@(Collision hash1 array) =
  case hash0 == hash1 of
    True  =>
      case lookupEntry k 0 keyeq (toList array) of
        Just (idx, _) =>
          let idx' = cast {to=Nat} idx
            in case tryNatToFin idx' of
                 Nothing    =>
                   assert_total $ idris_crash "Data.HashMap.Internal.HAMT.insertWithHash: couldn't convert Nat to Fin"
                 Just idx'' =>
                   let array' = setAt idx'' (k ** val) array.arr
                     in Collision hash1 (A array.size array')
        Nothing       =>
          let array' = append array.arr (fill 1 (k ** val))
            in Collision hash1 (A (array.size `plus` 1) array')
    False =>
      node2 (singletonWithHash hash0 k val) hash0 hamt hash1 depth

export
insert :  Hashable key
       => (k : key)
       -> val k
       -> (keyEq : (x : key) -> (y : key) -> Bool)
       -> HAMT key val
       -> HAMT key val
insert k x keyeq hamt =
  insertWithHash k
                 x
                 (hash k)
                 0
                 keyeq
                 hamt
