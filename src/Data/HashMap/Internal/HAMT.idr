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
%hide Data.Vect.toVect
%hide Data.Vect.updateAt
%hide Data.Vect.Quantifiers.All.drop
%hide Data.Vect.Quantifiers.All.updateAt
%hide Data.Vect.Stream.take
%hide Prelude.take

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          HAMT
--------------------------------------------------------------------------------

||| A non-empty dependently-typed hash-array mapped trie (HAMT).
public export
data HAMT : (key : Type) -> (val : key -> Type) -> Type where
  Leaf      : (hash : Bits64) -> (k : key) -> (v : val k) -> HAMT key val
  Node      : SparseArray (HAMT key val) -> HAMT key val
  Collision : (hash : Bits64) -> Array (k ** val k) -> HAMT key val

--------------------------------------------------------------------------------
--          HAMT internals
--------------------------------------------------------------------------------

||| The HAMT chunk size.
private
chunksize : Bits64
chunksize = 6

||| The max depth of a HAMT. (10 * 6 + 4)
private
maxdepth : Bits64
maxdepth = 10

||| Computes a bitmask for the current depth in the HAMT,
||| shifting a base mask by `depth * chunksize`.
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

||| Computes the index for a given hash
||| at the specified depth by masking and shifting the hash.
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

||| An HAMT with a single element via a precomputed hash.
export
singletonWithHash :  (hash : Bits64)
                  -> (k : key)
                  -> (v : val k)
                  -> HAMT key val
singletonWithHash hash k v =
  Leaf hash
       k
       v

||| An HAMT with a single element.
export
singleton :  Hashable key
          => (k : key)
          -> (v : val k)
          -> HAMT key val
singleton k v =
  singletonWithHash (hash k)
                    k
                    v

--------------------------------------------------------------------------------
--          Lookups
--------------------------------------------------------------------------------

||| Searches a list of key–value pairs for the given key.
||| Returns the index and entry if found.
lookupEntry :  {0 key : Type}
            -> {0 val : key -> Type}
            -> (keyEq : (x : key) -> (y : key) -> Bool)
            -> (k : key)
            -> (idx : Bits32)
            -> List (k ** val k)
            -> Maybe (Bits32, (k ** val k))
lookupEntry _     k idx []                    =
  Nothing
lookupEntry keyEq k idx ((k' ** entry) :: xs) =
  case keyEq k k' of
    True  =>
      Just (idx, (k' ** entry))
    False =>
      lookupEntry keyEq
                  k
                  (idx + 1)
                  xs

||| Looks up a key in the HAMT using a precomputed hash.
||| Returns the key–value pair if found.
export
lookupWithHash :  (keyEq : (x : key) -> (y : key) -> Bool)
               -> (k : key)
               -> (hash : Bits64)
               -> (depth : Bits64)
               -> HAMT key val
               -> Maybe (k ** val k)
lookupWithHash keyEq k0 hash0 depth (Leaf hash1 k1 val)   =
  case hash0 == hash1 of
    True  =>
      case keyEq k0 k1 of
        True  =>
          Just (k1 ** val)
        False =>
          Nothing
    False =>
      Nothing
lookupWithHash keyEq k0 hash0 depth (Node arr)            =
  let idx  = getIndex depth hash0
      idx' = index idx arr
    in case idx' of
         Nothing    =>
           Nothing
         Just idx'' =>
           lookupWithHash keyEq
                          k0
                          hash0
                          (assert_smaller depth $ depth + 1)
                          idx''
lookupWithHash keyEq k0 hash0 depth (Collision hash1 arr) =
  case hash0 == hash1 of
    True  =>
      let arrl  = toList arr
          arrl' = lookupEntry keyEq
                              k0
                              0
                              arrl
        in snd <$> arrl'
    False =>
      Nothing

||| Finds a key in the HAMT via it's hash.
export
lookup :  Hashable key
       => (keyEq : (x : key) -> (y : key) -> Bool)
       -> (k : key)
       -> HAMT key val
       -> Maybe (k ** val k)
lookup keyEq k hamt =
  lookupWithHash keyEq
                 k
                 (hash k)
                 0
                 hamt

||| Constructs an internal node combining two subtrees.
||| If the hash fragments at the current depth collide,
||| it recurses one level deeper, otherwise, it creates a node with both entries.
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
           Node ( singleton (idx0, (node2 hamt0 hash0 hamt1 hash1 (assert_smaller depth $ depth + 1)))
                )
         False =>
           Node ( doubleton (idx0, hamt0)
                            (idx1, hamt1)
                )

||| Inserts a key–value pair into the HAMT using a precomputed hash.
||| Collisions are resolved by branching,
||| replacing existing entries on key equality,
||| or creating a collision node when distinct keys share a hash.
export
insertWithHash :  (keyEq : (x : key) -> (y : key) -> Bool) 
               -> (k : key)
               -> val k
               -> (hash : Bits64)
               -> (depth : Bits64)
               -> HAMT key val
               -> HAMT key val
insertWithHash keyEq k0 val0 hash0 depth hamt@(Leaf hash1 k1 val1)    =
  case hash0 /= hash1 of
    True  =>
      node2 (singletonWithHash hash0 k0 val0)
            hash0
            hamt
            hash1
            depth
    False =>
      case keyEq k0 k1 of
        True  =>
          Leaf hash0
               k0
               val0 
        False =>
          Collision hash0
                    (fromList [(k0 ** val0), (k1 ** val1)])
insertWithHash keyEq k val hash0 depth   (Node array)                 =
  let idx = getIndex depth hash0
    in case index idx array of
         Just hamt =>
           Node ( set idx
                      ( insertWithHash keyEq
                                       k
                                       val
                                       hash0
                                       (assert_smaller depth $ depth + 1)
                                       hamt
                      )
                      array
                )
         Nothing =>
           Node ( set idx
                      (singletonWithHash hash0 k val)
                      array
                )
insertWithHash keyEq k val hash0 depth   hamt@(Collision hash1 array) =
  case hash0 == hash1 of
    True  =>
      case lookupEntry keyEq k 0 (toList array) of
        Just (idx, _) =>
          let idx' = cast {to=Nat} idx
            in case tryNatToFin idx' of
                 Nothing    =>
                   assert_total $ idris_crash "Data.HashMap.Internal.HAMT.insertWithHash: couldn't convert Nat to Fin"
                 Just idx'' =>
                   let array' = setAt idx'' (k ** val) array.arr
                     in Collision hash1
                                  (A array.size array')
        Nothing       =>
          let array' = append array.arr (fill 1 (k ** val))
            in Collision hash1
                         (A (array.size `plus` 1) array')
    False =>
      node2 (singletonWithHash hash0 k val)
            hash0
            hamt
            hash1
            depth

||| Inserts a key–value pair into the HAMT
||| by hashing the key and delegating to `insertWithHash`.
export
insert :  Hashable key
       => (keyEq : (x : key) -> (y : key) -> Bool)
       -> (k : key)
       -> val k
       -> HAMT key val
       -> HAMT key val
insert keyEq k x hamt =
  insertWithHash keyEq
                 k
                 x
                 (hash k)
                 0
                 hamt

||| Removes a key from the HAMT using a precomputed hash.
||| Returns `Nothing` if the entry is deleted and collapsing
||| nodes when possible to maintain a compact structure.
export
deleteWithHash :  Hashable key
               => (keyEq : (x : key) -> (y : key) -> Bool)
               -> (k : key)
               -> (hash : Bits64)
               -> (depth : Bits64)
               -> HAMT key val
               -> Maybe (HAMT key val)
deleteWithHash keyEq k0 h0  depth hamt@(Leaf h1 k1 _)       =
  case h0 == h1 && keyEq k0 k1 of
    True  =>
      Nothing
    False =>
      Just hamt
deleteWithHash keyEq k hash depth hamt0@(Node array)        =
    let idx = getIndex depth hash
      in case index idx array of
           Just hamt1 =>
             let hamt1' = deleteWithHash keyEq
                                         k
                                         hash
                                         (depth + 1) 
                                         (assert_smaller hamt0 hamt1)
               in case hamt1' of
                    Just hamt2 =>
                      Just ( Node
                               ( set idx hamt2 array
                               )
                           )
                    Nothing =>
                      let array' = delete idx array
                       in case length array' of
                            0 =>
                              Nothing
                            1 =>
                              case index 0 array' of
                                Just (Node _) =>
                                  Just ( Node array'
                                       )
                                hamt2         =>
                                  hamt2
                            _ =>
                              Just $
                                Node array'
           Nothing =>
             Just hamt0
deleteWithHash keyEq k h0   depth hamt@(Collision h1 array) =
  case h0 == h1 of
    True  =>
      let vect = toVect array.arr
          idx  = findIndex (keyEq k . fst) vect
        in case idx of
             Nothing   =>
               Just hamt
             Just idx' =>
               let preidxarray  = Data.Array.take (cast {to=Nat} idx') array
                   postidxarray = Data.Array.drop ((cast {to=Nat} idx') `plus` 1) array
                   array'       = preidxarray <+> postidxarray
                 in case array'.size of
                      0 =>
                        Nothing
                      1 =>
                        case tryNatToFin 0 of
                          Nothing   =>
                            assert_total $ idris_crash "Data.HashMap.Internal.HAMT.deleteWithHash: couldn't convert Nat to Fin"
                          Just zero =>
                            let (key ** val) = at array'.arr zero
                               in Just ( Leaf h1 key val
                                       )
                      _ =>
                        Just ( Collision h1 array'
                             )
    False =>    
      Just hamt

||| Removes a key from the HAMT
||| by hashing the key and delegating to `deleteWithHash`.
export
delete :  Hashable key
       => (keyEq : (x : key) -> (y : key) -> Bool)
       -> (k : key)
       -> HAMT key val
       -> Maybe (HAMT key val)
delete keyEq k hamt =
  deleteWithHash keyEq
                 k
                 (hash k)
                 0
                 hamt

||| Maps a function over all values stored in a HAMT,
||| preserving the keys and structure.
export
trieMap :  ({k : _} -> val0 k -> val1 k)
        -> HAMT key val0
        -> HAMT key val1
trieMap f (Leaf hash k v)        =
  Leaf hash k (f v)
trieMap f (Node array)           =
  Node ( assert_total $
           map (trieMap f) array
       )
trieMap f (Collision hash array) =
  Collision hash
            ( map (\(k ** v) => (k ** (f v))) array
            )

||| Folds over all key–value pairs in a HAMT,
||| combining them with an accumulator while preserving the traversal order.
export
foldWithKey :  ((k : _) -> val k -> acc -> acc)
            -> acc
            -> HAMT key val
            -> acc
foldWithKey f z (Leaf hash k v)        =
  f k v z
foldWithKey f z (Node array)           =
  assert_total $
    foldr (\trie, acc => foldWithKey f acc trie)
          z
          array
foldWithKey f z (Collision hash array) =
  foldr (\(k ** v), acc => f k v z)
        z
        array
