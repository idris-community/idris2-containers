||| HashMap Internals (SparseArray)
module Data.HashMap.Internal.SparseArray

import Data.Array
import Data.Array.Core
import Data.Array.Index
import Data.Array.Indexed
import Data.Bits
import Data.Fin
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
--          SparseArray
--------------------------------------------------------------------------------

||| An array storing up to 64 elements.
public export
data SparseArray : (a : Type) -> Type where
  MkSparseArray :  (bitmap : Bits64)
                -> (array  : Array a)
                -> SparseArray a

%runElab derive "SparseArray" [Eq,Ord,Show]

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| Utility specialized over Bits32.
private
bits32SortNub :  List (Bits32, a)
              -> List (Bits32, a)
              -> List (Bits32, a)
bits32SortNub []            acc =
  acc
bits32SortNub lst@(x :: xs) acc =
  let (lt, gt) = separate (fst x) xs [] []
    in bits32SortNub (assert_smaller lst lt) $ x :: bits32SortNub (assert_smaller lst gt) acc
  where
    separate :  Bits32
             -> List (Bits32, a)
             -> (lt : List (Bits32, a))
             -> (gt : List (Bits32, a))
             -> (List (Bits32, a), List (Bits32, a))
    separate x []        lt gt =
      (lt, gt)
    separate x (y :: xs) lt gt =
      case compare (fst y) x of
        LT =>
          separate x xs (y :: lt) gt
        EQ =>
          separate x xs lt gt
        GT =>
          separate x xs lt (y :: gt)

--------------------------------------------------------------------------------
--          Creating SparseArrays
--------------------------------------------------------------------------------

||| The empty array.
export
empty : SparseArray a
empty = MkSparseArray 0
                      empty

||| An array with a single element.
export
singleton :  (Bits32, a)
          -> SparseArray a
singleton (k, v) =
  let k'  = cast {to=Bits64} k
      k'' = cast {to=Nat} k'
    in case tryNatToFin k'' of
         Nothing  =>
           assert_total $ idris_crash "Data.HashMap.Internal.SparseArray.singleton: couldn't convert Nat to Fin"
         Just k''' =>
           MkSparseArray (bit k''')
                         (fill 1 v)

||| Create a new array from a list.
export
fromList :  List (Bits32, a)
         -> SparseArray a
fromList xs =
  let xs     = bits32SortNub xs []
      bitmap = foldl (\acc, (idx, _) =>
                        let idx'  = cast {to=Bits64} idx
                            idx'' = cast {to=Nat} idx'
                          in case tryNatToFin idx'' of
                               Nothing   =>
                                 assert_total $ idris_crash "Data.HashMap.Internal.SparseArray.fromList: couldn't convert Nat to Fin"
                               Just idx''' =>
                                 setBit acc idx''') (the Bits32 0) xs
      arr    = fromList (map snd xs)
    in MkSparseArray (cast {to=Bits64} bitmap)
                     arr

||| An array with two elements.
export
doubleton :  (Bits32, a)
          -> (Bits32, a)
          -> SparseArray a
doubleton (k0, v0) (k1, v1) =
  case compare k0 k1 of
    LT =>
      let k0'  = cast {to=Bits64} k0
          k0'' = cast {to=Nat} k0'
          k1'  = cast {to=Bits64} k1
          k1'' = cast {to=Nat} k1'
        in case (tryNatToFin k0'', tryNatToFin k1'') of
             (Nothing, Nothing)       =>
               assert_total $ idris_crash "Data.HashMap.Internal.SparseArray.doubleton: couldn't convert Nat to Fin"
             (_      , Nothing)       =>
               assert_total $ idris_crash "Data.HashMap.Internal.SparseArray.doubleton: couldn't convert Nat to Fin"
             (Nothing, _      )       =>
               assert_total $ idris_crash "Data.HashMap.Internal.SparseArray.doubleton: couldn't convert Nat to Fin"
             (Just k0''', Just k1''') =>
               MkSparseArray ((bit k0''') .|. (bit k1'''))
                             (fromList [v0, v1])
    EQ =>
      singleton (k1, v1)
    GT =>
      let k0'  = cast {to=Bits64} k0
          k0'' = cast {to=Nat} k0'
          k1'  = cast {to=Bits64} k1
          k1'' = cast {to=Nat} k1'
        in case (tryNatToFin k0'', tryNatToFin k1'') of
             (Nothing, Nothing)       =>
               assert_total $ idris_crash "Data.HashMap.Internal.SparseArray.doubleton: couldn't convert Nat to Fin"
             (_      , Nothing)       =>
               assert_total $ idris_crash "Data.HashMap.Internal.SparseArray.doubleton: couldn't convert Nat to Fin"
             (Nothing, _      )       =>
               assert_total $ idris_crash "Data.HashMap.Internal.SparseArray.doubleton: couldn't convert Nat to Fin"
             (Just k0''', Just k1''') =>
               MkSparseArray ((bit k1''') .|. (bit k0'''))
                             (fromList [v1, v0])

--------------------------------------------------------------------------------
--          Indexing
--------------------------------------------------------------------------------

||| Checks whether the given index has an entry in the array by
||| testing if the corresponding bit is set in the array's bitmap.
export
hasEntry :  Bits32
         -> SparseArray a
         -> Bool
hasEntry sparseidx (MkSparseArray bitmap _) =
  case sparseidx >= 64 of
    True  =>
      False
    False =>
      let sparseidx' = cast {to=Nat} sparseidx
        in case tryNatToFin sparseidx' of
             Nothing     =>
               assert_total $ idris_crash "Data.HashMap.Internal.SparseArray.hasEntry: couldn't convert Nat to Fin"
             Just sparseidx'' =>
               testBit bitmap sparseidx''

||| Computes the rank of the given bit index by counting how many bits
||| are set up to and including that position in the bitmap.
export
findIndex :  Bits32
          -> Bits64
          -> Bits32
findIndex idx bitmap =
  case idx == 0 of
    True  =>
      cast {to=Bits32} 0
    False =>
      let mask   = 64 - idx
          mask'  = cast {to=Bits64} mask
          mask'' = cast {to=Nat} mask'
        in case tryNatToFin mask'' of
             Nothing      =>
               assert_total $ idris_crash "Data.HashMap.Internal.SparseArray.findIndex: couldn't convert Nat to Fin"
             Just mask''' =>
               let mask'''' = (the Bits64 oneBits) `shiftR` mask'''
                 in cast {to=Bits32} $ popCount $ bitmap .&. mask''''

||| Looks up the element at the given index in the array,
||| returning `Nothing` if no entry exists at that position.
export
index :  (sparseidx : Bits32)
      -> (arr : SparseArray a)
      -> Maybe a
index sparseidx sa@(MkSparseArray bitmap array) =
  case sparseidx >= 64 of
    True  =>
      Nothing
    False =>  
      case hasEntry sparseidx sa of
        True  =>
          let arridx  = findIndex sparseidx bitmap
              arridx' = cast {to=Nat} arridx
            in case tryNatToFin arridx' of
                 Nothing       =>
                   Nothing
                 Just arridx'' =>
                   Just ( at array.arr arridx''
                        )
        False =>
          Nothing

--------------------------------------------------------------------------------
--          Insertion
--------------------------------------------------------------------------------

||| Set a value in an array.
export
set :  (sparseidx : Bits32)
    -> (val : a)
    -> (arr : SparseArray a)
    -> SparseArray a
set sparseidx val arr@(MkSparseArray bitmap array) =
  case sparseidx >= 64 of
    True  =>
      assert_total $ idris_crash "Data.HashMap.Internal.SparseArray.set: sparse index out of bounds"
    False =>
      case hasEntry sparseidx arr of
        True  =>
          let arridx  = findIndex sparseidx bitmap
              arridx' = cast {to=Nat} arridx
            in case tryNatToFin arridx' of
                 Nothing       =>
                   assert_total $ idris_crash "Data.HashMap.Internal.SparseArray.set: couldn't convert Nat to Fin"
                 Just arridx'' =>
                   let array' = setAt arridx'' val array.arr
                     in MkSparseArray bitmap
                                      (A array.size array')
        False =>
          let sparseidx'  = cast {to=Bits64} sparseidx
              sparseidx'' = cast {to=Nat} sparseidx'
            in case tryNatToFin sparseidx'' of
                 Nothing           =>
                   assert_total $ idris_crash "Data.HashMap.Internal.SparseArray.set: couldn't convert Nat to Fin"
                 Just sparseidx''' =>
                   let bitmap'      = setBit bitmap sparseidx'''
                       arridx       = findIndex sparseidx bitmap
                       preidxarray  = Data.Array.take (cast {to=Nat} arridx) array
                       atidxarray   = fill 1 val
                       postidxarray = Data.Array.drop ((cast {to=Nat} arridx) `plus` 1) array
                       array'       = preidxarray <+> atidxarray <+> postidxarray
                     in MkSparseArray bitmap'
                                      array'

--------------------------------------------------------------------------------
--          Deletion
--------------------------------------------------------------------------------

||| Remove a value from an array.
||| Returns the original array if the
||| value doesn't exist in the array.
export
delete :  (sparseidx : Bits32)
       -> (arr : SparseArray a)
       -> SparseArray a
delete sparseidx arr@(MkSparseArray bitmap array) =
  case sparseidx >= 64 of
    True  =>
      assert_total $ idris_crash "Data.HashMap.Internal.SparseArray.delete: sparse index out of bounds"
    False =>
      case hasEntry sparseidx arr of
        True  =>
          let sparseidx'  = cast {to=Bits64} sparseidx
              sparseidx'' = cast {to=Nat} sparseidx'
            in case tryNatToFin sparseidx'' of
                 Nothing     =>
                   assert_total $ idris_crash "Data.HashMap.Internal.SparseArray.delete: couldn't convert Nat to Fin"
                 Just sparseidx''' =>
                   let arridx       = findIndex sparseidx bitmap
                       bitmap'      = clearBit bitmap sparseidx'''
                       preidxarray  = Data.Array.take (cast {to=Nat} arridx) array
                       postidxarray = Data.Array.drop ((cast {to=Nat} arridx) `plus` 1) array
                       array'       = preidxarray <+> postidxarray
                     in MkSparseArray bitmap'
                                      array'
        False =>
          arr

--------------------------------------------------------------------------------
--          Length
--------------------------------------------------------------------------------

||| Return the size of an array.
export
length :  SparseArray a
       -> Nat
length (MkSparseArray bitmap _) =
  cast $ popCount bitmap

--------------------------------------------------------------------------------
--          Indices
--------------------------------------------------------------------------------

||| Return the list of all indices that have entries set in the array.
export
indices :  SparseArray a
        -> List Bits32
indices arr =
  filter (\idx => hasEntry idx arr) [0..63]

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Functor SparseArray where
  map f (MkSparseArray bitmap array) = MkSparseArray bitmap (map f array)

export
Foldable SparseArray where
    foldr f z (MkSparseArray _ array) = foldr f z array.arr
    foldl f z (MkSparseArray _ array) = foldl f z array.arr
    null (MkSparseArray bitmap _)     = bitmap == 0
    toList (MkSparseArray _ array)    = toList array.arr
    foldMap f (MkSparseArray _ array) = foldMap f array.arr

export
Show a => Show (SparseArray a) where
    show (MkSparseArray _ array) = "[" ++ fastConcat (intersperse ", " (map show (toList array.arr))) ++ "]"

export
Eq a => Eq (SparseArray a) where
  x == y = length x == length y &&
  all (\idx => index idx x == index idx y)
      (indices x)

--------------------------------------------------------------------------------
--          Creating Lists from SparseArrays
--------------------------------------------------------------------------------

export
toList :  SparseArray a
       -> List (Bits32, a)
toList arr =
  zip (indices arr)
      (toList arr)
