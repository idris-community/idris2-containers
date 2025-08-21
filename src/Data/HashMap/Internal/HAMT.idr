||| HashMap Internals (HAMT)
module Data.HashMap.Internal.HAMT

import Data.HashMap.Internal.SparseArray

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
