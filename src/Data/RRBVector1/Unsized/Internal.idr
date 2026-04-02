||| Linear RRB Vector Internals
module Data.RRBVector1.Unsized.Internal

import Data.RRBVector.Unsized.Internal

import Data.Linear.Ref1
import Derive.Prelude

%language ElabReflection

%default total

--------------------------------------------------------------------------------
--          Linear RRB Vectors
--------------------------------------------------------------------------------

||| A linear relaxed radix balanced vector (RRBVector1).
||| It supports fast indexing, iteration, concatenation and splitting.
public export
data RRBVector1 : (s : Type) -> Type -> Type where
  MkRRBVector1 :  Ref s (RRBVector a)
               -> RRBVector1 s a
