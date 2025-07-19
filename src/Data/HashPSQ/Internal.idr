||| Hash Priority Search Queue Internals
module Data.HashPSQ.Internal

import Data.NatPSQ.Internal as NatPSQI
import Data.OrdPSQ          as OrdPSQ
import Data.OrdPSQ.Internal as OrdPSQI

import Data.List
import Data.String
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Bucket
--------------------------------------------------------------------------------

public export
data Bucket : (k : Type) -> (p : Type) -> (v : Type) -> Type where
  MkBucket :  k
           -> v
           -> OrdPSQI.OrdPSQ k p v
           -> Bucket k p v

%runElab derive "Bucket" [Eq,Ord,Show]

export
toBucket :  Ord k
         => Ord p
         => OrdPSQI.OrdPSQ k p v
         -> Maybe (p, Bucket k p v)
toBucket opsq =
  case OrdPSQ.minView opsq of
    Just (k, p, x, opsq') =>
      Just (p, MkBucket k x opsq')
    Nothing               =>
      Nothing

||| Smart constructor which takes care of placing the minimum element directly
||| in the Bucket.
export
mkBucket :  Ord k
         => Ord p
         => k
         -> p
         -> v
         -> OrdPSQI.OrdPSQ k p v
         -> (p, Bucket k p v)
mkBucket k p x opsq =
  case toBucket (OrdPSQ.insert k p x opsq) of
    Just bucket =>
      bucket
    Nothing     =>
      assert_total $ idris_crash "Data.HashPSQ.Internal.mkBucket: internal error"

--------------------------------------------------------------------------------
--          HashPSQ
--------------------------------------------------------------------------------

||| A priority search queue with keys of type k and priorities of type p
||| and values of type v.
||| A HashPSQ offers very similar performance to NatPSQ.
||| In case of collisions, it uses an OrdPSQ locally to solve those.
||| This means worst case complexity is usually given by O(min(n,W), log n), where W is the number of bits in an Int.
||| This simplifies to O(min(n, W)) since log n is always smaller than W on current machines.
public export
data HashPSQ : (k : Type) -> (p : Type) -> (v : Type) -> Type where
  MkHashPSQ :  NatPSQI.NatPSQ p (Bucket k p v)
            -> HashPSQ k p v

%runElab derive "HashPSQ" [Eq,Ord,Show]
