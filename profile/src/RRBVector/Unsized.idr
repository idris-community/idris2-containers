module RRBVector.Unsized

import Data.RRBVector.Unsized as VU
import Data.RRBVector.Unsized.Internal as VSI

import Profile

%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.(<|)
%hide Prelude.(|>)

export
createRRBVectorUnsized : Nat -> RRBVector Nat
createRRBVectorUnsized n = VU.fromList [0..n]

export
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

export
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

export
appendRRBVectorUnsized : Nat -> RRBVector Nat
appendRRBVectorUnsized n = do
  let v = VU.fromList [0..n]
  v >< v

export
indexRRBVectorUnsized : Nat -> Maybe ()
indexRRBVectorUnsized n = do
  let v = VU.fromList [0..n]
  for_ (Prelude.id v) $ \v' =>
    VU.lookup v' v

export
mapRRBVectorUnsized : Nat -> RRBVector Nat
mapRRBVectorUnsized n = do
  let v = VU.fromList [0..n]
  map (\x => plus x 1) v

export
replicateRRBVectorUnsized : Nat -> RRBVector Nat
replicateRRBVectorUnsized n = do
  VU.replicate n 0

export
splitAtRRBVectorUnsized : Nat -> (RRBVector Nat, RRBVector Nat)
splitAtRRBVectorUnsized n = do
  let v = VU.fromList [0..n]
  VU.splitAt (n `div` 2) v

export
reverseRRBVectorUnsized : Nat -> RRBVector Nat
reverseRRBVectorUnsized n = do
  let v = VU.fromList [0..n]
  VU.reverse v
