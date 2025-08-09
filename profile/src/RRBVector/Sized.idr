module RRBVector.Sized

import Data.RRBVector.Sized as VS
import Data.RRBVector.Sized.Internal as VUI

import Profile

%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.(<|)
%hide Prelude.(|>)

export
createRRBVectorSized : (xs : List Nat) -> RRBVector (length xs) Nat
createRRBVectorSized xs = VS.fromList xs

export
consRRBVectorSized : (n : Nat) -> (n' ** RRBVector n' Nat)
consRRBVectorSized n = do
  let v          = VS.fromList [0..n]
      (_ ** v)   = 10 <| v
      (_ ** v)   = 11 <| v
      (_ ** v)   = 12 <| v
      (_ ** v)   = 13 <| v
      (_ ** v)   = 14 <| v
      (_ ** v)   = 15 <| v
      (_ ** v)   = 16 <| v
      (_ ** v)   = 17 <| v
      (_ ** v)   = 18 <| v
      (n' ** v') = 19 <| v
  (n' ** v')

export
snocRRBVectorSized : (n : Nat) -> (n' ** RRBVector n' Nat)
snocRRBVectorSized n = do
  let v          = VS.fromList [0..n]
      (_ ** v)   = v |> 10
      (_ ** v)   = v |> 11
      (_ ** v)   = v |> 12
      (_ ** v)   = v |> 13
      (_ ** v)   = v |> 14
      (_ ** v)   = v |> 15
      (_ ** v)   = v |> 16
      (_ ** v)   = v |> 17
      (_ ** v)   = v |> 18
      (n' ** v') = v |> 19
  (n' ** v')

export
appendRRBVectorSized : (n : Nat) -> (n' ** RRBVector n' Nat)
appendRRBVectorSized n = do
  let v          = VS.fromList [0..n]
      (n' ** v') = v >< v
  (n' ** v')

export
indexRRBVectorSized : Nat -> Maybe ()
indexRRBVectorSized n = do
  let v = VS.fromList [0..n]
  for_ (Prelude.id v) $ \v' =>
    VS.lookup v' v

export
mapRRBVectorSized : (n : Nat) -> RRBVector (length [0..n]) Nat
mapRRBVectorSized n = do
  let v = VS.fromList [0..n]
  map (\x => plus x 1) v

export
replicateRRBVectorSized : (n : Nat) -> RRBVector n Nat
replicateRRBVectorSized n = do
  VS.replicate n 0

export
splitAtRRBVectorSized : (n : Nat) -> ((n' ** RRBVector n' Nat), (n'' ** RRBVector n'' Nat))
splitAtRRBVectorSized n = do
  let v = VS.fromList [0..n]
  VS.splitAt (n `div` 2) v

export
reverseRRBVectorSized : (n : Nat) -> (n ** RRBVector n Nat)
reverseRRBVectorSized n = do
  let v = VS.fromList [0..n]
  VS.reverse v
