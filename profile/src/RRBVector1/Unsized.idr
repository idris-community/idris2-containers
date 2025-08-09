module RRBVector1.Unsized

import Seq.Sized

import Data.RRBVector1.Unsized as VU1
import Data.RRBVector1.Unsized.Internal as VU1I

import Data.Linear.Ref1
import Data.Linear.Token

%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.(<|)
%hide Prelude.(|>)

export
createRRBVector1Unsized : (n : Nat) -> IO ()
createRRBVector1Unsized n =
  ignore $ runIO $ \t =>
    VU1.fromList [0..n] t

export
consRRBVector1Unsized : (n : Nat) -> IO ()
consRRBVector1Unsized n =
  ignore $ runIO $ \t =>
    let vs  # t := VU1.fromList [0..n] t
        vs' # t := VU1.(<|) 10 vs t
        vs' # t := VU1.(<|) 11 vs' t
        vs' # t := VU1.(<|) 12 vs' t
        vs' # t := VU1.(<|) 13 vs' t
        vs' # t := VU1.(<|) 14 vs' t
        vs' # t := VU1.(<|) 15 vs' t
        vs' # t := VU1.(<|) 16 vs' t
        vs' # t := VU1.(<|) 17 vs' t
        vs' # t := VU1.(<|) 18 vs' t
      in VU1.(<|) 19 vs' t

export
snocRRBVector1Unsized : (n : Nat) -> IO ()
snocRRBVector1Unsized n =
  ignore $ runIO $ \t =>
    let vs  # t := VU1.fromList [0..n] t
        vs' # t := VU1.(|>) vs 10 t
        vs' # t := VU1.(|>) vs' 11 t
        vs' # t := VU1.(|>) vs' 12 t
        vs' # t := VU1.(|>) vs' 13 t
        vs' # t := VU1.(|>) vs' 14 t
        vs' # t := VU1.(|>) vs' 15 t
        vs' # t := VU1.(|>) vs' 16 t
        vs' # t := VU1.(|>) vs' 17 t
        vs' # t := VU1.(|>) vs' 18 t
      in VU1.(|>) vs' 19 t

export
appendRRBVector1Unsized : Nat -> IO ()
appendRRBVector1Unsized n =
  ignore $ runIO $ \t =>
    let v # t := VU1.fromList [0..n] t
      in VU1.(><) v v t

export
mapRRBVector1Unsized : Nat -> IO ()
mapRRBVector1Unsized n =
  ignore $ runIO $ \t =>
    let v # t := VU1.fromList [0..n] t
      in VU1.map id v t
