module RRBVector1.Sized

import Data.RRBVector1.Sized as VS1
import Data.RRBVector1.Sized.Internal as VS1I

import Data.Linear.Ref1
import Data.Linear.Token

%hide Prelude.Ops.infixr.(<|)
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.(<|)
%hide Prelude.(|>)

export
createRRBVector1Sized : (n : Nat) -> IO ()
createRRBVector1Sized n =
  ignore $ runIO $ \t =>
    VS1.fromList [0..n] t

export
consRRBVector1Sized : (n : Nat) -> IO ()
consRRBVector1Sized n =
  ignore $ runIO $ \t =>
    let vs         # t := VS1.fromList [0..n] t
        (_ ** vs') # t := VS1.(<|) 10 vs t
        (_ ** vs') # t := VS1.(<|) 11 vs' t
        (_ ** vs') # t := VS1.(<|) 12 vs' t
        (_ ** vs') # t := VS1.(<|) 13 vs' t
        (_ ** vs') # t := VS1.(<|) 14 vs' t
        (_ ** vs') # t := VS1.(<|) 15 vs' t
        (_ ** vs') # t := VS1.(<|) 16 vs' t
        (_ ** vs') # t := VS1.(<|) 17 vs' t
        (_ ** vs') # t := VS1.(<|) 18 vs' t
      in VS1.(<|) 19 vs' t

export
snocRRBVector1Sized : (n : Nat) -> IO ()
snocRRBVector1Sized n =
  ignore $ runIO $ \t =>
    let vs         # t := VS1.fromList [0..n] t
        (_ ** vs') # t := VS1.(|>) vs 10 t
        (_ ** vs') # t := VS1.(|>) vs' 11 t
        (_ ** vs') # t := VS1.(|>) vs' 12 t
        (_ ** vs') # t := VS1.(|>) vs' 13 t
        (_ ** vs') # t := VS1.(|>) vs' 14 t
        (_ ** vs') # t := VS1.(|>) vs' 15 t
        (_ ** vs') # t := VS1.(|>) vs' 16 t
        (_ ** vs') # t := VS1.(|>) vs' 17 t
        (_ ** vs') # t := VS1.(|>) vs' 18 t
      in VS1.(|>) vs' 19 t

export
appendRRBVector1Sized : Nat -> IO ()
appendRRBVector1Sized n =
  ignore $ runIO $ \t =>
    let v # t := VS1.fromList [0..n] t
      in VS1.(><) v v t

export
mapRRBVector1Sized : Nat -> IO ()
mapRRBVector1Sized n =
  ignore $ runIO $ \t =>
    let v # t := VS1.fromList [0..n] t
      in VS1.map id v t
