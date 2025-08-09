module Seq.Unsized

import Data.Fin
import Data.Seq.Unsized as SU

export
createSeqUnsized : Nat -> Seq Nat
createSeqUnsized n = SU.fromList [0..n]

export
consSeqUnsized : Nat -> Seq Nat
consSeqUnsized n = do
  let s = SU.fromList [0..n]
      s = cons 10 s
      s = cons 11 s
      s = cons 12 s
      s = cons 13 s
      s = cons 14 s
      s = cons 15 s
      s = cons 16 s
      s = cons 17 s
      s = cons 18 s
  cons 19 s

export
snocSeqUnsized : Nat -> Seq Nat
snocSeqUnsized n = do
  let s = SU.fromList [0..n]
      s = snoc s 10
      s = snoc s 11
      s = snoc s 12
      s = snoc s 13
      s = snoc s 14
      s = snoc s 15
      s = snoc s 16
      s = snoc s 17
      s = snoc s 18
  snoc s 19

export
appendSeqUnsized : Nat -> Seq Nat
appendSeqUnsized n = do
  let s = SU.fromList [0..n]
  s ++ s

export
indexSeqUnsized : Nat -> Maybe ()
indexSeqUnsized n = do
  let s = SU.fromList [0..n]
  for_ (Prelude.id s) $ \s' =>
    SU.index s' s

export
mapSeqUnsized : Nat -> Seq Nat
mapSeqUnsized n = do
  let s = SU.fromList [0..n]
  map (\x => plus x 1) s

export
replicateSeqUnsized : Nat -> Seq Nat
replicateSeqUnsized n = do
  SU.replicate n 0

export
splitAtSeqUnsized : Nat -> (Seq Nat, Seq Nat)
splitAtSeqUnsized n = do
  let s = SU.fromList [0..n]
  SU.splitAt (n `div` 2) s

export
reverseSeqUnsized : Nat -> Seq Nat
reverseSeqUnsized n = do
  let v = SU.fromList [0..n]
  SU.reverse v
