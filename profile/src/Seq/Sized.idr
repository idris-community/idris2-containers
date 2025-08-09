module Seq.Sized

import Data.Seq.Sized as SS

export
createSeqSized : (xs : List Nat) -> Seq (length xs) Nat
createSeqSized xs = SS.fromList xs

export
consSeqSized : (xs : List Nat) -> Seq (S (S (S (S (S (S (S (S (S (S (length xs))))))))))) Nat
consSeqSized xs = do
  let s = SS.fromList xs
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
snocSeqSized : (n : Nat) -> Seq (S (S (S (S (S (S (S (S (S (S (length [0..n]))))))))))) Nat
snocSeqSized n = do
  let s = SS.fromList [0..n]
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
appendSeqSized : (xs : List Nat) -> Seq (length xs + length xs) Nat
appendSeqSized xs = do
  let s = SS.fromList xs
  s ++ s

export
mapSeqSized : (xs : List Nat) -> Seq (length xs) Nat
mapSeqSized xs = do
  let v = SS.fromList xs
  map (\x => plus x 1) v

export
replicateSeqSized : (n : Nat) -> Seq n Nat
replicateSeqSized n = do
  SS.replicate n 0

export
splitAtSeqSized : (xs : List Nat) -> Seq (length xs) Nat
splitAtSeqSized xs = do
  let v         = SS.fromList xs
      (v', v'') = SS.splitAt Z v
  v''

export
reverseSeqSized : (xs : List Nat) -> Seq (length xs) Nat
reverseSeqSized xs = do
  let v = SS.fromList xs
  SS.reverse v
