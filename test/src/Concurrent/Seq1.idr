module Concurrent.Seq1

import Data.Seq.Internal
import Data.Seq.Unsized
import Data.Seq1.Unsized
import Data.Linear.Ref1
import Data.Vect as V
import System
import System.Concurrency

%default total

ITER : Nat
ITER = 10_000

DELAY : Nat
DELAY = 100_000

inc : Seq1 s Nat -> Nat -> F1' s
inc seq 0     t = snoc seq Z t
inc seq (S k) t = snoc seq k t

prog : Seq1 World Nat -> IO ()
prog q = runIO (forN ITER $ inc q DELAY)

runProg : Nat -> IO (List Nat)
runProg n = do
  q  <- runIO empty
  ts <- sequence $ V.replicate n (fork $ prog q)
  traverse_ (\t => threadWait t) ts
  runIO (toList q)

main : IO ()
main = do
  us <- runProg 4
  printLn (length us)
