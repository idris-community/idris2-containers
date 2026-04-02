module Concurrent.RRBVector1

import Data.RRBVector.Unsized.Internal
import Data.RRBVector.Unsized
import Data.RRBVector1.Unsized
import Data.Linear.Ref1
import Data.Vect as V
import System
import System.Concurrency

%hide Prelude.Ops.infixl.(|>)

%default total

ITER : Nat
ITER = 10_000

DELAY : Nat
DELAY = 100_000

inc : RRBVector1 s Nat -> Nat -> F1' s
inc rrbvector 0     t = (rrbvector |> Z) t
inc rrbvector (S k) t = (rrbvector |> k) t

prog : RRBVector1 World Nat -> IO ()
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
