module Concurrent.BoundedQueue1

import Data.BoundedQueue.Unsized.Internal
import Data.BoundedQueue1.Unsized.Internal
import Data.BoundedQueue1.Unsized
import Data.Linear.Ref1
import Data.Vect as V
import System
import System.Concurrency

%default total

ITER : Nat
ITER = 10_000

DELAY : Nat
DELAY = 100_000

inc : BoundedQueue1 s Nat -> Nat -> F1' s
inc q 0     = enqueue q 0
inc q (S k) = inc q k

prog : BoundedQueue1 World Nat -> IO ()
prog q = runIO (forN ITER $ inc q DELAY)

runProg : Nat -> IO (List Nat)
runProg n = do
  q  <- runIO (Unsized.empty 1_000_000_000_000)
  ts <- sequence $ V.replicate n (fork $ prog q)
  traverse_ (\t => threadWait t) ts
  runIO (toList q)

main : IO ()
main = do
  us <- runProg 4
  printLn (length us)
