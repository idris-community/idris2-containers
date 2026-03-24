module Concurrent.LRUCache1

import Data.Hashable
import Data.LRUCache1
import Data.Linear.Ref1
import Data.Vect as V
import System
import System.Concurrency

%default total

ITER  : Nat
ITER  = 1000

DELAY : Nat
DELAY = 100

inc : LRUCache1 s Nat Nat -> Nat -> F1' s
inc c 0     t = let _  # t := Data.LRUCache1.insert 0 0 c t in () # t
inc c (S k) t = let c' # t := Data.LRUCache1.insert (S k) (S k) c t in inc c' k t

prog : LRUCache1 World Nat Nat -> IO ()
prog c = runIO (forN ITER $ inc c DELAY)

runProg : Nat -> IO (List (Nat, Nat))
runProg n = do
  c  <- runIO (empty 1_000_000_000)
  ts <- sequence $ V.replicate n (fork $ prog c)
  traverse_ (\t => threadWait t) ts
  runIO (toList c)

main : IO ()
main = do
  us <- runProg 4
  printLn (length us)
