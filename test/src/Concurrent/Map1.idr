||| Concurrent tests for shared-store linear maps.
module Concurrent.Map1

import Data.Map
import Data.Map1
import Data.Linear.Ref1
import Data.SortedMap
import Data.Vect as V
import System
import System.Concurrency

%default total

private
ITER : Nat
ITER = 1000

private
THREADS : Nat
THREADS = 4

--------------------------------------------------------------------------------
--          Concurrent Updates
--------------------------------------------------------------------------------

||| Increment the same key using one atomic insertWith operation.
private
inc : Map1 s Nat Nat -> F1' s
inc m = Data.Map1.insertWith (+) 0 1 m

||| Perform repeated increments on a shared map.
private
incrementWorker : Map1 World Nat Nat -> IO ()
incrementWorker m = runIO (forN ITER $ inc m)

||| Verify that competing atomic increments do not lose updates.
private
checkIncrements : IO ()
checkIncrements = do
  store <- the (IO (MapStore1 World Nat Nat)) $
             runIO Data.Map1.newStore
  m <- runIO (Data.Map1.singleton 0 0 store)
  ts <- sequence $ V.replicate THREADS (fork $ incrementWorker m)
  traverse_ (\t => threadWait t) ts
  result <- runIO (Data.Map1.lookup 0 m)
  when (result /= Just (THREADS * ITER)) $
    assert_total $ idris_crash "Concurrent.Map1.checkIncrements: lost atomic increments"

--------------------------------------------------------------------------------
--          Atomic Swap
--------------------------------------------------------------------------------

||| Swap two maps in the same shared store.
private
swapOnce : Map1 s Nat Nat -> Map1 s Nat Nat -> F1' s
swapOnce = Data.Map1.swap

||| Perform repeated atomic swaps on one worker thread.
private
swapWorker : Map1 World Nat Nat -> Map1 World Nat Nat -> IO ()
swapWorker a b = runIO (forN ITER $ swapOnce a b)

||| Read two values from a single atomic store snapshot.
private
swapInvariant : Map1 World Nat Nat -> Map1 World Nat Nat -> IO Bool
swapInvariant (MkMap1 (MkMapStore1 ref) i) (MkMap1 _ j) = do
  maps <- runIO (read1 ref)
  let a = Data.SortedMap.lookup i maps >>= Data.Map.lookup 0
      b = Data.SortedMap.lookup j maps >>= Data.Map.lookup 0
  pure ((a == Just 1 && b == Just 2) ||
        (a == Just 2 && b == Just 1))

||| Observe snapshots while workers repeatedly swap two maps.
private
watchSwaps :  Map1 World Nat Nat
           -> Map1 World Nat Nat
           -> Ref World Bool
           -> Nat
           -> IO ()
watchSwaps _ _ _ 0 = pure ()
watchSwaps a b flag (S k) = do
  valid <- swapInvariant a b
  if valid
     then watchSwaps a b flag k
     else runIO (casswap1 flag False)

||| Verify that swaps cannot expose half-committed states.
private
checkSwaps : IO ()
checkSwaps = do
  store <- the (IO (MapStore1 World Nat Nat)) $
             runIO Data.Map1.newStore
  a <- runIO (Data.Map1.singleton 0 1 store)
  b <- runIO (Data.Map1.singleton 0 2 store)
  valid <- runIO (ref1 True)
  observer <- fork $ watchSwaps a b valid (ITER * THREADS)
  ts <- sequence $ V.replicate THREADS (fork $ swapWorker a b)
  traverse_ (\t => threadWait t) ts
  threadWait observer
  good <- runIO (read1 valid)
  final <- swapInvariant a b
  when (not (good && final)) $
    assert_total $ idris_crash "Concurrent.Map1.checkSwaps: non-atomic swap"

--------------------------------------------------------------------------------
--          Main
--------------------------------------------------------------------------------

||| Run concurrent increment and atomic-swap regression tests.
export
main : IO ()
main = do
  checkIncrements
  checkSwaps
