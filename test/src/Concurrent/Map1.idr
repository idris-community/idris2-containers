||| Concurrent tests for shared-store linear maps.
module Concurrent.Map1

import Data.Map
import Data.Map1
import Data.Map1.Internal
import Data.Linear.Ref1
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
inc : Map1 s region Nat Nat -> F1' s
inc m t =
  let _ # t := Data.Map1.insertWith (+) 0 1 m t
    in () # t

||| Perform repeated increments on a shared map.
private
incrementWorker : Map1 World region Nat Nat -> IO ()
incrementWorker m = runIO (forN ITER $ inc m)

||| Verify that competing atomic increments do not lose updates.
private
checkIncrements : IO ()
checkIncrements =
  Data.Map1.withStoreIO $ \store => do
    m <- runIO (Data.Map1.singleton 0 0 store)
    ts <- sequence $ V.replicate THREADS (fork $ incrementWorker m)
    traverse_ (\tid => threadWait tid) ts
    result <- runIO (Data.Map1.lookup 0 m)
    when (result /= Just (Just (THREADS * ITER))) $
      assert_total $ idris_crash "Concurrent.Map1: lost atomic increments"

--------------------------------------------------------------------------------
--          Atomic Swap
--------------------------------------------------------------------------------

||| Swap two maps in the same shared store.
private
swapOnce : Map1 s region Nat Nat -> Map1 s region Nat Nat -> F1' s
swapOnce a b t =
  let _ # t := Data.Map1.swap a b t
    in () # t

||| Perform repeated atomic swaps on one worker thread.
private
swapWorker : Map1 World region Nat Nat -> Map1 World region Nat Nat -> IO ()
swapWorker a b = runIO (forN ITER $ swapOnce a b)

||| Read two values from a single atomic store snapshot.
private
swapInvariant : Map1 World region Nat Nat -> Map1 World region Nat Nat -> IO Bool
swapInvariant a b = do
  result <- runIO $ Data.Map1.Internal.queryMaps
    (\first, second =>
      let x = Data.Map.lookup 0 first
          y = Data.Map.lookup 0 second
       in (x == Just 1 && y == Just 2) ||
          (x == Just 2 && y == Just 1)) a b
  pure (result == Just True)

||| Observe snapshots while workers repeatedly swap two maps.
private
watchSwaps :  Map1 World region Nat Nat
           -> Map1 World region Nat Nat
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
checkSwaps =
  Data.Map1.withStoreIO $ \store => do
    a <- runIO (Data.Map1.singleton 0 1 store)
    b <- runIO (Data.Map1.singleton 0 2 store)
    valid <- runIO (ref1 True)
    observer <- fork $ watchSwaps a b valid (ITER * THREADS)
    ts <- sequence $ V.replicate THREADS (fork $ swapWorker a b)
    traverse_ (\tid => threadWait tid) ts
    threadWait observer
    good <- runIO (read1 valid)
    final <- swapInvariant a b
    when (not (good && final)) $
      assert_total $ idris_crash "Concurrent.Map1: non-atomic swap"

--------------------------------------------------------------------------------
--          Main
--------------------------------------------------------------------------------

||| Run concurrent increment and atomic-swap regression tests.
export
main : IO ()
main = do
  checkIncrements
  checkSwaps
