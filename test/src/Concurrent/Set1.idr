||| Concurrent tests for shared-store linear sets.
module Concurrent.Set1

import Data.Set
import Data.Set1
import Data.Linear.Ref1
import Data.Vect as V
import Data.SortedMap
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
--          Concurrent Insertion
--------------------------------------------------------------------------------

||| Insert a disjoint range of values into a shared set.
private
fill : Set1 s Nat -> Nat -> Nat -> F1' s
fill set offset 0 t = () # t
fill set offset (S k) t =
  let _ # t := Data.Set1.insert (offset + k) set t
    in fill set offset k t

||| Insert a range on one worker thread.
private
insertWorker : Set1 World Nat -> Nat -> IO ()
insertWorker set i = runIO (fill set (i * ITER) ITER)

||| Verify that concurrent, disjoint insertions do not lose elements.
private
checkInserts : IO ()
checkInserts = do
  store <- the (IO (SetStore1 World Nat)) $
             runIO Data.Set1.newStore
  set <- runIO (Data.Set1.empty store)
  t1 <- fork $ insertWorker set 0
  t2 <- fork $ insertWorker set 1
  t3 <- fork $ insertWorker set 2
  t4 <- fork $ insertWorker set 3
  threadWait t1
  threadWait t2
  threadWait t3
  threadWait t4
  xs <- runIO (Data.Set1.toList set)
  when (length xs /= THREADS * ITER) $
    assert_total $ idris_crash "Concurrent.Set1.checkInserts: lost inserted values"

--------------------------------------------------------------------------------
--          Atomic Transfer
--------------------------------------------------------------------------------

||| Attempt to move one element between two sets.
private
move : Set1 s Nat -> Set1 s Nat -> F1' s
move source destination t =
  let _ # t := Data.Set1.transfer 1 source destination t
    in () # t

||| Repeatedly transfer one element in a chosen direction.
private
transferWorker : Set1 World Nat -> Set1 World Nat -> IO ()
transferWorker source destination =
  runIO (forN ITER $ move source destination)

||| Check whether an element belongs to exactly one of two sets.
private
transferInvariant : Set1 World Nat -> Set1 World Nat -> IO Bool
transferInvariant (MkSet1 (MkSetStore1 ref) i) (MkSet1 _ j) = do
  sets <- runIO (read1 ref)
  let a = Data.SortedMap.lookup i sets
      b = Data.SortedMap.lookup j sets
  pure $ case (a, b) of
    (Just xs, Just ys) =>
      Data.Set.member 1 xs /= Data.Set.member 1 ys
    _ =>
      False

||| Watch for an intermediate state that loses or duplicates an item.
private
watchTransfer :  Set1 World Nat
              -> Set1 World Nat
              -> Ref World Bool
              -> Nat
              -> IO ()
watchTransfer _ _ _ 0 = pure ()
watchTransfer a b flag (S k) = do
  valid <- transferInvariant a b
  if valid
     then watchTransfer a b flag k
     else runIO (casswap1 flag False)

||| Verify that competing transfers preserve exclusive membership.
private
checkTransfers : IO ()
checkTransfers = do
  store <- the (IO (SetStore1 World Nat)) $
             runIO Data.Set1.newStore
  a <- runIO (Data.Set1.singleton 1 store)
  b <- runIO (Data.Set1.empty store)
  valid <- runIO (ref1 True)
  observer <- fork $ watchTransfer a b valid (ITER * THREADS)
  t1 <- fork $ transferWorker a b
  t2 <- fork $ transferWorker b a
  t3 <- fork $ transferWorker a b
  t4 <- fork $ transferWorker b a
  threadWait t1
  threadWait t2
  threadWait t3
  threadWait t4
  threadWait observer
  good <- runIO (read1 valid)
  final <- transferInvariant a b
  when (not (good && final)) $
    assert_total $ idris_crash "Concurrent.Set1.checkTransfers: non-atomic transfer"

--------------------------------------------------------------------------------
--          Main
--------------------------------------------------------------------------------

||| Run concurrent insertion and atomic-transfer regression tests.
export
main : IO ()
main = do
  checkInserts
  checkTransfers
