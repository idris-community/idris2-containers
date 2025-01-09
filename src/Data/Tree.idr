||| Finite Rose Trees.
module Data.Tree

import Data.List
import Data.String

import Derive.Prelude

%language ElabReflection
%default total

--------------------------------------------------------------------------------
--          Finite Trees
--------------------------------------------------------------------------------

||| A finite rose tree
public export
record Tree (a : Type) where
  constructor T
  value : a
  forest : List (Tree a)

||| A finite forest of trees
public export
Forest : Type -> Type
Forest = List . Tree

%runElab derive "Tree" [Show,Eq]

--------------------------------------------------------------------------------
--          Creating Trees
--------------------------------------------------------------------------------

||| Wrap a single value in a tree
public export
singleton : a -> Tree a
singleton a = T a []

||| Create a regular tree of the given depth, where each branch has
||| `width` children.
public export
replicate : (width : Nat) -> (depth : Nat) -> a -> Tree a
replicate _         0 x = T x []
replicate width (S k) x = T x $ replicate width (replicate width k x)

||| Unfold a tree up to the given depth.
public export
unfold : (depth : Nat) -> (f : s -> (a,List s)) -> s -> Tree a
unfold 0     f s = T (fst $ f s) []
unfold (S k) f s =
  let (a,ss) := f s
   in T a (map (unfold k f) ss)

--------------------------------------------------------------------------------
--          Flattening Trees
--------------------------------------------------------------------------------

zipWithKeep : (a -> a -> a) -> List a -> List a -> List a
zipWithKeep f [] ys = ys
zipWithKeep f xs [] = xs
zipWithKeep f (x :: xs) (y :: ys) = f x y :: zipWithKeep f xs ys

||| Flatten a tree into a list.
public export
flatten : Tree a -> List a
flatten (T v vs) = v :: flattenF vs

  where
    flattenF : Forest a -> List a
    flattenF []        = Nil
    flattenF (x :: xs) = flatten x ++ flattenF xs

||| Convert a tree to a list of lists, so that all values at the same
||| depth appear in the same list.
public export
layers : Tree a -> List (List a)
layers (T v vs) = [v] :: layersF vs

  where
    layersF : Forest a -> List (List a)
    layersF []        = Nil
    layersF (x :: xs) = zipWithKeep (++) (layers x) (layersF xs)

--------------------------------------------------------------------------------
--          Accessing Elements
--------------------------------------------------------------------------------

||| Try to look up a value in the tree by following the given path.
public export
index : List Nat -> Tree a -> Maybe a
index []        x = Just x.value
index (y :: ys) x = ix y x.forest >>= index ys

  where
    ix : Nat -> List b -> Maybe b
    ix _ []            = Nothing
    ix 0     (z :: _)  = Just z
    ix (S k) (_ :: zs) = ix k zs

--------------------------------------------------------------------------------
--          Functor and Monad Implementations
--------------------------------------------------------------------------------

-- All implementations are boilerplaty to satisfy the totality checker.
foldlTree : (a -> e -> a) -> a -> Tree e -> a
foldlTree f acc (T v vs) = foldlF (f acc v) vs

  where
    foldlF : a -> Forest e -> a
    foldlF y []        = y
    foldlF y (x :: xs) = foldlF (foldlTree f y x) xs

foldrTree : (e -> a -> a) -> a -> Tree e -> a
foldrTree f acc (T v vs) = f v (foldrF acc vs)

  where
    foldrF : a -> Forest e -> a
    foldrF y []        = y
    foldrF y (x :: xs) = foldrTree f (foldrF y xs) x

traverseTree : Applicative f => (a -> f b) -> Tree a -> f (Tree b)
traverseTree fun (T v vs) = [| T (fun v) (traverseF vs) |]

  where
    traverseF : Forest a -> f (Forest b)
    traverseF []        = pure []
    traverseF (x :: xs) = [| traverseTree fun x :: traverseF xs |]

mapTree : (a -> b) -> Tree a -> Tree b
mapTree f (T v vs) = T (f v) (mapF vs)

  where
    mapF : Forest a -> Forest b
    mapF []       = []
    mapF (h :: t) = mapTree f h :: mapF t

bindTree : Tree a -> (a -> Tree b) -> Tree b
bindTree (T va tas) f =
  let T vb tbs := f va
   in T vb (tbs ++ bindF tas)

  where
    bindF : Forest a -> Forest b
    bindF []        = []
    bindF (x :: xs) = bindTree x f :: bindF xs

apTree : Tree (a -> b) -> Tree a -> Tree b
apTree tf ta = bindTree tf $ \f => mapTree (apply f) ta

joinTree : Tree (Tree a) -> Tree a
joinTree (T (T va tas) ftas) =
  T va $ tas ++ joinF ftas

  where
    joinF : Forest (Tree a) -> Forest a
    joinF []        = []
    joinF (x :: xs) = joinTree x :: joinF xs

--------------------------------------------------------------------------------
--          Visualizing Trees
--------------------------------------------------------------------------------

||| Pretty print a tree.
|||
||| Unlike `prettyTree`, this has support for multi-line strings and
||| will result in a vertically elongated representation.
export
drawTree : Tree String -> String
drawTree  = unlines . draw

  where
    drawForest : Forest String -> String
    drawForest  = unlines . map drawTree

    draw : Tree String -> List String
    draw (T x ts0) = lines x ++ subTrees ts0

      where
        shift : String -> String -> List String -> List String
        shift first other tails =
          zipWith (++) (first :: replicate (length tails) other) tails

        subTrees : Forest String -> List String
        subTrees []      = []
        subTrees [t]     = "│" :: shift "└╼" "  " (draw t)
        subTrees (t::ts) = "│" :: shift "├╼" "│ " (draw t) ++ subTrees ts

parameters (rev : Bool)

  lst : String
  lst = if rev then "┌─" else "└─"

  children : String -> List (Tree String) -> SnocList String -> SnocList String
  children _   []       ss = ss
  children pre [T l cs] ss =
    let s := pre ++ lst ++ "\{l}"
     in children (pre ++ "  ") cs (ss :< s)

  children pre (T l cs :: xs) ss =
    let s   := pre ++ "├─\{l}"
        ss2 := children (pre ++ "│ ") cs (ss :< s)
     in children pre xs ss2

  ||| Pretty print a tree.
  |||
  ||| Unlike `drawTree`, this does not work with multi-line node labels,
  ||| but will otherwise result in a vertically more compact representation.
  ||| In addition, it is possible to print the tree "upside-down" by
  ||| setting `rev` to `True`.
  export
  prettyTree : Tree String -> String
  prettyTree (T l cs) =
    let ss := children "" cs [<"\{l}"] <>> []
     in if rev then unlines (reverse ss) else unlines ss

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

public export %inline
Foldable Tree where
  foldl  = foldlTree
  foldr  = foldrTree
  null _ = False

public export %inline
Functor Tree where
  map = mapTree

public export %inline
Applicative Tree where
  pure a = T a Nil
  (<*>)  = apTree

public export %inline
Monad Tree where
  (>>=) = bindTree
  join  = joinTree

public export %inline
Traversable Tree where
  traverse = traverseTree
