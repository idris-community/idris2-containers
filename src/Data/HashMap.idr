module Data.HashMap

import Data.HashMap.Internal.HAMT

import public Data.Hashable

||| A hashmap.
export
data HashMap : (key : Type) -> (val : Type) -> Type where
  Empty : Hashable key => Eq key => HashMap key val
  Trie  : Hashable key => Eq key => HAMT key (const val) -> HashMap key val

export
empty :  Hashable key
      => Eq key
      => HashMap key val
empty =
  Empty

export
lookup :  key
       -> HashMap key val
       -> Maybe val
lookup key Empty       =
  Nothing
lookup key (Trie hamt) =
  let lookup' = lookup (==)
                       key
                       hamt
    in case lookup' of
         Nothing             =>
           Nothing
         Just (_ ** val') =>
           Just val'

export
insert :  key
       -> val
       -> HashMap key val
       -> HashMap key val
insert key val Empty       =
  Trie ( singleton key val
       )
insert key val (Trie hamt) =
  Trie ( insert (==) key val hamt
       )

export
delete :  key
       -> HashMap key val
       -> HashMap key val
delete key Empty       =
  Empty
delete key (Trie hamt) =
  case delete (==) key hamt of
    Nothing    =>
      Empty
    Just hamt' =>
      Trie hamt'

export
foldWithKey :  (f : k -> v -> acc -> acc)
            -> acc
            -> HashMap k v
            -> acc
foldWithKey f z Empty       =
  z
foldWithKey f z (Trie hamt) =
  foldWithKey f z hamt

export
toList :  HashMap k v
       -> List (k, v)
toList hm =
  foldWithKey (\key, val, acc => (key, val) :: acc) [] hm

export
keys :  HashMap k v
     -> List k
keys hm =
  foldWithKey (\key, val, acc => key :: acc) [] hm

export
fromList :  Hashable k
         => Eq k
         => List (k, v)
         -> HashMap k v
fromList lst =
  foldr (\(k, v) => insert k v) empty lst

export
Functor (HashMap key) where
  map f Empty       =
    Empty
  map f (Trie hamt) =
    Trie ( trieMap f hamt
         )

export
Show key => Show val => Show (HashMap key val) where
  show hm = "fromList \{show $ HashMap.toList hm}"
