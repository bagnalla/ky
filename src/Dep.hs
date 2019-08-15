{-# LANGUAGE GADTs #-}

-- | Variable dependency analysis.

module Dep (dep_cycle, sample_deps, sample_vars, var_deps) where

import Data.List (intersect, nub, union)
import Data.Maybe (fromJust, fromMaybe)
import Lang
import Symtab (Id(..))
import Util (debug)

-- Compute dependencies of variables in a command (possibly a sequence
-- of commands).
var_deps :: Com a -> [(Id, [Id])]
var_deps = iter_deps . init_deps

upd_deps :: Eq a => a -> ([b] -> [b]) -> [(a, [b])] -> [(a, [b])]
upd_deps x f ((x', y) : entries) =
  if x == x' then
    (x, f y) : entries
  else
    (x', y) : upd_deps x f entries
upd_deps x f [] = [(x, f [])]

-- Merge two sets of dependencies.
union_deps :: [(Id, [Id])] -> [(Id, [Id])] -> [(Id, [Id])]
union_deps deps [] = deps
union_deps deps ((x, ys) : deps') =
  union_deps (upd_deps x (union ys) deps) deps'

-- Initialize with direct dependencies.
init_deps :: Com a -> [(Id, [Id])]
init_deps (Assign (x, _) e) = [(Id x, id_of_name <$> fvs e)]
init_deps (Sample (x, _) e) = [(Id x, id_of_name <$> fvs e)]
init_deps (Seq c1 c2) = union_deps (init_deps c1) (init_deps c2)
init_deps (Ite _ c1 c2) = union_deps (init_deps c1) (init_deps c2)
init_deps (While e c) = init_deps c
init_deps _ = []

-- Compute transitive closure (iterate until fixed point).
iter_deps :: [(Id, [Id])] -> [(Id, [Id])]
iter_deps deps =
  if deps == deps' then deps else iter_deps deps'
  where
    deps' = f deps (fst <$> deps)
    f :: [(Id, [Id])] -> [Id] -> [(Id, [Id])]
    f deps (x:xs) =
      let ys = fromJust $ lookup x deps
          ys_deps = nub $ concat $ fromMaybe [] . flip lookup deps <$> ys
      in
        f (upd_deps x (union ys_deps) deps) xs
    f deps [] = deps


-- Collect variables that are directly assigned random values.
sample_vars :: Com a -> [Id]
sample_vars (Sample (x, _) _) = [Id x]
sample_vars (Seq c1 c2) = union (sample_vars c1) (sample_vars c2)
sample_vars _ = []

-- Given variables that are directly assigned random values together
-- with the set of dependencies, compute the set of variables that
-- transitively depend on randomness.
sample_deps :: [Id] -> [(Id, [Id])] -> [Id]
sample_deps xs ((x, ys) : deps) =
  if x `elem` xs || not (null $ intersect xs ys) then
    x : sample_deps xs deps
  else
    sample_deps xs deps
sample_deps _ [] = []

dep_cycle :: [(Id, [Id])] -> Maybe Id
dep_cycle ((x, ys) : deps) = if x `elem` ys then Just x else dep_cycle deps
dep_cycle [] = Nothing
