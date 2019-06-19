{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}

module Cotree where

import Data.List (sortBy)
import Data.Maybe (fromMaybe)

import Datatypes
import ListTree
import Nat
import Sexp
import Tree
import Util

-- | Greatest fixed point / final TreeF-coalgebra
type Cotree a = Fix (TreeF a)

instance Show a => Show (Cotree a) where
  show (Fix t) = "(" ++ show t ++ ")"

instance Show a => ToSexp (Cotree a) where
  toSexp = cata alg
    where
      alg (LeafF x) = show x
      alg (SplitF s1 s2) = "(" ++ s1 ++ " " ++ s2 ++ ")"
      alg NeverF = "Never"

mkLeaf :: a -> Cotree a
mkLeaf = Fix . LeafF

mkSplit :: Cotree a -> Cotree a -> Cotree a
mkSplit t1 t2 = Fix $ SplitF t1 t2

mkNever :: Cotree a
mkNever = Fix NeverF

-- fmap
cotreeMap :: (a -> b) -> Cotree a -> Cotree b
cotreeMap f = cata alg
  where
    alg (LeafF x) = mkLeaf $ f x
    alg (SplitF t1 t2) = mkSplit t1 t2
    alg NeverF = mkNever

-- product_coalg :: TreeCoalgebra a -> TreeCoalgebra b -> TreeCoalgebra (a, b)
-- product_coalg f g t = product_TreeF (f $ fst_tree t) (g $ snd_tree t)

-- -- TODO
-- -- product_coalg :: TreeCoalgebra a -> TreeCoalgebra b -> TreeCoalgebra (a, b)
-- -- product_coalg f g = join_TreeF . (bimap str' str') . str

-- fst_coalg :: TreeCoalgebra (a, b) -> TreeCoalgebra a
-- fst_coalg f = fst_TreeF . f . fmap (,undefined)

-- snd_coalg :: TreeCoalgebra (a, b) -> TreeCoalgebra b
-- snd_coalg f = snd_TreeF . f . fmap (undefined,)

-- -- Lift a tree transformation to a transformation of TreeF-coalgebras.
-- lift_to_coalg :: (Tree a -> Tree a) -> TreeCoalgebra a -> TreeCoalgebra a
-- lift_to_coalg f g = unfold . f . fold . g

-- view_coalg :: TreeCoalgebra a -> Tree a
-- view_coalg f = fold $ f $ Hole 0

-- canon_coalg :: (Ord a, Show a) => TreeCoalgebra a -> TreeCoalgebra a
-- canon_coalg = lift_to_coalg canon

subtree_map :: [Tree a] -> Int -> Tree a
subtree_map [] n = error $ "subtree_map: index " ++ show n ++ " not found"
subtree_map (t@(Split (Just n) _ _):ts) m = if n == m then t
                                            else subtree_map ts m
subtree_map (_:ts) n = subtree_map ts n

phi :: Tree a -> TreeCoalgebra a
phi = go . subtree_map . labelled_subtrees
  where
    go :: (Int -> Tree a) -> TreeCoalgebra a
    go f (Hole n) = unfold $ f n
    go _ t = unfold t

-- -- generate :: TreeCoalgebra a -> Cotree a
-- -- generate coalg = ana coalg Hole

generate :: Tree a -> Cotree a
-- generate t = ana (phi t) (Hole 0)
generate t = ana (phi t) (Hole $ label_of t)

-- prefixAlg :: NatAlgebra (Cotree a -> Tree a)
-- prefixAlg O _ = Hole
-- prefixAlg (S f)(Fix (SplitF t1 t2)) = Split (f t1) (f t2)
-- prefixAlg (S f)(Fix (LeafF x)) = Leaf x
-- prefixAlg _ (Fix NeverF) = Hole

-- -- First build up the nat from an int, then collapse it to build the
-- -- prefix function.
-- prefix :: Int -> Cotree a -> Tree a
-- prefix = hylo prefixAlg natOfIntCoalg
