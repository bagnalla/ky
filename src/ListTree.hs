module ListTree where

import Data.Bifunctor (second)
import Data.List (nub, sort)
import Sexp
import Tree
import Util

-- List form of trees.
type TreeL a = [[Tree a]]

-- List form of a tree.
to_list :: Tree a -> [[Tree a]]
to_list t = terminals_at_depth t <$> [0 .. depth t]

-- -- TODO: test this (generating trees from list representation).
-- list_coalg :: Coalgebra (TreeF a) [[a]]
-- list_coalg ([x]:_) = LeafF x
-- list_coalg ([]:l) =
--   let (left, right) = split_lists l in
--     SplitF left right
-- list_coalg [] = NeverF -- error?
-- list_coalg _ = error ""

-- Bottom-up algorithm for finite trees only
from_list2 :: [[Tree a]] -> Tree a
from_list2 = head . go
  where
    go :: [[Tree a]] -> [Tree a]
    go [] = error "from_list2 go"
    go (xs:[]) = xs
    go (xs:l) = xs ++ f (go l)
    f :: [Tree a] -> [Tree a]
    f [] = []
    f (x:y:zs) = Split x y : f zs
    f _ = error "from_list2 f"

split_lists :: [[a]] -> ([[a]], [[a]])
split_lists = bimap' f . go 1
  where
    go :: Int -> [[a]] -> ([[a]], [[a]])
    go _ [] = ([], [])
    go n (l:ls) =
      let (left, right) = go (2*n) ls in
        (take n l : left, drop n l : right)
    f :: [[a]] -> [[a]]
    f [] = []
    f [x,[]] = [x]
    f (x:xs) = x : f xs

-- from_list :: [[Tree a]] -> Tree a
-- from_list ([x]:l) = x
-- from_list ([]:l) =
--   let (left, right) = split_lists l in
--     Split (from_list left) (from_list right)
-- from_list [] = Hole -- error?
-- from_list _ = error "from_list"

-- TODO: fix..
from_list :: Show a => [[Tree a]] -> Tree a
from_list ([x]:l) = x
from_list ([]:[]:l) =
  let (left, right) = split_lists ([]:l) in
    Split (from_list left) (from_list right)
from_list [[], [x]] = x
from_list ([]:(x:xs):l) = Split x (from_list (xs:l))
from_list [] = Hole -- error?
from_list l = error $ "from_list: unexpected: " ++ show l

remove :: Eq a => a -> [a] -> [a]
remove _ [] = []
remove x (y:ys) = (if x == y then [] else [x]) ++ remove x ys

nodups :: Eq a => [a] -> Bool
nodups l = l == nub l

canon_list :: Eq a => [[a]] -> [[a]]
canon_list = reverse . go [] . reverse
  where
    go :: Eq a => [a] -> [[a]] -> [[a]]
    go xs [] = if null xs then [] else [xs]
    go xs (l:ls) =
      let (l', xs') = f [] (xs ++ l) in
        l' : go xs' ls
    f :: Eq a => [a] -> [a] -> ([a], [a])
    f seen [] = (seen, [])
    f seen (x:xs) =
      if x `elem` seen then
        second (x:) $ f (remove x seen) xs
      else
        f (x:seen) xs

is_canon_list :: Eq a => [[a]] -> Bool
is_canon_list = all nodups

has_hole_list :: Eq a => [[Tree a]] -> Bool
has_hole_list = any (elem Hole)

depth_list :: [[Tree a]] -> Int
depth_list = length

hole_depth_list :: Eq a => [[Tree a]] -> Int
hole_depth_list [] = 100000000
hole_depth_list (l:ls) =
  if Hole `elem` l then 0 else 1 + hole_depth_list ls

expand_list :: [[Tree a]] -> [[Tree a]]
expand_list = undefined

cocanon_list :: (Eq a, Show a) => [[Tree a]] -> (Int, [[Tree a]])
cocanon_list = go 1
  where
    go :: (Eq a, Show a) => Int -> [[Tree a]] -> (Int, [[Tree a]])
    go n t =
      debug "canoning..." $
      let t' = canon_list t in
        debug "canoned" $
        if has_hole_list t' then
          debug ("t': " ++ toSexp t') $
          debug ("depth: " ++ show (depth_list t')) $
          debug ("hole_depth: " ++ show (hole_depth_list t')) $
          let t'' = nTimes (depth_list t' - hole_depth_list t') expand_list t' in
            debug ("t'': " ++ toSexp t'') $
            if is_canon_list t'' then
              debug "canon" (n, t') else
              debug "not canon" $
              go (n+1) t''
        else
          (n, t')

sort_list :: Ord a => [[a]] -> [[a]]
sort_list l = map sort l
