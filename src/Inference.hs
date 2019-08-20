{-# LANGUAGE GADTs, RankNTypes, StandaloneDeriving #-}
module Inference
  -- (counts_pmf, generate_histogram, histogram_pmf, Hist(..), Pmf(..))
  (sample_infer, mk_pmf)
where

import Control.Monad
import Data.Bifunctor (bimap, second)
import Data.List (sum)
import Data.Maybe (fromMaybe)
import Data.Typeable

import Classes
import Lang
import Tree
import Util (counts, debug)

-- | Any g with a Sample instance admits sampling based inference.

sample_infer :: (Sample g, Eq a, Show a, Fractional b) =>
                g a -> Int -> IO [(a, b)]
sample_infer x n = do
  samples <- replicateM n $ sample x
  let cnts = counts samples
  return $ counts_pmf cnts

counts_pmf :: Fractional b => [(a, Int)] -> [(a, b)]
counts_pmf cnts =
  second ((/ c) . fromIntegral) <$> cnts
  where
    c = fromIntegral $ sum $ snd <$> cnts

mk_pmf :: (Eq a, Num b) => [(a, b)] -> a -> b
mk_pmf l x = fromMaybe 0 $ lookup x l


-- -- | Histogram generation from repeated sampling, and probability mass
-- -- functions from normalized histograms.

-- incr_count :: (Typeable m, Typeable g, Show a, Typeable a) =>
--               Val m g a -> [(SomeVal m g , Int)] -> [(SomeVal m g, Int)]
-- incr_count v [] = [(SomeVal v, 1)]
-- incr_count v ((SomeVal v', count) : rest) =
--   case cast v of
--     Just v'' -> if v' == v'' then
--                   (SomeVal v', count + 1) : rest
--                 else
--                   (SomeVal v', count) : incr_count v rest
--     Nothing ->
--       (SomeVal v', count) : incr_count v rest

-- type Hist m g = [(String, [(SomeVal m g, Int)])]
-- -- The type of probability mass functions over program states.
-- type Pmf m g = [(String, [(SomeVal m g, Double)])]


-- upd_hist :: (Typeable m, Typeable g, Show a, Typeable a) =>
--             Name a -> Val m g a -> Hist m g -> Hist m g
-- upd_hist (x, _) v [] = [(x, [(SomeVal v, 1)])]
-- upd_hist (x, proxy) v ((y, counts) : rest) =
--   if x == y then
--     (y, incr_count v counts) : rest
--   else
--     (y, counts) : upd_hist (x, proxy) v rest

-- -- NOTE: this assumes the state has no duplicate entries (no
-- -- shadowing).
-- upd_hist_st :: St m g -> Hist m g -> Hist m g
-- upd_hist_st [] hist = hist
-- upd_hist_st (SomeNameVal x v : st) hist =
--   upd_hist_st st $ upd_hist x v hist

-- generate_histogram :: [St m g] -> Hist m g
-- generate_histogram [] = []
-- generate_histogram (st : sts) =
--   upd_hist_st st $ generate_histogram sts

-- histogram_pmf :: Hist m g -> Pmf m g
-- histogram_pmf [] = []
-- histogram_pmf ((x, counts) : rest) =
--   let c = fromIntegral $ sum $ snd <$> counts
--       normalized = bimap id ((/ c) . fromIntegral) <$> counts
--       rest' = histogram_pmf rest
--   in
--     (x, normalized) : rest'


-- -- | Sampling based approximate inference for trees of arbitrary type.

-- -- counts_pmf :: [(a, Int)] -> [(a, Double)]
-- -- counts_pmf cnts =
-- --   second ((/ c) . fromIntegral) <$> cnts
-- --   where
-- --     c = fromIntegral $ sum $ snd <$> cnts


-- -- | Exact calculation of probabilities.

-- -- | NOTE: this probably doesn't work anymore now that trees can have
-- -- labelled holes.

-- -- subprobability :: Fractional b => (a -> Bool) -> Tree a -> b
-- -- subprobability = go 1
-- --   where
-- --     go :: Fractional b => b -> (a -> Bool) -> Tree a -> b
-- --     go p pred (Leaf x) = if pred x then p else 0
-- --     go p pred (Split t1 t2) = go (p/2) pred t1 + go (p/2) pred t2
-- --     go _ _ Hole = 0

-- -- total_mass :: Fractional b => Tree a -> b
-- -- total_mass = subprobability $ const True

-- -- probability :: Fractional b => (a -> Bool) -> Tree a -> b
-- -- probability pred t = subprobability pred t / total_mass t

-- -- probOf :: (Eq a, Fractional b) => a -> Tree a -> b
-- -- probOf x = probability (== x)

-- -- support :: Tree a -> [a]
-- -- support = foldMap (:[])

-- -- expected_value :: (Eq a, Fractional b) => (a -> b) -> Tree a -> b
-- -- expected_value f t =
-- --   sum ((\x -> f x * probOf x t) <$> supp) / fromIntegral (length supp)
-- --   where
-- --     supp = support t

-- -- exact_pmf :: (Eq a, Fractional b) => Tree a -> a -> b
-- -- exact_pmf = flip probOf


-- -- -- | Specialization to trees of states.

-- -- var_tree :: Typeable a => Tree St -> Name a -> Tree (Val a)
-- -- var_tree t x = t >>= \st -> fromMaybe Hole (Leaf <$> get x st)

-- -- var_pmf :: (Typeable a, Fractional b) => Tree St -> Name a -> Val a -> b
-- -- var_pmf t x v = probOf v $ var_tree t x
