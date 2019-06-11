{-# LANGUAGE GADTs, RankNTypes, StandaloneDeriving #-}
module Inference (generate_histogram, histogram_pmf, Hist(..), Pmf(..)) where

import Data.Bifunctor (bimap)
import Data.List (sum)
import Data.Typeable
import Lang


-- | Histogram generation from repeated sampling, and probability mass
-- functions from normalized histograms.

data SomeVal where
  SomeVal :: forall a. (Show a, Typeable a) => Val a -> SomeVal
deriving instance Show SomeVal

incr_count :: (Show a, Typeable a) => Val a ->
              [(SomeVal, Int)] -> [(SomeVal, Int)]
incr_count v [] = [(SomeVal v, 1)]
incr_count v ((SomeVal v', count) : rest) =
  case cast v of
    Just v'' -> if v' == v'' then
                  (SomeVal v', count + 1) : rest
                else
                  (SomeVal v', count) : incr_count v rest
    Nothing ->
      (SomeVal v', count) : incr_count v rest

type Hist = [(String, [(SomeVal, Int)])]
type Pmf = [(String, [(SomeVal, Float)])]

upd_hist :: (Show a, Typeable a) => Name a -> Val a -> Hist -> Hist
upd_hist (x, _) v [] = [(x, [(SomeVal v, 1)])]
upd_hist (x, proxy) v ((y, counts) : rest) =
  if x == y then
    (y, incr_count v counts) : rest
  else
    (y, counts) : upd_hist (x, proxy) v rest

upd_hist_st :: St -> Hist -> Hist
upd_hist_st [] hist = hist
upd_hist_st (StPkg x v : st) hist =
  upd_hist_st st $ upd_hist x v hist

generate_histogram :: [St] -> Hist
generate_histogram [] = []
generate_histogram (st : sts) =
  upd_hist_st st $ generate_histogram sts

histogram_pmf :: Hist -> Pmf
histogram_pmf [] = []
histogram_pmf ((x, counts) : rest) =
  let c = fromIntegral $ sum $ snd <$> counts
      normalized = bimap id ((/ c) . fromIntegral) <$> counts
      rest' = histogram_pmf rest
  in
    (x, normalized) : rest'
    
