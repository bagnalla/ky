module Sample where

import Control.Monad.State

import Cotree
import Datatypes
import Tree
import Util

type Bits = [Bool]
type Sampler = State Bits

sample :: Cotree a -> Sampler a
sample = cata alg
  where
    alg :: TreeAlgebra a (Sampler a)
    alg NeverF = error "sample: reached Never"
    alg (LeafF x) = return x
    alg (SplitF s1 s2) = do
      bit <- gets headMaybe
      case bit of
        Just b -> do
          modify tail
          if b then s1 else s2
        Nothing -> error "sample: out of bits"

run_sampler :: Sampler a -> Bits -> (a, Bits)
run_sampler = runState

eval_sampler :: Sampler a -> Bits -> a
eval_sampler = evalState

exec_sampler :: Sampler a -> Bits -> Bits
exec_sampler = execState

sample_tree :: Cotree a -> Bits -> (a, Bits)
sample_tree = run_sampler . sample

n_samples :: Cotree a -> Int -> Sampler [a]
n_samples t n = mapM (const $ sample t) [0..n]
