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

-- Define zippers over cotrees.
data Walk a = L (Cotree a) | R (Cotree a)
type Cozipper a = (Cotree a, [Walk a])

zipLeft :: Cozipper a -> Cozipper a
zipLeft (Fix (SplitF s1 s2), ws) = (s1, L s2:ws)
zipLeft _ = (mkNever, [])

zipRight :: Cozipper a -> Cozipper a
zipRight (Fix (SplitF s1 s2), ws) = (s2, R s1:ws)
zipRight _ = (mkNever, [])

zipUp :: Cozipper a -> Cozipper a
zipUp (s1, L s2:ws) = (mkSplit s1 s2, ws)
zipUp (s2, R s1:ws) = (mkSplit s1 s2, ws)
zipUp (_, []) = (mkNever, [])

mcmc_sample :: Cozipper a -> Int -> Sampler [a]
mcmc_sample _ 0 = return []
mcmc_sample cz@(ct, ws) n = cata alg ct
    where
        alg (NeverF) = error "mcmc_sample: reached Never"
        alg (LeafF x) = do
            case ws of
                -- Root is leaf => x is only sample.
                [] -> return (replicate n x)
                _ -> do
                    bit <- gets headMaybe
                    case bit of
                        Just b -> do
                            modify tail
                            if b then do
                                s <- mcmc_sample cz (n - 1)
                                return (x:s)
                            else do
                                s <- mcmc_sample (zipUp cz) (n - 1)
                                return (x:s)
                        Nothing -> error "mcmc_sample: out of bits"
        alg (SplitF s1 s2) = do
            case ws of
                [] -> do
                    bit <- gets headMaybe
                    case bit of
                        Just b -> do
                            modify tail
                            if b then
                                mcmc_sample (zipRight cz) n
                            else
                                mcmc_sample (zipLeft cz) n
                        Nothing -> error "mcmc_sample: out of bits"
                _ -> do
                    bit1 <- gets headMaybe
                    case bit1 of
                        Just b -> do
                            modify tail
                            if b then do
                                bit2 <- gets headMaybe
                                case bit2 of
                                    Just b' -> do
                                        modify tail
                                        if b' then
                                            mcmc_sample (zipRight cz) n
                                        else
                                            mcmc_sample (zipLeft cz) n
                                    Nothing -> error "mcmc_sample: out of bits"
                            else
                                mcmc_sample (zipUp cz) n
                        Nothing -> error "mcmc_sample: out of bits"
