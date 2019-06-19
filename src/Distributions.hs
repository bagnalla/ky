module Distributions where

import Data.Ratio

import Tree
import Util

-- Tree that generates the uniform distribution cotree over a given
-- list (assumed to not contain duplicates).
uniform :: Eq a => Int -> [a] -> Tree a
uniform lbl dom =
  set_label lbl $ canon $ go $
  -- canon $ go $
  (Leaf <$> dom) ++ (Hole lbl <$ [0 .. nextPow2 n - n - 1])
  where
    n = length dom
    go :: [Tree a] -> Tree a
    go [] = Hole n -- Shouldn't happen.
    go [x] = x
    go xs = let m = length xs `div` 2 in
              Split Nothing (go $ take m xs) (go $ drop m xs)

reduce_rational :: Rational -> Rational
reduce_rational r = (n `div` c) % (d `div` c)
  where
    n = numerator r
    d = denominator r
    c = gcd n d

bernoulli :: Int -> Rational -> Tree Bool
bernoulli lbl r =
  uniform lbl $ (True <$ [0..n-1]) ++ (False <$ [0..d-n-1])
  where
    n = numerator $ reduce_rational r
    d = denominator $ reduce_rational r

fair_coin :: Int -> Tree Bool
fair_coin = flip bernoulli $ 1/2
