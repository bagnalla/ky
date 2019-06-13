module Distributions where

import Data.Ratio

import Tree
import Util

-- Tree that generates the uniform distribution cotree over a given
-- list (assumed to not contain duplicates).
uniform :: Eq a => [a] -> Tree a
uniform dom =
  canon $ go $ (Leaf <$> dom) ++ (Hole <$ [0 .. nextPow2 n - n - 1])
  where
    n = length dom
    go :: [Tree a] -> Tree a
    go [] = Hole -- Shouldn't happen.
    go [x] = x
    go xs = let m = length xs `div` 2 in
              Split (go $ take m xs) (go $ drop m xs)

reduce_rational :: Rational -> Rational
reduce_rational r = (n `div` c) % (d `div` c)
  where
    n = numerator r
    d = denominator r
    c = gcd n d

bernoulli :: Rational -> Tree Bool
bernoulli r =
  uniform $ (True <$ [0..n-1]) ++ (False <$ [0..d-n-1])
  where
    n = numerator $ reduce_rational r
    d = denominator $ reduce_rational r

fair_coin :: Tree Bool
fair_coin = bernoulli $ 1/2
