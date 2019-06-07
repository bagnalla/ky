module Distributions where

import Tree
import Util

-- -- Tree that generates the uniform distribution cotree on [0, n).
-- uniform :: Int -> Tree Int
-- uniform n = go $ (Leaf <$> [0..n-1]) ++ (Hole <$ [0 .. nextPow2 n - n - 1])
--   where
--     go :: [Tree Int] -> Tree Int
--     go [] = Hole -- Shouldn't happen.
--     go [x] = x
--     go xs = let m = length xs `div` 2 in Split (go $ take m xs) (go $ drop m xs)

-- Tree that generates the uniform distribution cotree over a given
-- list (assumed to not contain duplicates).
uniform :: [a] -> Tree a
uniform dom =
  let n = length dom in
    go $ (Leaf <$> dom) ++ (Hole <$ [0 .. nextPow2 n - n - 1])
  where
    go :: [Tree a] -> Tree a
    go [] = Hole -- Shouldn't happen.
    go [x] = x
    go xs = let m = length xs `div` 2 in Split (go $ take m xs) (go $ drop m xs)

bernoulli :: Rational -> Tree Bool
bernoulli = undefined -- TODO

fair_coin :: Tree Bool
fair_coin = bernoulli $ 1/2
