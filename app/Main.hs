module Main where

import Control.Monad.State
import Data.Bifunctor (first, second)
import Data.List (nub, sort, (\\))
import Data.Proxy
import System.Environment (getArgs)
import System.Random
import Text.Megaparsec.Error

import Cotree
import Datatypes
import Inference
import Lang (interp', Val(..))
import ListTree
import Parser (parse)
import Sample (eval_sampler, n_samples)
import Sexp
import Tree
import Tycheck (tycheck)
import Untyped
import Util


main :: IO ()
main = do
  args <- getArgs

  let (filename, api_filename) =
        case args of
          (f:a:_) -> (f, Just a)
          f:_   -> (f, Nothing)
          []    -> error "Error: no input file"

  -- Read in source file
  src <- readFile filename

  let com = case parse filename src of
              Left err -> error $ errorBundlePretty err
              Right c -> c

  putStrLn "UNTYPED:"
  putStrLn $ show com

  case tycheck com of
    Left msg -> putStrLn msg
    Right tcom -> do
      putStrLn "TYPED:"
      putStrLn $ show tcom

      let t = interp' tcom
      putStrLn "TREE:"
      putStrLn $ toSexp t
      
      -- For testing bernoulli stuff.
      -- let xt = var_tree t ("x", Proxy :: Proxy Bool)
      -- putStrLn $ toSexp xt
      -- putStrLn "exact Pr(true):"
      -- putStrLn $ show $ probOf (VBool True) xt
      -- putStrLn "exact Pr(false):"
      -- putStrLn $ show $ probOf (VBool False) xt
      
      -- For testing tricky coin example.
      -- let xt = var_tree t ("is_tricky_coin", Proxy :: Proxy Bool)
      -- putStrLn $ toSexp $ canon xt
      -- putStrLn "exact Pr(true):"
      -- putStrLn $ show $ probOf (VBool True) xt
      -- putStrLn "exact Pr(false):"
      -- putStrLn $ show $ probOf (VBool False) xt

      -- Generate the cotree.
      let ct = generate t

      -- Sample it.
      g <- newStdGen
      let bits = randoms g :: [Bool]
      let samples = eval_sampler (n_samples ct 10000) bits

      -- Plot histogram.
      let hist = generate_histogram samples
      putStrLn "HISTOGRAM:"
      putStrLn $ show hist

      -- Compute probability mass function.
      let pmf = histogram_pmf hist
      putStrLn "PMF:"
      putStrLn $ show pmf
