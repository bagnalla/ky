module Main where

import Data.Proxy
import System.Environment (getArgs)

import Inference
import IORepr
import Lang (Type(..), Val(..), primitives, initEnv, interp)
import TreeRepr
import Sexp
import Tree
import Tycheck (SomeMG(..), load_repr)

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

  let n = 10000

  -- Load IO representation of the program.
  case load_repr (Proxy :: Proxy IO) filename src of
    Left msg -> putStrLn msg
    Right (SomeMG g) -> do
      -- Do stuff with it (not much to do).
      putStrLn "IO SAMPLING INFERENCE:"
      finite_pmf <- sample_infer g n
      putStrLn $ show finite_pmf

  -- Load tree representation of the program.
  case load_repr (Proxy :: Proxy Tree) filename src of
    Left msg -> putStrLn msg
    Right (SomeMG t) -> do
      -- Do stuff with it (more to do).
      putStrLn "TREE:"
      putStrLn $ toSexp $ reorder t
      putStrLn $ "size: " ++ (show $ tree_size t)

      putStrLn "TREE SAMPLING INFERENCE:"
      finite_pmf <- sample_infer t n
      putStrLn $ show finite_pmf
