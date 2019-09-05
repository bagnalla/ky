{-# LANGUAGE GADTs #-}

module Main where

import           Data.Proxy
import           Data.Typeable
import           System.Environment (getArgs)
-- import qualified Z3.Base
-- import qualified Z3.Monad as Z3

import Classes
import Inference
import IORepr
import Lang (Exp(..), Type(..), Val(..), primitives, initEnv, interp)
import TreeRepr
import Sexp
import SparseLinAlg (solve_tree)
import Tree
import Tycheck (SomeG(..), load_repr)
-- import Z3Infer (z3infer)

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

  -- -- Load IO representation of the program.
  -- case load_repr (Proxy :: Proxy IO) filename src of
  --   Left msg -> putStrLn msg
  --   Right (SomeG _ g) -> do
  --     -- Do stuff with it (not much to do).
  --     putStrLn "IO SAMPLING INFERENCE:"
  --     finite_pmf <- sample_infer g n
  --     putStrLn $ show finite_pmf

  -- Load tree representation of the program.
  case load_repr (Proxy :: Proxy Tree) filename src of
    Left msg -> putStrLn msg
    Right (SomeG ty t) -> do
      -- Do stuff with it (more to do).
      putStrLn "TREE:"
      putStrLn $ toSexp $ reorder t
      putStrLn $ "size: " ++ (show $ tree_size t)

      -- putStrLn "TREE SAMPLING INFERENCE:"
      -- finite_pmf <- sample_infer t n
      -- putStrLn $ show finite_pmf

      -- let t' = canon t
      -- putStrLn "REDUCED TREE:"
      -- putStrLn $ toSexp t'
      -- putStrLn $ "size: " ++ (show $ tree_size t')

      case ty of
        TExp TBool -> do
          putStrLn $ show $ (infers!!0) t (\(EVal (VBool b)) -> b)
          -- putStrLn $ show $ (infers!!0) t' (\(EVal (VBool b)) -> b)
          -- let tb = (\(EVal (VBool b)) -> b) <$> t
          -- let model = z3infer tb
          -- putStrLn $ show model

          -- let tb = (\(EVal (VBool b)) -> b) <$> t
          -- v <- solve_tree tb
          -- putStrLn $ show v
          
        _ ->
          putStrLn "expected bool tree"

      -- case cast t' of
      --   Just t'' -> putStrLn $ show $ (infers!!0) t'' id
      --   Nothing -> return ()
      -- putStrLn $ show $ (infers!!0) t' (\x -> case cast x of
      --                                           Just (EVal (VBool b)) -> b
      --                                           _ -> error "asd")
