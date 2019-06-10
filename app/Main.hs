module Main where

import Control.Monad.State
import Data.Bifunctor (first, second)
import System.Environment (getArgs)
import System.Random
import Text.Megaparsec.Error

import Cotree
import Datatypes
import Lang (interp')
import ListTree
import Parser (parse)
import Sexp
import Tree
import Tycheck (tycheck)
import Untyped

-- Fair coin coalgebra.
t1_coalg :: TreeCoalgebra Int
t1_coalg = ϕ $ Split (Leaf 0) (Leaf 1)

-- Fair coin tree.
t1 :: Cotree Int
t1 = generate t1_coalg

-- (2/3, 1/3) coalgebra.
t2_coalg :: TreeCoalgebra Int
t2_coalg = ϕ $ Split (Leaf 0) (Split (Leaf 1) Hole)

-- (2/3, 1/3) infinite KY tree.
t2 :: Cotree Int
t2 = generate t2_coalg

t3_coalg :: TreeCoalgebra (Int, Int)
t3_coalg = product_coalg t1_coalg t2_coalg

t3 = generate t3_coalg

t1'_coalg :: TreeCoalgebra Int
t1'_coalg = fst_coalg t3_coalg

t2'_coalg :: TreeCoalgebra Int
t2'_coalg = snd_coalg t3_coalg

t1' :: Cotree Int
t1' = generate t1'_coalg

t2' :: Cotree Int
t2' = generate t2'_coalg

-- Non canonical tree
ex1 :: Tree Int
ex1 = Split
      (Split Hole (Split (Leaf 1) (Split (Leaf 1) (Leaf 2))))
      (Split (Leaf 1) (Split (Leaf 1) (Leaf 2)))
      
ex1' :: Tree Int
ex1' = group_dupes ex1

ex1'' :: Tree Int
ex1'' = reduce ex1'

ex1''' :: Tree Int
ex1''' = group_dupes ex1''

ex1'''' :: Tree Int
ex1'''' = reduce ex1'''

ex1_canon :: Tree Int
ex1_canon = canon ex1


sample_space_size :: Int
sample_space_size = 2

gen_random_tree :: State (Bool, [Int]) (Tree Int)
gen_random_tree = do
  (hole_already_exists, a) <- gets $ second head
  modify $ second tail
  if hole_already_exists then
    case a `mod` 3 of
      n | n < 2 -> do
            (_, b) <- gets $ second $ (`mod` sample_space_size) . head
            modify $ second tail
            return $ Leaf b
      _ -> do
        t1 <- gen_random_tree
        t2 <- gen_random_tree
        return $ Split t1 t2
    else
    case a `mod` 3 of
      0 -> do
        (_, b) <- gets $ second $ (`mod` sample_space_size) . head
        modify $ second tail
        return $ Leaf b
      1 -> do
        t1 <- gen_random_tree
        t2 <- gen_random_tree
        return $ Split t1 t2
      _ -> do
        modify $ first $ const True
        return Hole

gen_random_trees :: Int -> State (Bool, [Int]) [Tree Int]
gen_random_trees n = mapM (\_ -> do
                              t <- gen_random_tree
                              modify $ first $ const False
                              return t) [0..n-1]

-- main :: IO ()
-- main = do
--   -- g <- newStdGen
--   -- let ints = abs <$> randoms g :: [Int]
--   -- let ts = canon <$> evalState (gen_random_trees 1) (False, ints)
--   -- let ls = to_list <$> ts
--   -- let ts' = canon . from_list <$> ls
--   -- let eqs = uncurry (==) <$> zip ts ts'
--   -- let xs = filter (not . fst) $ zip eqs ts
--   -- putStrLn $ show ts
--   -- putStrLn $ show xs
  
--   -- let t = evalState gen_random_tree (False, ints)
--   -- putStrLn $ show t

--   -- let t = canon $ Split (Split Hole (Split (Leaf 0) (Leaf 1))) (Leaf 0)
--   -- let l = to_list t
--   -- let t' = canon $ from_list l
--   -- putStrLn $ toSexp t
--   -- putStrLn $ show l
--   -- -- putStrLn $ show $ split_lists l
--   -- -- putStrLn $ show $ split_lists $ tail l
--   -- putStrLn $ toSexp t'

--   let t = canon $ Split (Leaf 1) (Split (Leaf 0) (Split (Leaf 1) (Split (Split Hole (Split (Leaf 0) (Leaf 1))) (Split (Leaf 1) (Leaf 0)))))
--   let l = to_list t
--   let t' = from_list l
--   putStrLn $ toSexp t
--   putStrLn $ show l
--   putStrLn $ toSexp t'


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
      putStrLn $ show t
