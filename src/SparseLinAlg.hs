module SparseLinAlg (solve_tree) where

import Data.Bifunctor (second)
import Data.Maybe (fromJust)
import Data.Sparse.SpMatrix
import Data.Sparse.SpVector
import Numeric.LinearAlgebra.Sparse
import System.IO.Unsafe (unsafePerformIO)

import LinEq
import Tree
import Util (debug)

-- Here our equations have a slightly different form, where the LHS is
-- a linear combination of the variables and the RHS is a single
-- rational value. E.g., 1x - 1/2y = 1/2.
type MatTerm = (Coeff, Var)
type MatEq = ([MatTerm], Rational)

mateq_of_equation :: Equation -> MatEq
mateq_of_equation (Equation (x, tms)) =
  case remove_term Nothing $ combine_terms tms of
    Just (c, tms') -> (second fromJust <$> tms', c)
    Nothing -> (second fromJust <$> tms, 0)

constraint_matrix :: [MatEq] -> SpMatrix Rational
constraint_matrix eqs = fromListSM (n, n) $ concat $ f <$> zip [0..] eqs
  where
    n = length eqs

    f :: (Int, MatEq) -> [(Int, Int, Rational)]
    f (x, (tms, _)) = g x <$> tms

    g :: Int -> MatTerm -> (Int, Int, Rational)
    g x (c, y) = (x, y, c)

tree_constraint_matrix :: Tree Bool -> SpMatrix Double
tree_constraint_matrix =
  fmap fromRational . constraint_matrix . map mateq_of_equation .
  equations_of_ltree . ltree_of_tree

solve_matrix :: SpMatrix Double -> IO (SpVector Double)
solve_matrix mat =
  mat <\> (fromListDenseSV n $ fromIntegral <$> [0..n])
  where
    n = nrows mat

solve_tree :: Tree Bool -> IO (SpVector Double)
solve_tree = solve_matrix . tree_constraint_matrix

infer_gmres :: Tree Bool -> Maybe Rational
infer_gmres t =
  toRational <$>
  (lookupSV 0 $ unsafePerformIO $ solve_matrix $ tree_constraint_matrix t)
