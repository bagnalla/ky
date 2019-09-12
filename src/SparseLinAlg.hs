module SparseLinAlg (solve_tree) where

import Data.Bifunctor (bimap, second)
import Data.List (sort)
import Data.Maybe (fromJust)
import Data.Sparse.SpMatrix
import Data.Sparse.SpVector
import Numeric.LinearAlgebra.Sparse
import System.IO.Unsafe (unsafePerformIO)

import LinEq
import Sexp
import Tree
import Util (debug, tupleFun)

-- Here our equations have a slightly different form, where the LHS is
-- a linear combination of the variables and the RHS is a single
-- rational value. E.g., 1x - 1/2y = 1/2.
type MatTerm = (Coeff, Var)
type MatEq = ([MatTerm], Rational)

-- mateq_of_equation :: Equation -> MatEq
-- mateq_of_equation (Equation (x, tms)) =
--   case remove_term Nothing $ combine_terms tms of
--     Just (c, tms') -> (second fromJust <$> tms', c)
--     Nothing -> (second fromJust <$> tms, 0)

mateq_of_equation :: Equation -> MatEq
mateq_of_equation (Equation (x, tms)) =
  case remove_term Nothing $ combine_terms tms of
    Just (c, tms') -> ((1, x) : (bimap negate fromJust <$> tms'), c)
    Nothing -> ((1, x) : (bimap negate fromJust <$> tms), 0)

constraint_matrix :: [MatEq] -> SpMatrix Rational
constraint_matrix eqs =
  let l = concat $ f <$> zip [0..] eqs in
    debug ("l: " ++ show ((\(x, y, z) -> (x, y, fromRational z)) <$> l)) $
    fromListSM (n, n) l
  where
    n = length eqs

    f :: (Int, MatEq) -> [(Int, Int, Rational)]
    f (x, (tms, _)) = g x <$> tms

    g :: Int -> MatTerm -> (Int, Int, Rational)
    g x (c, y) = (x, y, c)
    -- g x (c, y) = (y, x, c)

-- tree_constraint_matrix :: Tree Bool -> SpMatrix Double
-- tree_constraint_matrix =
--   fmap fromRational . constraint_matrix . map mateq_of_equation .
--   equations_of_ltree . ltree_of_tree

-- tree_constraint_matrix :: Tree Bool -> SpMatrix Double
-- tree_constraint_matrix =
--   fmap fromRational .
--   constraint_matrix .
--   map (\eq -> let mateq = mateq_of_equation eq in
--                 debug ("eq: " ++ show eq) $
--                 debug ("mateq" ++ show mateq) $
--                 mateq) .
--   equations_of_ltree .
--   ltree_of_tree

matrix_of_mateqs :: [MatEq] -> SpMatrix Double
matrix_of_mateqs = fmap fromRational . constraint_matrix

rhs_of_mateqs :: [MatEq] -> SpVector Double
rhs_of_mateqs eqs = fromListDenseSV n $ fromRational . snd <$> eqs
  where n = length eqs

solve_system_gmres :: SpMatrix Double -> SpVector Double -> IO (SpVector Double)
solve_system_gmres mat rhs =
  debug ("mat: " ++ show mat) $
  debug ("rhs: " ++ show rhs) $
  debug ("dense:") $
  -- let _ = unsafePerformIO $ prd mat in
  -- mat <\> (fromListDenseSV n )
  mat <\> rhs
  where
    n = nrows mat -- should also be the length of the rhs vector

solve_tree :: Tree Bool -> IO (SpVector Double)
-- solve_tree = solve_system_gmres . tree_constraint_matrix
solve_tree t =
  let lt = ltree_of_tree t
      eqs = sort $ equations_of_ltree lt
      mateqs = mateq_of_equation <$> eqs
      -- (mat, rhs) = (matrix_of_mateqs mateqs, rhs_of_mateqs mateqs)
      (mat, rhs) = tupleFun matrix_of_mateqs rhs_of_mateqs mateqs in
    debug ("eqs: " ++ show eqs) $
    debug ("mateqs: " ++ show mateqs) $
    debug ("ltree: " ++ toSexp lt) $ do
    prd mat
    prd rhs
    sol <- solve_system_gmres mat rhs
    prd sol
    return sol

-- infer_gmres :: Tree Bool -> Maybe Rational
-- infer_gmres t =
--   toRational <$>
--   (lookupSV 0 $ unsafePerformIO $ solve_matrix $ tree_constraint_matrix t)

-- [(0,[(0,1.0),(1,-0.5),(4,-0.5)]),
--  (1,[(0,-0.5),(1,1.0),(3,-0.5)]),
--  (2,[(1,-0.5),(3,1.0)]),
--  (3,[(0,-0.5),(2,-0.5),(4,1.0)]),
--  (4,[(2,1.0),(5,-0.5)]),
--  (5,[(0,-0.5),(2,-0.5),(5,1.0)])]
