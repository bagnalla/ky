{-# LANGUAGE DeriveFunctor #-}

module Nat where

import Datatypes

data NatF a =
  O
  | S a
  deriving (Functor, Show)

type Nat = Fix NatF
type NatAlgebra a = Algebra NatF a
type NatCoalgebra a = Coalgebra NatF a

natOfIntCoalg :: NatCoalgebra Int
natOfIntCoalg n | n <= 0 = O
natOfIntCoalg n = S (n-1)

natOfInt :: Int -> Nat
natOfInt = ana natOfIntCoalg

