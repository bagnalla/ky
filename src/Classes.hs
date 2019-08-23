{-# LANGUAGE RankNTypes, QuantifiedConstraints #-}

module Classes where

import Data.Typeable

-- EqF is the class of type constructors for which equality instances
-- can be lifted. It's short for "equality functor" although it
-- doesn't necessarily have to be a functor I guess.
class (forall a. Eq a => Eq (g a)) => EqF g where

-- Similar thing for Show.
class (forall a. Show a => Show (g a)) => ShowF g where

-- Any 'g a' can be interpreted as a sampler in the IO monad.
class Sample g where
  sample :: g a -> IO (a)

-- A list of inference methods associated with 'g'. Can be empty. Any
-- representation will have the default sampling based inference
-- method in addition to these.
class Infer g where
  infers :: [g a -> (a -> Bool) -> Float]

-- Bundle everything into a single class.
class (EqF g, Infer g, ShowF g, Sample g, Typeable g) => AllF g where
