{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving, DeriveAnyClass #-}

module TreeRepr () where

import Data.Proxy

import           Classes
import           Distributions
import           TreeInterp
import           Lang hiding (Env, Exp, SomeVal, SomeTypeVal, Val)
import qualified Lang as L (Env, Exp, SomeVal, SomeTypeVal(..), Val)
import           Sample
import           Tree

type Env         = L.Env         InterpM Tree
type Exp         = L.Exp         InterpM Tree
type SomeVal     = L.SomeVal     InterpM Tree
type SomeTypeVal = L.SomeTypeVal InterpM Tree
type Val         = L.Val         InterpM Tree

-- | The list of predefined primitives. Used by the typechecker (name
-- and type information) and interpreter (name and value). For now
-- primitives can't be polymorphic, so the uniform distribution must
-- be built directly into the language rather than being a primitive
-- here.
prims :: [(String, SomeTypeVal)]
prims =
  [
    ("bernoulli", L.SomeTypeVal (TArrow TRational (TDist TBool)) bernoulli_prim)
    -- Add more here
  ]

bernoulli_prim :: Val (Rational -> Tree Bool)
bernoulli_prim = VPrim f
  where
    f :: Val Rational -> InterpM (Exp (Tree Bool))
    f (VRational r) = do
      lbl <- freshLbl
      return $ EVal $ VDist $ EVal . VBool <$> bernoulli lbl r

-- Tree instances
instance Sample Tree where
  sample = samplerIO -- in Sample.hs
deriving instance EqF Tree
deriving instance ShowF Tree
deriving instance AllF Tree

-- Here we can provide other inference methods. (TODO: exact inference)
instance Infer Tree where
  infers = []

-- Representation instance for m = InterpM and g = Tree.
instance Repr InterpM Tree where
  primitives = prims
  interp     = runInterp' -- In TreeInterp.hs
