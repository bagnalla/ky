{-# LANGUAGE GADTs #-}
module Primitives where

import Data.Proxy

import Distributions
import Interp
import Lang hiding (SomeVal)
import Tree

-- | The list of predefined primitives. Used by the typechecker (name
-- and type information) and interpreter (name and value). For now
-- primitives can't be polymorphic, so the uniform distribution must
-- be built directly into the language rather than being a primitive
-- here.
primitives :: [(String, SomeTypeVal)]
primitives =
  [
    ("bernoulli", SomeTypeVal (TArrow TRational (TDist TBool)) bernoulli_prim)
    -- Add more here
  ]

initEnv :: Env
initEnv = (\(x, SomeTypeVal t v) ->
             SomeNameExp (x, Proxy) (EVal v)) <$> primitives

bernoulli_prim :: Val (Rational -> Tree Bool)
bernoulli_prim = VPrim f
  where
    f :: Val Rational -> InterpM (Exp (Tree Bool))
    f (VRational r) = do
      lbl <- freshLbl
      return $ EVal $ VTree $ EVal . VBool <$> bernoulli lbl r
