{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving, DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor, TypeSynonymInstances #-}

module IORepr (primitives) where

import Control.Monad.Identity
import Data.Proxy
import System.Random

import           Classes
import           IOInterp
import           Lang hiding (Env, Exp, SomeVal, SomeTypeVal, Val)
import qualified Lang as L (Env, Exp, SomeVal, SomeTypeVal(..), Val)

type Env         = L.Env         Identity IO
type Exp         = L.Exp         Identity IO
type SomeVal     = L.SomeVal     Identity IO
type SomeTypeVal = L.SomeTypeVal Identity IO
type Val         = L.Val         Identity IO


-- | The list of predefined primitives. Used by the typechecker (name
-- and type information) and interpreter (name and value). For now
-- primitives can't be polymorphic, so the uniform distribution must
-- be built directly into the language rather than being a primitive
-- here.
prims :: [(String, SomeTypeVal)]
prims =
  [
    ("bernoulli", L.SomeTypeVal (TArrow TRational $ TDist TBool) bernoulli_prim)
    -- Add more here
  ]

bernoulli_prim :: Val (Rational -> IO Bool)
bernoulli_prim = VPrim f
  where
    f :: Val Rational -> Identity (Exp (IO Bool))
    f (VRational r) =
      Identity $ EVal $ VDist $ do
      i <- randomRIO (0.0, 1.0) :: IO Double
      return $ EVal $ VBool $ i < fromRational r


-- IO actions are never equal.
instance Eq a => Eq (IO a) where
  f == g = False
-- Trivial show instance.
instance Show a => Show (IO a) where
  show _ = "IO"
instance Sample IO where
  sample = id
-- No exact inference methods.
instance Infer IO where
  infers = []

deriving instance EqF IO
deriving instance ShowF IO
deriving instance AllF IO

instance Repr Identity IO where
  primitives = prims
  interp     = sampler
