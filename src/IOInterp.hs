{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, DeriveAnyClass #-}

-- | Here we instantiate the language with m = Identity and g = IO,
-- yielding a straightforward sampling semantics in the IO monad.

module IOInterp (sampler) where

import           Control.Monad.Identity
import           Control.Monad.Loops
import           Data.Maybe (fromMaybe)
import           Data.Typeable
import           System.Random

import           Classes
import           Lang hiding (Com, Env, Exp, St, Val, interp)
import qualified Lang (Com, Env, Exp, St, Val)


-- Set up type synonyms.
type Com = Lang.Com Identity IO
type Env = Lang.Env Identity IO
type Exp = Lang.Exp Identity IO
type St  = Lang.St  Identity IO
type Val = Lang.Val Identity IO


-- | Eval
eval :: Typeable a => Env -> Exp a -> St -> Val a

eval _ (EVal v) _ = v

eval env (EVar x) st =
  case get x st of
    Just v -> v
    Nothing ->
      case envGet x env of
        Just e -> eval env e st
        Nothing ->
          error $ "eval: unbound identifier " ++ show x

eval env (EUnop u e) st =
  case (u, eval env e st) of
    (UNot, VBool b)   -> VBool $ not b
    (UFst, VPair x _) -> x
    (USnd, VPair _ y) -> y

eval env (EBinop b e1 e2) st =
  case (b, eval env e1 st, eval env e2 st) of
    (BPlus,  VRational r1, VRational r2) -> VRational $ r1 + r2
    (BPlus,  VInteger i1,  VInteger i2)  -> VInteger  $ i1 + i2
    (BPlus,  VFloat f1,    VFloat f2)    -> VFloat    $ f1 + f2
    (BMinus, VRational r1, VRational r2) -> VRational $ r1 - r2
    (BMinus, VInteger i1,  VInteger i2)  -> VInteger  $ i1 - i2
    (BMinus, VFloat f1,    VFloat f2)    -> VFloat    $ f1 - f2
    (BMult,  VRational r1, VRational r2) -> VRational $ r1 * r2
    (BMult,  VInteger i1,  VInteger i2)  -> VInteger  $ i1 * i2
    (BMult,  VFloat f1,    VFloat f2)    -> VFloat    $ f1 * f2
    (BAnd,   VBool b1,     VBool b2)     -> VBool     $ b1 && b2
    (BOr,    VBool b1,     VBool b2)     -> VBool     $ b1 || b2
    (BEq,    v1,           v2)           -> VBool     $ v1 == v2
    (BLt,    VRational r1, VRational r2) -> VBool     $ r1 < r2
    (BLt,    VInteger i1,  VInteger i2)  -> VBool     $ i1 < i2
    (BLt,    VFloat f1,    VFloat f2)    -> VBool     $ f1 < f2

eval _ ENil _ = VNil

eval env (ECons hd tl) st = VCons (eval env hd st) (eval env tl st)

eval env (EDestruct l z f) st =
  case eval env l st of
    VNil -> eval env z st
    VCons hd tl ->
      eval env (EApp (EApp f (EVal hd)) (EVal tl)) st

eval env (EUniform l) st =
  case eval env l st of
    VNil -> error "eval: empty list argument to uniform distribution"
    l' ->
      VDist $ do
      g <- newStdGen
      let n = (fst $ random g) :: Int
      return $ EVal $ vlist_nth (n `mod` vlist_length l') l'

eval _ (ELam x e) _ = VLam x e

eval env (EApp f x) st =
  case eval env f st of
    VLam y e -> eval env (subst y x e) st
    VPrim g  -> eval env (runIdentity $ g $ eval env x st) st

eval env (ECom args c) st =
  let st' = map (\(SomeNameExp x e) -> SomeNameVal x $ eval env e st) args in
    VDist $ untilJust $ interp env c st'

eval env (ECond b e1 e2) st =
  case eval env b st of
    VBool True -> eval env e1 st
    VBool False -> eval env e2 st

eval _ (EPrim f) _ = VPrim f


-- | Interp. A command is interpreted as a function from program
-- states to IO actions (one way of representing conditional
-- distributions, conditioned on states).
interp :: Env -> Com a -> St -> IO (Maybe a)

interp _ Skip st = return $ Just st

interp env (Assign x e) st = return $ Just $ upd x (eval env e st) st

interp env (Seq c1 c2) st = do
  m <- interp env c1 st
  fromMaybe (return Nothing) $ interp env c2 <$> m

interp env (Ite e c1 c2) st =
  case eval env e st of
    VBool True -> interp env c1 st
    VBool False -> interp env c2 st

interp env (Sample x e) st =
  case eval env e st of
    VDist f -> f >>= \y -> interp env (Assign x y) st

interp env (Observe e) st =
  case eval env e st of
    VBool True -> return $ Just st
    VBool False -> return Nothing

interp env (Return e) st = return $ Just $ EVal $ eval env e st

interp env Abort st = interp env (Observe $ EVal $ VBool False) st

interp env (While e c) st = interp env (Ite e (Seq c (While e c)) Skip) st


-- Produce a rejection sampler IO action from the given command and
-- environment.
sampler :: (Eq a, Show a) => Env -> Com a -> IO a
sampler env c = untilJust $ interp env c empty
