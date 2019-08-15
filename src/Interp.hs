{-# LANGUAGE GADTs #-}
module Interp where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State hiding (get)
import qualified Control.Monad.State as S (get)

import Data.List (intersect)
import Data.Typeable

import Dep
import Distributions
import Lang
import Sexp
import Tree
import Util

-- | Interpreting commands as (stateful) tree transformers.

freshLbl :: InterpM Int
freshLbl = do
  counter <- S.get
  put $ counter + 1
  return $ counter + 1

is_true :: Exp Bool -> St -> InterpM Bool
is_true e st = do
  b <- eval e st
  case b of
    VBool b' -> return b'


eval :: Typeable a => Exp a -> St -> InterpM (Val a)
eval (EVal v) _ = return v
eval (EVar x) st =
  -- First try a lookup in the local state.
  case get x st of
    Just v -> return v
    Nothing -> do
      -- If that fails, try the global environment.
      env <- ask
      case envGet x env of
        Just e -> eval e st
        Nothing ->
          let (x', proxy) = x
              ty = typeOf proxy in
            error $ "eval: unbound variable: " ++ show x
            ++ " of type " ++ show ty ++ ".\nst: " ++ show st
eval (EUnop u e) st = do
  v <- eval e st
  case u of
    UNot ->
      case v of
        VBool b -> return $ VBool $ not b
        _ -> error "eval: ill-typed UNot expression"
    UFst ->
      case v of
        VPair x _ -> return x
        _ -> error "eval: ill-typed UFst expression"
    USnd ->
      case v of
        VPair _ y -> return y
        _ -> error "eval: ill-typed USnd expression"
eval (EBinop b e1 e2) st = do
  v1 <- eval e1 st
  v2 <- eval e2 st
  case b of
    BPlus ->
      case (v1, v2) of
        (VRational r1, VRational r2) -> return $ VRational $ r1 + r2
        (VFloat f1, VFloat f2) -> return $ VFloat $ f1 + f2
        (VInteger i1, VInteger i2) -> return $ VInteger $ i1 + i2
        _ -> error "eval: ill-typed BPlus expression"
    BMinus ->
      case (v1, v2) of
        (VRational r1, VRational r2) -> return $ VRational $ r1 - r2
        (VFloat f1, VFloat f2) -> return $ VFloat $ f1 - f2
        (VInteger i1, VInteger i2) -> return $ VInteger $ i1 - i2
        _ -> error "eval: ill-typed BMinus expression"
    BMult ->
      case (v1, v2) of
        (VRational r1, VRational r2) -> return $ VRational $ r1 * r2
        (VFloat f1, VFloat f2) -> return $ VFloat $ f1 * f2
        (VInteger i1, VInteger i2) -> return $ VInteger $ i1 * i2
        _ -> error "eval: ill-typed BMult expression"
    BAnd ->
      case (v1, v2) of
        (VBool b1, VBool b2) -> return $ VBool $ b1 && b2
        _ -> error "eval: ill-typed BAnd expression"
    BOr ->
      case (v1, v2) of
        (VBool b1, VBool b2) -> return $ VBool $ b1 || b2
        _ -> error "eval: ill-typed BOr expression"
    BEq ->
      case (v1, v2) of
        (VRational r1, VRational r2) -> return $ VBool $ r1 == r2
        (VFloat f1, VFloat f2) -> return $ VBool $ f1 == f2
        (VInteger i1, VInteger i2) -> return $ VBool $ i1 == i2
        (VBool b1, VBool b2) -> return $ VBool $ b1 == b2
        _ -> error "eval: ill-typed BEq expression"
    BLt ->
      case (v1, v2) of
        (VRational r1, VRational r2) -> return $ VBool $ r1 < r2
        (VFloat f1, VFloat f2) -> return $ VBool $ f1 < f2
        (VInteger i1, VInteger i2) -> return $ VBool $ i1 < i2
        (VBool b1, VBool b2) -> return $ VBool $ b1 < b2
        _ -> error "eval: ill-typed BLt expression"
    BPair ->
      return $ VPair v1 v2

-- eval (EPair e1 e2) st = do
--   v1 <- eval e1 st
--   v2 <- eval e2 st
--   return $ VPair v1 v2

-- eval (EList es) st = do
--   vs <- mapM (flip eval st) es
--   return $ VList vs

eval ENil _ = return $ VList []

eval (ECons hd tl) st = do
  hd' <- eval hd st
  tl' <- eval tl st
  case tl' of
    VList l ->
      return $ VList $ hd' : l

eval (EDestruct l z f) st = do
  l' <- eval l st
  case l' of
    VList [] -> eval z st
    VList (v:vs) ->
      eval (EApp (EApp f $ EVal v) (EVal $ VList vs)) st

eval (ELam x body) _ = return $ VLam x body

eval (EApp f e) st = do
  f' <- eval f st
  v <- eval e st
  case f' of
    VLam x body -> eval (subst x (EVal v) body) st
    VPrim f -> f v >>= flip eval st


eval (ECom args com) st = do
  st' <- mapM (\(SomeNameExp x e) -> SomeNameVal x <$> eval e st) args
  lbl <- freshLbl
  VTree . set_label lbl <$> interp com (Leaf st')

-- TODO: do we need to introduce labels here? I think it's OK if we
-- don't because nothing bad will happen but in principle they should
-- be there.
eval (ECond b e1 e2) st = do
  b' <- is_true b st
  if b' then eval e1 st else eval e2 st

eval (EPrim x) _ = return $ VPrim x

eval (EUniform e) st = do
  lbl <- freshLbl
  v <- eval e st
  case v of
    VList vals -> return $ VTree $ uniform lbl $ EVal <$> vals


-- TODO: make this take the root label as an argument so parameterized
-- commands can use fresh labels as the roots.

interp' :: (Eq a, Show a) => Com a -> Tree St -> InterpM (Tree a)
-- Use this for incremental reduction. Not working right though?
-- interp' c t = canon <$> interp c t
interp' = interp

interp :: (Eq a, Show a) => Com a -> Tree St -> InterpM (Tree a)
interp Skip t = return t
interp (Assign x e) t = do
  mapJoin t $ \st -> do
    v <- eval e st
    return $ Leaf $ upd x v st
interp (Sample x e) t = do
  mapJoin t $ \st -> do
    v <- eval e st
    case v of
      VTree t' ->
        mapM (\e' -> do
                 v' <- eval e' st
                 return $ upd x v' st) t'

interp (Seq c1 c2) t = interp' c1 t >>= interp' c2

interp (Ite e c1 c2) t =
  mapJoin t $ \st -> do
    fresh_lbl1 <- freshLbl
    fresh_lbl2 <- freshLbl
    b <- is_true e st
    if b then
      set_label fresh_lbl1 <$> (interp' c1 $ Leaf st)
      else
      set_label fresh_lbl2 <$> (interp' c2 $ Leaf st)

interp (While e c) t =
  let deps = var_deps c
      svars = sample_vars c
      sdeps = sample_deps svars deps
      sdeps_in_e = intersect sdeps (id_of_name <$> fvs e) in
    if not $ null sdeps_in_e then
      -- Something in e depends on randomness.
      -- debug "DETECTED RANDOM LOOP" $
      case dep_cycle deps of
        Just x ->
          error $ "loop error: the variable '" ++ show x ++
          "' depends on itself within the body of a loop"
        Nothing ->
          mapJoin t $ \st -> do
          b <- is_true e st
          if b then do
            t' <- interp c $ Leaf st
            fresh_lbl <- freshLbl
            t'' <- mapJoin t' $ \st' -> do
              b' <- is_true e st'
              return $ if b' then Hole fresh_lbl else Leaf st'
            return $ set_label fresh_lbl t''
            else
            return $ Leaf st
    else
      -- debug "DETECTED UNROLLABLE LOOP" $
      -- Nothing in e depends on randomness so unfold the loop.
      interp' (Ite e (Seq c (While e c)) Skip) t

-- interp (While e c) t =
--   interp' (Ite e (Seq c (While e c)) Skip) t

interp (Return e) t = mapM (\st -> EVal <$> eval e st) t

interp (Observe e) t = do
  mapJoin t $ \st -> do
    b <- is_true e st
    if b then return $ Leaf st else return $ Hole 0

interp Abort t = interp' (Observe $ EVal $ VBool False) t


runInterp :: (Eq a, Show a) => Env -> Com a -> Tree St -> (Tree a, Int)
runInterp env c t =
  runIdentity $ runStateT (runReaderT (interp' c t) env) (-1)

runInterp' :: (Eq a, Show a) => Env -> Com a -> Tree a
runInterp' env c =
  set_label 0 $ fst $ runInterp env c (Leaf empty)
