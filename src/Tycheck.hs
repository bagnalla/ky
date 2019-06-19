{-# LANGUAGE GADTs, RankNTypes, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

-- | Some inspiration from:
-- http://augustss.blogspot.com/2009/06/more-llvm-recently-someone-asked-me-on.html

module Tycheck (tycheck) where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Data.Typeable hiding (typeOf)
import Text.Megaparsec

import           Lang as L
import qualified Untyped as U
import           Symtab (Id(..), Symtab)
import qualified Symtab (add, empty, get)
import           Tree (Tree)

data Type a where
  TBool :: Type Bool
  TFloat :: Type Double
  TRational :: Type Rational
  TDist :: (Eq a, Show a, Typeable a) => Type a -> Type (Tree a)
  TList :: (Eq a, Show a, Typeable a) => Type a -> Type [a]
  TNil :: Type ()
deriving instance Show (Type a)

instance Eq (Type a) where
  TBool == TBool = True
  TFloat == TFloat = True
  TRational == TRational = True
  TDist t1 == TDist t2 = t1 == t2
  TList t1 == TList t2 = t1 == t2

data SomeVal where
  SomeVal :: forall a. (Eq a, Show a, Typeable a) =>
             Type a -> Val a -> SomeVal

data SomeExp where
  SomeExp :: forall a. (Eq a, Show a, Typeable a) =>
             Type a -> Exp a -> SomeExp

data SomeType where
  SomeType :: forall a. (Eq a, Show a, Typeable a) => Type a -> SomeType

typeEq :: Type a -> Type b -> Maybe (a :~: b)
typeEq TBool TBool = Just Refl
typeEq TFloat TFloat = Just Refl
typeEq TRational TRational = Just Refl
typeEq (TDist s) (TDist t) =
  case typeEq s t of
    Just Refl -> Just Refl
    Nothing -> Nothing
typeEq (TList s) (TList t) =
  case typeEq s t of
    Just Refl -> Just Refl
    Nothing -> Nothing
typeEq TNil TNil = Just Refl
typeEq _ _ = Nothing


type Context = Symtab SomeType

type TycheckM a = ReaderT Context (ExceptT String Identity) a

runTycheck :: Context -> TycheckM a -> Either String a
runTycheck ctx = runIdentity . runExceptT . flip runReaderT ctx

typeError :: SourcePos -> String -> TycheckM b
typeError pos msg =
  throwError $ "Type error: " ++ msg ++ " at " ++ show pos


val_of_lit :: U.Lit -> SomeVal
val_of_lit (U.LRational r) = SomeVal TRational $ L.VRational r
val_of_lit (U.LFloat f) = SomeVal TFloat $ L.VFloat f
val_of_lit (U.LBool b) = SomeVal TBool $ L.VBool b


-- | Typechecking expressions.

tycheckExp :: U.Exp SourcePos -> TycheckM SomeExp

tycheckExp (U.ELit _ lit) =
  case val_of_lit lit of
    SomeVal t v -> return $ SomeExp t $ L.EVal v

tycheckExp (U.EVar pos x) = do
  ctx <- ask
  case Symtab.get x ctx of
    Just (SomeType t) -> return $ SomeExp t $ EVar $ (unId x, Proxy)
    Nothing -> typeError pos $ "unbound variable " ++ show x

tycheckExp (U.EUnop pos U.UNot e) = do
  SomeExp t e' <- tycheckExp e
  case t of
    TBool -> return $ SomeExp TBool $ L.EUnop L.UNot e'
    _ -> typeError pos $ "expected type Bool, found " ++ show t

-- This could be refactored to reduce code duplication.
tycheckExp (U.EBinop pos binop e1 e2) = do
  SomeExp t1 e1' <- tycheckExp e1
  SomeExp t2 e2' <- tycheckExp e2
  case binop of
    U.BPlus ->
      case (t1, t2) of
        (TFloat, TFloat) ->
          return $ SomeExp TFloat $ L.EBinop L.BPlus e1' e2'
        _ -> typeError pos $
             "expected TFloat for both sides, got "
             ++ show t1 ++ " and " ++ show t2
    U.BMinus ->
      case (t1, t2) of
        (TFloat, TFloat) ->
          return $ SomeExp TFloat $ L.EBinop L.BMinus e1' e2'
        _ -> typeError pos $
             "expected TFloat for both sides, got "
             ++ show t1 ++ " and " ++ show t2
    U.BMult ->
      case (t1, t2) of
        (TFloat, TFloat) ->
          return $ SomeExp TFloat $ L.EBinop L.BMult e1' e2'
        _ -> typeError pos $
             "expected TFloat for both sides, got "
             ++ show t1 ++ " and " ++ show t2
    U.BAnd ->
      case (t1, t2) of
        (TBool, TBool) ->
          return $ SomeExp TBool $ L.EBinop L.BAnd e1' e2'
        _ -> typeError pos $
             "expected TBool for both sides, got "
             ++ show t1 ++ " and " ++ show t2
    U.BOr ->
      case (t1, t2) of
        (TBool, TBool) ->
          return $ SomeExp TBool $ L.EBinop L.BOr e1' e2'
        _ -> typeError pos $
             "expected TBool for both sides, got "
             ++ show t1 ++ " and " ++ show t2
    U.BEq ->
      case typeEq t1 t2 of
        Just Refl ->
          return $ SomeExp TBool $ L.EBinop L.BEq e1' e2'
        _ -> typeError pos $
             "expected same type on both sides, got "
             ++ show t1 ++ " and " ++ show t2
    U.BLt ->
      case typeEq t1 t2 of
        Just Refl ->
          return $ SomeExp TBool $ L.EBinop L.BLt e1' e2'
        _ -> typeError pos $
             "expected same type on both sides, got "
             ++ show t1 ++ " and " ++ show t2
    U.BCons ->
      case (t2, e2') of
        (TList TNil, EList []) ->
          return $ SomeExp (TList t1) $ L.EList [e1']
        (TList t', EList l) ->
          case typeEq t1 t' of
            Just Refl ->
              return $ SomeExp t2 $ L.EList (e1' : l)
            _ -> typeError pos $ "incompatible types: "
                 ++ show t1 ++ " and " ++ show t'
        _ -> typeError pos $ "expected list type, got " ++ show t2

tycheckExp (U.ECall pos e1 es) = do
  es' <- mapM tycheckExp es
  case e1 of
    U.EVar _ (Id "uniform") ->
      case es' of
        [SomeExp (TList t) e] ->
          return $ SomeExp (TDist t) $ EUniform e
        _ -> typeError pos ""
    U.EVar _ (Id "bernoulli") ->
      case es' of
        [SomeExp TRational e] ->
          return $ SomeExp (TDist TBool) $ EBernoulli e
        _ -> typeError pos ""
    _ -> typeError pos ""

tycheckExp (U.ENil _) = return $ SomeExp (TList TNil) $ L.EList []


-- When assigning to a variable, check that the type of the expression
-- being assigned matches any previous assignments to that variable.
assert_var_type :: SourcePos -> Id -> Type a -> TycheckM ()
assert_var_type pos x ty = do
  ctx <- ask
  case Symtab.get x ctx of
    Just (SomeType ty') ->
      case typeEq ty ty' of
        Just Refl -> return ()
        Nothing -> typeError pos ""
    Nothing -> return ()


-- | Typechecking commands.

tycheckCom :: U.Com SourcePos -> TycheckM L.Com

tycheckCom (U.CSkip _) = return L.Skip
tycheckCom (U.CAbort _) = return L.Abort

tycheckCom (U.CAssign pos x e) = do
  SomeExp t e' <- tycheckExp e
  assert_var_type pos x t
  return $ Assign (unId x, Proxy) e'

tycheckCom (U.CSample pos x e) = do
  SomeExp t e' <- tycheckExp e
  case t of
    TDist t' -> do
      assert_var_type pos x t'
      return $ Sample (unId x, Proxy) e'
    _ -> typeError pos ""

tycheckCom (U.CSeq pos c1 c2) =
  case c1 of
    U.CAssign _ x e -> do
      SomeExp t e' <- tycheckExp e
      assert_var_type pos x t
      let c1' = Assign (unId x, Proxy) e'
      c2' <- local (Symtab.add x $ SomeType t) $ tycheckCom c2
      return $ Seq c1' c2'
    U.CSample _ x e -> do
      SomeExp t e' <- tycheckExp e
      case t of
        TDist t' -> do
          assert_var_type pos x t'
          let c1' = Sample (unId x, Proxy) e'
          c2' <- local (Symtab.add x $ SomeType t') $ tycheckCom c2
          return $ Seq c1' c2'
        _ -> typeError pos ""
    _ -> do
      c1' <- tycheckCom c1
      c2' <- tycheckCom c2
      return $ Seq c1' c2'

tycheckCom (U.CIte pos e c1 c2) = do
  SomeExp t e' <- tycheckExp e
  c1' <- tycheckCom c1
  c2' <- case c2 of
           Just c2' -> tycheckCom c2'
           Nothing -> return Skip
  case t of
    TBool -> return $ Ite e' c1' c2'
    _ -> typeError pos $ "expected Bool, got " ++ show t

tycheckCom (U.CFlip pos c1 c2) =
  pure Flip <*> tycheckCom c1 <*> tycheckCom c2

tycheckCom (U.CObserve pos e) = do
  SomeExp t e' <- tycheckExp e
  case t of
    TBool -> return $ Observe e'
    _ -> typeError pos $ "expected Bool, got " ++ show t

tycheckCom (U.CWhile pos e c) = do
  SomeExp t e' <- tycheckExp e
  c' <- tycheckCom c
  case t of
    TBool -> return $ While e' c'
    _ -> typeError pos $ "expected Bool, got " ++ show t


-- | UNTYPED
-- data Com a = 
--   -- Skip patterns for now..
--   -- | Combine Pattern Com Com
--   deriving Show

-- | LANG
-- data Com where 
--   Combine :: Pattern -> Com -> Com -> Com  


-- | The function exposed to the user of this module.
tycheck :: U.Com SourcePos -> Either String L.Com
tycheck com = runTycheck Symtab.empty $ tycheckCom com
