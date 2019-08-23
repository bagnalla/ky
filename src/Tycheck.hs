{-# LANGUAGE GADTs, RankNTypes, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}

-- | Some inspiration from:
-- http://augustss.blogspot.com/2009/06/more-llvm-recently-someone-asked-me-on.html

module Tycheck (SomeCom(..), SomeG(..), load_repr) where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Data.Bifunctor (first, second)
import Data.Typeable hiding (typeOf)
import Text.Megaparsec (SourcePos)
import Text.Megaparsec.Error


import           Classes
import           Lang as L hiding (SomeExp, SomeNameExp, SomeVal)
import qualified Lang as L (SomeNameExp(..), SomeVal(..))
import           Parser (parse)
import           Symtab (Id(..), Symtab)
import qualified Symtab as S (add, empty, get, fromList)
import qualified Untyped as U
import           Util (debug)

data SomeExp m g where
  SomeExp :: forall m g a. (Repr m g, Eq a, Show a, Typeable a) =>
             Type m g a -> Exp m g a -> SomeExp m g

data SomeNameExp m g where
  SomeNameExp :: forall m g a. (Eq a, Show a, Typeable a) =>
                 Name a -> Type m g a -> Exp m g a -> SomeNameExp m g

data SomeType m g where
  SomeType :: forall m g a. (Repr m g, Eq a, Show a, Typeable a) =>
              Type m g a -> SomeType m g

data SomeCom m g where
  SomeCom :: forall m g a. (Eq a, Show a, Typeable a) =>
             Type m g a -> Com m g a -> SomeCom m g
deriving instance Show (SomeCom m g)

typeEq :: Type m g a -> Type m g b -> Maybe (a :~: b)
typeEq TBool     TBool     = Just Refl
typeEq TFloat    TFloat    = Just Refl
typeEq TRational TRational = Just Refl
typeEq TInteger  TInteger  = Just Refl
typeEq (TDist s) (TDist t) =
  case typeEq s t of
    Just Refl -> Just Refl
    Nothing -> Nothing
typeEq (TList s) (TList t) =
  case typeEq s t of
    Just Refl -> Just Refl
    Nothing -> Nothing
typeEq (TPair s t) (TPair s' t') =
  case (typeEq s s', typeEq t t') of
    (Just Refl, Just Refl) -> Just Refl
    _ -> Nothing
typeEq (TArrow s t) (TArrow s' t') =
  case (typeEq s s', typeEq t t') of
    (Just Refl, Just Refl) -> Just Refl
    _ -> Nothing
typeEq TVar TVar = Just Refl
typeEq TSt TSt = Just Refl
typeEq (TExp s) (TExp t) =
  case typeEq s t of
    Just Refl -> Just Refl
    Nothing -> Nothing
typeEq _ _ = Nothing


nameOfType :: String -> Type m g a -> Name a
nameOfType x _ = (x, Proxy)

type Context m g = Symtab (SomeType m g)

type TycheckM m g a = ReaderT (Context m g) (ExceptT String Identity) a

runTycheck :: Context m g -> TycheckM m g a -> Either String a
runTycheck ctx = runIdentity . runExceptT . flip runReaderT ctx

typeError :: SourcePos -> String -> TycheckM m g b
typeError pos msg =
  throwError $ "Type error: " ++ msg ++ " at " ++ show pos

extendCtx :: [(Id, SomeType m g)] -> Context m g -> Context m g
extendCtx ((x, ty) : rest) ctx =
  extendCtx rest $ S.add x ty ctx
extendCtx [] ctx = ctx

val_of_lit :: Repr m g => U.Literal -> SomeTypeVal m g
val_of_lit (U.LRational r) = SomeTypeVal TRational $ L.VRational r
val_of_lit (U.LFloat f) = SomeTypeVal TFloat $ L.VFloat f
val_of_lit (U.LBool b) = SomeTypeVal TBool $ L.VBool b
val_of_lit (U.LInteger i) = SomeTypeVal TInteger $ L.VInteger i


-- It seems like this shouldn't be necessary, but when we use the
-- regular Proxy type we run into problems where GHC gets kinds
-- confused (maybe it defaults to * when introducing a type variable
-- which then refuses to unify with something of kind *->*). So, we
-- just use our own proxy type with the kind of its type parameter
-- fixed to *->*.
-- NO longer needed now that m is determined by g by a functional
-- dependency on the Repr class.
-- data ProxyF (f :: * -> *) where
--   ProxyF :: ProxyF f

tycheckType :: Repr m g => Proxy g -> U.Type -> SomeType m g
tycheckType _ U.TRational = SomeType TRational
tycheckType _ U.TInteger  = SomeType TInteger
tycheckType _ U.TFloat    = SomeType TFloat
tycheckType _ U.TBool     = SomeType TBool
tycheckType p (U.TPair s t) =
  case (tycheckType p s, tycheckType p t) of
    (SomeType s', SomeType t') -> SomeType $ TPair s' t'
tycheckType p (U.TList t) =
  case tycheckType p t of
    SomeType t' -> SomeType $ TList t'
tycheckType p (U.TArrow s t) =
  case (tycheckType p s, tycheckType p t) of
    (SomeType s', SomeType t') -> SomeType $ TArrow s' t'  
tycheckType p (U.TDist t) =
  case tycheckType p t of
    SomeType t' -> SomeType $ TDist t'


-- | Typechecking expressions.
tycheckExp :: Repr m g => Proxy g ->
              U.Exp SourcePos -> TycheckM m g (SomeExp m g)

tycheckExp _ (U.ELit _ lit) =
  case val_of_lit lit of
    SomeTypeVal t v -> return $ SomeExp t $ L.EVal v

tycheckExp _ (U.EVar pos x) = do
  ctx <- ask
  case S.get x ctx of
    Just (SomeType t) -> return $ SomeExp t $ EVar $ (unId x, Proxy)
    Nothing -> typeError pos $ "unbound variable " ++ show x

tycheckExp p (U.EUnop pos unop e) = do
  SomeExp t e' <- tycheckExp p e
  case unop of
    U.UNot -> 
      case t of
        TBool -> return $ SomeExp TBool $ L.EUnop L.UNot e'
        _ -> typeError pos $ "expected type Bool, found " ++ show t
    U.UFst ->
      case t of
        TPair s _ -> return $ SomeExp s $ L.EUnop L.UFst e'
        _ -> typeError pos $ "expected pair type, found " ++ show t
    U.USnd ->
      case t of
        TPair _ t' -> return $ SomeExp t' $ L.EUnop L.USnd e'
        _ -> typeError pos $ "expected pair type, found " ++ show t

-- This could be refactored to reduce code duplication.
tycheckExp p (U.EBinop pos binop e1 e2) = do
  SomeExp t1 e1' <- tycheckExp p e1
  SomeExp t2 e2' <- tycheckExp p e2
  case binop of
    U.BPlus ->
      case (t1, t2) of
        (TFloat, TFloat) ->
          return $ SomeExp TFloat $ L.EBinop L.BPlus e1' e2'
        (TInteger, TInteger) ->
          return $ SomeExp TInteger $ L.EBinop L.BPlus e1' e2'
        _ -> typeError pos $
             "expected TFloat for both sides, got "
             ++ show t1 ++ " and " ++ show t2
    U.BMinus ->
      case (t1, t2) of
        (TFloat, TFloat) ->
          return $ SomeExp TFloat $ L.EBinop L.BMinus e1' e2'
        (TInteger, TInteger) ->
          return $ SomeExp TInteger $ L.EBinop L.BMinus e1' e2'
        _ -> typeError pos $
             "expected TFloat for both sides, got "
             ++ show t1 ++ " and " ++ show t2
    U.BMult ->
      case (t1, t2) of
        (TFloat, TFloat) ->
          return $ SomeExp TFloat $ L.EBinop L.BMult e1' e2'
        (TInteger, TInteger) ->
          return $ SomeExp TInteger $ L.EBinop L.BMult e1' e2'
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
    U.BNe -> tycheckExp p $ U.EUnop pos U.UNot (U.EBinop pos U.BEq e1 e2)
    U.BLe -> tycheckExp p $ U.EBinop pos U.BOr
             (U.EBinop pos U.BLt e1 e2) (U.EBinop pos U.BEq e1 e2)
    U.BGt -> tycheckExp p $ U.EUnop pos U.UNot (U.EBinop pos U.BLe e1 e2)
    U.BGe -> tycheckExp p $ U.EUnop pos U.UNot (U.EBinop pos U.BLt e1 e2)
    U.BCons ->
      case typeEq (TList t1) t2 of
        Just Refl -> return $ SomeExp t2 $ L.ECons e1' e2'
        _ -> typeError pos $ "expected list type, got " ++ show t2
    U.BPair ->
      return $ SomeExp (TPair t1 t2) $ L.EPair e1' e2'

tycheckExp p (U.ELam pos (Id x) t e) =
  case tycheckType p t of
    SomeType t' -> do
      SomeExp s e' <- local (S.add (Id x) (SomeType t')) $ tycheckExp p e
      return $ SomeExp (TArrow t' s) $ L.ELam (nameOfType x t') e'

tycheckExp p (U.ECall pos e1 args) =
  case e1 of
    U.EVar _ (Id "uniform") -> do
      args' <- mapM (tycheckExp p) args
      case args' of
        [SomeExp (TList t) e] ->
          return $ SomeExp (TDist t) $ EUniform e
        _ -> typeError pos "1"
    _ -> go p $ reverse args
  where
    go :: Repr m g => Proxy g ->
          [U.Exp SourcePos] -> TycheckM m g (SomeExp m g)
    go p [] = tycheckExp p e1
    go p (arg:args) = do
      SomeExp t e <- tycheckExp p (U.ECall pos e1 args)
      SomeExp t' arg' <- tycheckExp p arg
      case t of
        TArrow a b ->
          case typeEq t' a of
            Just Refl -> return $ SomeExp b $ EApp e arg'
            Nothing -> typeError pos $ "expected arg type to be "
                       ++ show a ++ ", got " ++ show t'
        _ -> typeError pos $
             "expected arrow type in LHS of application, got " ++ show t

-- tycheckExp (U.ENil pos t) =
--   case tycheckType t of
--     SomeType (TList t') -> return $ SomeExp (TList t') $ L.ENil
--     _ -> typeError pos $ "expected list type, got " ++ show t

tycheckExp p (U.ENil pos t) =
  case tycheckType p t of
    SomeType t' ->
      case t' of
        TList t'' ->
          return $ SomeExp (TList t'') L.ENil
        _ ->
          typeError pos $ "expected list type, got " ++ show t'

tycheckExp p (U.EDestruct pos l z f) = do
  SomeExp lt l' <- tycheckExp p l
  SomeExp zt z' <- tycheckExp p z
  SomeExp ft f' <- tycheckExp p f
  case lt of
    TList lt' ->
      case ft of
        TArrow t1 (TArrow t2 t3) ->
          case (typeEq t1 lt', typeEq t2 lt, typeEq t3 zt) of
            (Just Refl, Just Refl, Just Refl) ->
              return $ SomeExp zt $ L.EDestruct l' z' f'
            _ -> typeError pos $ "expected the following type equalities: "
                 ++ show t1 ++ " ~ " ++ show lt' ++ ", " ++ show t2 ++ " ~ "
                 ++ show lt ++ ", " ++ show t3 ++ " ~ " ++ show zt
        _ -> typeError pos $
             "expected type of the form a -> [a] -> b, got " ++ show ft
    _ -> typeError pos $ "expected list type, got " ++ show lt

tycheckExp p (U.ECond pos b e1 e2) = do
  SomeExp tb b'  <- tycheckExp p b
  SomeExp t1 e1' <- tycheckExp p e1
  SomeExp t2 e2' <- tycheckExp p e2
  case tb of
    TBool ->
      case typeEq t1 t2 of
        Just Refl ->
          return $ SomeExp t1 $ ECond b' e1' e2'
        Nothing ->
          typeError pos $ "expected both branches of conditional " ++
          "expression to be the same. instead got " ++ show t1 ++
          " and " ++ show t2
    _ -> typeError pos $ "expected bool in discriminee of conditional " ++
         "expression, got " ++ show tb

-- When assigning to a variable, check that the type of the expression
-- being assigned matches any previous assignments to that variable.
assert_var_type :: SourcePos -> Id -> Type m g a -> TycheckM m g ()
assert_var_type pos x ty = do
  ctx <- ask
  case S.get x ctx of
    Just (SomeType ty') ->
      case typeEq ty ty' of
        Just Refl -> return ()
        Nothing -> typeError pos "3"
    Nothing -> return ()


-- | Typechecking commands.
tycheckCom :: Repr m g => U.Com SourcePos -> TycheckM m g (SomeCom m g)

tycheckCom (U.CSkip _) = return $ SomeCom TSt L.Skip
tycheckCom (U.CAbort _) = return $ SomeCom TSt L.Abort

tycheckCom (U.CAssign pos x e) = do
  SomeExp t e' <- tycheckExp Proxy e
  assert_var_type pos x t
  return $ SomeCom TSt $ Assign (unId x, Proxy) e'

tycheckCom (U.CSample pos x e) = do
  SomeExp t e' <- tycheckExp Proxy e
  case t of
    TDist t' -> do
      assert_var_type pos x t'
      return $ SomeCom TSt $ Sample (unId x, Proxy) e'
    _ -> typeError pos "4"

tycheckCom (U.CSeq pos c1 c2) =
  case c1 of
    U.CAssign _ x e -> do
      SomeExp t e' <- tycheckExp Proxy e
      assert_var_type pos x t
      let c1' = Assign (unId x, Proxy) e'
      SomeCom t2 c2' <- local (S.add x $ SomeType t) $ tycheckCom c2
      return $ SomeCom t2 $ Seq c1' c2'
    U.CSample _ x e -> do
      SomeExp t e' <- tycheckExp Proxy e
      case t of
        TDist t' -> do
          assert_var_type pos x t'
          let c1' = Sample (unId x, Proxy) e'
          SomeCom t2 c2' <- local (S.add x $ SomeType t') $ tycheckCom c2
          return $ SomeCom t2 $ Seq c1' c2'
        _ -> typeError pos "5"
    _ -> do
      SomeCom t1 c1' <- tycheckCom c1
      SomeCom t2 c2' <- tycheckCom c2
      case t1 of
        TSt -> return $ SomeCom t2 $ Seq c1' c2'
        _ -> typeError pos $
             "expected first command in sequence to have unit type, got "
             ++ show t1

tycheckCom (U.CIte pos e c1 c2) = do
  SomeExp t e' <- tycheckExp Proxy e
  SomeCom t1 c1' <- tycheckCom c1
  SomeCom t2 c2' <- case c2 of
                      Just c2' -> tycheckCom c2'
                      Nothing -> return $ SomeCom TSt Skip
  case t of
    TBool ->
      case typeEq t1 t2 of
        Just Refl -> return $ SomeCom t1 $ Ite e' c1' c2'
        Nothing ->
          typeError pos $ "expected both branches of conditional branch " ++
          "to have the same type. instead got: " ++ show t1 ++ " and " ++
          show t2
    _ -> typeError pos $ "expected Bool, got " ++ show t

-- tycheckCom (U.CFlip pos c1 c2) =
--   SomeCom <$> pure Flip <*> tycheckCom c1 <*> tycheckCom c2

tycheckCom (U.CObserve pos e) = do
  SomeExp t e' <- tycheckExp Proxy e
  case t of
    TBool -> return $ SomeCom TSt $ Observe e'
    _ -> typeError pos $ "expected Bool, got " ++ show t

tycheckCom (U.CReturn pos e) = do
  SomeExp t e' <- tycheckExp Proxy e
  return $ SomeCom (TExp t) $ Return e'

tycheckCom (U.CWhile pos e c) = do
  SomeExp t e' <- tycheckExp Proxy e
  SomeCom t' c' <- tycheckCom c
  case t of
    TBool ->
      case t' of
        TSt -> return $ SomeCom TSt $ While e' c'
        _ -> typeError pos $ "expected while body to have unit type, got "
             ++ show t'
    _ -> typeError pos $ "expected Bool, got " ++ show t


-- | Typechecking functions.
-- argument types -> return type -> function type
function_type :: [SomeType m g] -> SomeType m g -> SomeType m g
function_type (SomeType ty : tys) ret_ty =
  case function_type tys ret_ty of
    SomeType ty' -> SomeType $ TArrow ty ty'
function_type [] ret_ty = ret_ty

tycheckFunction :: Repr m g =>
                   U.Function SourcePos -> TycheckM m g (SomeNameExp m g)
tycheckFunction (U.Function { U.function_name = Id f_nm
                            , U.function_type = f_ty
                            , U.function_args = f_args
                            , U.function_body = f_body }) = do
  let f_ty' = tycheckType Proxy f_ty
  let f_args' = second (tycheckType Proxy) <$> f_args
  -- Extend the context when typechecking the body. Include a
  -- self-reference.
  f_body' <-
    local (extendCtx $
           (Id f_nm, function_type (snd <$> f_args') f_ty') : f_args') $
    tycheckExp Proxy f_body
  SomeNameExp x t e <- go f_ty' (first unId <$> f_args') f_body'
  -- Tie the knot.
  return $ SomeNameExp x t $ subst x e e
  where
    go :: SomeType m g -> [(String, SomeType m g)] -> SomeExp m g ->
          TycheckM m g (SomeNameExp m g)

    -- When there are no args, just return the body expression.
    go ty [] body =
      case (ty, body) of
        (SomeType ty', SomeExp ty'' body') ->
          case typeEq ty' ty'' of
            Just Refl ->
              return $ SomeNameExp (f_nm, Proxy) ty' body'
            Nothing ->
              typeError (U.data_of_exp f_body) $
              "function body has type " ++ show ty'' ++
              " but expected type " ++ show ty'

    -- Abstract over the arguments one at a time.
    go ty ((x, x_ty):xs) body = do
      body' <- go ty xs body
      case (x_ty, body') of
        (SomeType x_ty', SomeNameExp _ f_ty body'') ->
          return $ SomeNameExp (f_nm, Proxy) (TArrow x_ty' f_ty) $
          ELam (nameOfType x x_ty') body''


mkLam :: [(Id, SomeType m g)] -> SomeExp m g -> SomeExp m g
mkLam [] e = e
mkLam ((Id x, SomeType s) : args) e =
  case mkLam args e of
    SomeExp t e' ->
      SomeExp (TArrow s t) $ ELam (x, Proxy) e'


-- | Typechecking distributions
tycheckDist :: Repr m g => U.Dist SourcePos -> TycheckM m g (SomeNameExp m g)
tycheckDist (U.Dist { U.dist_name = Id dist_nm
                    , U.dist_type = dist_ty
                    , U.dist_args = dist_args
                    , U.dist_body = dist_body }) =
  case tycheckType Proxy dist_ty of
    SomeType dist_ty' -> do
      let dist_args' = second (tycheckType Proxy) <$> dist_args
      SomeCom t dist_body' <-
        -- Include self reference.
        local (extendCtx $
               (Id dist_nm, function_type (snd <$> dist_args')
                 (SomeType $ TDist dist_ty')) : dist_args') $
        tycheckCom dist_body
      case t of
        TExp t' ->
          case mkLam dist_args' (SomeExp (TDist t') $ ECom [] dist_body') of
            SomeExp t'' e ->
              let nm = (dist_nm, Proxy) in
                -- Tie the knot.
                return $ SomeNameExp nm t'' $ subst nm e e
        _ -> typeError (U.data_of_com dist_body) "6"


tycheckProg :: Repr m g =>
               [Either (U.Function SourcePos) (U.Dist SourcePos)] ->
               U.Com SourcePos -> TycheckM m g ([SomeNameExp m g], SomeCom m g)
tycheckProg = go
  where
    go [] com = do
      com' <- tycheckCom com
      return ([], com')
    go (x:xs) com = do
      SomeNameExp (x, _) t e <- either tycheckFunction tycheckDist x
      (es, com') <- local (S.add (Id x) $ SomeType t) $ go xs com
      return (SomeNameExp (x, Proxy) t e : es, com')

-- Build initial context from the primitives list.
initCtx :: Repr m g => [(String, SomeTypeVal m g)] -> Context m g
initCtx prims =
  S.fromList $ (\(x, SomeTypeVal t v) -> (Id x, SomeType t)) <$> prims


tycheck :: Repr m g =>
           [(String, SomeTypeVal m g)] ->
           [Either (U.Function SourcePos) (U.Dist SourcePos)] ->
           U.Com SourcePos -> Either String ([L.SomeNameExp m g], SomeCom m g)
tycheck prims funcs_dists com =
  second (first $ fmap $ \(SomeNameExp x _ e) -> L.SomeNameExp x e) $
  runTycheck (initCtx prims) $ tycheckProg funcs_dists com


data SomeG m g where
  SomeG :: forall m g a. (Repr m g, Eq a, Show a, Typeable a) =>
           Type m g a -> g a -> SomeG m g

load_repr :: Repr m g =>
             Proxy g -> String -> String -> Either String (SomeG m g)
load_repr _ filename src =
  let (funcs_dists, main_com) =
        case parse filename src of
          Left err -> error $ errorBundlePretty err
          Right c -> c in
    case tycheck primitives funcs_dists main_com of
      Left msg -> Left msg
      Right (es, SomeCom ty tcom) ->
        Right $ SomeG ty $ interp (initEnv ++ es) tcom
