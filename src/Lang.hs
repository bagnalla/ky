{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, GADTs, RankNTypes #-}
{-# LANGUAGE DataKinds, StandaloneDeriving, TypeFamilies #-}
{-# LANGUAGE TupleSections, TypeOperators #-}

module Lang where

import Control.Monad.State hiding (get)
import qualified Control.Monad.State as S (get)

import Data.Bifunctor (first)
import Data.Proxy
import Data.Typeable
import Distributions
import Tree hiding (mu)
import Util (debug, mapJoin)

mu :: (a -> a) -> a
mu f = f (mu f)

type Name a = (String, Proxy a)

data Val a where
  VRational :: Rational -> Val Rational
  VFloat :: Double -> Val Double
  VBool :: Bool -> Val Bool
  VTree :: Tree (Exp a) -> Val (Tree a)
  VList :: [Val a] -> Val [a]
  VPair :: Val a -> Val b -> Val (a, b)

-- Mark this as incoherent so GHC prefers the other instance when
-- possible.
-- instance {-# INCOHERENT #-} Eq (Val a) where
instance Eq (Val a) where
  VRational x == VRational y = x == y
  VFloat x == VFloat y = x == y
  VBool x == VBool y = x == y
  VTree _ == VTree _ = error "no equality on trees for now"
  VList _ == VList _ = error "no equality on lists for now"
  VPair _ _ == VPair _ _ = error "no equality on pairs for now"

-- instance {-# OVERLAPPING #-} Eq a => Eq (Val [a]) where
--   VList l1 == VList l2 = l1 == l2

-- instance {-# OVERLAPPING #-} Eq a => Eq (Val (Tree a)) where
--   VTree x == VTree y = x == y

instance Show a => Show (Val a) where
  show (VRational v) = "VRational " ++ show v
  show (VFloat v) = "VFloat " ++ show v
  show (VBool b) = "VBool " ++ show b
  show (VTree _) = "VTree"
  show (VList _) = "VList"
  show (VPair _ _) = "VPair"

-- instance {-# OVERLAPPING #-} Show a => Show (Val (Tree a)) where
--   show (VTree d) = "(VTree " ++ show d ++ ")"

data StPkg where
  StPkg :: forall a. (Show a, Typeable a) => Name a -> Val a -> StPkg

instance Eq StPkg where
  StPkg (x1, _) v1 == StPkg (x2, _) v2 =
    case cast v1 of
      Just v1' ->
        -- debug ("x1: " ++ show x1) $
        -- debug ("x2: " ++ show x2) $
        -- debug ("v1: " ++ show v1) $
        -- debug ("v2: " ++ show v2) $
        x1 == x2 && v1' == v2
      Nothing -> False

-- instance Eq StPkg where
--   _ == _ = False

instance Show StPkg where
  show (StPkg (x, _) v) = "{" ++ show x ++ ", " ++ show v ++ "}"

type St = [StPkg]

empty :: St
empty = []

nameEqT :: (Typeable a, Typeable b) => Name a -> Name b -> Maybe (a :~: b)
nameEqT _ _ = eqT

-- Replace old entries instead of shadowing.
upd :: (Show a, Typeable a) => Name a -> Val a -> St -> St
upd x v [] = [StPkg x v]
upd x v (StPkg x' v' : st) =
  if fst x == fst x' then
    case nameEqT x x' of
      Just Refl -> StPkg x v : st
      Nothing -> error ""
  else
    StPkg x' v' : upd x v st

get :: Typeable a => Name a -> St -> Maybe (Val a)
get _ [] = Nothing
get x (StPkg y v : rest) =
  case cast (y, v) of
    Just (y', v') ->
      if x == y' then Just v' else get x rest
    _ -> get x rest

data UnopTy =
  UTNot

data Unop a where
  UNot :: Unop UTNot
deriving instance Eq (Unop a)
deriving instance Show (Unop a)

type family UnopResTy (a :: UnopTy) (b :: *) where
  UnopResTy UTNot Bool = Bool

data BinopTy =
  BTPlus
  | BTMinus
  | BTMult
  | BTAnd
  | BTOr
  | BTEq
  | BTLt
  | BTPair

data Binop a where
  BPlus :: Binop BTPlus
  BMinus :: Binop BTMinus
  BMult :: Binop BTMult
  BAnd :: Binop BTAnd
  BOr :: Binop BTOr
  BEq :: Binop BTEq
  BLt :: Binop BTLt
  BPair :: Binop BTPair
deriving instance Eq (Binop a)
deriving instance Show (Binop a)

type family BinopResTy (a :: BinopTy) (b :: *) (c :: *) where
  BinopResTy BTPlus Double Double = Double
  BinopResTy BTPlus Rational Rational = Rational
  BinopResTy BTMinus Double Double = Double
  BinopResTy BTMinus Rational Rational = Rational
  BinopResTy BTMult Double Double = Double
  BinopResTy BTMult Rational Rational = Rational
  BinopResTy BTAnd Bool Bool = Bool
  BinopResTy BTOr Bool Bool = Bool
  BinopResTy BTEq t t = Bool
  BinopResTy BTLt t t = Bool
  BinopResTy BTPair s t = (s, t)

data Exp a where
  EVal :: Val a -> Exp a
  EVar :: Name a -> Exp a
  EUnop :: (Typeable a, Show b, Typeable b) =>
           Unop a -> Exp b -> Exp (UnopResTy a b)
  EBinop :: (Typeable a, Show b, Typeable b) =>
            Binop a -> Exp b -> Exp b -> Exp (BinopResTy a b b)
  EList :: (Show a, Typeable a) => [Exp a] -> Exp [a]
  EUniform :: (Show a, Typeable a) => Exp [a] -> Exp (Tree a)
  EBernoulli :: Exp Rational -> Exp (Tree Bool)

instance Eq (Exp a) where
  EVal x == EVal y = x == y
  EVar x == EVar y = x == y
  EUnop u1 e1 == EUnop u2 e2 =
    case cast (u1, e1) of
      Just (u1', e1') -> u1' == u2 && e1' == e2
      _ -> False
  EBinop b e1 e2 == EBinop b' e1' e2' =
    case cast (b, e1, e2) of
      Just (b'', e1'', e2'') ->
        b'' == b' && e1'' == e1' && e2'' == e2'
      _ -> False
  EList l1 == EList l2 = all (uncurry (==)) $ zip l1 l2
  EUniform e1 == EUniform e2 = e1 == e2
  EBernoulli e1 == EBernoulli e2 = e1 == e2
  _ == _ = False

instance Show a => Show (Exp a) where
  show (EVal v) = "(EVal " ++ show v ++ ")"
  show (EVar x) = "(EVar " ++ show x ++ ")"
  show (EUnop u e) = "(EUnop " ++ show u ++ " " ++ show e ++ ")"
  show (EBinop b e1 e2) =
    "(EBinop " ++ show b ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"
  show (EList l) = "(EList " ++ show l ++ ")"
  show (EUniform e) = "(EUniform " ++ show e ++ ")"
  show (EBernoulli e) = "(EBernoulli " ++ show e ++ ")"


type Pattern = forall a. Tree a -> Tree a -> Tree a

data Com where 
  Skip :: Com
  Combine :: Pattern -> Com -> Com -> Com  
  Assign :: (Eq a, Show a, Typeable a) => Name a -> Exp a -> Com
  Seq :: Com -> Com -> Com
  Ite :: Exp Bool -> Com -> Com -> Com
  Sample :: (Eq a, Show a, Typeable a) => Name a -> Exp (Tree a) -> Com
  Observe :: Exp Bool -> Com
  -- Derived commands:
  Abort :: Com
  Flip :: Com -> Com -> Com
  While :: Exp Bool -> Com -> Com

instance Eq Com where
  Skip == Skip = True
  Abort == Abort = True
  Combine p c1 c2 == Combine p' c1' c2' = False -- ?
  Assign x e == Assign x' e' =
    case cast (x, e) of
      Just (x'', e'') -> x' == x'' && e' == e''
      Nothing -> False
  Seq c1 c2 == Seq c1' c2' = c1 == c1' && c2 == c2'
  Ite b c1 c2 == Ite b' c1' c2' = b == b' && c1 == c1' && c2 == c2'
  Sample x e == Sample x' e' =
    case cast (x, e) of
      Just (x'', e'') -> x' == x'' && e' == e''
      Nothing -> False
  Flip c1 c2 == Flip c1' c2' = c1 == c1' && c2 == c2'
  Observe b == Observe b' = b == b'
  While b c == While b' c' = b == b' && c == c'
  _ == _ = False

instance Show Com where
  show Skip = "Skip"
  show Abort = "Abort"
  show (Combine p c1 c2) =
    "(Combine " ++ show c1 ++ ", " ++ show c2 ++ ")"
  show (Assign x e) = "(Assign " ++ show x ++ ", " ++ show e ++ ")"
  show (Seq c1 c2) = "(Seq " ++ show c1 ++ ", " ++ show c2 ++ ")"
  show (Ite b c1 c2) =
    "(Ite " ++ show b ++ ", " ++ show c1 ++ ", " ++ show c2 ++ ")"
  show (Sample x e) = "(Sample " ++ show x ++ ", " ++ show e ++ ")"
  show (Flip c1 c2) = "(Flip " ++ show c1 ++ ", " ++ show c2 ++ ")"
  show (Observe b) = "(Observe " ++ show b ++ ")"
  show (While b c) = "(While " ++ show b ++ ", " ++ show c ++ ")"

-- | Interpreting commands as tree transformers.

-- Gensym counter
type InterpState = Int

type InterpM = State InterpState

freshLbl :: InterpM Int
freshLbl = do
  counter <- S.get
  put $ counter + 1
  return $ counter + 1

is_true :: Exp Bool -> St -> InterpM Bool
is_true e st = do
  b <- einterp e st
  case b of
    VBool b' -> return b'


einterp :: Typeable a => Exp a -> St -> InterpM (Val a)
einterp (EVal v) _ = return v
einterp (EVar x) st =
  case get x st of
    Just v -> return v
    Nothing ->
      let (x', proxy) = x
          ty = typeOf proxy in
        error $ "einterp: unbound variable: " ++ show x
        ++ " of type " ++ show ty ++ ".\nst: " ++ show st
einterp (EUnop u e) st = do
  v <- einterp e st
  case u of
    UNot ->
      case v of
        VBool b -> return $ VBool $ not b
        _ -> error "einterp: ill-typed UNot expression"
einterp (EBinop b e1 e2) st = do
  v1 <- einterp e1 st
  v2 <- einterp e2 st
  case b of
    BPlus ->
      case (v1, v2) of
        (VRational r1, VRational r2) -> return $ VRational $ r1 + r2
        (VFloat f1, VFloat f2) -> return $ VFloat $ f1 + f2
        _ -> error "einterp: ill-typed BPlus expression"
    BMinus ->
      case (v1, v2) of
        (VRational r1, VRational r2) -> return $ VRational $ r1 - r2
        (VFloat f1, VFloat f2) -> return $ VFloat $ f1 - f2
        _ -> error "einterp: ill-typed BMinus expression"
    BMult ->
      case (v1, v2) of
        (VRational r1, VRational r2) -> return $ VRational $ r1 * r2
        (VFloat f1, VFloat f2) -> return $ VFloat $ f1 * f2
        _ -> error "einterp: ill-typed BMult expression"
    BAnd ->
      case (v1, v2) of
        (VBool b1, VBool b2) -> return $ VBool $ b1 && b2
        _ -> error "einterp: ill-typed BAnd expression"
    BOr ->
      case (v1, v2) of
        (VBool b1, VBool b2) -> return $ VBool $ b1 || b2
        _ -> error "einterp: ill-typed BOr expression"
    BEq ->
      case (v1, v2) of
        (VRational r1, VRational r2) -> return $ VBool $ r1 == r2
        (VFloat f1, VFloat f2) -> return $ VBool $ f1 == f2
        (VBool b1, VBool b2) -> return $ VBool $ b1 == b2
        _ -> error "einterp: ill-typed BEq expression"
    BLt ->
      case (v1, v2) of
        (VRational r1, VRational r2) -> return $ VBool $ r1 < r2
        (VFloat f1, VFloat f2) -> return $ VBool $ f1 < f2
        (VBool b1, VBool b2) -> return $ VBool $ b1 < b2
        _ -> error "einterp: ill-typed BLt expression"
    BPair ->
      return $ VPair v1 v2
einterp (EList es) st = do
  vs <- mapM (flip einterp st) es
  return $ VList vs
einterp (EUniform e) st = do
  lbl <- freshLbl
  v <- einterp e st
  case v of
    VList vals -> return $ VTree $ uniform lbl $ EVal <$> vals
einterp (EBernoulli p) st = do
  lbl <- freshLbl
  v <- einterp p st
  case v of
    VRational p' -> return $ VTree $ EVal . VBool <$> bernoulli lbl p'


interp :: Com -> Tree (Int, St) -> InterpM (Tree (Int, St))
interp Skip t = return t
interp (Assign x e) t = do
  mapJoin t $ \(lbl, st) -> do
    v <- einterp e st
    return $ Leaf $ (lbl, upd x v st)
interp (Sample x e) t = do
  mapJoin t $ \(lbl, st) -> do
    v <- einterp e st
    case v of
      VTree t' ->
        mapM (\e' -> do
                 v' <- einterp e' st
                 return (lbl, upd x v' st)) t'

interp (Seq c1 c2) t = interp c1 t >>= interp c2

interp (Ite e c1 c2) t = do
  mapJoin t $ \(_, st) -> do
    fresh_lbl <- freshLbl
    b <- is_true e st
    set_label fresh_lbl <$>
      if b then
        interp c1 $ Leaf (fresh_lbl, st)
      else
        interp c2 $ Leaf (fresh_lbl, st)

-- interp (While e c) t =
--   mfix $ \t -> do
--   mapJoin t $ \(_, st) -> do
--     fresh_lbl <- freshLbl
--     b <- is_true e st
--     set_label fresh_lbl <$>
--       if b then
--         interp c $ Leaf (fresh_lbl, st)
--       else
--         return $ Leaf (fresh_lbl, st)

interp (While e c) t = interp (Ite e (Seq c (While e c)) Skip) t

interp (Observe e) t = do
  mapJoin t $ \(lbl, st) -> do
    b <- is_true e st
    if b then return $ Leaf (lbl, st) else return $ Hole 0

interp Abort t = interp (Observe $ EVal $ VBool False) t

runInterp :: Com -> Tree St -> Tree St
runInterp c t = fmap snd $ evalState (interp c $ fmap ((-1,)) t) (-1)

runInterp' :: Com -> Tree St
runInterp' c = set_label 0 $ runInterp c (Leaf empty)
