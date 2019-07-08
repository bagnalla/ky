{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, GADTs, RankNTypes #-}
{-# LANGUAGE DataKinds, StandaloneDeriving, TypeFamilies #-}
{-# LANGUAGE TupleSections, TypeOperators #-}

module Lang where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State hiding (get)
import qualified Control.Monad.State as S (get)

import Data.Bifunctor (first)
import Data.Proxy
import Data.Typeable

import Distributions
import Tree hiding (mu)
import Util (debug, mapJoin)

-- This is weird but we have Show constraints all over the place for
-- debugging purposes, so we have a dummy instance for when the type
-- indices are arrow types.
instance Show (a -> b) where
  show f = "<function>"

mu :: (a -> a) -> a
mu f = f (mu f)

type Name a = (String, Proxy a)

data SomeName where
  SomeName :: forall a. Typeable a => Name a -> SomeName

instance Eq SomeName where
  SomeName x == SomeName y =
    case cast x of
      Just x' -> x' == y
      Nothing -> False

data Val a where
  VRational :: Rational -> Val Rational
  VInteger :: Integer -> Val Integer
  VFloat :: Double -> Val Double
  VBool :: Bool -> Val Bool
  VTree :: Tree (Exp a) -> Val (Tree a)
  VList :: [Val a] -> Val [a]
  VPair :: Val a -> Val b -> Val (a, b)
  VLam :: Show a => Name a -> Exp b -> Val (a -> b)
  VPrim :: (Show a, Typeable a) => (Val a -> InterpM (Exp b)) -> Val (a -> b)

data SomeVal where
  SomeVal :: forall a. (Show a, Typeable a) => Val a -> SomeVal
deriving instance Show SomeVal

-- data SomeNameVal where
--   SomeNameVal :: forall a. Typeable a => Name a -> Val a -> SomeNameVal

-- TODO: figure out how to support equality on trees, lists, and
-- pairs.
-- instance {-# INCOHERENT #-} Eq (Val a) where
-- instance {-# OVERLAPPING #-} Eq (Val a) where
instance Eq (Val a) where
  VRational x == VRational y = x == y
  VInteger x == VInteger y = x == y
  VFloat x == VFloat y = x == y
  VBool x == VBool y = x == y
  VTree _ == VTree _ = error "no equality on trees for now"
  VList _ == VList _ = error "no equality on lists for now"
  VPair _ _ == VPair _ _ = error "no equality on pairs for now"

-- -- instance {-# OVERLAPPING #-} Eq a => Eq (Val [a]) where
-- -- instance Eq a => Eq (Val [a]) where
-- instance {-# INCOHERENT #-} Eq a => Eq (Val [a]) where
--   VList l1 == VList l2 = l1 == l2

-- instance {-# OVERLAPPING #-} Eq a => Eq (Val (Tree a)) where
--   VTree x == VTree y = x == y

instance Show a => Show (Val a) where
  show (VRational v) = "VRational " ++ show v
  show (VInteger v) = "VInteger " ++ show v
  show (VFloat v) = "VFloat " ++ show v
  show (VBool b) = "VBool " ++ show b
  show (VTree _) = "VTree"
  show (VList _) = "VList"
  show (VPair _ _) = "VPair"

-- instance {-# OVERLAPPING #-} Show a => Show (Val (Tree a)) where
--   show (VTree d) = "(VTree " ++ show d ++ ")"

data SomeNameVal where
  SomeNameVal :: forall a. (Show a, Typeable a) =>
                 Name a -> Val a -> SomeNameVal

instance Eq SomeNameVal where
  SomeNameVal (x1, _) v1 == SomeNameVal (x2, _) v2 =
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

instance Show SomeNameVal where
  show (SomeNameVal (x, _) v) = "{" ++ show x ++ ", " ++ show v ++ "}"

type St = [SomeNameVal]
type Env = [SomeNameExp]

empty :: St
empty = []

nameEqT :: (Typeable a, Typeable b) => Name a -> Name b -> Maybe (a :~: b)
nameEqT _ _ = eqT

-- Replace old entries instead of shadowing.
upd :: (Show a, Typeable a) => Name a -> Val a -> St -> St
upd x v [] = [SomeNameVal x v]
upd x v (SomeNameVal x' v' : st) =
  if fst x == fst x' then
    case nameEqT x x' of
      Just Refl -> SomeNameVal x v : st
      Nothing -> error ""
  else
    SomeNameVal x' v' : upd x v st

get :: Typeable a => Name a -> St -> Maybe (Val a)
get _ [] = Nothing
get x (SomeNameVal y v : rest) =
  case cast (y, v) of
    Just (y', v') ->
      if x == y' then Just v' else get x rest
    _ -> get x rest

envGet :: Typeable a => Name a -> Env -> Maybe (Exp a)
envGet _ [] = Nothing
envGet x (SomeNameExp y v : rest) =
  case cast (y, v) of
    Just (y', v') ->
      if x == y' then Just v' else envGet x rest
    _ -> envGet x rest

data UnopTy =
  UTNot
  | UTFst
  | UTSnd

data Unop a where
  UNot :: Unop UTNot
  UFst :: Unop UTFst
  USnd :: Unop UTSnd
deriving instance Eq (Unop a)
deriving instance Show (Unop a)

type family UnopResTy (a :: UnopTy) (b :: *) where
  UnopResTy UTNot Bool = Bool
  UnopResTy UTFst (a, b) = a
  UnopResTy UTSnd (a, b) = b

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
  BinopResTy BTPlus  Double Double = Double
  BinopResTy BTMinus Double Double = Double
  BinopResTy BTMult  Double Double = Double
  BinopResTy BTPlus  Rational Rational = Rational
  BinopResTy BTMinus Rational Rational = Rational
  BinopResTy BTMult  Rational Rational = Rational
  BinopResTy BTPlus Integer Integer = Integer
  BinopResTy BTMinus Integer Integer = Integer
  BinopResTy BTMult Integer Integer = Integer
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
  EBinop :: (Typeable a, Show b, Typeable b, Show c, Typeable c) =>
            Binop a -> Exp b -> Exp c -> Exp (BinopResTy a b c)
  EPair :: (Show a, Typeable a, Show b, Typeable b) =>
           Exp a -> Exp b -> Exp (a, b)
  ENil :: (Show a, Typeable a) => Exp [a]
  ECons :: (Show a, Typeable a) => Exp a -> Exp [a] -> Exp [a]
  EDestruct :: (Show a, Typeable a, Show b) =>
               Exp [a] -> Exp b -> Exp (a -> [a] -> b) -> Exp b
  EUniform :: (Show a, Typeable a) => Exp [a] -> Exp (Tree a)
  ELam :: (Show a, Typeable a, Show b, Typeable b) =>
          Name a -> Exp b -> Exp (a -> b)
  EApp :: (Show a, Typeable a, Show b) => Exp (a -> b) -> Exp a -> Exp b
  ECom :: Show a => [SomeNameExp] -> Com (Exp a) -> Exp (Tree a)
  ECond :: (Show a, Typeable a) => Exp Bool -> Exp a -> Exp a -> Exp a
  EPrim :: (Show a, Typeable a) => (Val a -> InterpM (Exp b)) -> Exp (a -> b)

data SomeNameExp where
  SomeNameExp :: forall a. (Show a, Typeable a) =>
                 Name a -> Exp a -> SomeNameExp
deriving instance Show SomeNameExp

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
  ENil == ENil = True
  EUniform e1 == EUniform e2 = e1 == e2
  -- TODO finish
  _ == _ = False

instance Show a => Show (Exp a) where
  show (EVal v) = "(EVal " ++ show v ++ ")"
  show (EVar x) = "(EVar " ++ show x ++ ")"
  show (EUnop u e) = "(EUnop " ++ show u ++ " " ++ show e ++ ")"
  show (EBinop b e1 e2) =
    "(EBinop " ++ show b ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"
  show ENil = "ENil"
  show (ECons e1 e2) = "(ECons " ++ show e1 ++ " " ++ show e2 ++ ")"
  show (EDestruct l z f) = -- "(EDestruct " ++ show l ++ " " ++ show z ++ ")"
    "(EDestruct " ++ show l ++ " " ++ show z ++ " " ++ show f ++ ")"
  show (ELam x e) = "(ELam " ++ show x ++ " " ++ show e ++ ")"
  show (EApp e1 e2) = "(EApp " ++ show e1 ++ " " ++ show e2 ++ ")"
  show (ECom _ c) = "(ECom " ++ show c ++ ")"
  show (ECond b e1 e2) =
    "(ECond " ++ show b ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"
  show (EPrim f) = "EPrim"
  show (EUniform l) = "(EUniform " ++ show l ++ ")"


type Pattern = forall a. Tree a -> Tree a -> Tree a

data Com a where 
  Skip :: Com St
  Assign :: (Show a, Typeable a) => Name a -> Exp a -> Com St
  Seq :: Com St -> Com a -> Com a
  Ite :: Exp Bool -> Com a -> Com a -> Com a
  Sample :: (Show a, Typeable a) => Name a -> Exp (Tree a) -> Com St
  Observe :: Exp Bool -> Com St
  Return :: (Show a, Typeable a) => Exp a -> Com (Exp a)
  -- Derived commands:
  Abort :: Com St
  -- Flip :: Com -> Com -> Com
  While :: Exp Bool -> Com St -> Com St

instance Eq (Com a) where
  Skip == Skip = True
  Abort == Abort = True
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
  -- Flip c1 c2 == Flip c1' c2' = c1 == c1' && c2 == c2'
  Observe b == Observe b' = b == b'
  Return e1 == Return e2 = e1 == e2
  While b c == While b' c' = b == b' && c == c'
  _ == _ = False

instance Show a => Show (Com a) where
  show Skip = "Skip"
  show Abort = "Abort"
  show (Assign x e) = "(Assign " ++ show x ++ ", " ++ show e ++ ")"
  show (Seq c1 c2) = "(Seq " ++ show c1 ++ ", " ++ show c2 ++ ")"
  show (Ite b c1 c2) =
    "(Ite " ++ show b ++ ", " ++ show c1 ++ ", " ++ show c2 ++ ")"
  show (Sample x e) = "(Sample " ++ show x ++ ", " ++ show e ++ ")"
  show (Return e) = "(Return " ++ show e ++ ")"
  -- show (Flip c1 c2) = "(Flip " ++ show c1 ++ ", " ++ show c2 ++ ")"
  show (Observe b) = "(Observe " ++ show b ++ ")"
  show (While b c) = "(While " ++ show b ++ ", " ++ show c ++ ")"


-- | Capture-avoiding substitution.

-- Free variables of an expression.
fvs :: Typeable a => Exp a -> [SomeName]
fvs = go []
  where
    go :: Typeable a => [SomeName] -> Exp a -> [SomeName]
    go bound (EVar x) = if SomeName x `elem` bound then [] else [SomeName x]
    go bound (EUnop _ e) = go bound e
    go bound (EBinop _ e1 e2) = go bound e1 ++ go bound e2
    go bound (EPair e1 e2) = go bound e1 ++ go bound e2
    go bound (ECons e1 e2) = go bound e1 ++ go bound e2
    go bound (EDestruct l z f) = go bound l ++ go bound z ++ go bound f
    go bound (EApp e1 e2) = go bound e1 ++ go bound e2
    go bound (ELam x body) = go (SomeName x : bound) body
    go bound (ECom args com) =
      concatMap (\(SomeNameExp _ e) -> go bound e) args
    go bound (ECond b e1 e2) = go bound b ++ go bound e1 ++ go bound e2
    go _ _ = []

-- Substitution.
subst :: (Show a, Typeable a, Typeable b) => Name a -> Exp a -> Exp b -> Exp b
subst x e (EVar y) =
  case cast (x, e) of
    Just (x', e') -> if x' == y then e' else EVar y
    Nothing -> EVar y
subst x e (EUnop u e1) = EUnop u $ subst x e e1
subst x e (EBinop b e1 e2) = EBinop b (subst x e e1) (subst x e e2)
subst x e (EPair e1 e2) =
  EPair (subst x e e1) (subst x e e2)
subst x e (ECons e1 e2) = ECons (subst x e e1) (subst x e e2)
subst x e (EDestruct l z f) =
  EDestruct (subst x e l) (subst x e z) (subst x e f)
subst x e (EApp e1 e2) = EApp (subst x e e1) (subst x e e2)
subst x e (ELam y body) =
  if SomeName y `elem` fvs e then
    let y' = (fst y ++ "_", Proxy) in
      ELam y' $ subst x e (subst y (EVar y') body)
  else
    ELam y $
    if fst x == fst y then
      case nameEqT x y of
        Just Refl -> body
        Nothing -> error ""
    else
      subst x e body
subst x e (ECom args com) = ECom (SomeNameExp x e : args) com
subst x e (ECond b e1 e2) = ECond (subst x e b) (subst x e e1) (subst x e e2)
subst _ _ e = e


-- | Interpreter types. TODO: parameterize over these somehow.

-- Gensym counter
type InterpState = Int

type InterpM = ReaderT Env (State InterpState)


-- | The following is mostly just used for typechecking but is
-- included here to avoid cyclic imports.

data Type a where
  TBool :: Type Bool
  TFloat :: Type Double
  TRational :: Type Rational
  TInteger :: Type Integer
  TDist :: (Show a, Typeable a) => Type a -> Type (Tree a)
  TList :: (Show a, Typeable a) => Type a -> Type [a]
  TPair :: (Show a, Typeable a, Show b, Typeable b) =>
           Type a -> Type b -> Type (a, b)
  TArrow :: (Show a, Typeable a, Show b, Typeable b) =>
            Type a -> Type b -> Type (a -> b)
  TVar :: Type ()
  TSt :: Type St
  TExp :: (Show a, Typeable a) => Type a -> Type (Exp a)
deriving instance Show (Type a)

-- instance Eq (Type a) where
--   TBool == TBool = True
--   TFloat == TFloat = True
--   TRational == TRational = True
--   TDist t1 == TDist t2 = t1 == t2
--   TList t1 == TList t2 = t1 == t2
--   -- TODO: finish

data SomeTypeVal where
  SomeTypeVal :: forall a. (Show a, Typeable a) =>
                 Type a -> Val a -> SomeTypeVal
