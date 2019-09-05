{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, GADTs, RankNTypes #-}
{-# LANGUAGE DataKinds, StandaloneDeriving, TypeFamilies #-}
{-# LANGUAGE TupleSections, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

-- | GADT representation of program syntax. In addition to the regular
-- type index 'a' denoting the type of the value/expression/etc.,
-- there are two type parameters 'm' and 'g', both of kind '* ->
-- *'. 'g' is the type constructor for distributions, and 'm' a type
-- constructor for distribution constructing computations. 'g' should
-- generally be viewable as a probability monad (i.e., the Giry
-- monad). 'm' is only used for primitive functions (e.g., VPrim).

-- | For example, in the tree interpretation (see TreeInterp.hs), we
-- set g = Tree and m = InterpM (a combined reader and state monad
-- used for constructing trees). Also see IOInterp.hs for an example
-- with g = IO and m = Identity.

-- | The parser needn't be aware of our choice of 'm' and 'g', but
-- they must be chosen prior to typechecking.

module Lang where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State hiding (get)
import qualified Control.Monad.State as S (get)

import Data.Bifunctor (first)
import Data.Proxy
import Data.Typeable

import Classes
import Distributions
import Symtab (Id(..))
import Util (debug, mapJoin)

-- Dummy instances for arrow type indices.
instance Eq (a -> b) where
  _ == _ = False
instance Show (a -> b) where
  show _ = "<function>"

type Name a = (String, Proxy a)

data SomeName where
  SomeName :: forall a. Typeable a => Name a -> SomeName

instance Eq SomeName where
  SomeName x == SomeName y =
    case cast x of
      Just x' -> x' == y
      Nothing -> False

id_of_name :: SomeName -> Id
id_of_name (SomeName (x, _)) = Id x

data Val (m :: * -> *) (g :: * -> *) (a :: *) where
  VRational :: Rational -> Val m g Rational
  VInteger  :: Integer -> Val m g Integer
  VFloat    :: Double -> Val m g Double
  VBool     :: Bool -> Val m g Bool
  VDist     :: (Eq a, Show a) => g (Exp m g a) -> Val m g (g a)
  VNil      :: (Eq a, Show a) => Val m g [a]
  VCons     :: (Eq a, Show a, Typeable a) =>
               Val m g a -> Val m g [a] -> Val m g [a]
  VPair     :: (Eq a, Show a, Eq b, Show b) =>
               Val m g a -> Val m g b -> Val m g (a, b)
  VLam      :: (Show a, Typeable a, Eq b, Show b) =>
               Name a -> Exp m g b -> Val m g (a -> b)
  VPrim     :: (Show a, Typeable a) =>
               (Val m g a -> m (Exp m g b)) -> Val m g (a -> b)
  -- Experimental/unused. Polymorphic primitives.
  -- VPrim' :: (Show c, Typeable c) =>
  --           (forall a b. Val m g a -> m (Exp m g b)) -> Val m g (c -> d)

-- deriving instance Typeable Val

data SomeVal m g where
  SomeVal :: forall m g a. (Show a, Typeable a) => Val m g a -> SomeVal m g
deriving instance Show (SomeVal m g)

instance Eq (Val m g a) where
  VRational x == VRational y = x == y
  VInteger x == VInteger y = x == y
  VFloat x == VFloat y = x == y
  VBool x == VBool y = x == y
  VDist _ == VDist _ = error "no equality on dists"
  -- VDist x == VDist y = x == y
  -- VList x == VList y = x == y
  VNil == VNil = True
  VPair x y == VPair x' y' = x == x' && y == y'
  VLam x e == VLam x' e' =
    if fst x == fst x' then
      case nameEqT x x' of
        Just Refl -> e == e'
        Nothing -> False
    else False
  VPrim _ == VPrim _ = error "no equality on primitives for now"

instance Show a => Show (Val m g a) where
  show (VRational v) = "VRational " ++ show v
  show (VInteger v) = "VInteger " ++ show v
  show (VFloat v) = "VFloat " ++ show v
  show (VBool b) = "VBool " ++ show b
  -- show (VDist t) = "VDist " ++ show t
  show (VDist _) = "VDist"
  -- show (VList l) = "VList " ++ show l
  show VNil = "VNil"
  show (VCons hd tl) = "VCons " ++ show hd ++ " " ++ show tl
  show (VPair x y) = "VPair {" ++ show x ++ ", " ++ show y ++ "}"
  show (VLam x e) = "VLam " ++ show x ++ " " ++ show e
  show (VPrim f) = "VPrim " ++ show f

data SomeNameVal m g where
  SomeNameVal :: forall m g a. (Typeable m, Typeable g, Show a, Typeable a) =>
                 Name a -> Val m g a -> SomeNameVal m g

instance Eq (SomeNameVal m g) where
  SomeNameVal (x1, _) v1 == SomeNameVal (x2, _) v2 =
    case cast v1 of
      Just v1' ->
        x1 == x2 && v1' == v2
      Nothing -> False

instance Show (SomeNameVal m g) where
  show (SomeNameVal (x, _) v) = "{" ++ show x ++ ", " ++ show v ++ "}"

type St m g = [SomeNameVal m g]
type Env m g = [SomeNameExp m g]

empty :: St m g
empty = []

nameEqT :: (Typeable a, Typeable b) => Name a -> Name b -> Maybe (a :~: b)
nameEqT _ _ = eqT

-- Replace old entries instead of shadowing.
upd :: (Typeable m, Typeable g, Show a, Typeable a) =>
       Name a -> Val m g a -> St m g -> St m g
upd x v [] = [SomeNameVal x v]
upd x v (SomeNameVal x' v' : st) =
  if fst x == fst x' then
    case nameEqT x x' of
      Just Refl -> SomeNameVal x v : st
      Nothing -> error ""
  else
    SomeNameVal x' v' : upd x v st

get :: (Typeable m, Typeable g, Typeable a) =>
       Name a -> St m g -> Maybe (Val m g a)
get _ [] = Nothing
get x (SomeNameVal y v : rest) =
  case cast (y, v) of
    Just (y', v') ->
      if x == y' then Just v' else get x rest
    _ -> get x rest

envGet :: (Typeable m, Typeable g, Typeable a) =>
          Name a -> Env m g -> Maybe (Exp m g a)
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

data Binop a where
  BPlus  :: Binop BTPlus
  BMinus :: Binop BTMinus
  BMult  :: Binop BTMult
  BAnd   :: Binop BTAnd
  BOr    :: Binop BTOr
  BEq    :: Binop BTEq
  BLt    :: Binop BTLt
deriving instance Eq (Binop a)
deriving instance Show (Binop a)

type family BinopResTy (a :: BinopTy) (b :: *) (c :: *) where
  BinopResTy BTPlus  Double   Double   = Double
  BinopResTy BTMinus Double   Double   = Double
  BinopResTy BTMult  Double   Double   = Double
  BinopResTy BTPlus  Rational Rational = Rational
  BinopResTy BTMinus Rational Rational = Rational
  BinopResTy BTMult  Rational Rational = Rational
  BinopResTy BTPlus  Integer  Integer  = Integer
  BinopResTy BTMinus Integer  Integer  = Integer
  BinopResTy BTMult  Integer  Integer  = Integer
  BinopResTy BTAnd   Bool     Bool     = Bool
  BinopResTy BTOr    Bool     Bool     = Bool
  BinopResTy BTEq    t        t        = Bool
  BinopResTy BTLt    t        t        = Bool

data Exp (m :: * -> *) (g :: * -> *) (a :: *) where
  EVal      :: Val m g a -> Exp m g a
  EVar      :: Name a -> Exp m g a
  EUnop     :: (Typeable m, Typeable g, Typeable a, Show b, Typeable b) =>
               Unop a -> Exp m g b -> Exp m g (UnopResTy a b)
  EBinop    :: (Typeable m, Typeable g, Typeable a, Eq b, Show b, Typeable b) =>
               Binop a -> Exp m g b -> Exp m g b -> Exp m g (BinopResTy a b b)
  EPair     :: (Eq a, Show a, Typeable a, Eq b, Show b, Typeable b) =>
               Exp m g a -> Exp m g b -> Exp m g (a, b)
  ENil      :: (Eq a, Show a, Typeable a) => Exp m g [a]
  ECons     :: (Eq a, Show a, Typeable a) =>
               Exp m g a -> Exp m g [a] -> Exp m g [a]
  EDestruct :: (Show a, Typeable a, Show b) =>
               Exp m g [a] -> Exp m g b -> Exp m g (a -> [a] -> b) -> Exp m g b
  EUniform  :: (Eq a, Show a, Typeable a) => Exp m g [a] -> Exp m g (g a)
  ELam      :: (Show a, Typeable a, Eq b, Show b, Typeable b) =>
               Name a -> Exp m g b -> Exp m g (a -> b)
  EApp      :: (Show a, Typeable a, Show b) =>
               Exp m g (a -> b) -> Exp m g a -> Exp m g b
  ECom      :: (Eq a, Show a) =>
               [SomeNameExp m g] -> Com m g (Exp m g a) -> Exp m g (g a)
  ECond     :: (Show a, Typeable a) =>
               Exp m g Bool -> Exp m g a -> Exp m g a -> Exp m g a
  EPrim     :: (Show a, Typeable a) =>
               (Val m g a -> m (Exp m g b)) -> Exp m g (a -> b)

data SomeExp m g where
  SomeExp :: forall m g a. (Show a, Typeable a) => Exp m g a -> SomeExp m g
deriving instance Show (SomeExp m g)

data SomeNameExp m g where
  SomeNameExp :: forall m g a. (Typeable g, Show a, Typeable a) =>
                 Name a -> Exp m g a -> SomeNameExp m g
deriving instance Show (SomeNameExp m g)

instance Eq (Exp m g a) where
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

-- instance Show a => Show (Exp m g a) where
--   show (EVal v) = "(EVal " ++ show v ++ ")"
--   show (EVar x) = "(EVar " ++ show x ++ ")"
--   show (EUnop u e) = "(EUnop " ++ show u ++ " " ++ show e ++ ")"
--   show (EBinop b e1 e2) =
--     "(EBinop " ++ show b ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"
--   show ENil = "ENil"
--   show (ECons e1 e2) = "(ECons " ++ show e1 ++ " " ++ show e2 ++ ")"
--   show (EDestruct l z f) = -- "(EDestruct " ++ show l ++ " " ++ show z ++ ")"
--     "(EDestruct " ++ show l ++ " " ++ show z ++ " " ++ show f ++ ")"
--   show (ELam x e) = "(ELam " ++ show x ++ " " ++ show e ++ ")"
--   show (EApp e1 e2) = "(EApp " ++ show e1 ++ " " ++ show e2 ++ ")"
--   show (ECom _ c) = "(ECom " ++ show c ++ ")"
--   show (ECond b e1 e2) =
--     "(ECond " ++ show b ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"
--   show (EPrim f) = "EPrim"
--   show (EUniform l) = "(EUniform " ++ show l ++ ")"

instance Show a => Show (Exp m g a) where
  show (EVal v) = "EVal " ++ show v
  show (EVar x) = "EVar " ++ show x
  show (EUnop u e) = "EUnop " ++ show u ++ " " ++ show e
  show (EBinop b e1 e2) =
    "EBinop " ++ show b ++ " " ++ show e1 ++ " " ++ show e2
  show ENil = "ENil"
  show (ECons e1 e2) = "ECons " ++ show e1 ++ " " ++ show e2
  show (EDestruct l z f) = -- "(EDestruct " ++ show l ++ " " ++ show z ++ ")"
    "EDestruct " ++ show l ++ " " ++ show z ++ " " ++ show f
  show (ELam x e) = "ELam " ++ show x ++ " " ++ show e
  show (EApp e1 e2) = "EApp " ++ show e1 ++ " " ++ show e2
  show (ECom _ c) = "ECom " ++ show c
  show (ECond b e1 e2) =
    "ECond " ++ show b ++ " " ++ show e1 ++ " " ++ show e2
  show (EPrim f) = "EPrim"
  show (EUniform l) = "EUniform " ++ show l


data Com (m :: * -> *) (g :: * -> *) (a :: *) where
  Skip    :: Com m g (St m g)
  Assign  :: (Typeable m, Typeable g, Show a, Typeable a) =>
             Name a -> Exp m g a -> Com m g (St m g)
  Seq     :: Com m g (St m g) -> Com m g a -> Com m g a
  Ite     :: Exp m g Bool -> Com m g a -> Com m g a -> Com m g a
  Sample  :: (Typeable m, Typeable g, Show (g a), Show a, Typeable a) =>
             Name a -> Exp m g (g a) -> Com m g (St m g)
  Observe :: Exp m g Bool -> Com m g (St m g)
  Return  :: (Show a, Typeable a) => Exp m g a -> Com m g (Exp m g a)
  While   :: Exp m g Bool -> Com m g (St m g) -> Com m g (St m g)
  -- Derived commands:
  Abort   :: Com m g (St m g)

instance Eq (Com m g a) where
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

instance Show a => Show (Com m g a) where
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

-- Decompose a sequence of commands into a list of commands.
com_list :: Com m g a -> ([Com m g (St m g)], Com m g a)
com_list (Seq c1 c2) = (cs ++ [c], c2)
  where (cs, c) = com_list c1
com_list c = ([], c)

-- | Capture-avoiding substitution.

-- Free variables of an expression.
fvs :: Typeable a => Exp m g a -> [SomeName]
fvs = go []
  where
    go :: Typeable a => [SomeName] -> Exp m g a -> [SomeName]
    go bound (EVar x) = if SomeName x `elem` bound then [] else [SomeName x]
    go bound (EUnop _ e) = go bound e
    go bound (EBinop _ e1 e2) = go bound e1 ++ go bound e2
    go bound (ECons e1 e2) = go bound e1 ++ go bound e2
    go bound (EDestruct l z f) = go bound l ++ go bound z ++ go bound f
    go bound (EApp e1 e2) = go bound e1 ++ go bound e2
    go bound (ELam x body) = go (SomeName x : bound) body
    go bound (ECom args com) =
      concatMap (\(SomeNameExp _ e) -> go bound e) args
    go bound (ECond b e1 e2) = go bound b ++ go bound e1 ++ go bound e2
    go _ _ = []

-- Substitution.
subst :: (Typeable m, Typeable g, Show a, Typeable a, Typeable b) =>
         Name a -> Exp m g a -> Exp m g b -> Exp m g b
subst x e (EVar y) =
  case cast (x, e) of
    Just (x', e') -> if x' == y then e' else EVar y
    Nothing -> EVar y
subst x e (EUnop u e1) = EUnop u $ subst x e e1
subst x e (EBinop b e1 e2) = EBinop b (subst x e e1) (subst x e e2)
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


-- | The following is mostly just used for typechecking but is
-- included here to avoid cyclic imports.

data Type m g a where
  TBool     :: Type m g Bool
  TFloat    :: Type m g Double
  TRational :: Type m g Rational
  TInteger  :: Type m g Integer
  TDist     :: (Eq a, Show a, Typeable a) => Type m g a -> Type m g (g a)
  TList     :: (Eq a, Show a, Typeable a) => Type m g a -> Type m g [a]
  TPair     :: (Eq a, Show a, Typeable a, Eq b, Show b, Typeable b) =>
               Type m g a -> Type m g b -> Type m g (a, b)
  TArrow    :: (Show a, Typeable a, Eq b, Show b, Typeable b) =>
               Type m g a -> Type m g b -> Type m g (a -> b)
  TVar      :: Type m g ()
  TSt       :: Type m g (St m g)
  TExp      :: (Eq a, Show a, Typeable a) => Type m g a -> Type m g (Exp m g a)
deriving instance Show (Type m g a)

-- instance Eq (Type a) where
--   TBool == TBool = True
--   TFloat == TFloat = True
--   TRational == TRational = True
--   TDist t1 == TDist t2 = t1 == t2
--   TList t1 == TList t2 = t1 == t2
--   -- TODO: finish

data SomeTypeVal m g where
  SomeTypeVal :: forall m g a. (Typeable m, AllF g, Eq a, Show a, Typeable a) =>
                 Type m g a -> Val m g a -> SomeTypeVal m g


eval_val :: Show a => Val m g a -> a
eval_val (VRational r) = r
eval_val (VInteger i) = i
eval_val (VFloat f) = f
eval_val (VBool b) = b
eval_val VNil = []
eval_val (VCons hd tl) = eval_val hd : eval_val tl
eval_val (VPair x y) = (eval_val x, eval_val y)
eval_val v = error $ "eval_val: unsupported value: " ++ show v

-- List value lookup by index.
vlist_nth :: Int -> Val m g [a] -> Val m g a
vlist_nth _ VNil = error "vlist_nth: empty list"
vlist_nth n (VCons hd tl)
  | n < 0 = error "vlist_nth: negative index"
  | n == 0 = hd
  | otherwise = vlist_nth (n-1) tl

vlist_length :: Val m g [a] -> Int
vlist_length VNil = 0
vlist_length (VCons _ tl) = 1 + vlist_length tl

vlist_list :: Val m g [a] -> [Val m g a]
vlist_list VNil = []
vlist_list (VCons x xs) = x : vlist_list xs


------------------------------------------------------------------------
-- | Class of representations as defined by the type constructors 'm'
-- and 'g', each with a set of supported primitives and a way of
-- interpreting commands in that representation.
class (Typeable m, AllF g) => Repr m g | g -> m where
  primitives :: [(String, SomeTypeVal m g)]
  interp :: (Eq a, Show a) => Env m g -> Com m g a -> g a

-- Initial environment containing primitives.
initEnv :: Repr m g => Env m g
initEnv = (\(x, SomeTypeVal t v) ->
             SomeNameExp (x, Proxy) (EVal v)) <$> primitives
