{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, GADTs, RankNTypes #-}
{-# LANGUAGE DataKinds, StandaloneDeriving, TypeFamilies #-}

module Lang where

import Data.Proxy
import Data.Typeable hiding (typeOf)
import Distributions
import Tree hiding (mu)

mu :: (a -> a) -> a
mu f = f (mu f)

type Name a = (String, Proxy a)

data Val a where
  VRational :: Rational -> Val Rational
  VFloat :: Double -> Val Double
  VBool :: Bool -> Val Bool
  VTree :: Tree (Exp a) -> Val (Tree a)
  VList :: [Val a] -> Val [a]

instance Eq (Val a) where
  VRational x == VRational y = x == y
  VFloat x == VFloat y = x == y
  VBool x == VBool y = x == y
  
instance {-# OVERLAPPING #-} Eq a => Eq (Val (Tree a)) where
  VTree x == VTree y = x == y

instance Show a => Show (Val a) where
  show (VRational v) = "(VRational " ++ show v ++ ")"
  show (VFloat v) = "(VFloat " ++ show v ++ ")"
  show (VBool b) = "(VBool " ++ show b ++ ")"

instance {-# OVERLAPPING #-} Show a => Show (Val (Tree a)) where
  show (VTree d) = "(VTree " ++ show d ++ ")"

data StPkg where
  StPkg :: forall a. (Show a, Typeable a) => Name a -> Val a -> StPkg

instance Show StPkg where
  show (StPkg (x, _) v) = "(" ++ show x ++ ", " ++ show v ++ ")"

type St = [StPkg]

empty :: St
empty = []
  
upd :: (Show a, Typeable a) => Name a -> Val a -> St -> St
upd x v st = StPkg x v : st

get :: Typeable a => Name a -> St -> Maybe (Val a)
get _ [] = Nothing
get x (StPkg y v : rest) =
  case cast (y, v) of
    Just (y', v') -> if x == y' then v' else get x rest
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

data Binop a where
  BPlus :: Binop BTPlus
  BMinus :: Binop BTMinus
  BMult :: Binop BTMult
  BAnd :: Binop BTAnd
  BOr :: Binop BTOr
  BEq :: Binop BTEq
  BLt :: Binop BTLt
deriving instance Eq (Binop a)
deriving instance Show (Binop a)

type family BinopResTy (a :: BinopTy) (b :: *) where
  BinopResTy BTPlus Double = Double
  BinopResTy BTPlus Rational = Rational
  BinopResTy BTMinus Double = Double
  BinopResTy BTMinus Rational = Rational
  BinopResTy BTMult Double = Double
  BinopResTy BTMult Rational = Rational
  BinopResTy BTAnd Bool = Bool
  BinopResTy BTOr Bool = Bool
  BinopResTy BTEq t = Bool
  BinopResTy BTLt t = Bool

data Exp a where
  EVal :: Val a -> Exp a
  EVar :: Name a -> Exp a
  EUnop :: (Typeable a, Show b, Typeable b) =>
           Unop a -> Exp b -> Exp (UnopResTy a b)
  EBinop :: (Typeable a, Show b, Typeable b) =>
            Binop a -> Exp b -> Exp b -> Exp (BinopResTy a b)
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

einterp :: Typeable a => Exp a -> St -> Val a
einterp (EVal v) _ = v
einterp (EVar x) st =
  case get x st of
    Just v -> v
    Nothing -> error "einterp: EVar lookup fail"
einterp (EUnop u e) st =
  case u of
    UNot ->
      case einterp e st of
        VBool b -> VBool $ not b
        _ -> error "einterp: ill-typed UNot expression"
einterp (EBinop b e1 e2) st =
  case b of
    BPlus ->
      case (einterp e1 st, einterp e2 st) of
        (VRational r1, VRational r2) -> VRational $ r1 + r2
        (VFloat f1, VFloat f2) -> VFloat $ f1 + f2
        _ -> error "einterp: ill-typed BPlus expression"
    BMinus ->
      case (einterp e1 st, einterp e2 st) of
        (VRational r1, VRational r2) -> VRational $ r1 - r2
        (VFloat f1, VFloat f2) -> VFloat $ f1 - f2
        _ -> error "einterp: ill-typed BMinus expression"
    BMult ->
      case (einterp e1 st, einterp e2 st) of
        (VRational r1, VRational r2) -> VRational $ r1 * r2
        (VFloat f1, VFloat f2) -> VFloat $ f1 * f2
        _ -> error "einterp: ill-typed BMult expression"
    BAnd ->
      case (einterp e1 st, einterp e2 st) of
        (VBool b1, VBool b2) -> VBool $ b1 && b2
        _ -> error "einterp: ill-typed BAnd expression"
    BOr ->
      case (einterp e1 st, einterp e2 st) of
        (VBool b1, VBool b2) -> VBool $ b1 || b2
        _ -> error "einterp: ill-typed BOr expression"
    BEq ->
      case (einterp e1 st, einterp e2 st) of
        (VRational r1, VRational r2) -> VBool $ r1 == r2
        (VFloat f1, VFloat f2) -> VBool $ f1 == f2
        (VBool b1, VBool b2) -> VBool $ b1 == b2
        _ -> error "einterp: ill-typed BEq expression"
    BLt ->
      case (einterp e1 st, einterp e2 st) of
        (VRational r1, VRational r2) -> VBool $ r1 < r2
        (VFloat f1, VFloat f2) -> VBool $ f1 < f2
        (VBool b1, VBool b2) -> VBool $ b1 < b2
        _ -> error "einterp: ill-typed BLt expression"
einterp (EList l) st = VList $ flip einterp st <$> l  
einterp (EUniform e) st =
  let VList vals = einterp e st in
    VTree $ uniform $ EVal <$> vals
einterp (EBernoulli p) st =
  let VRational p' = einterp p st in
    VTree $ EVal . VBool <$> bernoulli p'

is_true :: Exp Bool -> St -> Bool
is_true e st = let VBool b = einterp e st in b


type Pattern = forall a. Tree a -> Tree a -> Tree a

data Com where 
  Skip :: Com
  Abort :: Com
  Combine :: Pattern -> Com -> Com -> Com  
  Assign :: (Eq a, Show a, Typeable a) => Name a -> Exp a -> Com
  Seq :: Com -> Com -> Com
  Ite :: Exp Bool -> Com -> Com -> Com
  Sample :: (Eq a, Show a, Typeable a) => Name a -> Exp (Tree a) -> Com
  -- Derived commands:
  Flip :: Com -> Com -> Com  
  Observe :: Exp Bool -> Com
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

interp :: Com -> Tree St -> Tree St
interp Skip t = t
interp Abort t = bind t (\_ -> Hole)
interp (Combine p c1 c2) t =
  t >>= \st -> p (interp c1 (Leaf st)) (interp c2 (Leaf st))
interp (Assign x e) t =
  t >>= \st -> Leaf $ upd x (einterp e st) st
interp (Seq c1 c2) t = interp c2 (interp c1 t)
interp (Ite e c1 c2) t =
  t >>= \st -> if is_true e st then interp c1 (Leaf st)
               else interp c2 (Leaf st)
interp (Sample x e) t =
  t >>= \st -> case einterp e st of
                 VTree t' -> fmap (\e' -> upd x (einterp e' st) st) t'

-- Derived commands:
interp (Flip c1 c2) t = interp (Combine Split c1 c2) t
interp (Observe e) t = interp (Ite e Skip Abort) t
interp (While e c) t =
  mu (\f t ->
        t >>= \st -> if is_true e st then f (interp c (Leaf st))
                     else Leaf st) t


-- We can interpret a command as just a tree by applying its
-- interpretation to the empty state (Leaf empty). Then we can take
-- the cotree generated by the tree.

interp' :: Com -> Tree St
interp' c = interp c (Leaf empty)
