{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, GADTs, RankNTypes #-}

module Lang where

-- import Data.Proxy
import Data.Typeable
import Distributions
import Tree hiding (mu)

mu :: (a -> a) -> a
mu f = f (mu f)

-- type Name a = (String, Proxy a)
type Name = String

data Val a where
  VRational :: Rational -> Val Rational
  VFloat :: Float -> Val Float
  VBool :: Bool -> Val Bool
  VTree :: Tree (Exp a) -> Val (Tree a)

instance Eq a => Eq (Val a) where
  VRational x == VRational y = x == y
  VFloat x == VFloat y = x == y
  VBool x == VBool y = x == y
  
instance {-# OVERLAPPING #-} Eq a => Eq (Val (Tree a)) where
  VTree x == VTree y = x == y
  
data ValPkg where
  ValPkg :: forall a. Typeable a => Val a -> ValPkg

instance Show a => Show (Val a) where
  show (VRational v) = "(VRational " ++ show v ++ ")"
  show (VFloat v) = "(VFloat " ++ show v ++ ")"
  show (VBool b) = "(VBool " ++ show b ++ ")"

instance {-# OVERLAPPING #-} Show a => Show (Val (Tree a)) where
  show (VTree d) = "(VTree " ++ show d ++ ")"

type St = [(Name, ValPkg)]

empty :: St
empty = []
  
upd :: Typeable a => Name -> Val a -> St -> St
upd x v st = (x, ValPkg v) : st

get :: Name -> St -> ValPkg
get x [] = error $ "name '" ++ show x ++ "' not bound"
get x ((y, v) : rest) = if x==y then v else get x rest

data Exp a where
  EVal :: Val a -> Exp a
  EVar :: Name -> Exp a
  ENeg :: Exp Float -> Exp Float
  EEq :: Exp Float -> Exp Float -> Exp Bool
  ELt :: Exp Float -> Exp Float -> Exp Bool
  EPlus :: Exp Float -> Exp Float -> Exp Float
  EUniform :: Typeable a => [Exp a] -> Exp (Tree a)
  EBernoulli :: Exp Rational -> Exp (Tree Bool)

instance Eq a => Eq (Exp a) where
  EVal x == EVal y = x == y
  EVar x == EVar y = x == y
  EEq e1 e2 == EEq e1' e2' = e1 == e1' && e2 == e2'
  ELt e1 e2 == ELt e1' e2' = e1 == e1' && e2 == e2'
  EPlus e1 e2 == EPlus e1' e2' = e1 == e1' && e2 == e2'

instance Show a => Show (Exp a) where
  show (EVal v) = "(EVal " ++ show v ++ ")"
  show (EVar x) = "(EVar " ++ show x ++ ")"
  show (EEq e1 e2) = "(EEq " ++ show e1 ++ ", " ++ show e2 ++ ")"
  show (ELt e1 e2) = "(ELt " ++ show e1 ++ ", " ++ show e2 ++ ")"
  show (EPlus e1 e2) = "(EPlus " ++ show e1 ++ ", " ++ show e2 ++ ")"

einterp :: Typeable a => Exp a -> St -> Val a
einterp (EVal v) _ = v
einterp (EVar x) st =
  case get x st of
    ValPkg v ->
      case cast v of
        Just v' -> v'
        Nothing -> error "EVar lookup type mismatch"
einterp (EEq e1 e2) st =
  case (einterp e1 st, einterp e2 st) of
    (VFloat r1, VFloat r2) -> VBool (r1 == r2)
einterp (ELt e1 e2) st =
  case (einterp e1 st, einterp e2 st) of
    (VFloat r1, VFloat r2) -> VBool (r1 < r2)
einterp (EPlus e1 e2) st =
  case (einterp e1 st, einterp e2 st) of
    (VFloat r1, VFloat r2) -> VFloat (r1 + r2)
einterp (EUniform es) st =
  VTree $ uniform $ EVal . flip einterp st <$> es
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
  Assign :: (Eq a, Show a, Typeable a) => Name -> Exp a -> Com
  Seq :: Com -> Com -> Com
  Ite :: Exp Bool -> Com -> Com -> Com
  Sample :: (Eq a, Show a, Typeable a) => Name -> Exp (Tree a) -> Com
  -- Derived commands:
  Flip :: Com -> Com -> Com  
  Observe :: Exp Bool -> Com
  While :: Exp Bool -> Com -> Com

instance Eq Com where
  Skip == Skip = True
  Abort == Abort = True
  Combine p c1 c2 == Combine p' c1' c2' = False -- ?
  Assign x e == Assign x' e' = x == x' && case cast e of
                                            Just e'' -> e' == e''
                                            Nothing -> False
  Seq c1 c2 == Seq c1' c2' = c1 == c1' && c2 == c2'
  Ite b c1 c2 == Ite b' c1' c2' = b == b' && c1 == c1' && c2 == c2'
  Sample x e == Sample x' e' = x == x' && case cast e of
                                            Just e'' -> e' == e''
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
