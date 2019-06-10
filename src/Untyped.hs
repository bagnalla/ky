module Untyped where

import Symtab (Id)

data Binop =
  BPlus
  | BMinus
  | BMult
  | BAnd
  | BOr
  | BEq
  | BLt
  | BCons
  deriving Show

data Unop =
  UNot
  deriving Show

data Lit =
  LRational Rational
  | LFloat Double
  | LBool Bool
  deriving Show

data Exp a =
  ELit a Lit
  | EVar a Id
  | EUnop a Unop (Exp a)
  | EBinop a Binop (Exp a) (Exp a)
  | ECall a (Exp a) [Exp a]
  | ENil a
  deriving Show

data Com a = 
  CSkip a
  | CAbort a
  -- Skip patterns for now..
  -- | Combine Pattern Com Com
  | CAssign a Id (Exp a)
  | CSample a Id (Exp a)
  | CSeq a (Com a) (Com a)
  | CIte a (Exp a) (Com a) (Maybe (Com a))
  -- Derived commands:
  | CFlip a (Com a) (Com a)
  | CObserve a (Exp a)
  | CWhile a (Exp a) (Com a)
  deriving Show

data_of_exp :: Exp a -> a
data_of_exp (ELit x _) = x
data_of_exp (EVar x _) = x
data_of_exp (EUnop x _ _) = x
data_of_exp (EBinop x _ _ _) = x
data_of_exp (ECall x _ _) = x
data_of_exp (ENil x) = x

data_of_com :: Com a -> a
data_of_com (CSkip x) = x
data_of_com (CAbort x) = x
data_of_com (CAssign x _ _) = x
data_of_com (CSample x _ _) = x
data_of_com (CSeq x _ _) = x
data_of_com (CIte x _ _ _) = x
data_of_com (CFlip x _ _) = x
data_of_com (CObserve x _) = x
data_of_com (CWhile x _ _) = x

mkSeq :: [Com a] -> Com a
mkSeq [] = error "mkSeq: empty list"
mkSeq (c:[]) = c
mkSeq (c:cs) = CSeq (data_of_com c) c $ mkSeq cs

mkList :: a -> [Exp a] -> Exp a
mkList x [] = ENil x
mkList x (e:es) = EBinop x BCons e $ mkList x es
