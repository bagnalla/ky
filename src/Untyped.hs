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
  deriving Show

data Unop =
  UNeg
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
data_of_exp = undefined

data_of_com :: Com a -> a
data_of_com = undefined

mkSeq :: [Com a] -> Com a
mkSeq [] = error "mkSeq: empty list"
mkSeq (c:[]) = c
mkSeq (c:cs) = CSeq (data_of_com c) c $ mkSeq cs
