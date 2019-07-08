module Untyped where

import Sexp
import Symtab (Id(..))

data Unop =
  UNot
  | UFst
  | USnd
  deriving Show

data Binop =
  BPlus
  | BMinus
  | BMult
  | BAnd
  | BOr
  | BEq
  | BNe
  | BLt
  | BLe
  | BGt
  | BGe
  | BCons
  | BPair
  deriving Show

data Literal =
  LRational Rational
  | LInteger Integer
  | LFloat Double
  | LBool Bool
  | LPair Literal Literal
  deriving Show

data Type =
  TRational
  | TInteger
  | TFloat
  | TBool
  | TPair Type Type
  | TList Type
  | TArrow Type Type
  -- | TFun [Type] Type
  deriving Show

data Exp a =
  ELit a Literal
  | EVar a Id
  | EUnop a Unop (Exp a)
  | EBinop a Binop (Exp a) (Exp a)
  -- | EFun a [(Id, Type)] (Exp a)
  | ELam a Id Type (Exp a)
  | ECall a (Exp a) [Exp a]
  | ENil a Type
  | EDestruct a (Exp a) (Exp a) (Exp a) -- list, nil -> b, head and tail -> b
  | ECond a (Exp a) (Exp a) (Exp a)
  deriving Show

data Function a =
  Function {
  -- name
  function_name :: Id
  -- return type
  , function_type :: Type
  -- names and types of formal parameters
  , function_args :: [(Id, Type)]
  -- body expression possibly with parameter variables appearing free
  , function_body :: Exp a }
  deriving Show

data Dist a =
  Dist {
  -- name
  dist_name :: Id
  -- domain of the distribution
  , dist_type :: Type
  -- names and types of arguments
  , dist_args :: [(Id, Type)]
  -- body command with parameter variables appearing free
  , dist_body :: Com a }
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
data_of_exp (ENil x _ ) = x

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

mkList :: a -> Type -> [Exp a] -> Exp a
mkList x ty [] = ENil x ty
mkList x ty (e:es) = EBinop x BCons e $ mkList x ty es


-- | ToSexp instances.

instance ToSexp Id where
  toSexp (Id x) = show x

instance ToSexp Unop where
  toSexp = show

instance ToSexp Binop where
  toSexp = show

instance ToSexp Literal where
  toSexp (LRational r) = "(LRational " ++ show r ++ ")"
  toSexp (LInteger i) = "(LInteger " ++ show i ++ ")"
  toSexp (LFloat f) = "(LFloat " ++ show f ++ ")"
  toSexp (LBool b) = "(LBool " ++ show b ++ ")"
  toSexp (LPair l1 l2) = "(LPair " ++ toSexp l1 ++ " " ++ toSexp l2 ++ ")"

instance ToSexp Type where
  toSexp TRational = "TRational"
  toSexp TInteger = "TInteger"
  toSexp TFloat = "TFloat"
  toSexp TBool = "TBool"
  toSexp (TPair s t) = "(TPair " ++ toSexp s ++ " " ++ toSexp t ++ ")"
  toSexp (TList t) = "(TList " ++ toSexp t ++ ")"
  toSexp (TArrow s t) = "(TArrow " ++ toSexp s ++ " " ++ toSexp t ++ ")"

instance ToSexp (Exp a) where
  toSexp (ELit _ lit) = "(ELiteral " ++ toSexp lit ++ ")"
  toSexp (EVar _ (Id x)) = "(EVar " ++ show x ++ ")"
  toSexp (EUnop _ u e) = "(EUnop " ++ toSexp u ++ " " ++ toSexp e ++ ")"
  toSexp (EBinop _ b e1 e2) =
    "(EBinop " ++ toSexp b ++ " " ++ toSexp e1 ++ " " ++ toSexp e2 ++ ")"
  toSexp (ELam _ (Id x) t e) =
    "(ELam " ++ show x ++ " " ++ toSexp t ++ " " ++ toSexp e ++ ")"
  toSexp (ECall _ e es) = "(ECall " ++ toSexp e ++ " " ++ toSexp es ++ ")"
  toSexp (ENil _ t) = "(ENil " ++ toSexp t ++ ")"
  toSexp (EDestruct _ e1 e2 e3) =
    "(EDestruct " ++ toSexp e1 ++ " " ++ toSexp e2 ++ " " ++ toSexp e2 ++ ")"
  toSexp (ECond _ e1 e2 e3) =
    "(ECond " ++ toSexp e1 ++ " " ++ toSexp e2 ++ " " ++ toSexp e2 ++ ")"

instance ToSexp (Com a) where
  toSexp (CSkip _) = "CSkip"
  toSexp (CAbort _) = "CAbort"
  toSexp (CAssign _ x e) = "(CAssign " ++ toSexp x ++ " " ++ toSexp e ++ ")"
  toSexp (CSample _ x e) = "(CSample " ++ toSexp x ++ " " ++ toSexp e ++ ")"
  toSexp (CSeq _ c1 c2) = "(CSeq " ++ toSexp c1 ++ " " ++ toSexp c2 ++ ")"
  toSexp (CIte _ e c1 c2) =
    "(CIte " ++ toSexp e ++ " " ++ toSexp c1 ++ " " ++ toSexp c2 ++ ")"
  toSexp (CFlip _ c1 c2) = "(CSeq " ++ toSexp c1 ++ " " ++ toSexp c2 ++ ")"
  toSexp (CObserve _ e) = "(CObserve " ++ toSexp e ++ ")"
  toSexp (CWhile _ e c) = "(CWhile " ++ toSexp e ++ " " ++ toSexp c ++ ")"

instance ToSexp (Function a) where
  toSexp (Function { function_name = Id nm
                   , function_type = ty
                   , function_args = args
                   , function_body = body }) =
    "(Function " ++ show nm ++ " " ++ toSexp ty ++ " " ++
    toSexp args ++ " " ++ toSexp body ++ ")"

instance ToSexp (Dist a) where
  toSexp (Dist { dist_name = Id nm
               , dist_type = ty
               , dist_args = args
               , dist_body = body }) =
    "(Dist " ++ show nm ++ " " ++ toSexp ty ++ " " ++
    toSexp args ++ " " ++ toSexp body ++ ")"
