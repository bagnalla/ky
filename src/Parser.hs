module Parser where

import Control.Monad (void)

import Control.Monad.Combinators.Expr -- from parser-combinators
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe (fromMaybe)
import Data.Ratio
import Data.Set (singleton)
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Untyped
import Symtab (Id(..))
import Token
import Util (debug)


parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

commaSep :: Parser a -> Parser [a]
commaSep p = p `sepBy` symbol ","

commaSep1 :: Parser a -> Parser [a]
commaSep1 p = p `sepBy1` symbol ","

bool :: Parser Bool
bool = choice
  [ keyword "true" >> return True
  , keyword "false" >> return False ]

rational :: Parser Rational
rational = do
  num <- integer
  symbol "/"
  denom <- integer
  return $ num % denom

literal :: Parser Literal
literal = choice
  [ LBool <$> bool
  , LFloat <$> try float
  , LRational <$> try rational
  -- , LFloat . fromInteger <$> integer ]
  , LInteger . fromInteger <$> integer ]

call :: SourcePos -> Parser (Exp SourcePos)
call pos = do
  f <- EVar pos <$> ident
  args <- parens $ commaSep expr
  return $ ECall pos f args

cond :: SourcePos -> Parser (Exp SourcePos)
cond pos = do
  symbol "if"
  b <- expr
  symbol "then"
  e1 <- expr
  symbol "else"
  e2 <- expr
  return $ ECond pos b e1 e2

list :: SourcePos -> Parser (Exp SourcePos)
list pos = do
  l <- brackets (commaSep expr)
  symbol ":"
  t <- ty
  return $ mkList pos t l

nil :: SourcePos -> Parser (Exp SourcePos)
nil pos = do
  symbol "nil"
  symbol ":"
  t <- ty
  return $ ENil pos t

pair :: SourcePos -> Parser (Exp SourcePos)
pair pos = do
  symbol "("
  e1 <- expr
  symbol ","
  e2 <- expr
  symbol ")"
  return $ EBinop pos BPair e1 e2

-- destruct :: SourcePos -> Parser (Exp SourcePos)
-- destruct pos = do
--   symbol "destruct"
--   l <- expr
--   z <- expr
--   f <- expr
--   symbol "end"
--   return $ EDestruct pos l z f

destruct :: SourcePos -> Parser (Exp SourcePos)
destruct pos = do
  symbol "destruct"
  symbol "("
  l <- expr
  symbol ","
  z <- expr
  symbol ","
  f <- expr
  symbol ")"
  return $ EDestruct pos l z f

fst_proj :: SourcePos -> Parser (Exp SourcePos)
fst_proj pos = do
  symbol "fst"
  symbol "("
  p <- expr
  symbol ")"
  return $ EUnop pos UFst p

snd_proj :: SourcePos -> Parser (Exp SourcePos)
snd_proj pos = do
  symbol "snd"
  symbol "("
  p <- expr
  symbol ")"
  return $ EUnop pos USnd p

lam :: SourcePos -> Parser (Exp SourcePos)
lam pos = do
  symbol "\\"
  x <- ident
  symbol ":"
  t <- ty
  symbol "."
  e <- expr
  return $ ELam pos x t e

term :: Parser (Exp SourcePos)
term = do
  pos <- getSourcePos
  choice
    [ nil pos
    , list pos
    , destruct pos
    , fst_proj pos
    , snd_proj pos
    , try $ pair pos
    , try $ call pos
    , try $ cond pos
    , lam pos
    , ELit pos <$> literal
    , EVar pos <$> ident
    , parens expr ]

binary :: String ->
          (SourcePos -> Exp SourcePos ->
           Exp SourcePos -> Exp SourcePos) ->
          Operator Parser (Exp SourcePos)
binary name f = InfixL $ do
  symbol name
  s <- getSourcePos
  return $ f s

binaryNoAssoc :: String ->
                 (SourcePos -> Exp SourcePos ->
                  Exp SourcePos -> Exp SourcePos) ->
                 Operator Parser (Exp SourcePos)
binaryNoAssoc name f = InfixN $ do
  symbol name
  s <- getSourcePos
  return $ f s

prefix, postfix :: String ->
                   (SourcePos -> Exp SourcePos ->
                    Exp SourcePos) ->
                   Operator Parser (Exp SourcePos)
prefix name f = Prefix $ do
  symbol name
  s <- getSourcePos
  return $ f s
postfix name f = Postfix $ do
  symbol name
  s <- getSourcePos
  return $ f s

-- -- Helper for single-character operators that overlap with others. For
-- -- example, we must use this for the regular addition operator '+' or
-- -- else '+=' won't work.
-- op' :: Binop -> String -> [Char] -> Operator Parser (Exp SourcePos)
-- op' b s cs = InfixL $ getSourcePos >>= \pos -> EBinop pos b <$ op s cs

op n ms =
  (lexeme . try) (string n <* notFollowedBy (choice (char <$> ms)))

operatorTable :: [[Operator Parser (Exp SourcePos)]]
operatorTable =
  [ [ binary "*" $ flip EBinop BMult ],
    [ binary "+" $ flip EBinop BPlus
    , binary "-" $ flip EBinop BMinus ],
    [ binary "=" $ flip EBinop BEq
    , InfixN $ getSourcePos >>= \s -> EBinop s BLt <$ op "<" ['=']
    , InfixN $ getSourcePos >>= \s -> EBinop s BGt <$ op ">" ['=']
    , binary "<=" $ flip EBinop BLe
    , binary ">=" $ flip EBinop BGe
    , binary "<>" $ flip EBinop BNe ],
    [ prefix "~" $ flip EUnop UNot ],
    [ binary "&" $ flip EBinop BAnd
    , binary "|" $ flip EBinop BOr ],
    [ binary "::" $ flip EBinop BCons ] ]

expr :: Parser (Exp SourcePos)
expr = makeExprParser term operatorTable

cSkip :: SourcePos -> Parser (Com SourcePos)
cSkip pos = keyword "skip" >> return (CSkip pos)

cAbort :: SourcePos -> Parser (Com SourcePos)
cAbort pos = keyword "abort" >> return (CAbort pos)

cAssign :: SourcePos -> Parser (Com SourcePos)
cAssign pos = do
  x <- ident
  symbol "<-"
  e <- expr
  return $ CAssign pos x e

cSample :: SourcePos -> Parser (Com SourcePos)
cSample pos = do
  x <- ident
  symbol "<~"
  e <- expr
  return $ CSample pos x e

cObserve :: SourcePos -> Parser (Com SourcePos)
cObserve pos = do
  keyword "observe"
  e <- expr
  return $ CObserve pos e

cIf :: SourcePos -> Parser (Com SourcePos)
cIf pos = do
  (e, if') <- L.indentBlock scn p
  else' <- optional cElse
  return $ CIte pos e (mkSeq if') (mkSeq <$> else')
  where
    p = do
      keyword "if"
      e <- expr
      symbol ":"
      return $ L.IndentSome Nothing
        (\coms -> return (e, coms)) com

cElse :: Parser [Com SourcePos]
cElse = L.indentBlock scn p
  where
    p = do
      keyword "else"
      symbol ":"
      return $ L.IndentSome Nothing return com

cWhile :: SourcePos -> Parser (Com SourcePos)
cWhile pos = do
  (e, s) <- L.indentBlock scn p
  return $ CWhile pos e (mkSeq s)
  where
    p = do
      keyword "while"
      e <- expr
      symbol ":"
      return $ L.IndentSome Nothing
        (\coms -> return (e, coms)) com

cReturn :: SourcePos -> Parser (Com SourcePos)
cReturn pos = do
  symbol "return"
  e <- expr
  return $ CReturn pos e

com :: Parser (Com SourcePos)
com = do
  pos <- getSourcePos
  choice
    [ cSkip pos
    , cAbort pos
    , cObserve pos
    , cReturn pos
    , cIf pos
    , cWhile pos
    , try $ cAssign pos
    , cSample pos ]

pair_ty :: Parser Type
pair_ty = do
  symbol "("
  s <- ty
  symbol ","
  t <- ty
  symbol ")"
  return $ TPair s t

list_ty :: Parser Type
list_ty = do
  symbol "["
  t <- ty
  symbol "]"
  return $ TList t

dist_ty :: Parser Type
dist_ty = do
  symbol "dist"
  symbol "("
  t <- ty
  symbol ")"
  return $ TDist t

atomic_ty :: Parser Type
atomic_ty = choice
  [ keyword "rational" >> return TRational
  , keyword "float" >> return TFloat
  , keyword "bool" >> return TBool
  , keyword "int" >> return TInteger
  , try dist_ty
  , try pair_ty
  , list_ty
  , parens ty ]

ty :: Parser Type
ty = do
  s <- atomic_ty
  x <- optional $ symbol "->"
  case x of
    Just _ -> do
      t <- ty
      return $ TArrow s t
    Nothing ->
      return s

func_arg :: Parser (Id, Type)
func_arg = do
  x <- ident
  symbol ":"
  t <- ty
  return (x, t)

func :: Parser (Function SourcePos)
func = L.indentBlock scn $ do
  keyword "func"
  f_nm <- ident
  args <- parens $ commaSep func_arg
  f_ty <- symbol "->" >> ty
  symbol ":"
  return $ L.IndentSome Nothing
    (\es -> case es of
        [e] -> return $ Function { function_name = f_nm
                                 , function_type = f_ty
                                 , function_args = args
                                 , function_body = e }
        _ -> failure Nothing $ singleton $
             Label $ NonEmpty.fromList "unexpected expression")
    expr

dist :: Parser (Dist SourcePos)
dist = L.indentBlock scn $ do
  keyword "dist"
  dist_nm <- ident
  args <- parens $ commaSep func_arg
  dist_ty <- symbol "->" >> ty
  symbol ":"
  return $ L.IndentSome Nothing
    (\coms ->
       return $ Dist { dist_name = dist_nm
                     , dist_type = dist_ty
                     , dist_args = args
                     , dist_body = mkSeq coms })
    com

main :: Parser (Com SourcePos)
main = L.indentBlock scn $ do
  keyword "main"
  symbol ":"
  return $ L.IndentSome Nothing (return . mkSeq) com

prog :: Parser ([Either (Function SourcePos) (Dist SourcePos)], Com SourcePos)
prog = L.nonIndented scn (L.indentBlock scn p)
  where      
    p = do
      funcs_dists <- many $ choice [Left <$> func, Right <$> dist]
      com <- main
      eof
      return $ L.IndentNone (funcs_dists, com)


-- Main parsing function called from the outside.
parse :: String -> String ->
         Either (ParseErrorBundle String Void)
         ([Either (Function SourcePos) (Dist SourcePos)], Com SourcePos)
parse filename src =
  runParser prog filename src
