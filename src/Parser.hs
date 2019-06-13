module Parser where

-- TODO: Syntax for patterns.. a small calculus for manipulating
-- distributions?

-- Also, multiple commands in a file? Formal parameters?

import Control.Monad (void)

import Control.Monad.Combinators.Expr -- from parser-combinators
import Data.Maybe (fromMaybe)
import Data.Ratio
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

literal :: Parser Lit
literal = choice
  [ LBool   <$> bool
  , LFloat  <$> try float
  , LRational <$> try rational
  , LFloat . fromInteger <$> integer ]

call :: SourcePos -> Parser (Exp SourcePos)
call pos = do
  f <- EVar pos <$> ident
  args <- parens $ commaSep expr
  return $ ECall pos f args

-- Nil list
nil :: SourcePos -> Parser (Exp SourcePos)
nil pos = symbol "nil" >> return (ENil pos)

term :: Parser (Exp SourcePos)
term = do
  pos <- getSourcePos
  choice
    [ nil pos
    , mkList pos <$> brackets (commaSep expr)
    , try $ call pos
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

operatorTable :: [[Operator Parser (Exp SourcePos)]]
operatorTable =
  [ [ binary "*" $ flip EBinop BMult ],
    [ binary "+" $ flip EBinop BPlus
    , binary "-" $ flip EBinop BMinus ],
    [ binary "=" $ flip EBinop BEq
    , binary "<" $ flip EBinop BLt ],
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

com :: Parser (Com SourcePos)
com = do
  pos <- getSourcePos
  choice
    [ cSkip pos
    , cAbort pos
    , cObserve pos
    , cIf pos
    , cWhile pos
    , try $ cAssign pos
    , cSample pos ]

-- func_arg :: Parser (Id, Type)
-- func_arg = do
--   x <- ident
--   t <- (try $ symbol ":" >> ty) <|> (return $ TDynamic)
--   return (x, t)

main :: Parser (Com SourcePos)
main = L.indentBlock scn $ do
  keyword "main"
  symbol ":"
  return $ L.IndentSome Nothing (return . mkSeq) com

-- func :: SourcePos -> Parser (Command SourcePos)
-- func pos = L.indentBlock scn $ do
--   static <- (keyword "static" >> return True) <|> return False
--   keyword "func"
--   f <- ident
--   args <- parens $ commaSep func_arg
--   f_ty <- (symbol "->" >> ty) <|> return TDynamic
--   symbol ":"
--   return $ L.IndentSome Nothing
--     (return . (CFunc pos static f f_ty args)) stmt

-- signal :: SourcePos -> Parser (Command SourcePos)
-- signal pos = L.indentBlock scn $ do
--   keyword "signal"
--   nm <- ident
--   args <- optional $ parens $ commaSep ident
--   return $ L.IndentNone $ CSignal pos nm $ fromMaybe [] args

-- extends :: SourcePos -> Parser (Command SourcePos)
-- extends pos = L.indentBlock scn $ do
--   -- c <- keyword "extends" >> expr >>= return . CExtends pos
--   c <- keyword "extends" >> ty >>= return . CExtends pos
--   return $ L.IndentNone c

-- classname :: SourcePos -> Parser (Command SourcePos)
-- classname pos = L.indentBlock scn $ do
--   keyword "class_name"
--   nm <- ident
--   path <- optional $ symbol "," >> stringLiteral
--   return $ L.IndentNone $ CClassName pos nm path

-- command :: Parser (Command SourcePos)
-- command = do
--   pos <- getSourcePos
--   choice
--     [ enum pos
--     , cvar pos
--     , cconst pos
--     , func pos
--     , extends pos
--     , nestedCls pos
--     , signal pos
--     , classname pos ]

-- nestedCls :: SourcePos -> Parser (Command SourcePos)
-- nestedCls pos = L.indentBlock scn $ do
--   keyword "class"
--   nm <- ident
--   symbol ":"
--   return $ L.IndentSome Nothing
--     (\coms -> return $ CClass pos $
--               Class { class_name = nm
--                     , class_commands = coms }) command

-- cls :: Id -> Parser (Class SourcePos)
-- cls nm = L.nonIndented scn (L.indentBlock scn p)
--   where      
--     p = do
--       coms <- some command
--       eof
--       return $ L.IndentNone (Class { class_name = nm
--                                    , class_commands = coms })

-- prog :: Parser (Com SourcePos)
-- -- prog = L.nonIndented scn (L.indentBlock scn p)
-- prog = L.indentBlock scn p
--   where      
--     p = do
--       coms <- some com
--       eof
--       return $ L.IndentNone $ mkSeq coms

prog :: Parser (Com SourcePos)
prog = L.nonIndented scn (L.indentBlock scn p)
  where      
    p = do
      com <- main
      eof
      return $ L.IndentNone com


parse :: String -> String ->
         Either (ParseErrorBundle String Void) (Com SourcePos)
parse filename src =
  runParser prog filename src
