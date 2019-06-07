module Token where

import Control.Monad (void)
import Control.Monad.Combinators.Expr -- from parser-combinators
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Symtab (Id(..))

type Parser = Parsec Void String

lineComment :: Parser ()
lineComment = L.skipLineComment "#"

blockComment :: Parser ()
blockComment = L.skipBlockComment "\"\"\"" "\"\"\""

scn :: Parser ()
scn = L.space space1 lineComment blockComment

sc :: Parser ()
sc = L.space (void $ some (char ' ' <|> char '\t')) lineComment blockComment
-- sc = L.space space1 lineComment blockComment

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol s = lexeme $ string s

quotation :: Parser Char
quotation = char '\'' <|> char '"'

charLiteral :: Parser Char
charLiteral = between quotation quotation L.charLiteral

stringLiteral :: Parser String
stringLiteral = lexeme $ quotation *> manyTill L.charLiteral quotation

integer :: Parser Integer
integer = lexeme L.decimal

float :: Parser Double
float = lexeme L.float

signedInteger :: Parser Integer
signedInteger = L.signed sc integer

signedFloat :: Parser Double
signedFloat = L.signed sc float

keyword :: String -> Parser String
-- keyword k = lexeme (string k <* notFollowedBy alphaNumChar)
-- Add 'try' here so it doesn't consume the string k when
-- 'notFollowedBy' fails.
keyword k = (lexeme . try) (string k <* notFollowedBy (alphaNumChar <|> char '_'))

ident :: Parser Id
ident = Id <$> lexeme
  ((:) <$> (letterChar <|> char '_') <*> many (alphaNumChar <|> char '_')
   <?> "variable")

-- | @postfixChain p op@ is used to remove left recursion like
-- @chainl1@, except @op@ is a postfix operator instead of infix
postfixChain :: Parser a -> Parser (a -> a) -> Parser a
postfixChain p op = do
  x <- p
  rest x
  where
    rest x = (do f <- op
                 rest $ f x) <|> return x
