module Sexp where

import Data.List (intercalate)

class ToSexp a where
  toSexp :: a -> String

instance ToSexp a => ToSexp [a] where
  toSexp l = "(" ++ intercalate " " (toSexp <$> l) ++ ")"

instance ToSexp Int where
  toSexp = show
