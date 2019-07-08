module Sexp where

import Data.List (intercalate)

class ToSexp a where
  toSexp :: a -> String

instance ToSexp a => ToSexp [a] where
  toSexp l = "(" ++ intercalate " " (toSexp <$> l) ++ ")"

instance (ToSexp a, ToSexp b) => ToSexp (a, b) where
  toSexp (x, y) = "(" ++ toSexp x ++ " " ++ toSexp y ++ ")"

instance ToSexp a => ToSexp (Maybe a) where
  toSexp (Just x) = toSexp x
  toSexp Nothing = "Nothing"

instance (ToSexp a, ToSexp b) => ToSexp (Either a b) where
  toSexp (Left x) = toSexp x
  toSexp (Right y) = toSexp y

instance ToSexp Int where
  toSexp = show
