{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, TupleSections #-}

module DeltaTree where

-- import Control.Monad
-- import Data.Proxy

-- import Interp (eval)
-- import Lang
-- import Symtab (Id(..))
-- import Util (mapJoin)

-- -- data Tree a b =
-- --   Leaf b
-- --   | Split (Maybe Int) (a -> (Delta, Tree a b))
-- --   | Hole Int

-- data Tree a =
--   Leaf a
--   | Split (DeltaTree a) (DeltaTree a)
--   | Branch (Exp Bool) (DeltaTree a) (DeltaTree a)
--   -- | Loop (Exp Bool) (DeltaTree a) (DeltaTree a)
--   | Obs (Exp Bool)
--   | Hole Int
--   deriving (Foldable, Functor, Show, Traversable)

-- -- type Delta = [(Id, SomeExp)]
-- data Delta =
--   DAssign Id SomeExp
--   | DSample Id SomeExp
--   deriving Show

-- data DeltaTree a = DeltaTree { tree_label :: Maybe Int
--                              , tree_delta :: [Delta]
--                              , tree_tree :: Tree a }
--   deriving (Foldable, Functor, Show, Traversable)

-- append_delta :: [Delta] -> DeltaTree a -> DeltaTree a
-- append_delta δ (DeltaTree { tree_label = lbl
--                           , tree_delta = δ'
--                           , tree_tree = t }) =
--   DeltaTree { tree_label = lbl, tree_delta = δ' ++ δ, tree_tree = t }

-- -- Monadic join for trees.
-- mu :: DeltaTree (DeltaTree a) -> DeltaTree a
-- mu (DeltaTree { tree_label = lbl
--               , tree_delta = δ
--               , tree_tree = t }) =
--   case t of
--     Leaf t' -> append_delta δ t'
--     Split t1 t2 ->
--       DeltaTree { tree_label = lbl, tree_delta = δ, tree_tree = Split (mu t1) (mu t2)}
--     Branch e t1 t2 ->
--       DeltaTree { tree_label = lbl, tree_delta = δ, tree_tree = Branch e (mu t1) (mu t2)}
--     -- Loop e body cont ->
--     --   DeltaTree { tree_label = lbl, tree_delta = δ, tree_tree = Loop e (mu body) (mu cont) }
--     Hole n ->
--       DeltaTree { tree_label = lbl, tree_delta = δ, tree_tree = Hole n }

-- -- Monadic bind for trees.
-- bind :: DeltaTree a -> (a -> DeltaTree b) -> DeltaTree b
-- bind t g = mu $ fmap g t

-- instance Applicative DeltaTree where
--   pure = DeltaTree Nothing [] . Leaf
--   (<*>) = ap

-- instance Monad DeltaTree where
--   (>>=) = bind
--   return = pure

-- mkTree :: Tree a -> DeltaTree a
-- mkTree = DeltaTree Nothing []

-- mkLeaf :: a -> DeltaTree a
-- mkLeaf = mkTree . Leaf

-- interp :: (Eq a, Show a) => Com a -> DeltaTree () -> DeltaTree ()
-- interp Skip t = t

-- interp (Assign (x, _) e) t =
--   t >> DeltaTree Nothing [DAssign (Id x) (SomeExp e)] (Leaf ())

-- interp (Sample (x, _) e) t =
--   t >> DeltaTree Nothing [DSample (Id x) (SomeExp e)] (Leaf ())

-- interp (Seq c1 c2) t = interp c2 (interp c1 t)
  
-- interp (Ite e c1 c2) t =
--   t >> DeltaTree Nothing []
--   (Branch e (interp c1 (mkLeaf ())) (interp c2 (mkLeaf ())))

-- -- TODO: generate fresh labels. probably in a later pass
-- interp (While e c) t =
--   t >> DeltaTree (Just $ -1) []
--   (Branch e
--     (interp c (mkLeaf ()) >>
--      DeltaTree Nothing [] (Branch e (DeltaTree Nothing [] (Hole (-1))) (mkLeaf ())))
--     (mkLeaf ()))

-- -- assign to special variable.
-- interp (Return e) t = interp (Assign ("_r", Proxy) e) t

-- interp (Observe e) t = t >> DeltaTree Nothing [] (Obs e)

-- interp Abort t = interp (Observe $ EVal $ VBool False) t
