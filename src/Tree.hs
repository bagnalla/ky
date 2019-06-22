{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, TupleSections #-}

module Tree where

import Control.Monad
import Data.Bifunctor
import Data.List (nub, sort, (\\))
import Data.Maybe (fromMaybe)

import Datatypes
import Sexp
import Util

-- The tree functor.
data TreeF a b =
  LeafF a
  | SplitF b b
  | NeverF
  deriving (Functor, Show)

instance Bifunctor TreeF where
  bimap f _ (LeafF x) = LeafF (f x)
  bimap _ g (SplitF y1 y2) = SplitF (g y1) (g y2)
  bimap _ _ NeverF = NeverF

-- Special case of algebras/coalgebras for trees.
type TreeAlgebra a b = Algebra (TreeF a) b
type TreeCoalgebra a = Coalgebra (TreeF a) (Tree a)

-- Type of well-founded trees with nat-indexed holes (we never produce
-- infinite trees of this type).
data Tree a =
  Leaf a
  | Split (Maybe Int) (Tree a) (Tree a)
  | Hole Int
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

tree_sexp :: Show a => Tree a -> String
tree_sexp (Leaf x) = "(" ++ show x ++ ")"
tree_sexp (Split n t1 t2) =
  "(" ++ fromMaybe "" (show <$> n) ++ " " ++
  tree_sexp t1 ++ " " ++ tree_sexp t2 ++ ")"
tree_sexp (Hole n) = "(Hole " ++ show n ++ ")"

instance Show a => ToSexp (Tree a) where
  toSexp = tree_sexp

-- Monadic join for trees.
mu :: Tree (Tree a) -> Tree a
mu (Leaf t) = t
mu (Split n t1 t2) = Split n (mu t1) (mu t2)
mu (Hole n) = Hole n

-- Monadic bind for trees.
bind :: Tree a -> (a -> Tree b) -> Tree b
bind t g = mu $ fmap g t

instance Applicative Tree where
  pure = Leaf
  (<*>) = ap

instance Monad Tree where
  (>>=) = bind
  return a = pure a

-- Product distribution trees.
product_tree :: Tree a -> Tree b -> Tree (a, b)
product_tree t1 t2 = t1 >>= \x -> (x,) <$> t2

fst_tree :: Tree (a, b) -> Tree a
fst_tree = fmap fst

snd_tree :: Tree (a, b) -> Tree b
snd_tree = fmap snd


set_label :: Int -> Tree a -> Tree a
set_label n (Split Nothing t1 t2) = Split (Just n) t1 t2
-- set_label n t@(Split (Just m) _ _) =
--   error $ "set_label: trying to set label " ++ show n ++
--   ", already has label " ++ show m
set_label _ t = t

label_of :: Tree a -> Int
label_of (Split (Just lbl) _ _) = lbl
label_of _ = error "label_of: no label"

-- -- Coupled product. May not work when the two trees have holes in
-- -- different locations.
-- coupling :: Tree a -> Tree b -> Tree (a, b)
-- coupling t1 (Leaf y) = fmap (,y) t1
-- coupling (Leaf x) t2 = fmap (x,) t2
-- coupling Hole _ = Hole
-- coupling _ Hole = Hole
-- coupling (Split t1 t2) (Split t1' t2') =
--   Split (product_tree t1 t1') (product_tree t2 t2')

-- Depth of a tree.
depth :: Tree a -> Int
depth (Split _ t1 t2) = max (depth t1) (depth t2) + 1
depth _ = 0

hole_depth :: Tree a -> Int
hole_depth (Leaf _) = 100000000
hole_depth (Hole _) = 0
hole_depth (Split _ t1 t2) = min (hole_depth t1) (hole_depth t2) + 1

has_hole :: Tree a -> Bool
has_hole (Leaf _) = False
has_hole (Hole _) = True
has_hole (Split _ t1 t2) = has_hole t1 || has_hole t2

terminals_at_depth :: Tree a -> Int -> [Tree a]
terminals_at_depth (Split _ t1 t2) n
  | n > 0 =
      terminals_at_depth t1 (n-1) ++ terminals_at_depth t2 (n-1)
terminals_at_depth (Split _ _ _) 0 = []
terminals_at_depth t 0 = [t]
terminals_at_depth _ _ = []

-- Leaf values at a particular depth level.
leaves_at_depth :: Tree a -> Int -> [a]
leaves_at_depth (Leaf x) 0 = [x]
leaves_at_depth (Split _ t1 t2) n
 | n > 0 =
     leaves_at_depth t1 (n-1) ++ leaves_at_depth t2 (n-1)
leaves_at_depth _ _ = []

-- sort_tree :: Ord a => Tree a -> Tree a
-- sort_tree = from_list . sort_list . to_list

leaves :: Tree a -> [a]
leaves (Leaf x) = [x]
leaves (Hole _) = []
leaves (Split _ t1 t2) = leaves t1 ++ leaves t2

holes :: Tree a -> [Int]
holes (Leaf _) = []
holes (Hole n) = [n]
holes (Split _ t1 t2) = holes t1 ++ holes t2

terminals :: Tree a -> [Tree a]
terminals (Split _ t1 t2) = terminals t1 ++ terminals t2
terminals t = [t]

-- This attempts to find entire subtrees which contain only a single
-- leaf value (perhaps multiple occurrences) and whose holes all point
-- back to the root of the subtree. Any such subtrees are replaced by
-- a single leaf.
reduce_whole :: (Eq a, Show a) => Tree a -> (Tree a, [(Int, Tree a)])
reduce_whole (Split Nothing t1 t2) =
  let (t1', ps1) = reduce_whole t1
      (t2', ps2) = reduce_whole t2 in
    (Split Nothing t1' t2', ps1 ++ ps2)
reduce_whole (Split (Just lbl) t1 t2) =
  let (t1', ps1) = reduce_whole t1
      (t2', ps2) = reduce_whole t2
      ps = ps1 ++ ps2
      ls = leaves t1' ++ leaves t2'
      hs = holes t1' ++ holes t2'
  in
    if all (== lbl) hs then
      case ls of
        [] -> error "reduce_hole: no leaves or outgoing holes"
        (x:xs) | allEq ls -> (Leaf x, (lbl, Leaf x) : ps)
        _ -> (Split (Just lbl) t1' t2', ps)
    else
      (Split (Just lbl) t1' t2', ps)
reduce_whole t = (t, [])

is_terminal :: Tree a -> Bool
is_terminal (Split _ _ _) = False
is_terminal _ = True

-- Produce the reduced tree as well as a list of patches* to be
-- applied afterward. *When a labelled split node is replaced by a
-- terminal node, we have to go through the tree and replace all holes
-- with that label by the terminal node.
-- By reduce here we just mean collapsing split nodes with duplicate
-- children.
reduce :: Eq a => Tree a -> (Tree a, [(Int, Tree a)])
reduce (Split lbl t1 t2) =
  let (t1', ps1) = reduce t1
      (t2', ps2) = reduce t2
      ps = ps1 ++ ps2 in
    case (terminals t1' ++ terminals t2') of
      [] -> error "reduce: no terminals (INFINITE TREE?)"
      (x:xs) | allEq (x:xs) ->
               case lbl of
                 Just lbl' ->
                   case x of
                     Split x_lbl x_t1 x_t2 ->
                       case x_lbl of
                         Just x_lbl' -> (x, (lbl', Hole x_lbl') : ps)
                         Nothing -> (Split (Just lbl') x_t1 x_t2, ps)
                     _ -> (x, (lbl', x) : ps)
                 Nothing -> (x, ps)
      _ -> (Split lbl t1' t2', ps)
reduce t = (t, [])

-- Apply patches to a tree.
apply_patches :: [(Int, Tree a)] -> Tree a -> Tree a
apply_patches ps (Hole lbl) = case lookup lbl ps of
                             Just t -> t
                             Nothing -> Hole lbl
apply_patches ps (Split lbl t1 t2) =
  Split lbl (apply_patches ps t1) (apply_patches ps t2)
apply_patches _ t = t

-- Sort leaves at each level and always keep leaves and holes to the
-- left of split siblings.
reorder :: Tree a -> Tree a
reorder (Split n t1@(Split _ _ _) t2@(Split _ _ _)) =
  Split n (reorder t1) (reorder t2)
reorder (Split n t1@(Split _ _ _) t2) = Split n (reorder t2) (reorder t1)
reorder (Split n t1 t2) = Split n (reorder t1) (reorder t2)
reorder t = t

type Path = [Bool]

-- Assign a subtree to a location in a tree.
update_subtree :: Path -> Tree a -> Tree a -> Tree a
update_subtree [] subtree _ = subtree
update_subtree (False:bs) subtree (Split n t1 t2) =
  Split n (update_subtree bs subtree t1) t2
update_subtree (True:bs) subtree (Split n t1 t2) =
  Split n t1 (update_subtree bs subtree t2)
update_subtree _ _ t = t

get_subtree :: Path -> Tree a -> Tree a
get_subtree (False:bs) (Split _ t1 _) = get_subtree bs t1
get_subtree (True:bs)  (Split _ _ t2) = get_subtree bs t2
get_subtree _ t = t

-- Subtrees at a depth level and their coordinate paths into the tree.
at_depth :: Tree a -> Int -> [(Tree a, Path)]
at_depth t 0 = [(t, [])]
at_depth (Split _ t1 t2) n
  | n > 0 =
    map (second (False:)) (at_depth t1 (n-1)) ++
    map (second (True:)) (at_depth t2 (n-1))
at_depth _ _ = []

-- If there are two duplicate leaves at the same level, group them
-- together as siblings. Doesn't necessarily group all such duplicates
-- together, but will do at least one grouping if possible. We can
-- iteratively apply this function together with reduce to
-- canonicalize a tree.
-- TODO: fix for labelled trees.
group_dupes :: Eq a => Tree a -> Tree a
group_dupes t = foldl f t [0 .. depth t]
  where
    f :: Eq a => Tree a -> Int -> Tree a
    f t n =
      let subtrees = at_depth t n in
        if length subtrees <= 2 then t else
          case dupes [] subtrees of
            Just (p1, p2) -> swap_subtrees (sibling_path p1) p2 t
            Nothing -> t
    dupes :: Eq a => [(Tree a, Path)] -> [(Tree a, Path)] -> Maybe (Path, Path)
    dupes _ [] = Nothing
    dupes seen ((t, p):rest) = case lookup t seen of
      Just p' -> Just (p', p)
      Nothing -> dupes ((t, p) : seen) rest

sibling_path :: Path -> Path
sibling_path [] = error "sibling_path: no sibling"
sibling_path [False] = [True]
sibling_path [True] = [False]
sibling_path (b:bs) = b : sibling_path bs

swap_subtrees :: Path -> Path -> Tree a -> Tree a
swap_subtrees p1 p2 t =
  let t1 = get_subtree p1 t
      t2 = get_subtree p2 t in
    update_subtree p1 t2 (update_subtree p2 t1 t)

canon :: (Eq a, Show a) => Tree a -> Tree a
canon t =
  let
    (t1, ps) = reduce_whole t
    t2 = apply_patches ps t1
    -- t3 = group_dupes t
    (t4, ps') = reduce t2
    t5 = apply_patches ps' t4
    t6 = reorder t5
    -- t6 = t5
  in
    -- debug ("\nt: " ++ toSexp t) $
    -- debug ("\nt1: " ++ toSexp t1) $
    -- debug ("t2: " ++ toSexp t2) $
    -- debug ("t3: " ++ toSexp t3) $
    -- debug ("t4: " ++ toSexp t4) $
    -- debug ("t5: " ++ toSexp t5) $
    -- debug ("t6: " ++ toSexp t6) $
    if t6 == t then t6 else canon t6

-- Unfold holes once.
expand :: Tree a -> Tree a
expand t = go t t
  where
    go :: Tree a -> Tree a -> Tree a
    go _ (Leaf x) = Leaf x
    go t (Split n t1 t2) = Split n (go t t1) (go t t2)
    go t (Hole _) = t

-- Check if a tree is in canonical form (not necessarily the case that
-- canon would have no effect).
is_canon :: Eq a => Tree a -> Bool
is_canon t =
  all (\n -> nub (leaves_at_depth t n) == leaves_at_depth t n)
  [0 .. depth t]

-- Ensure that a tree gives rise to a canonical cotree when lifted to
-- a coalgebra by ϕ. TODO: check if this terminates on randomly
-- generated trees.
cocanon :: (Eq a, Show a) => Tree a -> Tree a
cocanon t =
  let t' = canon t
      -- t'' = expand t' in
      t'' = nTimes (depth t') expand t' in
    if is_canon t'' then t' else
      cocanon t''

cocanon2 :: (Eq a, Show a) => Tree a -> (Int, Tree a)
cocanon2 = go 1
  where
    go :: (Eq a, Show a) => Int -> Tree a -> (Int, Tree a)
    go n t =
      debug "canoning..." $
      let t' = canon t in
        debug "canoned" $
        -- debug (show t') $
        if has_hole t' then
          debug ("t': " ++ tree_sexp t') $
          debug ("depth: " ++ show (depth t')) $
          -- debug ("hole_depth: " ++ show (hole_depth t')) $
          -- let t'' = nTimes (depth t' - hole_depth t') expand t' in
          let t'' = expand t' in
            debug ("t'': " ++ tree_sexp t'') $
            if is_canon t'' then
              debug "canon" (n, t') else
              debug "not canon" $
              go (n+1) t''
        else
          debug "done" $
          (n, t')

-- -- Tensorial strength.
-- str :: (TreeF a (Tree a), b) -> TreeF (a, b) (Tree (a, b))
-- str (t, y) = unfold $ fmap (,y) (fold t)

-- -- Tensorial strength.
-- str' :: (a, TreeF b (Tree b)) -> TreeF (a, b) (Tree (a, b))
-- str' (x, t) = unfold $ fmap (x,) (fold t)

-- join_TreeF :: TreeF (TreeF a (Tree a)) (Tree (TreeF a (Tree a))) -> TreeF a (Tree a)
-- join_TreeF = unfold . mu . fmap fold . fold

-- Here it may be more convenient to actually define Tree as the least
-- fixed point of the TreeF functor, so that we can use Fix and unFix.

-- Retract? We lose information in unfold but not here.
-- fold :: TreeF a (Tree a) -> Tree a
-- fold (LeafF x) = Leaf x
-- fold (SplitF t1 t2) = Split Nothing t1 t2
-- fold NeverF = Hole 0

unfold :: Tree a -> TreeF a (Tree a)
unfold (Leaf x) = LeafF x
unfold (Split _ t1 t2) = SplitF t1 t2
unfold (Hole _) = NeverF

-- bind_TreeF :: TreeF a (Tree a) -> (a -> TreeF b (Tree b)) -> TreeF b (Tree b)
-- bind_TreeF (LeafF x) g = g x
-- bind_TreeF (SplitF t1 t2) g =
--   SplitF (fold $ bind_TreeF (unfold t1) g) (fold $ bind_TreeF (unfold t2) g)
-- bind_TreeF NeverF _ = NeverF

-- product_TreeF :: TreeF a (Tree a) -> TreeF b (Tree b) ->
--                  TreeF (a, b) (Tree (a, b))
-- product_TreeF t1 t2 = bind_TreeF t1 $ \x -> bimap (x,) (fmap (x,)) t2

-- fst_TreeF :: TreeF (a, b) (Tree (a, b)) -> TreeF a (Tree a)
-- fst_TreeF = bimap fst (fmap fst)

-- snd_TreeF :: TreeF (a, b) (Tree (a, b)) -> TreeF b (Tree b)
-- snd_TreeF = bimap snd (fmap snd)


-- | Experimental

-- data KYTree a =
--   KYTree (Tree a)
--   | KYSplit (KYTree a) (KYTree a)

-- asdf :: Tree (KYTree a) -> KYTree a
-- -- asdf t = KYTree $ fmap $ \x -> case x of
-- --                                  KYTree t'
-- asdf (Leaf kyt) = kyt
-- asdf (Split kyt1 kyt2) = KYTree $ Split (asdf kyt1) (asdf kyt2)

-- -- Monadic join.
-- mu' :: KYTree (KYTree a) -> KYTree a
-- mu' (KYTree t) = asdf t

-- -- Monadic bind.
-- bind' :: KYTree a -> (a -> KYTree b) -> KYTree b
-- bind' (KYTree t) g = undefined


labelled_subtrees :: Tree a -> [Tree a]
labelled_subtrees t@(Split n t1 t2) =
  fromMaybe [] ([t] <$ n) ++ labelled_subtrees t1 ++ labelled_subtrees t2
labelled_subtrees _ = []

-- labels_of_tree :: Tree a -> [Int]
-- labels_of_tree t = f <$> labelled_subtrees t
--   where
--     f :: Tree a -> Int
--     f (Split (Just lbl) _ _) = lbl
--     f _ = error "labels_of_tree: no label"

-- remove_orphan_holes :: Eq a => Tree a -> Tree a
-- remove_orphan_holes t =
--   let t' = go (labels_of_tree t) t in
--     if t == t' then t' else remove_orphan_holes t'
--   where
--     go :: [Int] -> Tree a -> Tree a

--     -- Collapse duplicate holes as well..
--     -- go _ (Split x (Hole lbl1) (Hole lbl2)) | lbl1 == lbl2 = Hole lbl1
    
--     go lbls (Split x t1 t2) =
--       let t1' = go lbls t1
--           t2' = go lbls t2 in
--         case t1' of
--           Hole lbl1 | not $ lbl1 `elem` lbls -> relabel x t2'
--           _ ->
--             case t2' of
--               Hole lbl2 | not $ lbl2 `elem` lbls -> relabel x t1'
--               _ ->
--                 case (t1', t2') of
--                   (Hole lbl1, Hole lbl2) | lbl1 == lbl2 -> Hole lbl1
--                   _ -> Split x t1' t2'
--     go _ t = t

--     -- TODO
--     relabel :: Maybe Int -> Tree a -> Tree a
--     relabel = const id

-- -- Make all holes with label -1 point to the root.
-- fix_holes :: Tree a -> Tree a
-- fix_holes t@(Split lbl t1 t2) =
--   case lbl of
--     Just lbl' ->
--       go lbl' t
--     Nothing -> error "fix_holes: expected label at root"
--   where
--     go :: Int -> Tree a -> Tree a
--     go _ (Leaf x) = Leaf x
--     go lbl (Hole lbl') = Hole $ if lbl' == -1 then lbl else lbl'
--     go lbl (Split lbl' t1 t2) = Split lbl' (go lbl t1) (go lbl t2)
-- fix_holes t = t

tree_size :: Tree a -> Int
tree_size (Split _ t1 t2) = 1 + tree_size t1 + tree_size t2
tree_size _ = 1
