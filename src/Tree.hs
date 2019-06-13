{-# LANGUAGE DeriveFunctor, TupleSections #-}

module Tree where

import Control.Monad
import Data.Bifunctor
import Data.List (nub, sort, (\\))

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

-- Type of well-founded trees (we never produce infinite trees of this type).
data Tree a =
  Leaf a
  | Split (Tree a) (Tree a)
  | Hole
  deriving (Eq, Ord, Functor, Show)

tree_sexp :: Show a => Tree a -> String
tree_sexp (Leaf x) = "(" ++ show x ++ ")"
tree_sexp (Split t1 t2) = "(" ++ tree_sexp t1 ++ " " ++ tree_sexp t2 ++ ")"
tree_sexp Hole = "(Hole)"

instance Show a => ToSexp (Tree a) where
  toSexp = tree_sexp

-- Monadic join for trees.
mu :: Tree (Tree a) -> Tree a
mu (Leaf t) = t
mu (Split t1 t2) = Split (mu t1) (mu t2)
mu Hole = Hole

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

-- Coupling trees. May not work when the two trees have holes in
-- different locations.
coupling :: Tree a -> Tree b -> Tree (a, b)
coupling t1 (Leaf y) = fmap (,y) t1
coupling (Leaf x) t2 = fmap (x,) t2
coupling Hole _ = Hole
coupling _ Hole = Hole
coupling (Split t1 t2) (Split t1' t2') =
  Split (product_tree t1 t1') (product_tree t2 t2')

-- Depth of a tree.
depth :: Tree a -> Int
depth (Split t1 t2) = max (depth t1) (depth t2) + 1
depth _ = 0

hole_depth :: Tree a -> Int
hole_depth (Leaf _) = 100000000
hole_depth Hole = 0
hole_depth (Split t1 t2) = min (hole_depth t1) (hole_depth t2) + 1

has_hole :: Tree a -> Bool
has_hole (Leaf _) = False
has_hole Hole = True
has_hole (Split t1 t2) = has_hole t1 || has_hole t2

terminals_at_depth :: Tree a -> Int -> [Tree a]
terminals_at_depth (Split t1 t2) n
  | n > 0 =
      terminals_at_depth t1 (n-1) ++ terminals_at_depth t2 (n-1)
terminals_at_depth (Split _ _) 0 = []
terminals_at_depth t 0 = [t]
terminals_at_depth _ _ = []

-- Leaf values at a particular depth level.
leaves_at_depth :: Tree a -> Int -> [a]
leaves_at_depth (Leaf x) 0 = [x]
leaves_at_depth (Split t1 t2) n
 | n > 0 =
     leaves_at_depth t1 (n-1) ++ leaves_at_depth t2 (n-1)
leaves_at_depth _ _ = []

-- sort_tree :: Ord a => Tree a -> Tree a
-- sort_tree = from_list . sort_list . to_list

leaves :: Tree a -> [a]
leaves (Leaf x) = [x]
leaves Hole = []
leaves (Split t1 t2) = leaves t1 ++ leaves t2

terminals :: Tree a -> [Tree a]
terminals (Split t1 t2) = terminals t1 ++ terminals t2
terminals t = [t]

reduce_whole :: Eq a => Tree a -> Tree a
reduce_whole t =
  case leaves t of
    [] -> Hole
    (x:xs) | allEq (x:xs) -> Leaf x
    _ -> t

reduce :: Eq a => Tree a -> Tree a
reduce (Split t1 t2) =
  let t1' = reduce t1
      t2' = reduce t2 in
    case (terminals t1' ++ terminals t2') of
      [] -> error "reduce: no terminals (INFINITE TREE?)"
      (x:xs) | allEq (x:xs) -> x
      _ -> Split t1' t2'
reduce t = t

-- Sort leaves at each level and always keep leaves and holes to the
-- left of split siblings.
reorder :: Tree a -> Tree a
reorder (Split t1@(Split _ _) t2@(Split _ _)) = Split (reorder t1) (reorder t2)
reorder (Split t1@(Split _ _) t2) = Split (reorder t2) (reorder t1)
reorder (Split t1 t2) = Split (reorder t1) (reorder t2)
reorder t = t

type Path = [Bool]

-- Assign a subtree to a location in a tree.
update_subtree :: Path -> Tree a -> Tree a -> Tree a
update_subtree [] subtree _ = subtree
update_subtree (False:bs) subtree (Split t1 t2) =
  Split (update_subtree bs subtree t1) t2
update_subtree (True:bs) subtree (Split t1 t2) =
  Split t1 (update_subtree bs subtree t2)
update_subtree _ _ t = t

get_subtree :: Path -> Tree a -> Tree a
get_subtree (False:bs) (Split t1 _) = get_subtree bs t1
get_subtree (True:bs)  (Split _ t2) = get_subtree bs t2
get_subtree _ t = t

-- Subtrees at a depth level and their coordinate paths into the tree.
at_depth :: Tree a -> Int -> [(Tree a, Path)]
at_depth t 0 = [(t, [])]
at_depth (Split t1 t2) n
  | n > 0 =
    map (second (False:)) (at_depth t1 (n-1)) ++
    map (second (True:)) (at_depth t2 (n-1))
at_depth _ _ = []

-- If there are two duplicate leaves at the same level, group them
-- together as siblings. Doesn't necessarily group all such duplicates
-- together, but will do at least one grouping if possible. We can
-- iteratively apply this function together with reduce to
-- canonicalize a tree.
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

canon :: Eq a => Tree a -> Tree a
canon t =
  let t' = reorder $ reduce (group_dupes $ reduce_whole t) in
    if t == t' then
      t'
    else
      -- debug (toSexp t ++ " not equal to " ++ toSexp t') $
      canon t'

-- Unfold holes once.
expand :: Tree a -> Tree a
expand t = go t t
  where
    go :: Tree a -> Tree a -> Tree a
    go _ (Leaf x) = Leaf x
    go t (Split t1 t2) = Split (go t t1) (go t t2)
    go t Hole = t

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

-- Tensorial strength.
str :: (TreeF a (Tree a), b) -> TreeF (a, b) (Tree (a, b))
str (t, y) = unfold $ fmap (,y) (fold t)

-- Tensorial strength.
str' :: (a, TreeF b (Tree b)) -> TreeF (a, b) (Tree (a, b))
str' (x, t) = unfold $ fmap (x,) (fold t)

join_TreeF :: TreeF (TreeF a (Tree a)) (Tree (TreeF a (Tree a))) -> TreeF a (Tree a)
join_TreeF = unfold . mu . fmap fold . fold

-- Here it may be more convenient to actually define Tree as the least
-- fixed point of the TreeF functor, so that we can use Fix and unFix.

-- Isomorphism up to equivalence.
fold :: TreeF a (Tree a) -> Tree a
fold (LeafF x) = Leaf x
fold (SplitF t1 t2) = Split t1 t2
fold NeverF = Hole

unfold :: Tree a -> TreeF a (Tree a)
unfold (Leaf x) = LeafF x
unfold (Split t1 t2) = SplitF t1 t2
unfold Hole = NeverF

bind_TreeF :: TreeF a (Tree a) -> (a -> TreeF b (Tree b)) -> TreeF b (Tree b)
bind_TreeF (LeafF x) g = g x
bind_TreeF (SplitF t1 t2) g =
  SplitF (fold $ bind_TreeF (unfold t1) g) (fold $ bind_TreeF (unfold t2) g)
bind_TreeF NeverF _ = NeverF

-- The monad we need is the Tree monad! We can still interpret
-- programs as tree transformers (only on finite trees) which then
-- coinductively give rise to trees that may be infinite.

-- bind_coalg :: TreeCoalgebra a -> (a -> TreeCoalgebra b) -> TreeCoalgebra b
-- f :: Tree a -> TreeF a (Tree a)
-- g :: a -> Tree b -> TreeF b (Tree b)
-- t :: Tree b
-- need :: TreeF b (Tree b)
-- bind_coalg f g t = 

product_TreeF :: TreeF a (Tree a) -> TreeF b (Tree b) ->
                 TreeF (a, b) (Tree (a, b))
product_TreeF t1 t2 = bind_TreeF t1 $ \x -> bimap (x,) (fmap (x,)) t2

fst_TreeF :: TreeF (a, b) (Tree (a, b)) -> TreeF a (Tree a)
fst_TreeF = bimap fst (fmap fst)

snd_TreeF :: TreeF (a, b) (Tree (a, b)) -> TreeF b (Tree b)
snd_TreeF = bimap snd (fmap snd)
