module Datatypes where


-- | Fixed point of a functor.
newtype Fix f = Fix { unFix :: f (Fix f) }

-- | General setup for algebras/coalgebras and cata-/anamorphisms.
type Algebra f a = f a -> a
type Coalgebra f a = a -> f a

cata :: Functor f => Algebra f b -> Fix f -> b
cata alg = alg . fmap (cata alg) . unFix

ana :: Functor f => Coalgebra f b -> b -> Fix f
ana coalg = Fix . fmap (ana coalg) . coalg

hylo :: Functor f => Algebra f b -> Coalgebra f a -> a -> b
hylo alg coalg = cata alg . ana coalg
