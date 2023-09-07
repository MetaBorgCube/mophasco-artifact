module Data.HFunctor where

infixr 5 $$
newtype (:~>) h1 h2 = NT { ($$) :: forall (f :: * -> *) x. h1 f x -> h2 f x }

type f ~> g = forall a. f a -> g a

o :: (h2 :~> h3) -> (h1 :~> h2) -> (h1 :~> h3)
f1 `o` f2 = NT $ \ x -> f1 $$ f2 $$ x

class (forall f. Functor (h f)) => HFunctor h where
  hmap :: (f ~> g) -> h f ~> h g

data (<~>) f g = Iso { to :: f :~> g, from :: g :~> f }

(<~>) :: (f :~> g) -> (g :~> f) -> f <~> g
(<~>) = Iso

isoRefl :: f <~> f
isoRefl = NT id <~> NT id

isoSym :: f <~> g -> g <~> f
isoSym iso = from iso <~> to iso

isoTrans :: f <~> g -> g <~> h -> f <~> h
isoTrans iso1 iso2 = (to iso2 `o` to iso1) <~> (from iso1 `o` from iso2)

-- hfunctor sum

infixr 6 +
data (h1 + h2) (f :: * -> *) a = L (h1 f a) | R (h2 f a)
  deriving Functor

instance (HFunctor h1, HFunctor h2) => HFunctor (h1 + h2) where
  hmap f (L x) = L $ hmap f x
  hmap f (R x) = R $ hmap f x

-- HFunctor subsumption

sum_ :: (h1 f a -> b) -> (h2 f a -> b) -> (h1 + h2) f a -> b
sum_ f _ (L x) = f x
sum_ _ g (R x) = g x

isoSumCong :: g <~> h -> (f + g) <~> (f + h)
isoSumCong iso = NT (sum_ L (R . ($$) (to iso)))
             <~> NT (sum_ L (R . ($$) (from iso)))

isoSumSwap :: (f + (g + h)) <~> (g + (f + h))
isoSumSwap = NT (sum_ (R . L) (sum_ L (R . R)))
         <~> NT (sum_ (R . L) (sum_ L (R . R)))
