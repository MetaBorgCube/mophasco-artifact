module Hefty (module Data.HFunctor, module Hefty) where

import Control.Monad
import Data.HFunctor

data Hefty h a
  = Pure a
  | Op (h (Hefty h) (Hefty h a))


-- Algebras and folds

data Alg h g = Alg { alg :: forall a. h g (g a) -> g a }

aId :: forall h' h.
       ( HFunctor h
       , HFunctor h'
       , h < h' )
    => Alg h (Hefty h')
aId = Alg $ Op . inj

hfold :: forall g h a.
         HFunctor h
      => (forall c. c -> g c)
      -> Alg h g
      -> Hefty h a
      -> g a
hfold gen _ (Pure a) = gen a
hfold gen a (Op f)   = alg a $ hmap (hfold gen a) (fmap (hfold gen a) f)


-- Generalized fold:

data AlgG h (g :: * -> *) a = AlgG { algG :: h g a -> a }

gfold :: forall g h a b.
         HFunctor h
      => (forall c. c -> g c)
      -> Alg h g
      -> (a -> b)
      -> AlgG h g b
      -> Hefty h a
      -> b
gfold _    _  gen2 _  (Pure x) = gen2 x
gfold gen1 a1 gen2 a2 (Op f)   = algG a2 $ hmap (hfold gen1 a1) $ fmap (gfold gen1 a1 gen2 a2) f

instance HFunctor h => Applicative (Hefty h) where pure = Pure; (<*>) = ap
instance HFunctor h => Functor (Hefty h) where fmap = liftM
instance HFunctor h => Monad (Hefty h) where
  m >>= k = gfold Pure (Alg Op) k (AlgG Op) m


-- Forephism witness
data Forephism c h h'
  = forall h''. c h'' => Forephism { forephism :: h' <~> (h + h'') }


-- Higher-order functor subsumption
infixr 5 <
class (HFunctor f, HFunctor g) => f < g where
  witness :: Forephism HFunctor f g

-- Algebraic higher-order functor subsumption
infixr 5 <^
class f <^ g where
  witnessA :: Forephism Algebraic f g


-- Short-hands

inj :: forall h1 h2 f a.
       ( HFunctor h1
       , HFunctor h2
       , h1 < h2 )
    => h1 f a -> h2 f a
inj x = case witness @h1 @h2 of
  Forephism iso -> from iso $$ L x

injA :: forall h1 h2 f a.
        ( Algebraic h1
        , Algebraic h2
        , h1 <^ h2 )
    => h1 f a -> h2 f a
injA x = case witnessA @h1 @h2 of
  Forephism iso -> from iso $$ L x

proj :: forall h1 h2 f a.
        ( HFunctor h1
        , HFunctor h2
        , h1 < h2 )
     => h2 f a -> Maybe (h1 f a)
proj x = case witness @h1 @h2 of
  Forephism iso -> sum_ Just (const Nothing) $ to iso $$ x

projA :: forall h1 h2 f a.
         ( Algebraic h1
         , Algebraic h2
         , h1 <^ h2 )
     => h2 f a -> Maybe (h1 f a)
projA x = case witnessA @h1 @h2 of
  Forephism iso -> sum_ Just (const Nothing) $ to iso $$ x

-- Sum instances

data Nop (m :: * -> *) a
  deriving Functor

un :: Hefty Nop a -> a
un (Pure x) = x
un (Op op)  = case op of

nopAlg :: Alg Nop f
nopAlg = Alg $ \case

instance {-# OVERLAPPING #-} HFunctor h => h < h where
  witness = Forephism (NT L <~> NT (sum_ id (\(x :: Nop f k) -> case x of)))

instance {-# OVERLAPPING #-} (HFunctor h1, HFunctor h2) => h1 < h1 + h2 where
  witness = Forephism isoRefl

instance {-# OVERLAPPING #-} (HFunctor h1, HFunctor h2, HFunctor h3, h1 < h2) => h1 < h3 + h2 where
  witness = case witness @h1 @h2 of
    Forephism iso ->
      Forephism (isoTrans (isoSumCong iso) isoSumSwap)


instance {-# OVERLAPPING #-} Algebraic h => h <^ h where
  witnessA = Forephism (NT L <~> NT (sum_ id (\(x :: Nop f k) -> case x of)))

instance {-# OVERLAPPING #-} (Algebraic h1, Algebraic h2) => h1 <^ h1 + h2 where
  witnessA = Forephism isoRefl

instance {-# OVERLAPPING #-} (Algebraic h1, Algebraic h2, Algebraic h3, h1 <^ h2) => h1 <^ h3 + h2 where
  witnessA = case witnessA @h1 @h2 of
    Forephism iso ->
      Forephism (isoTrans (isoSumCong iso) isoSumSwap)


-- instance {-# OVERLAPPING #-} h <^ h' => h < h' where
--   witness = case witnessA @h @h' of
--     Forephism iso -> Forephism iso


infixr 6 \+/
(\+/) :: Alg h1 g -> Alg h2 g -> Alg (h1 + h2) g
a1 \+/ a2 = Alg $ \ x -> case x of
  L y -> alg a1 y
  R y -> alg a2 y


-- Algebraic effects
-- = A hefty tree without forks (sub-computations)

class (forall f. Functor (h f)) => Algebraic (h :: (* -> *) -> * -> *) where
  algebraic :: h m a -> h n a

instance {-# OVERLAPPING #-}
         ( forall f. Functor (h f)
         , Algebraic h ) => HFunctor h where
  hmap _ h = algebraic h

instance ( Algebraic h1
         , Algebraic h2 )
      => Algebraic (h1 + h2) where
  algebraic (L x) = L $ algebraic x
  algebraic (R x) = R $ algebraic x

instance Algebraic Nop where
  algebraic = \case


-- Algebraic effect handlers

-- simple handler

data Handler h a h' b
  = Handler { ret :: a -> Hefty h' b
            , hdl :: h (Hefty h') (Hefty h' b) -> Hefty h' b }

handle :: ( Algebraic h
          , Algebraic h' )
       => Handler h a h' b
       -> Hefty (h + h') a
       -> Hefty h' b
handle h = gfold pure (Alg Op)
  (ret h)
  (AlgG $ sum_ (hdl h . algebraic) (Op . algebraic))


-- parameterized handler

data Handler_ h a p h' b
  = Handler_ { ret_ :: a -> p -> Hefty h' b
             , hdl_ :: h (Hefty h') (p -> Hefty h' b) -> p -> Hefty h' b }

handle_ :: ( Algebraic h
           , Algebraic h' )
        => Handler_ h a p h' b
        -> Hefty (h + h') a
        -> p
        -> Hefty h' b
handle_ h = gfold pure (Alg Op)
  (ret_ h)
  (AlgG $ sum_
    (\ x p -> hdl_ h (algebraic x) p)
    (\ x p -> Op $ (flip ($) p) <$> algebraic x))


-- convert a tree using a natural transformation

convert :: forall h h' a.
           HFunctor h
        => (h :~> h')
        -> Hefty h a -> Hefty h' a
convert g = hfold Pure (Alg $ Op . ($$) g)


-- effect masking

mask :: HFunctor h
     => Hefty h a -> Hefty (h' + h) a
mask = hfold Pure (Alg $ Op . R)


-- apply a handler and mask that the effect was handled

hup :: forall h h' a b.
       ( Algebraic h
       , Algebraic h'
       , h <^ h' )
    => (forall h''. Algebraic h'' => Hefty (h + h'') a -> Hefty h'' b)
    -> Hefty h' a -> Hefty h' b
hup h = case witnessA @h @h' of
  Forephism iso -> convert (from iso) . mask . h . convert (to iso)


-- apply an identity function modulo an insertion witness

hid :: forall h h' a.
       ( Algebraic h
       , Algebraic h'
       , h <^ h' )
    => (forall h''. Algebraic h'' => Hefty (h + h'') a -> Hefty (h + h'') a)
    -> Hefty h' a -> Hefty h' a
hid h = case witnessA @h @h' of
  Forephism iso -> convert (from iso) . h . convert (to iso)
