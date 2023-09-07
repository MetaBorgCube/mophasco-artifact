module Data.Functor.Monplicative where

-- Monoidal applicative interface

class Functor f => Monplicative f where
  unit :: f ()
  infixr 6 &
  (&)  :: f a -> f b -> f (a, b)

instance (Functor f, Monplicative f) => Applicative f where
  pure x = fmap (const x) unit
  f <*> x = fmap (\ (f, x) -> f x) (f & x)
  xs *> ys = fmap snd (xs & ys)

instance {-# OVERLAPPABLE #-} (Functor m, Monad m) => Monplicative m where
  unit = return ()
  xs & ys = do { x <- xs; y <- ys; return (x , y) }

