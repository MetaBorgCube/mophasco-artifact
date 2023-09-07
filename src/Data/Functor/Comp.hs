module Data.Functor.Comp where

import Data.Functor.Monplicative
-- import Control.Monad (join)

infixr 6 :.:
newtype (f :.: g) a = Comp { runComp :: f (g a) } deriving (Functor, Show)

instance (Monplicative f, Monplicative g) => Monplicative (f :.: g) where
  unit = Comp (pure unit)
  Comp fg0 & Comp fg1 = Comp $ uncurry (&) <$> fg0 & fg1

here :: (Functor f, Monplicative g) => f a -> (f :.: g) a
here xs = Comp $ pure <$> xs

there :: (Functor g, Monplicative f) => g a -> (f :.: g) a
there ys = Comp $ pure ys

infixr 6 &>-
(&>-) :: Functor f => f a -> (a -> g b) -> (f :.: g) b
xs &>- k = Comp $ k <$> xs

infixr 6 &>
(&>) :: Functor f => f a -> g b -> (f :.: g) b
xs &> ys = xs &>- const ys

infixr 6 &>>-
(&>>-) :: Monad f => f a -> (a -> (f :.: g) b) -> (f :.: g) b
xs &>>- k = Comp $ xs >>= runComp . k


data Phases f a
  = Pure a
  | Link (f (Phases f a))

instance Functor f => Functor (Phases f) where
  fmap :: Functor f => (a -> b) -> Phases f a -> Phases f b
  fmap f (Pure a)  = Pure (f a)
  fmap f (Link xs) = Link $ (fmap f) <$> xs

instance Monplicative f => Monplicative (Phases f) where
  unit = Pure ()
  Pure x  & ys      = fmap (x,) ys
  xs      & Pure y  = fmap (,y) xs
  Link xs & Link ys = Link $ uncurry (&) <$> xs & ys

runPhases :: Monad f => Phases f a -> f a
runPhases (Pure x)  = pure x
runPhases (Link xs) = xs >>= runPhases

now :: Monplicative f => f a -> Phases f a
now xs = Link $ Pure <$> xs

infixr 6 &:>-
(&:>-) :: Functor f => f a -> (a -> Phases f b) -> Phases f b
m &:>- k = Link $ k <$> m

infixr 6 &:>
(&:>) :: Functor f => f a -> Phases f b -> Phases f b
m1 &:> xs = m1 &:>- const xs

instance Monad f => Monad (Phases f) where -- unclear why Haskell insists f be a monad here.
  Pure x >>= k = k x
  Link f >>= k = Link (fmap (>>= k) f)

{-

  (m1 &>- k1) & (m2 &>- k2)
=
  (m1 & m2) &>- \(x1,x2) -> k1 x1 & k2 x2

-}
