module Data.Functor.Aggr where

import Data.Functor.Monplicative

data Aggr r a
  = Aggr r (r -> a)
  deriving Functor

aggr = Aggr

instance (Monoid r) => Monplicative (Aggr r) where
  unit = Aggr mempty (const ())
  Aggr xs m & Aggr ys n = Aggr (xs <> ys) (\ r -> (m r, n r))

instance Monoid r => Monad (Aggr r) where
  Aggr r f >>= k = k $ f r

unAggr :: Monoid m => Aggr m a -> a
unAggr (Aggr r m) = m r
