module Hefty.Op.Scope.Critical where

import Control.Monad (when)

import Hefty

import Hefty.Op.Scope
    ( Scope(..),
      Q(..),
      Sc,
      new,
      edge,
      sink,
      unsafeQuery,
      queryA,
      unsafeMark,
      unsafeRollback,
      unsafeMarkA,
      unsafeRollbackA )
import Hefty.Op.State
import Data.List

data Critical e m k
  = forall a. Critical (m (Maybe a)) (e -> m a) (a -> k)

deriving instance Functor (Critical e m)

instance HFunctor (Critical e) where
  hmap f (Critical t c k) = Critical (f t) (f . c) k

critical :: Critical e < h
         => Hefty h (Maybe a) -> (e -> Hefty h a) -> Hefty h a
critical t c = Op $ inj $ Critical t c Pure

type Cache l d = [(Q Sc l d, [d])]

instance Show l => Show (Q Sc l d) where
  show (Q s re _ _) = "(Q " ++ " " ++ show s ++ " " ++ show re ++ ")"


-- Insert guards around each query to check that the query result didn't change.
-- If a query result is changed, an exception is raised.
eSC :: forall g l d h.
       ( Eq d
       , Eq l
       , Show d
       , Show l
       , Scope g Sc l d < h
       , State (Cache l d) < h
       , Algebraic h )
    => Alg (Scope g Sc l d) (Hefty h)
eSC = Alg $ \case
  Query mode q@(Q s re po ad) k -> do
    ds <- unsafeQuery @g @Sc @l @d s re po ad -- disable adding query stability information
    when mode $ do c <- get; put ((q,ds):c)   -- if query should have added stability info, put it into cache
    k ds
  New k -> new @g @Sc @l @d >>= k
  Edge s l s' k -> edge @g @_ @_ @d s l s' >> k
  Sink s l d  k -> sink @g @_ @_ @_ s l d  >> k
  Mark k -> unsafeMark @g @Sc @l @d >>= k
  Rollback g k -> unsafeRollback @g @Sc @l @d g >> k

eCritical :: forall g l d h.
             ( Eq d
             , Eq l
             , Show d
             , Show l
             , Scope g Sc l d <^ h
             , Algebraic h )
          => Alg (Critical ()) (Hefty h)
eCritical = Alg $  \ (Critical @_ @_ @_ @a t c k) -> case witnessA @(Scope g Sc l d) @h of -- Hasochism.
  Forephism @_ @_ @_ @h'' iso -> do
    g <- unsafeMarkA @g @Sc @l @d
    r <- convert (from iso) -- ugh
         $ flip (handle_ hState) []
         $ hfold
             pure
             (   aId @(State (Cache l d) + Scope g Sc l d + h'')
             \+/ eSC
             \+/ aId )
             ( (do r <- mask $ convert (to iso) t
                   c <- get
                   pure (r,c) )
             :: Hefty (State (Cache l d) + Scope g Sc l d + h'') (Maybe a, Cache l d) )
    case r of
     (Nothing, _) -> unsafeRollbackA @g @Sc @l @d g >> c () >>= k
     (Just r, ch) -> go g r c k ch
  where
    go :: forall g a b l d h.
          ( Algebraic h
          , Scope g Sc l d <^ h
          , Eq d
          )
       => g
       -> a
       -> (() -> Hefty h a) -- error handler
       -> (a -> Hefty h b)  -- continuation
       -> [(Q Sc l d, [d])] -- queries that happened while evaluating the block
       -> Hefty h b
    go _ r _ k [] = k r -- all queries are stable, so invoke continuation
    go g r c k ((Q s re po ad,ds):ch') = do
      ds' <- queryA @g @Sc @_ @_ @_ s re po ad
      if ds `permutationOf` ds'
        then go g r c k ch'                                   -- current query stable, verify remaining
        else unsafeRollbackA @g @Sc @l @d @_ g >> c () >>= k  -- current query unstable, invoke error handler (`c ()`), then continue with continuation

    permutationOf :: Eq a => [a] -> [a] -> Bool
    permutationOf xs ys | length xs == length ys = go xs ys
      where
        go [] []                      = True
        go (x:_)  ys | x `notElem` ys = False
        go (x:xs) ys                  = go xs $ delete x ys
        go _ _                        = False
    permutationOf _ _ = False
