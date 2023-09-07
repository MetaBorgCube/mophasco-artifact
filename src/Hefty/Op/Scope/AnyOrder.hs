module Hefty.Op.Scope.AnyOrder where

import Data.List

import Hefty

import Hefty.Op.Scope.Critical

-- Instead of unit, use any monoidal value?
data AnyOrder m k
  = AnyOrder [m (Maybe ())] (m ()) (() -> k)
  deriving Functor

instance HFunctor AnyOrder where
  hmap f (AnyOrder as err k) = AnyOrder (map f as) (f err) k

anyOrder :: AnyOrder < h
         => [Hefty h (Maybe ())]
         -> Hefty h ()
         -> Hefty h ()
anyOrder as err = Op $ inj $ AnyOrder as err Pure

eAnyOrd2Crit :: forall h.
             Critical () < h
          => Alg AnyOrder (Hefty h)
eAnyOrd2Crit = Alg $ \ x -> case x of
  (AnyOrder @_ @a as err k) ->
    go (permutations as) >>= k
      where
        go [] = err             -- no valid permutation, invoke error handler
        go ([]:_) = return ()   -- current permutation was successful
        go ((a:as):ass) =       -- execute current computation `a` in critical block
          critical @()
            (a >>= maybe
              (return Nothing)  -- if fails, return failure (which will cause line 39 to be executed, but **outside** the critical block)
              (const $ Just <$> go (as:ass)) -- continue with other computations (`as`), providing the other untried permutations (`ass`) as fallback
            )
            (const $ go ass)    -- current permutation failed, try other ones (`ass`)
