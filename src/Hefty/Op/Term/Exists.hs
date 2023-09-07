module Hefty.Op.Term.Exists where

import Hefty

import Data.Term

data Exists trm m k
  = Exists (trm -> k)
  deriving Functor

instance Algebraic (Exists trm) where
  algebraic (Exists k) = Exists k
  

exists :: Exists trm < h => Hefty h trm
exists = Op $ inj $ Exists Pure


---------------
--- HANDLER ---
---------------

-- A handler that creates fresh variables, assuming a suitably chosen initial
-- integer parameter

hExists :: Algebraic h'
        => Handler_ (Exists (Term c)) a Int h' a
hExists = Handler_ {
    ret_ = \ x _ -> return x
  , hdl_ = \ f i -> case f of
      Exists k -> k (Var i) (i + 1)
  }

