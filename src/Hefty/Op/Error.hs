module Hefty.Op.Error where

import Hefty

data Error e m k = Error e
  deriving Functor

instance Algebraic (Error e) where
  algebraic (Error e) = Error e

err :: ( HFunctor h
       , Error e < h )
    => e -> Hefty h a
err e = Op $ inj $ Error e

hErr :: ( HFunctor h
        , Algebraic h )
     => Handler (Error e) a h (Either e a)
hErr = Handler
  (return . Right)
  (\ (Error e) -> return $ Left e)
