module Hefty.Op.State where

import Hefty

data State s m k
  = Put s k
  | Get (s -> k)
  deriving Functor

instance Algebraic (State s) where
  algebraic (Put s k) = Put s k
  algebraic (Get k) = Get k

put :: State s < h => s -> Hefty h ()
put s = Op $ inj $ Put s $ Pure ()

get :: State s < h => Hefty h s
get = Op $ inj $ Get Pure


hState :: forall s h' a. Algebraic h' => Handler_ (State s) a s h' a
hState = Handler_
  (\ x _ -> pure x)
  (\ op s -> case op of
      Put s k -> k s
      Get k -> k s s)
