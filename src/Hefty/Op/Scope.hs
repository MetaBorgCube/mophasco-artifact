module Hefty.Op.Scope where

import Hefty

import Data.Regex

-- Scopes

type Sc = Int

-- ScopePaths

data ScopePath l
  = Start Sc
  | Step (ScopePath l) l Sc
  deriving (Eq, Show)

data ResolvedPath l d
  = ResolvedPath (ScopePath l) l d
  deriving (Eq, Show)

type PathOrder l d = ResolvedPath l d -> ResolvedPath l d -> Bool

-- Operations

data Q s l d
  = Q s (RE l) (PathOrder l d) (d -> Bool)

data Scope g s l d m k
  = New (s -> k)
  | Edge s l s k
  | Sink s l d k
  | Query Bool (Q s l d) ([d] -> k)  -- Boolean indicates whether to track stability
  | Mark (g -> k)
  | Rollback g k
  deriving Functor


-- Algebraic instance

instance Algebraic (Scope g s l d) where
  algebraic (New k) = New k
  algebraic (Edge s l s' k) = Edge s l s' k
  algebraic (Sink s l d  k) = Sink s l d  k
  algebraic (Query b q k) = Query b q k
  algebraic (Mark k) = Mark k
  algebraic (Rollback g k) = Rollback g k


-- Smart constructors

new :: forall g s l d h.
       Scope g s l d < h
    => Hefty h s
new = Op $ inj $ New @g @s @l @d $ Pure

edge :: forall g s l d h.
        Scope g s l d < h
     => s -> l -> s -> Hefty h ()
edge s l s' = Op $ inj $ Edge @g @s @l @d s l s' $ Pure ()

sink :: forall g s l d h.
        Scope g s l d < h
     => s -> l -> d -> Hefty h ()
sink s l d = Op $ inj $ Sink @g @s @l @d s l d $ Pure ()

query :: forall g s l d h.
         Scope g s l d < h
      => s -> RE l -> PathOrder l d -> (d -> Bool) -> Hefty h [d]
query s re po ad = Op $ inj $ Query @g @s @l @d True (Q s re po ad) Pure

unsafeQuery :: forall g s l d h.
               Scope g s l d < h
            => s -> RE l -> PathOrder l d -> (d -> Bool) -> Hefty h [d]
unsafeQuery s re po ad = Op $ inj $ Query @g @s @l @d False (Q s re po ad) Pure

queryA :: forall g s l d h.
          ( Algebraic h
          , Scope g s l d <^ h )
       => s -> RE l -> PathOrder l d -> (d -> Bool) -> Hefty h [d]
queryA s re po ad = Op $ injA $ Query @g @s @l @d True (Q s re po ad) Pure

unsafeQueryA :: forall g s l d h.
                ( Algebraic h
                , Scope g s l d <^ h )
             => s -> RE l -> PathOrder l d -> (d -> Bool) -> Hefty h [d]
unsafeQueryA s re po ad = Op $ injA $ Query @g @s @l @d False (Q s re po ad) Pure

unsafeMark :: forall g s l d h.
              Scope g s l d < h
           => Hefty h g
unsafeMark = Op $ inj $ Mark @g @s @l @d Pure

unsafeRollback :: forall g s l d h.
                  Scope g s l d < h
               => g -> Hefty h ()
unsafeRollback g = Op $ inj $ Rollback @g @s @l @d g $ Pure ()

unsafeMarkA :: forall g s l d h.
               ( Algebraic h
               , Scope g s l d <^ h )
            => Hefty h g
unsafeMarkA = Op $ injA $ Mark @g @s @l @d Pure

unsafeRollbackA :: forall g s l d h.
                   ( Algebraic h
                   , Scope g s l d <^ h )
                => g -> Hefty h ()
unsafeRollbackA g = Op $ injA $ Rollback @g @s @l @d g $ Pure ()

