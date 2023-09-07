module Data.Regex where

import Data.List


data RE l
  = Epsilon            -- empty language (accepting state)
  | Empty              -- invalid language (rejecting state)
  | Atom l
  | Pipe (RE l) (RE l)
  | Dot (RE l) (RE l)
  | Star (RE l)
  deriving (Show, Eq)


-- Short-hand defs

eps :: RE l
eps = Epsilon

bot :: RE l
bot = Empty

atom :: l -> RE l
atom = Atom

(~|) :: RE l -> RE l -> RE l
(~|) = Pipe

(~.) :: RE l -> RE l -> RE l
(~.) = Dot

plus :: RE l -> RE l
plus r = r ~. Star r

star :: RE l -> RE l
star = Star

qmark :: RE l -> RE l
qmark r = eps ~| r


-- Computes the list of valid "next" atoms
frontier :: Eq l => RE l -> [l]
frontier Epsilon = []
frontier Empty = []
frontier (Atom l) = [l]
frontier (Pipe r1 r2) = nub $ frontier r1 ++ frontier r2
frontier (Dot r1 r2)  = if possiblyEmpty r1
                        then if definitelyEmpty r1
                             then frontier r2
                             else frontier r1 ++ frontier r2
                        else frontier r1    
frontier (Star r) = frontier r


-- Check if regular expression matches the empty word
possiblyEmpty :: RE l -> Bool
possiblyEmpty Epsilon        = True
possiblyEmpty Empty          = False
possiblyEmpty (Atom _)       = False
possiblyEmpty (Pipe r1 r2)   = possiblyEmpty r1 || possiblyEmpty r2
possiblyEmpty (Dot r1 r2)    = possiblyEmpty r1 && possiblyEmpty r2
possiblyEmpty (Star _)       = True


-- Check if regular expression only matches the empty word
definitelyEmpty :: RE l -> Bool
definitelyEmpty Epsilon      = True
definitelyEmpty Empty        = False
definitelyEmpty (Atom _)     = False
definitelyEmpty (Pipe r1 r2) = definitelyEmpty r1 && definitelyEmpty r2
definitelyEmpty (Dot r1 r2)  = definitelyEmpty r1 && definitelyEmpty r2
definitelyEmpty (Star r)     = definitelyEmpty r


-- Brzozowski derivative of regular expression
-- From https://www.ccs.neu.edu/home/turon/re-deriv.pdf, page 5
-- Slight normalizations applied on stuck/epsilon RE's
derive :: Eq l => l -> RE l -> RE l
derive _ Epsilon = Empty
derive _ Empty   = Empty
derive l (Atom l') | l == l' = Epsilon
                   | otherwise = Empty
derive l (Pipe r1 r2) = case (derive l r1, derive l r2) of
  (Empty, r2') -> r2'
  (r1', Empty) -> r1'
  (r1', r2')   -> Pipe r1' r2'
derive l (Dot r1 r2)
  | definitelyEmpty r1 = derive l r2
  | possiblyEmpty r1   = Pipe (Dot (derive l r1) r2) $ derive l r2
  | otherwise          = Dot (derive l r1) r2
derive l (Star r) = Dot (derive l r) (Star r)


match :: Eq l => [l] -> RE l -> Bool
match w r = possiblyEmpty $ foldl (flip derive) r w
