module Hefty.Op.Scope.Util where

import Hefty.Op.Scope ( ResolvedPath(..), ScopePath(..), Sc );

-- List/tuple helpers

lookupAll :: Eq a => a -> [(a, b)] -> [b]
lookupAll key = map snd . filter ((== key) . fst)

mapFst :: (a -> b) -> (a, c) -> (b, c)
mapFst f (a,c) = (f a, c)

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd f (a,b) = (a, f b)

mapPair :: (a -> c, b -> d) -> (a, b) -> (c, d)
mapPair (f1, f2) (a, b) = (f1 a, f2 b)

invListPair :: [([a], [b])] -> ([a], [b])
invListPair = mapPair (concat, concat) . unzip

-- Path helpers

dst :: ScopePath l -> Sc
dst (Start    s) = s
dst (Step _ _ s) = s

inPath :: Sc -> ScopePath l -> Bool
inPath sc (Start sc') = sc == sc'
inPath sc (Step p _ sc') = sc == sc' || inPath sc p

lenPath :: ScopePath l -> Int
lenPath (Start _) = 0
lenPath (Step p _ _) = 1 + lenPath p

dataOfPath :: ResolvedPath l d -> d
dataOfPath (ResolvedPath _ _ d) = d

lenRPath :: ResolvedPath l d -> Int
lenRPath (ResolvedPath p _ _) = lenPath p

pShortest :: ResolvedPath l d -> ResolvedPath l d -> Bool
pShortest p1 p2 = lenRPath p1 < lenRPath p2