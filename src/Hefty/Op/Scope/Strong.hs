module Hefty.Op.Scope.Strong where

import Data.List
import Data.Regex

import Hefty
import Hefty.Op.Scope (Sc, PathOrder, ResolvedPath (ResolvedPath), Scope (..), Q (Q), ScopePath (..))
import Hefty.Op.Scope.Util (mapFst, mapSnd, dst, invListPair, dataOfPath, lookupAll, inPath)
import Hefty.Op.Error

data QRes s l d
  = QRes (ScopePath l) (RE l) (PathOrder l d) (d -> Bool)

data Graph l d
  = Graph { scopes  :: Sc
          , edges   :: Sc -> [(l, Sc)]
          , sinks   :: Sc -> [(l, d)]
          , rqs     :: Sc -> [(QRes Sc l d, [ ResolvedPath l d ])] }

instance (Show l, Show d) => Show (Graph l d) where
  show g = "Graph {\n  edges:\n" ++ formatEdges ++ "  sinks:\n" ++ formatSinks ++ "}"
    where
      edgesOf sc = map (\(l, sc') -> (sc, l, sc')) $ edges g sc
      edges'     = concatMap edgesOf [0..scopes g]

      formatEdge (sc, l, sc') = "    " ++ show sc ++ " -" ++ show l ++ "-> " ++ show sc' ++ "\n"
      formatEdges = concatMap formatEdge edges'

      sinksOf sc = map (\(l, d) -> (sc, l, d)) $ sinks g sc
      sinks'     = concatMap sinksOf [0..scopes g]

      formatSink (sc, l, d) = "    " ++ show sc ++ " |-" ++ show l ++ "-> " ++ show d ++ "\n"
      formatSinks = concatMap formatSink sinks'

-- Monotonicity

validateMonotonicity :: (Eq l, Eq d, Show l, Show d)
                      => Graph l d
                      -> Sc
                      -> l
                      -> Either String (Graph l d)
validateMonotonicity g s l = foldl (\agg (QRes p re po ad, ps) -> do
                                           g' <- agg
                                           let (ps', rqs') = findLbl g' p re po ad l
                                           if any (notShadowed ps po) ps' then
                                             Left "Monotonicity error: Some previous query result changed."
                                           else
                                             Right $ updateRQS True g' rqs' ps
                                   )
                                   (Right g)
                                   (rqs g s)
  where
    notShadowed ps po p = not $ any (`po` p) ps

updateRQS :: Bool -> Graph l d -> [(Sc, QRes Sc l d)] -> [ResolvedPath l d] -> Graph l d
updateRQS True g rqs' pps = g { rqs = \sc -> map ((, pps) . snd) (filter ((sc ==) . fst) rqs') ++ rqs g sc }
updateRQS False g _ _ = g

-- Semantic actions

emptyGraph :: Graph l d
emptyGraph = Graph 0 (const []) (const []) (const [])

addScope :: Graph l d -> (Sc, Graph l d)
addScope g = let sc' = scopes g + 1
  in (sc', g { scopes = sc' })

addEdge :: ( Eq l, Eq d
           , Show l, Show d )
        => Graph l d -> Sc -> l -> Sc -> Either String (Graph l d)
addEdge g s l s' =
  if s <= scopes g
  then if s' <= scopes g
       then let g' = rawAdd g s l s' in
            validateMonotonicity g' s l
       else Left $ "Invalid scope: " ++ show s'
  else Left $ "Invalid scope: " ++ show s
  where
    rawAdd g s l s' =
      g { edges = \ sc -> if sc == s
                            then (l, s'):edges g s
                            else edges g sc }

addSink :: ( Eq l
           , Eq d
           , Show d
           , Show l )
        => Graph l d -> Sc -> l -> d -> Either String (Graph l d)
addSink g s l d =
  if s <= scopes g
  then if (l,d) `elem` sinks g s
       then Left $ "Error: there is already a declaration " ++ show d ++ " at label " ++ show l
       else let g' = rawAdd g s l d in
            validateMonotonicity g' s l
  else Left $ "Invalid scope: " ++ show s
  where
    rawAdd g s l d =
      g { sinks = \ sc -> if sc == s
                            then (l, d):sinks g s
                            else sinks g sc }

execQuery :: ( Show d , Show l , Eq l, Eq d )
          => Bool
          -> Graph l d
          -> Sc
          -> RE l
          -> PathOrder l d
          -> (d -> Bool)
          -> (Graph l d, [ResolvedPath l d])
execQuery mode g sc re po ad =
  let (ps, rqs) = mapFst (shortest po) $ findAll g re po ad $ Start sc
      g'        = updateRQS mode g rqs ps
    in (g', ps)
  where
    -- derived from https://hackage.haskell.org/package/partial-order-0.2.0.0/docs/src/Data.PartialOrd.html#minima
    shortest :: (Eq l, Eq d) => PathOrder l d -> [ResolvedPath l d] -> [ResolvedPath l d]
    shortest po ps = nub $ filter isExtremal ps
      where
        isExtremal p = not $ any (`po` p) $ filter (/= p) ps

findAll :: ( Show d , Show l , Eq l, Eq d )
          => Graph l d
          -> RE l
          -> PathOrder l d
          -> (d -> Bool)
          -> ScopePath l
          -> ([ResolvedPath l d], [(Sc, QRes s l d)])
findAll g re po ad p = mapSnd ((dst p, QRes p re po ad) :) . invListPair . map (findLbl g p re po ad) $ frontier re

findLbl :: ( Show d , Show l , Eq l, Eq d )
          => Graph l d
          -> ScopePath l
          -> RE l
          -> PathOrder l d
          -> (d -> Bool)
          -> l
          -> ([ResolvedPath l d], [(Sc, QRes s l d)])
findLbl g p re_old po ad l =
  let re = derive l re_old
      -- declarations in current scope
      sinks' = if possiblyEmpty re then map (ResolvedPath p l) . filter ad . lookupAll l $ sinks g $ dst p else []
      -- targets of traversible edges (filtering scopes in `p`: prevent cycles)
      tgts = filter (not . flip inPath p) . lookupAll l $ edges g $ dst p
      -- results of residual queries over `tgts`
      (ps, rqs) = invListPair $ map (findAll g re po ad . Step p l) tgts
  in (sinks' ++ ps, rqs)

-- Handler

hScope :: ( Eq l, Show l
          , Eq d, Show d
          , Error String < h )
       => Handler_ (Scope (Graph l d) Sc l d) a (Graph l d) h (a, Graph l d)
hScope = Handler_
  (curry return)
  (\ f g -> case f of
      New k ->
        let (sc, g') = addScope g
        in k sc g'
      Edge sc l sc' k ->
        case addEdge g sc l sc' of
          Left s -> err s
          Right g' -> k g'
      Sink sc l d k ->
        case addSink g sc l d of
          Left s -> err s
          Right g' -> k g'
      Query mode (Q sc re po ad) k ->
        let (g', rs) = execQuery mode g sc re po ad
        in k (map dataOfPath rs) g'
      Mark k -> k g g
      Rollback g' k -> k g')



