module Hefty.Op.Scope.Weak where

import Data.List
import Data.Regex

import Hefty
import Hefty.Op.Scope 
    (Sc, PathOrder, ResolvedPath (ResolvedPath), Scope (..), Q (Q), ScopePath (..))
import Hefty.Op.Scope.Util
    ( lookupAll, mapSnd, dst, inPath, dataOfPath )
import Hefty.Op.Error


-- Semantic scope graph

data Graph l d
  = Graph { scopes  :: Sc
          , edges   :: Sc -> [(l, Sc)]
          , sinks   :: Sc -> [(l, d)]
          , clos    :: Sc -> [l] }

instance (Show l, Show d) => Show (Graph l d) where
  show g = "Graph {\n  edges:\n" ++ formatEdges ++ "  sinks:\n" ++ formatSinks ++ "}"
    where
      edgesOf sc = map (\(l, sc') -> (sc, l, sc')) $ edges g sc
      edges'     = concatMap edgesOf [0..scopes g]

      formatEdge (sc, l, sc') = "    " ++ show sc ++ " -" ++ show l ++ "-> " ++ show sc' ++ "\n"
      formatEdges = concatMap formatEdge edges'

      sinksOf sc = map (\case (l, d) -> (sc, l, d)) $ sinks g sc
      sinks'     = concatMap sinksOf [0..scopes g]

      formatSink (sc, l, d) = "    " ++ show sc ++ " |-" ++ show l ++ "-> " ++ show d ++ "\n"
      formatSinks = concatMap formatSink sinks'


-- Semantic actions

emptyGraph :: Graph l d
emptyGraph = Graph 0 (const []) (const []) (const [])

addScope :: Graph l d -> (Sc, Graph l d)
addScope g = let sc' = scopes g + 1
  in (sc', g { scopes = sc' })

addEdge :: ( Eq l
           , Show l )
        => Graph l d -> Sc -> l -> Sc -> Either String (Graph l d)
addEdge g s l s' =
  if s <= scopes g
  then if s' <= scopes g
       then if l `elem` clos g s
            then Left $ "Monotonicity error: the scope " ++ show s ++ " has already been queried for labels " ++ show l
            else Right $ rawAdd g s l s'
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
  then if l `elem` clos g s
       then Left $ "Monotonicity error: the scope " ++ show s ++ " has already been queried for labels " ++ show l
       else case sinks g s of
         [] -> Right $ rawAdd g s l d
         sinks ->
           if (l,d) `elem` sinks
           then Left $ "Error: there is already a declaration " ++ show d ++ " at label " ++ show l
           else Right $ rawAdd g s l d
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
execQuery mode g sc re po ad = mapSnd (shortest po) $ findAll g re ad $ Start sc
  where
    -- derived from https://hackage.haskell.org/package/partial-order-0.2.0.0/docs/src/Data.PartialOrd.html#minima
    shortest :: (Eq l, Eq d) => PathOrder l d -> [ResolvedPath l d] -> [ResolvedPath l d]
    shortest po ps = nub $ filter isExtremal ps
      where
        isExtremal p = not $ any (`po` p) $ filter (/= p) ps

    resolveLbl p re_old ad l g =
      let sc = dst p
          re = derive l re_old
          -- declarations in current scope
          sinks' = if possiblyEmpty re then map (ResolvedPath p l) . filter ad . lookupAll l $ sinks g $ dst p else []
          -- targets of traversible edges (filtering scopes in `p`: prevent cycles)
          tgts = filter (not . flip inPath p) . lookupAll l $ edges g $ dst p
          -- close `l` in `g` if not already closed
          g' = if not mode || l `elem` clos g sc
               then g
               else g { clos = \ sc' -> if sc == sc'
                                        then l : clos g sc
                                        else clos g sc'
                      }
      in  -- results of residual queries over `tgts`
          foldr find (g', sinks') tgts
        where
          find s (g, p') = mapSnd (p' ++) $ findAll g re ad $ Step p l s

    findAll g re ad p = foldr find (g, []) $ frontier re
      where
        find l (g, p') = mapSnd (p' ++) $ resolveLbl p re ad l g


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
