module CriticalTest where

import Data.Regex


import Hefty

import Hefty.Op.Error

import Hefty.Op.Scope hiding (new, edge, sink)
import qualified Hefty.Op.Scope as S (new, edge, sink)
import Hefty.Op.Scope.Weak
import Hefty.Op.Scope.Util (pShortest)
import Hefty.Op.Scope.Critical

data Label = P | D
  deriving (Show, Eq)
type Decl = String

type G = Graph Label Decl

type TC = Scope G Sc Label Decl
        + Error String
        + Nop

edge :: forall h. Scope G Sc Label Decl < h => Sc -> Label -> Sc -> Hefty h ()
edge = S.edge @G @_ @Label @Decl

new :: forall h. Scope G Sc Label Decl < h => Hefty h Sc
new = S.new @G @_ @Label @Decl

sink :: forall h. Scope G Sc Label Decl < h => Sc -> Label -> Decl -> Hefty h ()
sink = S.sink @G @_ @Label @Decl


re :: RE Label
re = Star (Atom P) `Dot` Atom D

dAll :: Decl -> Bool
dAll = const True

testEarlierQError :: ( Scope G Sc Label Decl < h
                     , Critical () < h
                     , Error String < h)
                  => Hefty h ()
testEarlierQError = do
    s1 <- new
    query @G s1 re pShortest dAll
    critical @()
      (do
        sink s1 D "decl"
        return $ Just ()
      )
      (\_ -> return ())

testInsideQFailure :: ( Scope G Sc Label Decl < h
                      , Critical () < h
                      , Error String < h)
                   => Hefty h Bool
testInsideQFailure = do
    s1 <- new
    critical @()
      (do
        query @G s1 re pShortest dAll
        sink s1 D "decl"
        return $ Just True
      )
      (const $ return False)

testLaterQError :: ( Scope G Sc Label Decl < h
                   , Critical () < h
                   , Error String < h)
                => Hefty h ()
testLaterQError = do
    s1 <- new
    critical @()
      (do
        query @G s1 re pShortest dAll
        return $ Just ()
      )
      (\_ -> return ())
    sink s1 D "decl"
    return ()

type TH = Critical ()
        + Scope G Sc Label Decl
        + Error String
        + Nop

runTestC :: Hefty TH a -> Either String (a, G)
runTestC test =
  let x = un
        $ handle hErr
        $ flip (handle_ hScope) emptyGraph
        $ hfold pure (  eCritical @G @Label @Decl
                    \+/ aId
                    \+/ aId
                    \+/ aId )
        $ test
  in x
