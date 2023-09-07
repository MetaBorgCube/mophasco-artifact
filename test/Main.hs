module Main (main) where

import Control.Monad (void)

import Data.Either (isRight)
import Hefty.Op.Term.Equals (UMap)
import Hefty.Op.Scope
    ( PathOrder )
import Hefty.Op.Scope.Util ( lenRPath )
import Hefty.Op.Scope.Strong
    ( Graph, emptyGraph, addScope, addEdge, addSink, execQuery )
import Lang.LM (runTCS, Label, Decl, Prog)
import Lang.MiniML hiding (Label, Decl)
import LMParser (parseFromString)
import System.Exit (exitFailure, exitSuccess)
import Test.HUnit
import Data.Regex

import qualified CriticalTest as CT hiding (Label, Decl)

main :: IO ()
main = do
  res <- runTestTT $ TestList [testsLM, testsSG, testC]
  print res
  if errors res > 0 || failures res > 0 then exitFailure else exitSuccess


pid :: MiniML
pid = Let (PVar "id") (Abs (PVar "x") (Ident "x")) (Ident "id")

evenOdd :: MiniML
evenOdd = LetRec (PPair (PVar "even") (PVar "odd"))
                 (PExpr
                   (Abs (PVar "x")
                     $ If (Eq (Ident "x") $ Num 0)
                       Tru
                       (App (Ident "odd") (Sub (Ident "x") (Num 1)))
                   )
                   (Abs (PVar "x")
                     $ If (Eq (Ident "x") $ Num 0)
                       Fls
                       (App (Ident "even") (Sub (Ident "x") (Num 1)))
                   )
                 )
                 (App (Ident "even") (Num 3))

testsLM :: Test
testsLM = TestList
  [ goodWeatherTest "cycles-big.aterm"
  , goodWeatherTest "cycles-self.aterm"
  , goodWeatherTest "cycles-simple.aterm"
  , goodWeatherTest "cycles-with-defs.aterm"
  , goodWeatherTest "empty.aterm"
  , badWeatherTest "import-ambiguity.no.aterm"
  , goodWeatherTest "import-inner-then-outer.aterm"
  , goodWeatherTest "import-outer-then-inner.aterm"
  , goodWeatherTest "import-shadowing-twice.aterm"
  , goodWeatherTest "import-shadowing.aterm"
  , goodWeatherTest "import-sibling.aterm"
  , badWeatherTest "inner-invisible-in-outer.no.aterm"
  , goodWeatherTest "inner-shadows-outer.aterm"
  , badWeatherTest "missing-def.no.aterm"
  , goodWeatherTest "mutual-ref-def.aterm"
  , goodWeatherTest "outer-visible-in-inner.aterm"
  , goodWeatherTest "param-shadows-def.aterm"
  , badWeatherTest "param-shadows-def.no.aterm"
  , goodWeatherTest "rec-defs.aterm"
  , goodWeatherTest "rec-function-def.aterm"
  , goodWeatherTest "rec-function-letrec.aterm"
  , goodWeatherTest "seq-defs.aterm"
  , goodWeatherTest "self-ref-def.aterm"
  , badWeatherTest "type-mismatch.no.aterm"
  ]


goodWeatherTest :: String -> Test
goodWeatherTest path = path ~: do
  contents <- readFile (lm path)
  let parsed = parseFromString contents
  assertEqual "It parsed properly" True $ isRight parsed
  assertEqual "It passes type checking" True $ isRight $ typeCheck parsed

badWeatherTest :: String -> Test
badWeatherTest path = path ~: do
  contents <- readFile (lm path)
  let parsed = parseFromString contents
  assertEqual "It parsed properly" True $ isRight parsed
  assertEqual "It fails type checking" False $ isRight $ typeCheck parsed

typeCheck :: Either String Prog -> Either String (Graph Label Decl, UMap ())
typeCheck input = input >>= runTCS

lm :: String -> String
lm s = "./test/programs/lm/" ++ s

-- Scope Graph Tests

noOrd :: PathOrder l d
noOrd _ _ = False

lenOrd :: PathOrder l d
lenOrd p p' = lenRPath p < lenRPath p'


testValidExtension1 = do
  let g0 = emptyGraph @Int @String
  let (s1, g1) = addScope g0
  let (s2, g2) = addScope g1
  let (g3, _)  = execQuery True g2 s2 (Atom 1) noOrd (const True)
  addEdge g3 s2 1 s1

testInValidExtension2 = do
  let g0 = emptyGraph @Int @String
  let (s2, g1) = addScope g0
  let (g2, _)  = execQuery True g1 s2 (Atom 1) noOrd (const True)
  addSink g2 s2 1 "Test"

testValidExtension3 = do
  let g0 = emptyGraph @Int @String
  let (s2, g1) = addScope g0
  let (g2, _)  = execQuery True g1 s2 (Atom 1) noOrd (const True)
  addSink g2 s2 2 "Test"

testInValidExtensionTransitive = do
  let g0 = emptyGraph @Int @String
  let (s1, g1) = addScope g0
  let (s2, g2) = addScope g1
  let (g3, _)  = execQuery True g2 s2 (Star $ Atom 1) noOrd (const True)
  g4 <- addEdge g3 s2 1 s1
  addSink g4 s1 1 "Test"

testValidExtensionShadowed = do
  let g0 = emptyGraph @Int @String
  let (s1, g1) = addScope g0
  let (s2, g2) = addScope g1
  g3 <- addEdge g2 s2 1 s1
  g4 <- addSink g3 s2 1 "Test1"
  let (g5, _)  = execQuery True g4 s2 (Star $ Atom 1) lenOrd (const True)
  addSink g5 s1 1 "Test2"

testInValidExtensionShadowed = do
  let g0 = emptyGraph @Int @String
  let (s1, g1) = addScope g0
  let (s2, g2) = addScope g1
  g3 <- addEdge g2 s2 1 s1
  g4 <- addSink g3 s1 1 "Test1"
  let (g5, _)  = execQuery True g4 s2 (Star $ Atom 1) lenOrd (const True)
  addSink g5 s2 1 "Test2"

expectSuccess :: Either String a -> IO a
expectSuccess = either assertFailure return

expectFailure :: String -> Either String a -> IO ()
expectFailure msg = either (const $ return ()) (const $ assertFailure msg)

testsSG :: Test
testsSG = TestList $ map TestCase
  [ expectSuccess $ void testValidExtension1
  , expectFailure "New sink should have invalidated query" $ void testInValidExtension2
  , expectSuccess $ void testValidExtension3
  , expectFailure "New sink should have invalidated query" $ void testInValidExtensionTransitive
  , expectSuccess $ void testValidExtensionShadowed
  , expectFailure "New sink invalidates old result" $ void testInValidExtensionShadowed
  ]

testC :: Test
testC = TestList
  [ "testEarlierQError" ~: expectFailure "No critical edge error" $ void $ CT.runTestC CT.testEarlierQError
  , "testInsideQFailure" ~: do
      let r = CT.runTestC CT.testInsideQFailure
      either
        assertFailure
        (assertEqual "Query validation succeeded unexpectedly" False . fst)
        r
  , "testLaterQError" ~: expectFailure "No critical edge error" $ void $ CT.runTestC CT.testLaterQError
  ]