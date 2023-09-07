module Lang.MiniML where

import Hefty

import Hefty.Op.Error
import qualified Hefty.Op.Scope as S (edge, new, sink, query)
import Hefty.Op.Scope hiding (edge, new, sink, query)
import Hefty.Op.Term.Exists
import Hefty.Op.Term.Equals

import Data.List
-- import qualified Data.Map as Map
import Data.Term
import Data.Regex
import Hefty.Op.Scope.Util (pShortest)
import Hefty.Op.Scope.Weak (Graph, emptyGraph, hScope)
import Data.Map (empty)
import Data.Functor ((<&>))
import Control.Monad (when)

-- import Debug.Trace (trace)
trace = const id

{- TYPES -}

type Ty = Term Int

instance Show Ty where
  show (Const i) = "cα" ++ show i
  show (Var i) = "α" ++ show i
  show (Term "->" [t1, t2]) = show t1 ++ " -> " ++ show t2
  show (Term "Num" []) = "Num"
  show (Term "Bool" []) = "Bool"
  show (Term "Null" []) = "Null"
  show (Term "Pair" [t1, t2]) = "<" ++ show t1 ++ ", " ++ show t2 ++ ">"
  show (Term f ts) = f ++ "(" ++ unwords (map show ts) ++ ")"

-- Type construction
numT = Term "Num" []
boolT = Term "Bool" []
pairT t1 t2 = Term "Pair" [t1, t2]
nullT = Term "Null" []
funT s t = Term "->" [s, t]

-- Free variables
fv :: Term Int -> [Int]
fv (Const _) = []
fv (Var i) = [i]
fv (Term _ ts) = nub $ concatMap fv ts

data Scheme
    = Scheme [Int] Ty
  deriving (Eq)

sfv :: Scheme -> [Int]
sfv (Scheme xs t) = fv t \\ xs

instance Show Scheme where
    show (Scheme [] t) = show t
    show (Scheme xs t) = "(∀ " ++ unwords (map (("α" ++) . show) xs) ++ ". " ++ show t ++ ")"

{- DECLS, LABELS, AND PATHS -}

data Label = P | D deriving (Eq, Show)
data Decl
  = Decl { dname :: String, dtype :: Scheme }
  deriving (Eq, Show)

{- miniml SYNTAX -}

data Pat
  = PPair Pat Pat
  | PNull
  | PVar String
  deriving (Eq, Show)

data MiniML
  = Num Int
  | Fls
  | Tru
  | Null
  | If MiniML MiniML MiniML
  | PExpr MiniML MiniML
  | Plus MiniML MiniML
  | Sub MiniML MiniML
  | Eq MiniML MiniML
  | Abs Pat MiniML
  | Ident String
  | App MiniML MiniML
  | Let Pat MiniML MiniML
  | LetRec Pat MiniML MiniML
  deriving (Eq, Show)


{- OP SHORT-HANDS -}

edge :: forall g h. Scope g Sc Label Decl < h => Sc -> Label -> Sc -> Hefty h ()
edge sc lbl sc' = trace (show sc ++ " -" ++ show lbl ++ "-> " ++ show sc')
                  $ S.edge @g @_ @Label @Decl  sc lbl sc'

new :: forall g h. Scope g Sc Label Decl < h => Hefty h Sc
new = S.new @g @_ @Label @Decl

sink :: forall g h. Scope g Sc Label Decl < h => Sc -> Label -> Decl -> Hefty h ()
sink sc lbl d = trace (show sc ++ " |-" ++ show lbl ++ "-> " ++ show d)
                $ S.sink @g sc lbl d

query :: forall g h. Scope g Sc Label Decl < h => Sc -> RE Label -> PathOrder Label Decl -> (Decl -> Bool) -> Hefty h [Decl]
query sc re po ad = trace (show sc ++ " ~>" ++ show re)
                    $ S.query @g sc re po ad

instantiate :: ( Error String < h
               , Exists Ty < h
               , Equals Ty < h )
            => Scheme -> Hefty h Ty
instantiate (Scheme xs t) = do
    -- sanity check: quantified variables should not be instantiated later
    mapM_ isFree xs
    substs <- mapM (\i -> exists <&> (i,)) xs
    t <- inspect t
    return $ substsIn substs t

generalize :: forall g h.
              ( Scope g Sc Label Decl < h
              , Equals Ty < h
              , Error String < h)
           => Sc -> Ty -> Hefty h Scheme
generalize sc t = do
    ds <- trace "gen: " $ query @g
                      sc
                      (Atom P `Dot` Star (Atom P) `Dot` Atom D)
                      (\_ _ -> False)
                      (const True)
    let fv_s = concatMap (sfv . dtype) ds
    t <- inspect t
    let fv_t = fv t
    return $ Scheme (fv_t \\ fv_s) t

isFree :: (Equals Ty < h, Error String < h) => Int -> Hefty h ()
isFree v = do
  let v' = Var v :: Ty
  v'' <- inspect v'
  when (v' /= v'') $ err $ "BUG: Quantifier variable " ++ show v' ++ " was later instantiated to " ++ show v''

{- Type Checker -}

-- Type checker for an MLy language
miniml :: forall g h.
       ( HFunctor h
       , Exists Ty < h
       , Equals Ty < h
       , Error String < h
       , Scope g Sc Label Decl < h )
    => MiniML -> Sc -> Ty -> Hefty h ()
miniml (Num _) _ t = equals t numT
miniml Fls _ t = equals t boolT
miniml Tru _ t = equals t boolT
miniml Null _ t = equals t nullT
miniml (If c e1 e2) sc t = do
  miniml' @g c sc boolT
  miniml' @g e1 sc t
  miniml' @g e2 sc t
miniml (PExpr e1 e2) sc t = do
  t1 <- exists
  t2 <- exists
  miniml' @g e1 sc t1
  miniml' @g e2 sc t2
  t1 <- inspect t1
  t2 <- inspect t2
  equals t $ pairT t1 t2
miniml (Plus e1 e2) sc t = do
  equals t numT
  miniml' @g e1 sc numT
  miniml' @g e2 sc numT
miniml (Sub e1 e2) sc t = do
  equals t numT
  miniml' @g e1 sc numT
  miniml' @g e2 sc numT
miniml (Eq e1 e2) sc t = do
  equals t boolT
  miniml' @g e1 sc numT
  miniml' @g e2 sc numT
miniml (Abs p b) sc t = do
  t' <- exists
  sc' <- new @g
  edge @g sc' P sc
  s <- tpat @g p sc'
  miniml' @g b sc' t'
  t' <- inspect t'
  equals t (funT s t')
miniml (Ident x) sc t = do
  ds <- trace "ref" $ query @g
          sc
          (Star (Atom P) `Dot` Atom D)
          pShortest
          ((x ==) . dname)
  if length ds == 1
    then do
      dt <- instantiate $ dtype $ head ds
      equals t dt
    else if null ds
         then err $ "Query failed: unbound identifier " ++ x
         else err $ "Query yielded ambiguous binders for " ++ x
miniml (App f a) sc t = do
  s <- exists
  miniml' @g f sc (funT s t)
  miniml' @g a sc s
miniml (Let p e body) sc t = do
  t' <- exists
  miniml' @g e sc t'
  st <- inspect t'
  sc' <- new @g
  edge @g sc' P sc
  spat @g p st sc'
  miniml' @g body sc' t
miniml (LetRec p e body) sc t = do
  sc' <- new @g
  edge @g sc' P sc
  t' <- tpat @g p sc'
  miniml' @g e sc' t'
  miniml' @g body sc' t

miniml' :: forall g h.
        ( Scope g Sc Label Decl < h,
          Error String < h,
          Exists Ty < h,
          Equals Ty < h)
     => MiniML -> Sc -> Ty -> Hefty h ()
miniml' e sc t = do
  t' <- inspect t
  trace (show sc ++ " |- " ++ show e ++ " : " ++ show t') $ miniml @g e sc t
-- miniml' == miniml

-- Used for recursive lets and lambda abstractions
-- For each variable in the pattern
-- * creates a fresh meta-variable
-- * creates a declaration in the scope graph
-- Returns the expected type of the pattern
tpat :: forall g h.
        ( Scope g Sc Label Decl < h
        , Exists Ty < h )
     => Pat -> Sc -> Hefty h Ty
tpat PNull _ = return nullT
tpat (PVar x) sc = do
  t <- exists
  sink @g sc D (Decl x $ Scheme [] t)
  return t
tpat (PPair p1 p2) sc = do
  t1 <- tpat @g p1 sc
  t2 <- tpat @g p2 sc
  return $ pairT t1 t2

-- Used for generalizing lets
-- For each variable in the pattern
-- * generalizes the corresponding type
-- * creates a declaration in the scope graph
spat :: forall g h.
        ( Scope g Sc Label Decl < h
        , Exists Ty < h
        , Error String < h
        , Equals Ty < h)
     => Pat -> Ty -> Sc -> Hefty h ()
spat (PVar x) t sc = do
  s <- generalize @g sc t
  sink @g sc D (Decl x s)
spat (PPair p1 p2) (Term "Pair" [t1, t2]) sc = do
  spat @g p1 t1 sc
  spat @g p2 t2 sc
spat PNull (Term "Null" []) _ = return ()
spat _ _ _ = err "Let initializer does not match pattern"

{- Handler -}

runTC :: MiniML -> Either String (UMap Int, Graph Label Decl, Scheme)
runTC e =
  let x = un
        $ handle hErr
        $ flip (handle_ hScope) emptyGraph
        $ flip (handle_ hEquals) empty
        $ flip (handle_ hExists) 0
        (do t <- exists
            miniml' @(Graph Label Decl) e 0 t
        :: Hefty ( Exists Ty
                 + Equals Ty
                 + Scope (Graph Label Decl) Sc Label Decl
                 + Error String
                 + Nop )
                 () )
  in case x of
    Left s                                   -> Left s
    Right (Left (UnificationError t1 t2), _) -> Left $ "Unification error: " ++ show t1 ++ " != " ++ show t2
    Right (Right (_, u), sg)                 ->
      let t' = inspectVar u 0
          vs = fv t'
       in Right (u, sg, Scheme vs t')
