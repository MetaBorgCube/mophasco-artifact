module Lang.LM where

import Hefty

import Hefty.Op.Error
import qualified Hefty.Op.Scope as S (edge, new, sink)
import Hefty.Op.Scope hiding (edge, new, sink)
import Hefty.Op.Scope.Weak as SW
import Hefty.Op.Scope.Strong as SS
import Hefty.Op.Scope.Critical
import Hefty.Op.Scope.AnyOrder
import Hefty.Op.Term.Exists
import Hefty.Op.Term.Equals
import Data.Foldable

import Control.Monad

import Data.Functor.Comp
import Data.Functor.Aggr
import Data.List
-- import qualified Data.Map as Map
import Data.Term
import Data.Regex

import qualified Data.Map as Map
-- import qualified Data.Functor.Aggr as h


{- TYPES -}

type Ty = Term ()

instance Show Ty where
  show (Const ()) = "()"
  show (Var i) = "α" ++ show i
  show (Term "->" [t1, t2]) = show t1 ++ " -> " ++ show t2
  show (Term "Num" []) = "Num"
  show (Term "Bool" []) = "Bool"
  show (Term f ts) = "(" ++ f ++ intercalate " " (map show ts) ++ ")"

-- Type construction
numT = Term "Num" []
boolT = Term "Bool" []
funT s t = Term "->" [s, t]


{- DECLS, LABELS, AND PATHS -}

data Label = P | D | M | I deriving (Eq, Show)
data Decl
  = Member { mname :: String, mtype :: Ty }
  | Unit { uname :: String, uscope :: Sc }
  deriving (Eq, Show)


-- Path order based on Ministatix priorities.
pPriority :: PathOrder Label Decl
pPriority p1 p2 = val == LT || val == EQ
  where
    val = pPriority' p1 p2

    pPriority' :: ResolvedPath Label Decl -> ResolvedPath Label Decl -> Ordering
    pPriority' (ResolvedPath p1 _ _) (ResolvedPath p2 _ _) = comparePaths (extractPath p1) (extractPath p2)

    comparePaths [] [] = EQ
    comparePaths (_:_) [] = GT
    comparePaths [] (_:_) = LT
    comparePaths (x:xs) (y:ys) = case compareLabel x y of
      Just r -> r
      Nothing -> comparePaths xs ys

    compareLabel M P = Just LT
    compareLabel P M = Just GT
    compareLabel M I = Just LT
    compareLabel I M = Just GT
    compareLabel D P = Just LT
    compareLabel P D = Just GT
    compareLabel D I = Just LT
    compareLabel I D = Just GT
    compareLabel I P = Just LT
    compareLabel P I = Just GT
    compareLabel _ _ = Nothing

    extractPath (Start _) = []
    extractPath (Step p l _) = extractPath p ++ [l]


{- OP SHORT-HANDS -}

edge :: forall g h. Scope g Sc Label Decl < h => Sc -> Label -> Sc -> Hefty h ()
edge = S.edge @g @_ @Label @Decl

new :: forall g h. Scope g Sc Label Decl < h => Hefty h Sc
new = S.new @g @_ @Label @Decl

sink :: forall g h. Scope g Sc Label Decl < h => Sc -> Label -> Decl -> Hefty h ()
sink = S.sink @g @_ @Label @Decl



{- LM SYNTAX -}

data Expr
  = Lit Int
  | Tru
  | Fls
  | Name String
  | Plus Expr Expr
  | Minus Expr Expr
  | Mult Expr Expr
  | Eql Expr Expr
  | If Expr Expr Expr
  | Fn (String, TyAnno) Expr
  | App Expr Expr
  | LetRec (String, Expr) Expr
  deriving (Eq, Show)

data Lm
  = Def String Expr
  | Mod String [Lm]
  | Imp String
  deriving (Eq, Show)

data TyAnno
  = LInt
  | LBool
  | LFn TyAnno TyAnno
  deriving (Eq, Show)

type Prog = Lm


{- LM TYPE CHECKER -}

lm :: forall g h.
      ( HFunctor h
      , Exists Ty < h
      , Equals Ty < h
      , Error String < h
      , Scope g Sc Label Decl < h
      , AnyOrder < h )
   => Lm -> Sc -> ( Hefty h
                  :.: Aggr (Sc -> [String])
                  :.: Hefty h
                  :.: Hefty h ) ()
lm (Def x e) s =
  -- create def declarations
  (do t <- exists
      sink @g s D (Member x t)
      pure t)
  &>- \t ->
  there $ there $ expr @g e s t
lm (Imp i) s =
  there $ here $ aggr (\s' -> [i | s == s']) $ const ()
lm (Mod x ms) s =
  (do s' <- new @g
      edge @g s' P s
      sink @g s M (Unit x s')
      pure s' ) &>>- \s' ->
  (  traverse_ (flip (lm @g) s') ms
  <* ( there (aggr (const []) id &>- \ im ->
       here $ imports @g (im s') s') ) )

imports :: forall g h.
           ( HFunctor h
           , Error String < h
           , Scope g Sc Label Decl < h
           , AnyOrder < h )
        => [String] -> Sc -> Hefty h ()
imports is s = anyOrder
  (map (\i -> modScope @g s i >>= maybe
    (pure Nothing)                            -- no module scope found, return error value (Nothing)
    (\s' -> edge @g s I s' >>= pure . Just)   -- module scope found, assert edge and return success
  ) is)
  -- No dynamic scheduling was correct: 
  (err "Could not resolve imports")

expr :: forall g h.
        ( HFunctor h
        , Exists Ty < h
        , Equals Ty < h
        , Error String < h
        , Scope g Sc Label Decl < h )
     => Expr -> Sc -> Ty -> Hefty h ()
expr (Lit _) _ t = equals t numT
expr Tru _ t = equals t boolT
expr Fls _ t = equals t boolT
expr (Name x) s t = do
  memberType @g x s >>= maybe
    (err $ "Unresolved variable: " ++ x)
    (equals t)
expr (Plus l r) g t = exprBinOp @g l r numT numT g t
expr (Minus l r) g t = exprBinOp @g l r numT numT g t
expr (Mult l r) g t = exprBinOp @g l r numT numT g t
expr (Eql l r) g t = exprBinOp @g l r numT boolT g t
expr (If c i f) g t = do
  c' <- exists
  expr @g c g c'
  equals c' boolT
  i' <- exists
  f' <- exists
  expr @g i g i'
  expr @g f g f'
  equals i' f'
  equals t i'
expr (Fn (p, pt) b) g t = do
  let paramType = toTy pt
  t' <- exists
  g' <- new @g
  edge @g g' P g
  sink @g g' D (Member p paramType)
  expr @g b g' t'
  equals t (funT paramType t')
  where toTy LInt = numT
        toTy LBool = boolT
        toTy (LFn f t) = funT (toTy f) (toTy t)
expr (App fn a) g t = do
  argType <- exists
  expr @g fn g (funT argType t)
  expr @g a g argType
expr (LetRec (v, e) b) g t = do
  t' <- exists
  g' <- new @g
  edge @g g' P g
  sink @g g' D (Member v t')
  expr @g e g' t'
  expr @g b g' t

exprBinOp :: forall g h.
             ( HFunctor h
             , Exists Ty < h
             , Equals Ty < h
             , Error String < h
             , Scope g Sc Label Decl < h )
             => Expr -> Expr -> Ty -> Ty -> Sc -> Ty -> Hefty h ()
exprBinOp l r wantInput wantOutput g t = do
  equals wantOutput t
  expr @g l g wantInput
  expr @g r g wantInput

modScope :: forall g h.
            Scope g Sc Label Decl < h
         => Sc -> String -> Hefty h (Maybe Sc)
modScope s x = do
  ds <- query @g s (star (atom P) ~. (eps ~| atom I) ~. atom M)
              pPriority
              (\ (Unit y _) -> x == y)
  if (length ds == 1)
    then pure $ Just $ uscope $ head ds
    else pure Nothing

memberType :: forall g h.
              Scope g Sc Label Decl < h
           => String -> Sc -> Hefty h (Maybe Ty)
memberType x s = do
  ds <- query @g s (star (atom P) ~. (eps ~| atom I) ~. atom D)
              pPriority
              (\ (Member y _) -> x == y)
  if (length ds == 1)
    then pure $ Just $ mtype $ head ds
    else pure $ Nothing

{- RUNNER -}

type LMA g = Exists Ty
           + Equals Ty
           + Scope g Sc Label Decl
           + Error String
           + Nop

type LMH g = AnyOrder
           + LMA g

type LMU = Either (UErr (Term ())) ((), UMap ())

runTC' :: forall g.
          Lm
       -> Handler_ (Scope g Sc Label Decl) LMU g (Error String + Nop) (LMU, g)
       -> (g -> (Sc, g))
       -> g
       -> Either String (g, UMap ())
runTC' l hScope addScope emptyGraph =
  let (sc, g) = addScope emptyGraph
      x = un
        $ handle hErr
        $ flip (handle_ hScope) g
        $ flip (handle_ hEquals) Map.empty
        $ flip (handle_ hExists) 0
        $ hfold pure (  eCritical @g @Label @Decl
                    \+/ aId @(LMA g)
                    \+/ aId
                    \+/ aId
                    \+/ aId
                    \+/ aId )
        $ hfold pure (  eAnyOrd2Crit
                    \+/ aId @(Critical () + LMA g)
                    \+/ aId
                    \+/ aId
                    \+/ aId
                    \+/ aId )
        $ join
        $ join
        $ fmap (runComp . unAggr . runComp)
        $ runComp
        $ ( lm @g @_ l sc
          :: ( Hefty (LMH g)
             :.: Aggr (Sc -> [String])
             :.: Hefty (LMH g)
             :.: Hefty (LMH g) ) () )
  in case x of
    Left s -> Left s
    Right (Left (UnificationError t1 t2), _) -> Left $ "Unification error: " ++ show t1 ++ " != " ++ show t2
    Right (Right (_, u), g) -> Right (g, u)


runTCW l = runTC' l SW.hScope SW.addScope SW.emptyGraph
runTCS l = runTC' l SS.hScope SS.addScope SS.emptyGraph


{- TEST PROGRAMS -}

basicdef :: Lm
basicdef = Def "x" (Lit 0)

selfref :: Lm
selfref = Def "x" (Name "x")

basicmod :: Lm
basicmod = Mod "Main"
  [ Def "x" (Name "y")
  , Def "y" (Lit 0) ]

importmod :: Lm
importmod = Mod "Main"
  [ Mod "A"
    [ Imp "B"
    , Def "x" (Name "y") ]
  , Mod "B"
    [ Def "y" (Lit 0) ] ]

nestedimportmod :: Lm
nestedimportmod = Mod "Main"
  [ Mod "A"
    [ Def "x" (Name "y")
    , Imp "C"
    , Imp "B" ]
  , Mod "B"
    [ Mod "C"
      [ Def "y" (Lit 0) ] ] ]

nestednomodel :: Lm
nestednomodel = Mod "Main"
  [ Mod "A"
    [ Imp "B"
    , Def "x" (Name "y") ]
  , Mod "B"
    [ Mod "B"
      [ Def "y" (Lit 0) ] ] ]

cyclicmod :: Lm
cyclicmod = Mod "Main"
  [ Mod "A" [ Imp "B" ]
  , Mod "B" [ Imp "A" ] ]

importshadow :: Lm
importshadow = Mod "Main"
  [ Mod "A" [ Mod "B" [] ]
  , Mod "B" []
  , Mod "M"
    [ Imp "B"
    , Imp "C"
    , Def "y" $ Lit 0 ]
  , Mod "C" [ Mod "B" [ Def "x" (Lit 19) ] ] ]

importambig :: Lm
importambig = Mod "Main"
  [ Mod "B" [ Mod "B" [ Def "x" (Lit 5) ] ]
  , Mod "M" [ Imp "B"
            , Imp "B"
            , Def "y" (Name "x") ] ]
