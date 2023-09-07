module Hefty.Op.Term.Equals where

import Hefty

import Data.Term
import qualified Data.Map as Map

data Equals trm m k
  = Equals trm trm k
  | Unifiable trm trm (Bool -> k)
  | Inspect trm (trm -> k)
  deriving Functor

instance Algebraic (Equals trm) where
  algebraic (Equals t t' k) = Equals t t' k
  algebraic (Unifiable t t' k) = Unifiable t t' k
  algebraic (Inspect t k) = Inspect t k

equals :: forall trm h.
          Equals trm < h
       => trm -> trm -> Hefty h ()
equals t1 t2 = Op $ inj $ Equals t1 t2 (Pure ())

unifiable :: forall trm h.
             Equals trm < h
          => trm -> trm -> Hefty h Bool
unifiable t1 t2 = Op $ inj $ Unifiable t1 t2 Pure


inspect :: forall trm h.
           Equals trm < h
        => trm -> Hefty h trm
inspect t = Op $ inj $ Inspect t Pure


---------------
--- HANDLER ---
---------------

-- A handler that uses unification to resolve equality constraints

-- Unification errors
-- TODO: support error info
data UErr trm
  = UnificationError trm trm
  deriving Show

-- A unification map maps variables to terms
type UMap c = Map.Map Int (Term c)

-- Unification yields a unification map or errs
-- TODO: no occurs check
unify :: (Eq c, Show c) => Term c -> Term c -> UMap c -> Either (UErr (Term c)) (UMap c)
unify (Var i) c u | c /= Var i = if Map.member i u
                                 then unify (u Map.! i) c u
                                 else Right
                                    $ Map.alter (const $ Just $ inspectTerm u c) i
                                    $ Map.map (substIn i c) u
                  | otherwise = Right $ u
unify c (Var i) u = unify (Var i) c u
unify (Const c1) t2 u | t2 == Const c1 = Right u
                      | otherwise = Left $ UnificationError (Const c1) t2
unify t1 (Const c2) u | t1 == Const c2 = Right u
                      | otherwise = Left $ UnificationError t1 (Const c2)
unify (Term s1 as1) (Term s2 as2) u | s1 /= s2 || length as1 /= length as2 =
                                      Left $ UnificationError (Term s1 as1) (Term s2 as2)
                                    | otherwise = foldr
                                      (\ (t1, t2) ru -> do
                                          u' <- ru
                                          unify t1 t2 u')
                                      (Right u)
                                      (zip as1 as2)


-- -- Project a term without any free variables; or fail
-- -- TODO: no occurs check
-- projTerm :: UMap c -> Int -> Maybe (Term c)
-- projTerm u i = do
--   Map.lookup i u >>= foldTerm
--     (return . Const)
--     (projTerm u)
--     (\ s' tsm -> do
--         ts' <- mapM id tsm
--         return $ Term s' ts')

-- Project a term that may contain free variables
-- Note: does not implement occurs check
inspectVar :: UMap c -> Int -> Term c
inspectVar u i = case Map.lookup i u of
  Just t -> foldTerm
    Const
    (inspectVar u)
    Term
    t
  Nothing -> Var i

inspectTerm :: UMap c -> Term c -> Term c
inspectTerm m = foldTerm Const (inspectVar m) Term

hEquals :: ( Eq c
           , Show c
           , Algebraic h' )
        => Handler_ (Equals (Term c)) a (UMap c) h' (Either (UErr (Term c)) (a, UMap c))
hEquals = Handler_ {
    ret_ = \ x m -> return $ Right (x, m)
  , hdl_ = \ f m -> case f of
      Equals t1 t2 k ->
        let m'  = trace ("  " ++ show t1 ++ " === " ++ show t2) $ unify t1 t2 m
            m''   = case m' of
                      Right m'' -> trace (show m'') m'
                      Left _    -> m'
        in case m'' of
            Right m'' -> k m''
            Left err -> return $ Left err
      Unifiable t1 t2 k ->
        case unify t1 t2 m of
          Right m' -> k True m'
          Left _ -> k False m
      Inspect t k ->
        k (inspectTerm m t) m
  }
  where
    trace = const id

