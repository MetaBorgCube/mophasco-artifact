module Data.Term where

data Term c
  = Const c
  | Var Int
  | Term String [Term c]
  deriving (Eq, Show)

foldTerm :: (c -> b)
         -> (Int -> b)
         -> (String -> [b] -> b)
         -> Term c
         -> b
foldTerm genC _    _   (Const c)   = genC c
foldTerm _    genV _   (Var i)     = genV i
foldTerm genC genV alg (Term s ts) = alg s (map (foldTerm genC genV alg) ts)

substIn :: Int -> Term c -> Term c -> Term c
substIn i t = foldTerm
  Const
  (\ j -> if i == j then t else Var j)
  Term

substsIn :: [(Int, Term c)] -> Term c -> Term c
substsIn substs = foldTerm
  Const
  (\ j -> case lookup j substs of
      Just t -> t
      Nothing -> Var j)
  Term
