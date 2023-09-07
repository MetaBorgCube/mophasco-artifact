module LMParser (parseFromString) where

import ATerms.ATerm (ATerm(..))
import qualified ATerms.Parser as P
import Lang.LM (Expr(..), Lm(..), Prog, TyAnno(..))

parseFromString :: String -> Either String Prog
parseFromString str = do
  root <- aterms str
  case root of
    (AFunc "Program" [_ignored, decls]) -> fmap (Mod "") $ mapM parseLm $ listify decls
    _ -> Left $ "Unknown top-level coonstruct: " ++ show root

parseLm :: ATerm -> Either String Lm
parseLm (AFunc "Module" [AStr name, decls]) = do
  decls' <- mapM parseLm $ listify decls
  return $ Mod name decls'    
parseLm (AFunc "Import" [n]) = do
  n' <- parseMod n
  return $ Imp n'
parseLm (AFunc "Def" (b:_)) = do
  (p, q) <- parseBind b
  return $ Def p q
  where
    parseBind (AFunc "DefBind" [AStr n, e]) = do
      e' <- parseExp e
      return (n, e')
    parseBind t = Left $ "Unknown bind: " ++ show t
parseLm t = Left $ "Unknown declaration: " ++ show t

parseExp :: ATerm -> Either String Expr
parseExp (AFunc "Int" [AStr v]) = return $ Lit (read v :: Int)
parseExp (AFunc "True" []) = return Tru
parseExp (AFunc "False" []) = return Fls
parseExp (AFunc "Var" [v]) = do
  v' <- parseVar v
  return $ Name v'
parseExp (AFunc "If" [c, t, f]) = do
  c' <- parseExp c
  t' <- parseExp t
  f' <- parseExp f
  return $ If c' t' f'
parseExp (AFunc "Fun" [AFunc "ArgDecl" [AStr n, a], b]) = do
  a' <- parseType a
  b' <- parseExp b
  return $ Fn (n, a') b'
parseExp (AFunc "App" [fn, a]) = do
  fn' <- parseExp fn
  a' <- parseExp a
  return $ App fn' a'
parseExp (AFunc "LetRec" [ACons (AFunc "DefBind" [AStr n, e]) _, b]) = do
  e' <- parseExp e
  b' <- parseExp b
  return $ LetRec (n, e') b'
parseExp (AFunc bin [l, r]) = do
  l' <- parseExp l
  r' <- parseExp r
  case bin of
    "Add" -> return $ Plus l' r'
    "Sub" -> return $ Minus l' r'
    "Mul" -> return $ Mult l' r'
    "Eq" -> return $ Eql l' r'
    _ -> Left $ "Unknown binop: " ++ bin 
parseExp t = Left $ "Unknown construct: " ++ show t

parseMod :: ATerm -> Either String String
parseMod (AFunc "ModRef" [AStr n]) = return n
parseMod x = Left $ "Unknown module reference: " ++ show x

parseVar :: ATerm -> Either String String
parseVar (AFunc "VarRef" [AStr n]) = return n
parseVar x = Left $ "Unknown var reference: " ++ show x

parseType :: ATerm -> Either String TyAnno
parseType (AFunc "TInt" []) = return LInt
parseType (AFunc "TBool" []) = return LBool
parseType t = Left $ "Unknown type: " ++ show t

listify :: ATerm -> [ATerm]
listify ANil = []
listify (ACons h t) = h : listify t
listify x = [x]

aterms :: String -> Either String ATerm
aterms = P.parse