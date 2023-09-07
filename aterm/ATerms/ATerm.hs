module ATerms.ATerm where

import Data.List

data ATerm  = AFunc String [ATerm]
            | AStr String
            | ACons ATerm ATerm
            | ANil
            | ATuple [ATerm]
            deriving (Eq)

pretty :: ATerm -> String
pretty (AFunc sym rs) = sym ++ "(" ++ intercalate "," (fmap pretty rs) ++ ")"
pretty (AStr txt)     = "\"" ++ txt ++ "\""
pretty (ACons r rs)   = pretty r ++ ":" ++ pretty rs
pretty ANil           = "[]"
pretty (ATuple ts)    = "(" ++ intercalate "," (fmap pretty ts) ++ ")"

instance Show ATerm where
  show = pretty

atermList :: [ATerm] -> ATerm
atermList = foldr ACons ANil
