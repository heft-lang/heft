module Heft.Util where

import Heft.Syntax.Expr

getMainExpr :: Program -> Maybe Expr
getMainExpr (Program ds) = go ds where
  go (Function "main" Nothing [] e:_) = Just e
  go (_:xs) = go xs
  go [] = Nothing

letify :: Program -> Expr -> Expr
letify (Program ds0) expr = go ds0 where
  go (Function f Nothing [] e : ds) = Letrec f e (go ds)
  go (_ : ds) = go ds
  go [] = expr
