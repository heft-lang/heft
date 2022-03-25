{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Heft.Parser where

import Data.Char (isAlphaNum, isSpace)
import Data.String (IsString (..))
import Heft.AST
import Text.ParserCombinators.UU hiding (pReturn)
import Text.ParserCombinators.UU.BasicInstances hiding (Parser)

--------------------------------------------------------------------------------
-- ParseUtils
--------------------------------------------------------------------------------

type Parser a = P (Str Char String LineColPos) a

lexeme :: Parser a -> Parser a
lexeme p = p <* whitespace

-- Here we specify that our language uses Haskell-like '--' syntax for line comments
whitespace :: Parser ()
whitespace =
  () <$ pList1 ((pToken "--" *> pMunch (/= '\n') <?> "Line Comment") <|> pSatisfy isSpace (Insertion "Space" ' ' 5) *> pMunch isSpace)
    `opt` ()

-- We define an instance of IsString so that we can write literal strings to mean parsers that parse exactly those literal strings.
instance (a ~ String) => IsString (Parser a) where
  fromString = lexeme . pToken

pList2 :: IsParser p => p a -> p [a]
pList2 p = (:) <$> p <*> pList1 p

-- | The lower-level interface. Returns all errors.
execParser :: Parser a -> String -> (a, [Error LineColPos])
execParser p = parse_h ((,) <$ whitespace <*> p <*> pEnd) . createStr (LineColPos 0 0 0)

-- | The higher-level interface. (Calls 'error' with a simplified error).
--   Runs the parser; if the complete input is accepted without problems  return the
--   result else fail with reporting unconsumed tokens
runParser :: String -> Parser a -> String -> a
runParser inputName p str
  | (a, b) <- execParser p str =
    if null b
      then a
      else error (unlines ["Failed parsing '" ++ inputName ++ "' :", pruneError str b])
  where
    -- We do 'pruneError' above because otherwise you can end
    -- up reporting huge correction streams, and that's
    -- generally not helpful... but the pruning does discard info...
    pruneError :: String -> [Error LineColPos] -> String
    pruneError _ [] = ""
    pruneError _ (DeletedAtEnd x : _) = "Unexpected '" ++ x ++ "' at end."
    pruneError s (Inserted _ pos e : _) = prettyError s e pos
    pruneError s (Deleted _ pos e : _) = prettyError s e pos
    pruneError s (Replaced _ _ pos e : _) = prettyError s e pos

    prettyError :: String -> [String] -> LineColPos -> String
    prettyError s expect lcp@(LineColPos _ _ pos) =
      unlines
        [ "Parser error" ++ show_expecting lcp expect ++ ":",
          aboveString,
          inputFrag,
          belowString
        ]
      where
        s' = map (\c -> if c == '\n' || c == '\r' || c == '\t' then ' ' else c) s
        aboveString = replicate 30 ' ' ++ "v"
        belowString = replicate 30 ' ' ++ "^"
        inputFrag = replicate (30 - pos) ' ' ++ take 71 (drop (pos - 30) s')

pCon, pVar, pLam, pOp :: Parser String
pCon = lexeme $ ((:) <$> pRange ('A', 'Z') <*> pMunch isAlphaNum) <?> "Constructor"
pVar =
  lexeme $
    ((:) <$> (pRange ('a', 'z') <|> pSym '_') <*> pMunch (\c -> c == '_' || c == '\'' || isAlphaNum c))
-- We add a micro step to variables to disambiguate keywords. This extra micro step means 
-- that the parser prefers other options (such as keywords) in case of ambiguity
      `micro` 1
      <?> "Variable"
pOp = lexeme $ (:) <$ pSym '`' <*> pRange ('a', 'z') <*> pMunch isAlphaNum <?> "Operator"
pLam = "λ" <|> "\\"

pBraces, pParens :: Parser a -> Parser a
pBraces p = "{" *> p <* "}"
pParens p = "(" *> p <* ")"

pExpr :: Parser Expr
pExpr =
  (Lam <$ pLam <*> pVar <* "->" <*> pExpr <?> "Lambda")
    <|> (Letrec <$ "let" <*> pVar <* "=" <*> pExpr <* "in" <*> pExpr <?> "Let")
    <|> (Handle <$ "handle" <*> pBraces (pList pHClause) <*> pExpr1 <*> pExpr1 <?> "Handle")
    <|> (Match <$ "match" <*> pExpr <*> pBraces (pList pMClause) <?> "Match")
    -- We make the constructor, operator, and normal application non-greedy (ng), 
    -- because it should stop if it encounters other syntax such as the 'in' part
    -- of a 'let ... in ...' expression or the brackets of a 'match ... { ... }' expression.
    <|> Con <$> pCon <*> pList1_ng pExpr1
    <|> Op <$> pOp <*> pList1_ng pExpr1
    -- We add a micro step to function application to prefer constructor and operator application
    <|> foldl1 App <$> pList_ng (pExpr1 `micro` 1)
  where
    -- This parser is split into two parts. Above are cases that must be surrounded by parentheses
    -- unless they occur at the top level. Below are cases that never have to be parenthesized.
    pExpr1 :: Parser Expr
    pExpr1 =
      -- This fold maps over the Maybe type, so it is either applied once or not at all.
      foldr (const Run)
        <$> ( (Susp <$> pBraces pExpr <?> "Suspension")
                <|> Var <$> pVar
                -- Constructors and operators are duplicated here, because they do not have to be
                -- parenthesized if they are not applied to any arguments.
                <|> Con <$> pCon <*> pure []
                <|> Op <$> pOp <*> pure []
                <|> (pParens pExpr <?> "Parens")
            )
          <*> pMaybe "!"

-- Handler clauses
pHClause :: Parser (CPat, Expr)
pHClause = (,) <$ "|" <*> pCPat <* "->" <*> pExpr <?> "Handler Clause"

-- Handler clause patterns
pCPat :: Parser CPat
pCPat =
  (PRet <$ "return" <*> pVar <*> pVar <?> "Return Clause")
    <|> (mkPOp <$> pVar <*> pList2 pVar <?> "Operator Clause")

-- | Transforms a name and a list of at least two elements into an operator pattern
mkPOp :: String -> [String] -> CPat
mkPOp op = go id
  where
    go f [x3, x4] = POp op (f []) x3 x4
    go f (x : xs') = go (f . (x :)) xs'
    go _ _ = error "Operator patterns should be given at least two parameters"

-- Match clauses
pMClause :: Parser (Pat, Expr)
pMClause = (,) <$ "|" <*> pPat <* "->" <*> pExpr <?> "Match Case"

-- Match patterns
pPat :: Parser Pat
pPat = (PCon <$> pCon <*> pList pPat1 <?> "Constructor Pattern") <|> pPat1
  where
    -- Here we again split the parser into two parts, see the explanation of this in 'pExpr'
    pPat1 = (PVar <$> pVar <?> "Variable Pattern") <|> pParens pPat
