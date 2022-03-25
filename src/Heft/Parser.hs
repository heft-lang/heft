{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module Heft.Parser where

import Control.Applicative (Alternative ((<|>)))
import Data.Char (isAlphaNum, isSpace)
import Data.Foldable (asum)
import Debug.Trace (trace)
import Heft.AST
import Text.ParserCombinators.UU
  ( ExtAlternative (opt, (<?>)),
    P,
    micro,
    pEnd,
    pList,
    pList1,
    pList_ng,
    pState,
    parse_h, IsParser, parse
  )
import Text.ParserCombinators.UU.BasicInstances
  ( Error (Deleted, DeletedAtEnd, Inserted, Replaced),
    Insertion (Insertion),
    LineColPos (LineColPos),
    Str,
    createStr,
    pMunch,
    pSatisfy,
    pToken,
    show_expecting,
  )
import Text.ParserCombinators.UU.Utils
  ( pLower,
    pUpper,
  )

--------------------------------------------------------------------------------
-- ParseUtils
--------------------------------------------------------------------------------

type Parser a = P (Str Char String LineColPos) a

lexeme :: Parser a -> Parser a
lexeme p = p <* ignore

ignore :: Parser ()
ignore =
  () <$ pList1 ((pToken "--" *> pMunch (/= '\n') <?> "Line Comment") <|> pSatisfy isSpace (Insertion "Space" ' ' 5) *> pMunch isSpace)
    `opt` ()

pKey :: String -> Parser String
pKey k = lexeme $ pToken k

-- | The lower-level interface. Returns all errors.
execParser :: Parser a -> String -> (a, [Error LineColPos])
execParser p = parse_h ((,) <$ ignore <*> p <*> pEnd) . createStr (LineColPos 0 0 0)

onlineParser :: Parser a -> String -> (a, [Error LineColPos])
onlineParser p = parse ((,) <$ ignore <*> p <*> pEnd) . createStr (LineColPos 0 0 0)

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

-- Tokens

pTrace :: String -> P s a -> P s a
pTrace msg p = (\s x -> s `seq` trace msg x) <$> pState <*> p

pCon, pVar, pLam, pArr, pEq, pIn, pLet, pHandle, pReturn, pMatch, pPipe, pBang, pLBrace, pRBrace, pLParen, pRParen :: Parser String
pCon = lexeme $ ((:) <$> pUpper <*> pMunch isAlphaNum) <?> "Constructor"
pVar = lexeme $ ((:) <$> pLower <*> pMunch isAlphaNum) `micro` 1 <?> "Variable"
pLam = pKey "λ" <|> pKey "\\"
pArr = pKey "->"
pEq = pKey "="
pIn = pKey "in"
pLet = pKey "let"
pHandle = pKey "handle"
pReturn = pKey "return"
pMatch = pKey "match"
pPipe = pKey "|"
pBang = pKey "!"
pLBrace = pKey "{"
pRBrace = pKey "}"
pLParen = pKey "("
pRParen = pKey ")"

pBraces, pParens :: Parser a -> Parser a
pBraces p = pLBrace *> p <* pRBrace
pParens p = pLParen *> p <* pRParen

pExpr :: Parser Expr
pExpr =
  asum
    [ Lam <$ pLam <*> pVar <* pArr <*> pExpr <?> "Lambda",
      Letrec <$ pLet <*> pVar <* pEq <*> pExpr <* pIn <*> pExpr <?> "Let",
      Handle <$ pHandle <*> pBraces (pList pHClause) <*> pExpr1 <*> pExpr1 <?> "Handle",
      Match <$ pMatch <*> pExpr <*> pBraces (pList pMClause) <?> "Match",
      Con <$> pCon <*> pList_ng pExpr1,
      foldl1 App <$> pList_ng (pExpr1 `micro` 1)
    ]
  where
    pExpr1 :: Parser Expr
    pExpr1 = foldr (const Run) <$>
      asum
        [ Susp <$> pBraces pExpr <?> "Suspension",
          Con <$> pCon <*> pure [] `micro` 1,
          Var <$> pVar,
          pParens pExpr <?> "Parens"
        ] <*> pList pBang

pHClause :: Parser (CPat, Expr)
pHClause = (,) <$ pPipe <*> pCPat <* pArr <*> pExpr <?> "Handler Clause"

pCPat :: Parser CPat
pCPat =
  asum
    [ PRet <$ pReturn <*> pVar <*> pVar <?> "Return Clause",
      mkPOp <$> pVar <*> pList2 pVar <?> "Operator Clause"
    ]

pList2 :: IsParser p => p a -> p [a]
pList2 p = (:) <$> p <*> pList1 p

mkPOp :: String -> [String] -> CPat
mkPOp op = go id
  where
    go f [x3, x4] = POp op (f []) x3 x4
    go f (x:xs') = go (f . (x :)) xs'
    go _ _ = error "Impossible"

pMClause :: Parser (Pat, Expr)
pMClause = (,) <$ pPipe <*> pPat <* pArr <*> pExpr <?> "Match Case"

pPat :: Parser Pat
pPat =
  asum
    [ PCon <$> pCon <*> pList pPatL <?> "Constructor Pattern",
      pPatL
    ]
  where
    pPatL =
      asum
        [ PVar <$> pVar <?> "Variable Pattern",
          pParens pPat
        ]
