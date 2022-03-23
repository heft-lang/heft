module Main where

import Heft.Parser
import Heft.Interpreter
import System.Environment

main :: IO ()
main = do
  x : _ <- getArgs
  xs <- readFile x
  let expr = runParser x pExpr xs
  putStrLn "Parsed Expression:"
  print expr
  putStrLn "Result Value:"
  print (drive expr)

{-

import Control.Applicative (Alternative ((<|>)))
import Data.Char (isAlphaNum, isSpace)
import Data.Foldable (asum)
import Text.ParserCombinators.UU
  ( ExtAlternative (opt, (<?>)),
    P,
    micro,
    pChainl_ng,
    pEnd,
    pList,
    pList1,
    pList1Sep,
    pList_ng,
    parse_h,
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
  (
    pLower,
    pUpper
  )
import Prelude hiding (lex)

--------------------------------------------------------------------------------
-- ParseUtils
--------------------------------------------------------------------------------

type Parser a = P (Str Char String LineColPos) a

lexeme :: Parser a -> Parser a
lexeme p = p <* ignore

ignore :: Parser ()
ignore =
  () <$ pList1 (pToken "--" *> pMunch (/= '\n') <|> pSatisfy isSpace (Insertion "space" ' ' 5) *> pMunch isSpace)
    `opt` ()

pKey :: String -> Parser String
pKey k = lexeme $ pToken k `micro` 1

-- | The lower-level interface. Returns all errors.
execParser :: Parser a -> String -> (a, [Error LineColPos])
execParser p = parse_h ((,) <$> p <*> pEnd) . createStr (LineColPos 0 0 0)

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
    prettyError s expect lcp@(LineColPos _ _ pos) = unlines
      [ "Parser error" ++ show_expecting lcp expect ++ ":"
      , aboveString
      , inputFrag
      , belowString
      ]
      where
        s' = map (\c -> if c == '\n' || c == '\r' || c == '\t' then ' ' else c) s
        aboveString = replicate 30 ' ' ++ "v"
        belowString = replicate 30 ' ' ++ "^"
        inputFrag = replicate (30 - pos) ' ' ++ take 71 (drop (pos - 30) s')

--------------------------------------------------------------------------------
-- Hof
--------------------------------------------------------------------------------

data Hof
  = App Hof Hof
  | Let String {- = -} Hof {- in -} Hof
  | Handle [HClause]
  | Enact Hof
  | Var String
  | Abs String {- -> -} Hof
  | Con String
  | Susp Hof
  | Match Hof {- with -} [MClause]
  deriving (Show)

data HClause
  = Op String [String] String String {- = -} Hof
  | Ret String String {- = -} Hof
  deriving (Show)

data MClause = Case String [String] {- = -} Hof
  deriving (Show)

-- Tokens

pCon, pVar, pLam, pArr, pEq, pIn, pLet, pHandle, pReturn, pComma, pMatch, pWith, pPipe, pBang, pLBrace, pRBrace, pLParen, pRParen :: Parser String
pCon = lexeme $ (:) <$> pUpper <*> pMunch isAlphaNum `micro` 2 <?> "Constructor"
pVar = lexeme $ (:) <$> pLower <*> pMunch isAlphaNum `micro` 2 <?> "Variable"
pLam = pKey "λ" <|> pKey "\\"
pArr = pKey "->"
pEq = pKey "="
pIn = pKey "in"
pLet = pKey "let"
pHandle = pKey "handle"
pReturn = pKey "return"
pComma = pKey ","
pMatch = pKey "match"
pWith = pKey "with"
pPipe = pKey "|"
pBang = pKey "!"
pLBrace = pKey "{"
pRBrace = pKey "}"
pLParen = pKey "("
pRParen = pKey ")"

pBraces, pParens :: Parser a -> Parser a
pBraces p = pLBrace *> p <* pRBrace
pParens p = pLParen *> p <* pRParen

pHof :: Parser Hof
pHof =
  asum
    [ Abs <$ pLam <*> pVar <* pArr <*> pHof <?> "Abstraction",
      Let <$ pLet <*> pVar <* pEq <*> pHof <* pIn <*> pHof <?> "Let",
      pChainl_ng (pure App) ((Enact <$> pHofL <* pBang <?> "Enact") <|> pHofL)
    ]
  where
    pHofL :: Parser Hof
    pHofL =
      asum
        [ Susp <$> pBraces pHof <?> "Suspension",
          Con <$> pCon,
          Var <$> pVar,
          Handle <$ pHandle <*> pBraces (pList1Sep pComma pHClause) <?> "Handle",
          Match <$ pMatch <*> pHof <* pWith <*> pBraces (pList pMClause) <?> "Match",
          pParens pHof <?> "Parens"
        ]

pHClause :: Parser HClause
pHClause =
  asum
    [ Ret <$ pReturn <*> pVar <*> pVar <* pEq <*> pHof <?> "Return Clause",
      Op <$> pVar <*> pList_ng pVar <*> pVar <*> pVar <* pEq <*> pHof <?> "Operator Clause"
    ]

pMClause :: Parser MClause
pMClause = Case <$ pPipe <*> pCon <*> pList pVar <* pArr <*> pHof <?> "Case"

main :: IO ()
main = interact ((++ "\n") . show . runParser "<interactive>" pHof)
-}
