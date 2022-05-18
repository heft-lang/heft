{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Heft.Parser where

import Data.Bifunctor (second)
import Data.Char (isAlphaNum, isLower, isSpace, isAlpha)
import Data.String (IsString (..))
import Heft.Syntax.Expr
import Heft.Syntax.Type
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
  () <$ pList ((pToken "--" *> pMunch (/= '\n') <?> "") <|> (pSatisfy isSpace (Insertion "" ' ' 5) *> pMunch isSpace))

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

pCon, pOp :: Parser String
pCon = lexeme $ ((:) <$> pRange ('A', 'Z') <*> pMunch (\c -> isAlphaNum c || c == '_' || c == '\'')) <?> "Constructor"
pOp = lexeme $ (:) <$ pSym '`' <*> pRange ('a', 'z') <*> pMunch (\c -> isAlphaNum c || c == '_' || c == '\'') <?> "Operation"

keywords :: [String]
keywords = ["let", "in", "match", "return", "data", "effect", "handle", "val", "fun", "end"]

pIdent :: Parser String
pIdent = lexeme $ pSymExt splitState (Succ Zero) Nothing <?> "Identifier"
  where
    splitState :: (String -> Str Char String LineColPos -> Steps a) -> Str Char String LineColPos -> Steps a
    splitState k inp@(Str (x : xs) msgs pos del_ok)
      | (l, r) <- span (\c -> isAlphaNum c || c == '_' || c == '\'') xs,
        isAlpha x || x == '_' || x == '\'',
        x : l `notElem` keywords =
          Step (length (x : l)) (k (x : l) (Str r msgs (advance pos (x : l)) del_ok))
    splitState k inp@(Str tts msgs pos del_ok) =
      let msg = "Identifier"
          ins exp = (1, k "x" (Str tts (msgs ++ [Inserted msg pos exp]) pos False))
       in case tts of
            [] -> Fail [msg] [ins]
            t : ts ->
              let del exp = (5, splitState k (Str ts (msgs ++ [Deleted (show t) pos exp]) (advance pos t) True))
               in Fail [msg] (ins : [del | del_ok])

pVar :: Parser String
pVar = lexeme $ pSymExt splitState (Succ Zero) Nothing <?> "Variable"
  where
    splitState :: (String -> Str Char String LineColPos -> Steps a) -> Str Char String LineColPos -> Steps a
    splitState k inp@(Str (x : xs) msgs pos del_ok)
      | isLower x || x == '_',
        (l, r) <- span (\c -> isAlphaNum c || c == '_' || c == '\'') xs,
        x : l `notElem` keywords =
          Step (length (x : l)) (k (x : l) (Str r msgs (advance pos (x : l)) del_ok))
    splitState k inp@(Str tts msgs pos del_ok) =
      let msg = "Variable"
          ins exp = (1, k "x" (Str tts (msgs ++ [Inserted msg pos exp]) pos False))
       in case tts of
            [] -> Fail [msg] [ins]
            t : ts ->
              let del exp = (5, splitState k (Str ts (msgs ++ [Deleted (show t) pos exp]) (advance pos t) True))
               in Fail [msg] (ins : [del | del_ok])

fixApply :: [Expr] -> Expr -> Expr
fixApply s (App x y) = fixApply (fixApply [] y : s) x
fixApply s (Con x xs) = Con x (xs ++ s)
fixApply s (Op x xs) = Op x (xs ++ s)
fixApply s x = foldl App (mapSubExpr (fixApply []) x) s

mapValExpr :: (Expr -> Expr) -> Val -> Val
mapValExpr f = \case
  VLam s ex -> VLam s (f ex)
  VSusp ex -> VSusp (f ex)
  VNum n -> VNum n
  VCon s vals -> VCon s (map (mapValExpr f) vals)

mapSubExpr :: (Expr -> Expr) -> Expr -> Expr
mapSubExpr f = \case
  V val -> V $ case val of
    (VLam s ex) -> VLam s (f ex)
    (VSusp ex) -> VSusp (f ex)
    (VNum n) -> VNum n
    (VCon s vals) -> VCon s (map (mapValExpr f) vals)
  Num n -> Num n
  Lam s ex -> Lam s (f ex)
  Var s -> Var s
  App ex ex' -> App (f ex) (f ex')
  Susp ex -> Susp (f ex)
  Run ex -> Run (f ex)
  Con s exs -> Con s (map f exs)
  Match ex x0 -> Match (f ex) (map (second f) x0)
  Handle l x0 ex ex' -> Handle l (map (second f) x0) (f ex) (f ex')
  Handle' x0 ex ex' -> Handle' (map (second f) x0) (f ex) (f ex')
  Op s exs -> Op s (map f exs)
  Letrec s ex ex' -> Letrec s (f ex) (f ex')
  BOp ex bo ex' -> BOp (f ex) bo (f ex')

pBraces, pParens, pAngles :: Parser a -> Parser a
pBraces p = "{" *> p <* "}"
pParens p = "(" *> p <* ")"
pAngles p = "<" *> p <* ">"

pKind :: Parser Kind
pKind = pChainr (FunK <$ "->") (Star <$ "*" <|> RowK <$ "R" <|> pParens pKind)

pRow :: Parser Row
pRow = pAngles (pure NilR) <|> pAngles (ConsR <$> pCon <* "," <*> pRow) <|> VarR <$> pVar

pType :: Parser Type
pType = pChainr (FunT <$ "->") (foldl1 AppT <$> pList1 pTypeInner)

pTypeInner :: Parser Type
pTypeInner = VarT <$> pIdent <|> NumT <$ "Num" <|> BoolT <$ "Bool" <|> pSus <|> pParens pType
  where
    pSus = pBraces (SusT <$> pType <* "/" <*> ((,) <$> pRow <* "*" <*> pRow))

pProgram :: Parser Program
pProgram = Program <$> pList pDecl

pDecl :: Parser Decl
pDecl =
  (Effect <$ "effect" <*> pCon <*> pList pEClause <?> "Effect Declaration")
    <|> (Datatype <$ "data" <*> pCon <*> pList (pParens ((,) <$> pVar <* ":" <*> pKind)) <*> pList pDClause <?> "Data Declaration")
    <|> (Function <$ "val" <*> pVar <*> pure Nothing <*> pure [] <* "=" <*> pExpr <?> "Value Declaration")

pExpr :: Parser Expr
pExpr =
  fmap (fixApply []) $
    (Lam <$ "\\" <*> pVar <* "->" <*> pExpr <?> "Lambda")
      <|> (Letrec <$ "let" <*> pVar <* "=" <*> pExpr <* "in" <*> pExpr <?> "Let")
      <|> (Handle <$ "handle" <*> pCon <*> (pList pHClause) <* "end" <*> pExpr' <*> pExpr' <?> "Handle")
      <|> (Match <$ "match" <*> pExpr <*> pList pMClause <* "end" <?> "Match")
      <|> foldl1 App <$> pList1_ng pExpr'
  where
    -- This parser is split into two parts. Above are cases that must be surrounded by parentheses
    -- unless they occur at the top level. Below are cases that never have to be parenthesized.
    pExpr' :: Parser Expr
    pExpr' =
      -- This fold maps over the Maybe type, so it is either applied once or not at all.
      foldr (const Run)
        <$> ( (Susp <$> pBraces pExpr <?> "Suspension")
                <|> Var <$> pVar
                -- We only parse unapplied constructors and operators,
                -- these are later applied as much as possible using the 'fixApply' function
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
    <|> (mkPOp <$> pVar <*> pList2 pVar <?> "Operation Clause")

-- Transforms a name and a list of at least two elements into an operator pattern
mkPOp :: String -> [String] -> CPat
mkPOp op = go id
  where
    go f [x3, x4] = POp op (f []) x3 x4
    go f (x : xs') = go (f . (x :)) xs'
    go _ _ = error "Operation patterns should be given at least two arguments"

-- Match clauses
pMClause :: Parser (Pat, Expr)
pMClause = (,) <$ "|" <*> pPat <* "->" <*> pExpr <?> "Match Case"

-- Match patterns
pPat :: Parser Pat
pPat = (PCon <$> pCon <*> pList pPatInner <?> "Constructor Pattern") <|> pPatInner

-- Here we again split the parser into two parts, see the explanation of this in 'pExpr'
pPatInner :: Parser Pat
pPatInner = (PVar <$> pVar <?> "Variable Pattern") <|> pParens pPat

-- Effect declaration clauses
pEClause :: Parser (String, (String, String, String), Type, [Type])
pEClause = (\n (r, t, args) -> (n, r, t, args)) <$ "|" <*> pVar <* ":" <*> (opSig <$> pType)
  where
    opSig :: Type -> ((String, String, String), Type, [Type])
    opSig (FunT x xs) = let (r, t, args) = opSig xs in (r, t, x : args)
    opSig (SusT t (ConsR _ (VarR r), NilR)) = ((r, "TODO", "TODO"), t, [])
    opSig _ = error "pEClause: malformed operation signature"

-- Data declaration clauses
pDClause :: Parser (String, [Type])
pDClause = (,) <$ "|" <*> pCon <*> pList pTypeInner
