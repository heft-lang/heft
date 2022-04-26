module Heft.Syntax.Type where

import qualified Data.Map as Map

import Heft.Syntax.Misc 

-- Kind syntax
data Kind = Star
          | RowK 
          | FunK Kind Kind
          deriving Eq

-- Row syntax.
--
-- Rows can be (1) empty, (2) a label cons another row, (3) a row variable.
data Row = NilR 
         | ConsR Label Row
         | VarR Name
         deriving (Eq) 

-- Type syntax
-- 
data Type = FunT Type Type
          | AppT Type Type
          | SusT Type (Row , Row)
          | NumT | BoolT 
          | VarT Name
          deriving (Eq)

-- The type `Env a` contains a collection of unapplied substitutions of
-- variables for "syntax" typed by `a`.
newtype Env a = Env
  { entries :: Map.Map Name a
  } deriving Eq

instance Functor Env where
  fmap f (Env xs) = Env (f <$> xs)

instance Foldable Env where
  foldr f z (Env xs) = foldr f z xs

instance Semigroup (Env a) where
  (Env xs) <> (Env ys) = Env (xs <> ys)  

instance Monoid (Env a) where
  mempty = Env mempty

-- A type scheme universally qualifies over zero or more type and row variables
data Scheme = Scheme
  { typeVars :: [Name] 
  , rowVars  :: [Name]
  , ty       :: Type 
  } deriving (Eq)


instance Show Kind where
  show Star = "★"
  show RowK = "𝓡"
  show (FunK k1@(FunK _ _) k2) = "(" ++ show k1 ++ ") → " ++ show k2 
  show (FunK k1 k2) = show k1 ++ " → " ++ show k2 

instance Show Scheme where
  show s@(Scheme xs ys t)
    | null xs && null ys = show t
    | otherwise          =
      "∀ " <> foldr (\v s -> v <> " " <> s) ""
                         (typeVars s <> rowVars s)
                <> ". " <> show t

instance Show Type where
  show (VarT x)              = x
  show (FunT t@(FunT _ _) u) = "(" <> show t <> ") → " <> show u
  show (FunT t u)            = show t <> " → " <> show u
  show (AppT t u)         = show t <> "(" <> show u  <> ")"
  show (SusT t (ε , εl)) = "{ " ++ show t ++ " | " ++ show ε ++ " * " ++ show εl ++ " }" 
  show NumT = "ℤ"
  show BoolT = "𝔹" 

instance Show Row where
  show NilR             = "<>"
  show (ConsR l NilR)   = "<" <> l <> ">" 
  show els@(ConsR _ _ ) = "<" <> showElements els <> ">"
    where showElements NilR = ""
          showElements (ConsR e NilR) = show e
          showElements (ConsR e r) = show e <> "," <> showElements r
          showElements (VarR x) = x
  show (VarR r) = r 
