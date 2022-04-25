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
         deriving (Eq , Show) 

-- Type syntax
-- 
data Type = FunT Type Type
          | AppT Type Type
          | SusT Type Row
          | VarT Name
          deriving (Eq , Show)

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
  } deriving (Eq , Show)

