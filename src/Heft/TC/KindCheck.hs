module Heft.TC.KindCheck where

import Data.Functor 
import qualified Data.Map as Map 

import Heft.Syntax.Type
import Heft.Syntax.Expr

import Heft.TC.Substitution
import Heft.TC.Unification
import Heft.TC.TCMonad

import Control.Monad.Except
import Control.Monad.Reader

import Debug.Trace


-- Environment "transformer" that binds a new type 
bindT :: String -> Type -> Env Scheme -> Env Scheme
bindT x t (Env xs) = Env (Map.insert x (Scheme [] [] t) xs)

-- Environment "transformer" that binds a new scheme
bindS :: String -> Scheme -> Env Scheme -> Env Scheme
bindS x σ (Env xs) = Env (Map.insert x σ xs) 


kc :: Type -> KC Kind
kc (FunT t u) = do
  checkKindEqualTo (kc t) Star
  checkKindEqualTo (kc u) Star
  return Star
kc (AppT t u) = do
  kt <- kc t
  case kt of
    (FunK k1 k2) -> do
      checkKindEqualTo (kc u) k1
      return k2 
    kt'          ->
      throwError $ "Kinding error: expected an arrow kind, but inferred " ++ show kt' 
kc (SusT t _) = do
  checkKindEqualTo (kc t) Star
  return Star
kc NumT = return Star
kc BoolT = return Star
kc (VarT x) = do
  (KCEnv (Env nv)) <- ask
  case Map.lookup x nv of
    Just k  -> return k
    Nothing ->
      throwError $ "Unbound type variable: " ++ x 
