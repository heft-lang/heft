module Heft.TC.Unification where

import Heft.Syntax.Type
import Heft.TC.Substitution
import Heft.TC.TCMonad

import Control.Monad.Except

import qualified Data.Set as Set
import qualified Data.Map as Map

unifyTypeVar :: String -> Type -> TC Substitution
unifyTypeVar x t
  | t == VarT x          = return mempty
  | Set.member x (ftv t) =
      throwError $  "Occurs check failed: the name "
                 <> x <> " occurs in the type "
                 <> show t  
  | otherwise            = return (Substitution (Env $ Map.singleton x t) mempty)

unifyRowVar :: String -> Row -> TC Substitution
unifyRowVar x r
  | r == VarR x        = return mempty
  | Set.member x (frv r) =
      throwError $ "Occurs check failed: the name "
                 <> x <> " occurs as par of the row "
                 <> show r
  | otherwise            = return (Substitution mempty (Env $ Map.singleton x r))


class TypeSyntax a => Unify a where
  unify :: a -> a -> TC Substitution 

instance Unify Type where
  unify (FunT t u) (FunT u' t') = do
    s1 <- unify t t'
    s2 <- unify (s1 <$$> u) (s1 <$$> u')
    return (s2 <> s1)
  unify (AppT t u) (AppT u' t') = do
    s1 <- unify t t'
    s2 <- unify (s1 <$$> u) (s1 <$$> u')
    return (s2 <> s1)
  unify (SusT t (r1 , r2)) (SusT t' (r1' , r2')) = do
    s1 <- unify t t'
    s2 <- unify (s1 <$$> r1) (s1 <$$> r1')
    s3 <- unify ((s2 <> s1) <$$> r2) ((s2 <> s1) <$$> r2')
    return (s3 <> s2 <> s1)
  unify NumT  NumT  = return mempty
  unify BoolT BoolT = return mempty
  unify t (VarT x) = unifyTypeVar x t
  unify (VarT x) t = unifyTypeVar x t
  unify t u =
    throwError $  "Unification failed for types "
               ++ show t ++ " , " ++ show u 

instance Unify Row where
  unify NilR NilR = return mempty
  unify (ConsR l r) (ConsR l' r')
    | l == l'   = unify r r' 
    | otherwise = throwError
        $  "Unification failed: the labels " ++ l
        ++ " and " ++ l' ++ " are not equal."
  unify (VarR x) r = unifyRowVar x r
  unify r (VarR x) = unifyRowVar x r
  unify r1 r2 = throwError $
    "Unification failed for rows "
    <> show r1 <> " , " <> show r2

