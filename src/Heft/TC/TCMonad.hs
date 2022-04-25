module Heft.TC.TCMonad where

import qualified Data.Set as Set
import qualified Data.Map as Map 

import Heft.Syntax.Type
import Heft.TC.Substitution

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader

import Debug.Trace

data TCState = TCState
  { typevarCount        :: Int
  , rowvarCount         :: Int
  , inferredConstraints :: () -- We don't use this right now, but may in the future when adding qualified types  
  }

data TCEnv = TCEnv
  { typeContext       :: Env Scheme 
  }

emptyEnv :: TCEnv
emptyEnv = TCEnv
  { typeContext      = mempty
  }

type TC = ReaderT TCEnv (ExceptT String (State TCState))

conclude :: (Substitution , Type , Row) -> TC (Substitution , Type , Row)
conclude (s , t , ε) =
  modify (\st ->
    st { inferredConstraints = () {- apply s `Set.map` (inferredConstraints st) -}  })
  >> return (s , t , ε)

freshT :: TC Type
freshT = do
  s <- get
  put (s { typevarCount = typevarCount s + 1})
  return (VarT ("x_" ++ show (typevarCount s)))

runTC :: TC a -> (Either String a , TCState)
runTC f = runState (runExceptT (runReaderT f emptyEnv)) (TCState
  { typevarCount        = 0
  , rowvarCount         = 0
  , inferredConstraints = mempty
  } )

runTC' :: TC a -> TCEnv -> (Either String a , TCState)
runTC' f nv = runState
  (runExceptT (runReaderT f nv ))
  (TCState
    { typevarCount        = 0
    , rowvarCount         = 0
    , inferredConstraints = mempty
    } ) 

printResult :: Either String Scheme -> String
printResult (Left err) = "error: \n\t\x1b[4m" <> err <> "\x1b[0m"
printResult (Right t)  = "scheme: \n\t\x1b[1m \x1b[36m" <> show t <> "\x1b[0m \x1b[0m" 

freshR :: TC Row
freshR = do
  s <- get
  put (s { rowvarCount = rowvarCount s + 1})
  return (VarR ("r_" ++ show (rowvarCount s)))


-- Uses the typevar counter
freshName :: String -> TC String
freshName x = do
  st <- get
  put (st { typevarCount = typevarCount st + 1 })
  return (x <> "_" <> show (rowvarCount st))

-- Instantiate the quantified type and row variables of a scheme with
-- fresh variables 
instantiate :: Scheme -> TC Type
instantiate σ@(Scheme xs ys t) = do
  s1 <- mapM (\x -> freshT >>= \fv -> return (x , fv)) xs
  s2 <- mapM (\x -> freshR >>= \fv -> return (x , fv)) ys 
  return (apply (Substitution (Env $ Map.fromList s1) (Env $ Map.fromList s2) ) t)


-- Generalize over the free variables in a type 
generalize :: Type -> TC Scheme
generalize t = do
  nv <- ask
  return $ 
    Scheme
      ( Set.toList $
        Set.difference
          (ftv t) (ftv (typeContext nv)))
      ( Set.toList $
        Set.difference
          (frv t) (frv (typeContext nv))) t


withEnv :: (Env Scheme -> Env Scheme) -> TC a -> TC a
withEnv f = local (\nv -> nv { typeContext = f (typeContext nv) })



resolve :: String -> Env a -> TC a
resolve x (Env xs) =
  case Map.lookup x xs of
    Just x -> return x
    Nothing -> throwError $ "Name not in scope: " ++ x 
