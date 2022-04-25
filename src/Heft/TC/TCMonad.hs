module Core.TC.TCMonad where

import Debug.Trace

import qualified Data.Map as Map
import qualified Data.Set as Set

import Heft.Syntax.Type
import Heft.TC.Substitution

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader

data TCState = TCState
  { typevarCount        :: Int
  , rowvarCount         :: Int
  , inferredConstraints :: () -- We don't use this right now, but may in the future when adding qualified types  
  }

data TCEnv = TCEnv
  { typeContext       :: Env Type 
  }

emptyEnv :: TCEnv
emptyEnv = TCEnv
  { typeContext      = mempty
  }

type TC = ReaderT TCEnv (ExceptT String (State TCState))

conclude :: (Substitution , Type) -> TC (Substitution , Type)
conclude (s , t) =
  modify (\st ->
    st { inferredConstraints = () {- apply s `Set.map` (inferredConstraints st) -}  })
  >> return (s , t)

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


-- Only collects free variables from the type environment. What about the
-- row constraints? 
generalize :: Type -> TC Scheme
generalize t = do
  nv <- ask
  st <- get
  put (st { inferredConstraints = mempty })
  return $ 
    Scheme
      ( Set.toList $
        Set.difference
          (ftv t {- `Set.union` ftv st -} 
          ) (ftv (typeContext nv)))
      ( Set.toList $
        Set.difference
          (frv t {- `Set.union` frv st -} 
          ) (frv (typeContext nv))) t


withEnv :: (Env Type -> Env Type) -> TC a -> TC a
withEnv f = local (\nv -> nv { typeContext = f (typeContext nv) })
