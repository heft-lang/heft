module Heft.TC.TCMonad where

import Data.Functor 
import qualified Data.Set as Set
import qualified Data.Map as Map 

import Heft.Syntax.Type
import Heft.TC.Substitution

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader

import Debug.Trace


{- Type checker -} 

data TCState = TCState
  { typevarCount        :: Int
  , rowvarCount         :: Int
  , inferredConstraints :: () -- We don't use this right now, but may in the future when adding qualified types
  , declaredEffects     :: [(String , [String])] 
  , declaredDatatypes   :: [(String , [String])]  
  }

data KCEnv = KCEnv
  { kindContext :: Env Kind
  } 

data TCEnv = TCEnv
  { typeContext :: Env Scheme 
  }

emptyEnv :: TCEnv
emptyEnv = TCEnv
  { typeContext      = mempty
  }

-- Type checking monad
type TC = ReaderT TCEnv (ExceptT String (State TCState))

conclude :: (Substitution , Type , (Row , Row)) -> TC (Substitution , Type , (Row , Row))
conclude (s , t , (ε , εl)) =
  modify (\st ->
    st { inferredConstraints = () {- apply s `Set.map` (inferredConstraints st) -}  })
  >> return (s , t , (ε , εl))

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
  , declaredEffects     = []
  , declaredDatatypes   = []
  } )

runTC' :: TC a -> TCEnv -> (Either String a , TCState)
runTC' f nv = runState
  (runExceptT (runReaderT f nv ))
  (TCState
    { typevarCount        = 0
    , rowvarCount         = 0
    , inferredConstraints = mempty
    , declaredEffects     = []
    , declaredDatatypes   = [] 
    } ) 

{-
printResult :: Either String Scheme -> String
printResult (Left err) = "error: \n\t\x1b[4m" <> err <> "\x1b[0m"
printResult (Right t)  = "scheme: \n\t\x1b[1m \x1b[36m" <> show t <> "\x1b[0m \x1b[0m" 
-}

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


generalize' :: Type -> Set.Set String -> Set.Set String -> Scheme
generalize' t tbl rbl = 
  Scheme
 ( Set.toList $
       Set.difference
       (ftv t) tbl)
  ( Set.toList $
    Set.difference
         (frv t) rbl) t

-- Generalize over the free variables in a type, ignoring
-- all free variables in the environment. 
generalize :: Type -> TC Scheme
generalize t = do
  nv <- ask
  st <- get 
  return $
    generalize' t
      ((ftv $ typeContext nv)
         `Set.union`
        Set.fromList (fst <$> declaredDatatypes st))
      (frv $ typeContext nv) 


withEnv :: (Env Scheme -> Env Scheme) -> TC a -> TC a
withEnv f = local (\nv -> nv { typeContext = f (typeContext nv) })

resolve :: String -> Env a -> TC a
resolve x (Env xs) =
  case Map.lookup x xs of
    Just x -> return x
    Nothing -> throwError $ "Name not in scope: " ++ x 

mkFunT :: [Type] -> Type -> Type
mkFunT []     u = u
mkFunT (t:ts) u = FunT t (mkFunT ts u)

registerEffect :: (String , [String]) -> TC ()
registerEffect x = do
  effects <- get <&> declaredEffects
  if fst x `elem` (fst <$> effects) then
    throwError $ "An effect with the name " ++ fst x ++ " already exists in scope"
  else
    modify (\st -> st { declaredEffects = (x:declaredEffects st) } )

-- Declares a new operation for the effect "l" 
declareOp :: String -> (String , String , Type , [Type]) -> TC (String , Scheme)
declareOp l (op , r , t , args) = do
  let ft = mkFunT args (SusT t ( ConsR l (VarR r) , NilR ))
  -- TODO: when we add a global tc state with all declared effects, we'll want[
  -- to add declared operations here. For now, we just return the calculated type.
  datatypes <- get <&> declaredDatatypes
  return (op , generalize' ft (Set.fromList (fst <$> datatypes)) mempty) 

registerDatatype :: (String , [String]) -> TC ()
registerDatatype x = do
  datatypes <- get <&> declaredDatatypes
  if fst x `elem` (fst <$> datatypes) then
    throwError $ "A datatype with the name " ++ fst x ++ " already exists in scope"
  else 
    modify (\st -> st { declaredDatatypes = (x:declaredDatatypes st) })
  
declareCons :: String -> [String] -> (String , [Type]) -> TC (String , Scheme)
declareCons dname params (con , args) = do
  let cty = mkFunT args (mkAppT dname (reverse params))
  -- This doesn't effect the global state in any way currently. 
  return (con , generalize' cty (Set.singleton dname) mempty)

  where mkAppT :: String -> [String] -> Type
        mkAppT dname []         = VarT dname
        mkAppT dname (p:params) = AppT (mkAppT dname params) (VarT p) 

checkDeclaredConstructor :: String -> TC ()
checkDeclaredConstructor x = do
  datatypes <- get <&> declaredDatatypes
  if any (any (==x) . snd) datatypes then
    return ()
  else
    throwError $ x ++ " is not a constructor of any declared data type."

checkDeclaredOperation :: String -> String -> TC ()
checkDeclaredOperation op l = do 
  effects <- get <&> declaredEffects
  case lookup l effects of
    (Just ops) ->
      if op `elem` ops then
        return ()
      else
        throwError $ op ++ " is not a declared operation of the effect " ++ l
    Nothing ->
      throwError $ "No effect with name " ++ l ++ " in scope"

{- Kind checker -} 

-- Kind checking monad 
type KC = ReaderT KCEnv (Except String) 

checkKindEqualTo :: KC Kind -> Kind -> KC ()
checkKindEqualTo kc k = do
  k' <- kc
  if k == k' then
    return ()
  else
    throwError $ "Kinding error: expected " ++ show k ++ ", but inferred " ++ show k' 


runKC :: KC a -> KCEnv -> Either String a
runKC f nv = runExcept (runReaderT f nv) 
