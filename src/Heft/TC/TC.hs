module Heft.TC.TC where

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


tc :: Expr -> TC (Substitution , Type , Row)

-- Values
tc (V _) = throwError "Internal error" 

-- Number literals
tc (Num n) = do
  ε <- freshR 
  return (mempty , NumT , ε)

-- Lambda abstraction 
tc (Lam x e) = do
  t           <- freshT
  (s , u , _) <- withEnv (bindT x t) (tc e)
  --_           <- unify ε NilR
  ε'          <- freshR 
  conclude
    ( s
    , FunT (s <$$> t) u
    , ε'
    )

tc (Var x) = do
  nv <- ask <&> typeContext
  σ  <- resolve x nv
  t  <- instantiate σ 
  ε  <- freshR 
  conclude (mempty , t , ε) 

-- Function application 
tc (App e1 e2) = do
  u <- freshT
  (s1 , t' , _) <- tc e1
  (s2 , t  , _) <- withEnv (s1<$$>) (tc e2)
  s3            <- unify (s2 <$$> t') (FunT t u)
  conclude
    ( s3 <> s2 <> s1
    , s3 <$$> u
    , NilR 
    )


{- 
-- Suspension
tc (Susp e) = _
tc (Run e) = _
tc (Con x es) = _
tc (Match e cs) = _ 
tc (Handle ps ep e) = _
tc (Op x es) = _
-}

--TODO effects
tc (Letrec x e1 e2) = do
  (s1 , t , _) <- tc e1
  σ            <- withEnv (s1<$$>) (generalize t)
  (s2 , u , _) <- withEnv ((s1<$$>) . bindS x σ) (tc e2)
  conclude (s2 <> s1 , u , NilR) 

{- 
tc (BOp e1 op e2) = _ 
-}

type Result = Either String Scheme

-- | Infers the type of an expression, returning either an error string, or the
--   inferred type scheme.
infer :: Expr -> Result
infer e = normalizeAlpha <$> 
  ( fst $ runTC $
      tc e 
        >>= \(s , t , _) -> generalize (apply s t))


e0  =  Letrec "id" (Lam "x" (Var "x"))
        (Var "id")

e1  =  Letrec "id" (Lam "x" (Var "x"))
        (App (Var "id") (Var "id"))

e2  =  Letrec "id" (Lam "x" (Letrec "y" (Var "x") (Var "y")))
        (App (Var "id") (Var "id"))
e3  =  Letrec "id" (Lam "x" (Letrec "y" (Var "x") (Var "y")))
        (App (App (Var "id") (Var "id")) (Num 2) )
e4  =  Letrec "id" (Lam "x" (App (Var "x") (Var "x")))
        (Var "id")
e5  =  Lam "m" (Letrec "y" (Var "m")
                 (Letrec "x" (App (Var "y") (Num 0))
                       (Var "x")))
 

test :: IO ()
test = mapM_ runTest [e0,e1,e2,e3,e4,e5]
  where runTest e = putStrLn (show $ infer e) >> putStr "\n" 
