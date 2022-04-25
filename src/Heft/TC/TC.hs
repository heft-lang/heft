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


tc :: Expr -> TC (Substitution , Type , (Row , Row))

-- Values
tc (V _) = throwError "Internal error" 

-- Number literals
tc (Num n) = do
  ε  <- freshR
  εl <- freshR  
  conclude 
    ( mempty , NumT , (ε , εl))

-- Lambda abstraction 
tc (Lam x e) = do
  t                   <- freshT
  (s1 , u , (ε , εl)) <- withEnv (bindT x t) (tc e)
  s2                  <- unify ε  NilR
  s3                  <- unify εl NilR 
  ε'                  <- freshR
  εl'                 <- freshR 
  conclude
    ( s3 <> s2 <> s1 
    , FunT
        ((s3 <> s2 <> s1) <$$> t)
        ((s3 <> s2)       <$$> u)
    , (ε' , εl')
    )

tc (Var x) = do
  nv <- ask <&> typeContext
  σ  <- resolve x nv
  t  <- instantiate σ 
  ε  <- freshR
  εl <- freshR 
  conclude
   ( mempty
   , t
   , (ε , εl)
   ) 

-- Function application 
tc (App e1 e2) = do
  u <- freshT
  (s1 , t' , (ε1 , εl1)) <- tc e1
  (s2 , t  , (ε2 , εl2)) <- withEnv (s1<$$>) (tc e2)
  s3                     <- unify (s2 <$$> t') (FunT t u)
  s4                     <- unify ((s3 <> s2) <$$> ε1) (s3 <$$> ε2)
  s5                     <- unify ((s4 <> s3 <> s2) <$$> εl1) ((s4 <> s3) <$$> εl2)
  conclude
    ( s3 <> s2 <> s1
    , s3 <$$> u
    , ( (s5 <> s4 <> s3 <> s2) <$$> ε1 , (s5 <> s4 <> s3 <> s2) <$$> εl1)
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
  (s1 , t , (ε1 , εl1)) <- tc e1
  σ                     <- withEnv (s1<$$>) (generalize t)
  (s2 , u , (ε2 , εl2)) <- withEnv ((s1<$$>) . bindS x σ) (tc e2)
  s3                    <- unify (s2 <$$> ε1) ε2
  s4                    <- unify ((s3 <> s2) <$$> εl1) (s3 <$$> εl2) 
  conclude
    ( s4 <> s3 <> s2 <> s1
    , (s4 <> s3) <$$> u
    , ( (s4 <> s3 <> s2) <$$> ε1 , (s4 <> s3 <> s2) <$$> εl1 )
    ) 

{- 
tc (BOp e1 op e2) = _ 
-}

type Result = Either String (Scheme , (Row , Row)) 

-- | Infers the type of an expression, returning either an error string, or the
--   inferred type scheme.
infer :: Expr -> Result
infer e = (\(σ , ann) -> (normalizeAlpha σ , normalizeAnn ann))  <$> 
  ( fst $ runTC $
      tc e >>= \(s , t , ann) -> generalize (apply s t) >>= \σ -> return (σ , ann))


expr0  =  Letrec "id" (Lam "x" (Var "x"))
           (Var "id")

expr1  =  Letrec "id" (Lam "x" (Var "x"))
           (App (Var "id") (Var "id"))

expr2  =  Letrec "id" (Lam "x" (Letrec "y" (Var "x") (Var "y")))
           (App (Var "id") (Var "id"))
expr3  =  Letrec "id" (Lam "x" (Letrec "y" (Var "x") (Var "y")))
           (App (App (Var "id") (Var "id")) (Num 2) )
expr4  =  Letrec "id" (Lam "x" (App (Var "x") (Var "x")))
           (Var "id")
expr5  =  Lam "m" (Letrec "y" (Var "m")
                    (Letrec "x" (App (Var "y") (Num 0))
                          (Var "x")))
 

printResult :: Result -> IO ()
printResult (Left err) = do
  putStrLn err
printResult (Right (σ , (ε , εl))) = do
  putStrLn $ "Inferred:\t " ++ show σ ++ " | " ++ show ε ++ " * " ++ show εl 

test :: IO ()
test = mapM_ runTest [expr0,expr1,expr2,expr3,expr4,expr5]
  where runTest e = putStrLn ("Term:\t\t " ++ show e) >> printResult (infer e) >> putStr "\n" 
