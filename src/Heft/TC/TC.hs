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
  s4                     <- unify
                              ((s3 <> s2) <$$> ε1)
                              (s3         <$$> ε2)
  s5                     <- unify
                              ((s4 <> s3 <> s2) <$$> εl1)
                              ((s4 <> s3)       <$$> εl2)
  conclude
    ( s3 <> s2 <> s1
    , s3 <$$> u
    , ( (s5 <> s4 <> s3 <> s2) <$$> ε1
      , (s5 <> s4 <> s3 <> s2) <$$> εl1
      )
    )

-- Suspension
tc (Susp e) = do 
  ε                     <- freshR
  εl                    <- freshR 
  (s1 , u , (ε' , εl')) <- tc e 
  conclude
    ( s1
    , SusT u (ε' , εl')
    , (ε , εl)
    ) 

-- Enactment 
tc (Run e) = do
  t                     <- freshT 
  ε                     <- freshR
  εl                    <- freshR 
  (s1 , u , (ε' , εl')) <- tc e
  s2                    <- unify (SusT t (ε , εl)) u
  s3                    <- unify (s2 <$$> ε) (s2 <$$> ε')
  s4                    <- unify
                             ((s3 <> s2) <$$> εl)
                             ((s3 <> s2) <$$> εl')
  conclude
    ( s4 <> s3 <> s2 <> s1
    , t
    , ( (s4 <> s3 <> s2) <$$> ε
      , (s4 <> s3 <> s2) <$$> εl
      )
    ) 

{- 
tc (Con x es) = _
tc (Match e cs) = _ 
tc (Handle ps ep e) = _
-} 

-- Operations. Defined in terms of Var/App rules 
tc (Op x es) = tc (mkE x (reverse es))

  where mkE :: String -> [Expr] -> Expr
        mkE x [] = Var x
        mkE x (e:es) = App (mkE x es) e 


-- (Recursive) Let bindings
-- TODO: no recursive argument is added to the environment yet
tc (Letrec x e1 e2) = do
  t                      <- freshT 
  (s1 , t' , (ε1 , εl1)) <- withEnv (bindT x t) (tc e1)
  σ                      <- withEnv (s1<$$>) (generalize t') 
  (s2 , u , (ε2 , εl2))  <- withEnv ((s1<$$>) . bindS x σ) (tc e2)
  s3                     <- unify (s2 <$$> ε1) ε2
  s4                     <- unify
                              ((s3 <> s2) <$$> εl1)
                              (s3         <$$> εl2)
  let s = s4 <> s3 <> s2 <> s1 
  s5                     <- unify (s <$$> t') (s <$$> t) 
  conclude
    ( s5 <> s
    , (s5 <> s4 <> s3) <$$> u
    , ( (s5 <> s4 <> s3 <> s2) <$$> ε1
      , (s5 <> s4 <> s3 <> s2) <$$> εl1
      )
    ) 

 
tc (BOp e1 Eq e2) = do
  (s1 , t , (ε1 , εl1)) <- tc e1
  (s2 , u , (ε2 , εl2)) <- tc e2
  s3                    <- unify ((s2 <> s1) <$$> t) NumT
  s4                    <- unify ((s3 <> s2 <> s1) <$$> u) NumT
  s5                    <- unify
                             ((s4 <> s3 <> s2 <> s1) <$$> ε1)
                             ((s4 <> s3 <> s2 <> s1) <$$> ε2)
  s6                    <- unify
                             ((s5 <> s4 <> s3 <> s2 <> s1) <$$> εl1)
                             ((s5 <> s4 <> s3 <> s2 <> s1) <$$> εl2) 
  let s = s6 <> s5 <> s4 <> s3 <> s2 <> s1 
  conclude
    ( s
    , BoolT
    , (s <$$> ε1 , s <$$> εl1) ) 

tc (BOp e1 Plus e2) = do
  (s1 , t , (ε1 , εl1)) <- tc e1
  (s2 , u , (ε2 , εl2)) <- tc e2
  s3                    <- unify ((s2 <> s1) <$$> t) NumT
  s4                    <- unify ((s3 <> s2 <> s1) <$$> u) NumT
  s5                    <- unify
                             ((s4 <> s3 <> s2 <> s1) <$$> ε1)
                             ((s4 <> s3 <> s2 <> s1) <$$> ε2)
  s6                    <- unify
                             ((s5 <> s4 <> s3 <> s2 <> s1) <$$> εl1)
                             ((s5 <> s4 <> s3 <> s2 <> s1) <$$> εl2) 
  let s = s6 <> s5 <> s4 <> s3 <> s2 <> s1 
  conclude
    ( s
    , NumT
    , (s <$$> ε1 , s <$$> εl1) ) 

tc (BOp e1 Minus e2) = tc (BOp e1 Plus e2) 

tc (BOp e1 Times e2) = tc (BOp e1 Plus e2) 

-- Effect declarations 
tc (LetEff l ops e) = do
  ops' <- mapM (declareOp l) ops
  foldr (\(op , σ) f m -> f (withEnv (bindS op σ) m)) id ops' (tc e) 


type Result = Either String (Scheme , (Row , Row)) 

-- Infers the type of an expression, returning either an error string, or the
-- inferred type scheme.
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

expr6  = Susp expr0

expr7  = Run (Susp expr0)

expr8  = Letrec "enact" (Lam "x" (Run (Var "x"))) (Var "enact")


expr9  = Letrec "enact" (Lam "x" (Susp (Run (Var "x")))) (Var "enact") 

expr10 = LetEff "Abort" [("abort" , "r" , (VarT "a") , [])] (Op "abort" [])
expr11 = LetEff "Abort" [("abort" , "r" , (VarT "a") , [])] (Run $ Op "abort" [])

-- catch throw { 0 } :: { ℤ ∣ [Catch,ρ] * [] } ∣ ε * εₗ
expr12 =
  LetEff "Catch"
    [ ("throw" , "r" , (VarT "a") , [])
    , ("catch" , "r" , (VarT "a") , [ (SusT (VarT "a") (ConsR "Catch" (VarR "r"),NilR)) , (SusT (VarT "a") (ConsR "Catch" (VarR "r"), NilR))])
    ]
    (Op "catch" [Op "throw" [] , Susp (Num 0)])

-- let catch_fun = λ c t -> catch c t in catch_fun
--   :: ∀ α ρ . { a | [Catch,ρ] * [] } → { a | [Catch,ρ] * [] } → { a | [Catch,ρ] * [] } | ε * εₗ
expr13 =
  LetEff "Catch"
    [ ("throw" , "r" , (VarT "a") , [])
    , ("catch" , "r" , (VarT "a") , [ (SusT (VarT "a") (ConsR "Catch" (VarR "r"),NilR)) , (SusT (VarT "a") (ConsR "Catch" (VarR "r"), NilR))])
    ]
    (Letrec "catch_fun" (Lam "t" (Lam "c" (Op "catch" [Var "t" , Var "c"]))) (Var "catch_fun"))

-- Should fail: A function body cannot have any effects (unless they're suspended)
expr14 = LetEff "Abort" [("abort" , "r" , (VarT "a") , [])] (Lam "x" (Run (Op "abort" []))) 

-- let f = λ x → f 10 in f 
expr15 = Letrec "f" (Lam "x" (App (Var "f") (Num 10))) (Var "f")

-- letrec f = λ x → { (f (num x)!)! }  in f 
expr16 = LetEff "Num" [("num" , "r" , NumT , [NumT])] (Letrec "f" (Lam "x" (Susp (Run (App (Var "f") (Run (Op "num" [Var "x"])))))) (Var "f"))

expr17 = Letrec "f" (Lam "x" (Lam "y" (BOp (Var "x") Plus (Var "y")))) (Var "f")

expr18 = BOp (Num 10) Eq (Num 11) 

printResult :: Result -> IO ()
printResult (Left err) = do
  putStrLn err
printResult (Right (σ , (ε , εl))) = do
  putStrLn $ "Inferred:\t " ++ show σ ++ " | " ++ show ε ++ " * " ++ show εl 

test :: IO ()
test =
  mapM_ runTest
    [ expr0
    , expr1
    , expr2
    , expr3
    , expr4
    , expr5
    , expr6
    , expr7
    , expr8
    , expr9
    , expr10
    , expr11
    , expr12
    , expr13
    , expr14
    , expr15
    , expr16
    , expr17
    , expr18
    ]
  where runTest e = putStrLn ("Term:\t\t " ++ show e) >> printResult (infer e) >> putStr "\n" 

