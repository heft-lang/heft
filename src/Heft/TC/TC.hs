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

type TCResult = (Substitution , Type , (Row , Row))

tc :: Expr -> TC TCResult

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


tc (Con x es) = tc (mkE x (reverse es))

  where mkE :: String -> [Expr] -> Expr
        mkE x []     = Var x
        mkE x (e:es) = App (mkE x es) e 


tc (Match e cs) = do
  (s , t , (ε , εl))   <- tc e
  (_ , xs)             <- foldM (\(t, xs) clause -> tcMatchClause t clause >>= \(t' , result) -> return (t' , result:xs)) (t , []) cs 
  u                    <- freshT 
  foldM unifyResults (s , u , (ε , εl)) xs >>= conclude 

  where tcMatchClause :: Type -> (Pat , Expr) -> TC (Type , TCResult)
        tcMatchClause t (pat , e) = do
          (s1 , patternBindings) <- processPattern t pat
          (s2 , u , (ε , εl))    <- withEnv ((s1<$$>) . patternBindings) (tc e)
          return ((s2 <> s1) <$$> t , (s2 <> s1 , (s2 <> s1) <$$> u , (ε , εl)))

        processPattern :: Type -> Pat -> TC (Substitution , Env Scheme -> Env Scheme)
        processPattern t (PCon x pats) = do
          checkDeclaredConstructor x 
          σ  <- (ask <&> typeContext) >>= resolve x
          ct <- instantiate σ
          s1 <- unify t (returnTypeOf ct) 
          (s2 , patternBindings) <- processArgPatterns (map (s1<$$>) $ argTypesOf ct) pats (mempty , id)
          return (s2 <> s1, patternBindings)
        processPattern t (PVar x     ) = return (mempty , bindT x t)

        processArgPatterns :: [Type] -> [Pat] -> (Substitution , Env Scheme -> Env Scheme) -> TC (Substitution , Env Scheme -> Env Scheme)
        processArgPatterns [] []           acc = return acc
        processArgPatterns (t:ts) (p:pats) acc = do
          (s , patternBindings) <- processPattern t p
          processArgPatterns ts pats (s <> fst acc , patternBindings . snd acc) 
        processArgPatterns _      _        _ = throwError $ "Incorrect number of arguments in constructor pattern" 

        returnTypeOf :: Type -> Type
        returnTypeOf (FunT _ u) = returnTypeOf u
        returnTypeOf t          = t

        argTypesOf :: Type -> [Type]
        argTypesOf (FunT t u) = t:argTypesOf u
        argTypesOf _          = [] 
                                         
        unifyResults :: TCResult -> TCResult -> TC TCResult
        unifyResults (s , t , (ε , εl)) (s' , t' , (ε' , εl')) = do 
          s1 <- unify ((s' <> s) <$$> t) ((s' <> s) <$$> t')
          s2 <- unify ((s1 <> s' <> s) <$$> ε) ((s1 <> s' <> s) <$$> ε')
          s3 <- unify ((s2 <> s1 <> s' <> s) <$$> εl) ((s2 <> s1 <> s' <> s) <$$> εl')
          let sf = s3 <> s2 <> s1 <> s' <> s 
          return
            ( sf
            ,   sf <$$> t
            , ( sf <$$> ε , sf <$$> εl )
            ) 
{- 
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

tc (LetData dname params cons e) = do
  registerDatatype (dname , fst <$> cons) 
  cons' <- mapM (declareCons dname (fst <$> params)) cons
  foldr (\(con , σ) f m -> f (withEnv (bindS con σ) m )) id cons' (tc e) 

type Result = Either String (Scheme , (Row , Row)) 

-- Infers the type of an expression, returning either an error string, or the
-- inferred type scheme.
infer :: Expr -> Result
infer e = (\(σ , ann) -> (normalizeAlpha σ , normalizeAnn ann))  <$> 
  ( fst $ runTC $
      tc e >>= \(s , t , ann) -> generalize (apply s t) >>= \σ -> return (σ , ann))

