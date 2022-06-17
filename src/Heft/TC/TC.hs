module Heft.TC.TC where

import Data.Functor 
import qualified Data.Map as Map
import qualified Data.Set as Set 

import Heft.Syntax.Type
import Heft.Syntax.Expr

import Heft.TC.Substitution
import Heft.TC.Unification
import Heft.TC.TCMonad

import Control.Monad.Except
import Control.Monad.Reader

import Debug.Trace

type Bindings = Env Scheme -> Env Scheme 

-- Environment "transformer" that binds a new type 
bindT :: String -> Type -> Bindings
bindT x t (Env xs) = Env (Map.insert x (Scheme [] [] t) xs)

-- Environment "transformer" that binds a new scheme
bindS :: String -> Scheme -> Bindings 
bindS x σ (Env xs) = Env (Map.insert x σ xs) 

type TCResult = (Substitution , Type , (Row , Row))

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

-- TODO: current implementation doesn't do any coverage checking
tc (Match e cs) = do
  (s , t , (ε , εl))   <- tc e
  (_ , xs)             <- foldM (\(t, acc) clause ->
                                   tcMatchClause t clause
                                     >>= \(t' , result) -> return (t' , result:acc))
                                (t , []) cs 
  u                    <- freshT 
  foldM unifyResults (s , u , (ε , εl)) xs >>= conclude 

  where tcMatchClause :: Type -> (Pat , Expr) -> TC (Type , TCResult)
        tcMatchClause t (pat , e) = do
          (s1 , patternBindings) <- processPattern t pat
          (s2 , u , (ε , εl))    <- withEnv ((s1<$$>) . patternBindings) (tc e)
          return ((s2 <> s1) <$$> t , (s2 <> s1 , (s2 <> s1) <$$> u , (ε , εl)))

        processPattern :: Type -> Pat -> TC (Substitution , Bindings)
        processPattern t (PCon x pats) = do
          checkDeclaredConstructor x 
          σ  <- (ask <&> typeContext) >>= resolve x
          ct <- instantiate σ
          s1 <- unify t (returnTypeOf ct) 
          (s2 , patternBindings) <- processArgPatterns
                                      (map (s1<$$>) $ argTypesOf ct) pats (mempty , id)
          return (s2 <> s1, patternBindings)
        processPattern t (PVar x     ) = return (mempty , bindT x t)

        processArgPatterns
          :: [Type] -> [Pat] -> (Substitution , Bindings)
           -> TC (Substitution , Bindings)
        processArgPatterns [] []           acc = return acc
        processArgPatterns (t:ts) (p:pats) acc = do
          (s , patternBindings) <- processPattern t p
          processArgPatterns ts pats (s <> fst acc , patternBindings . snd acc) 
        processArgPatterns _      _        _ =
          throwError $ "Incorrect number of arguments in constructor pattern" 

-- TODO: no coverage checking!  
tc (Handle label cs e_param e) = do
  (s1 , t_param , (ε', εl')) <- tc e_param
  (s2 , t       , (ε , εl )) <- tc e
  ε''                        <- freshR
  s3                         <- unify ε (ConsR label ε'')
  t_clause                   <- freshT 
  let s = s3 <> s2 <> s1
  (_ , xs)                         <- foldM
                                        (\(t_param , acc) clause ->
                                           tcHandleClause
                                             label
                                             (s <$$> t)
                                             (s <$$> t_clause)
                                             t_param
                                             (s <$$> ε'' , s <$$> εl)
                                             clause
                                           >>= \(t_param' , result) -> return (t_param' , result:acc))
                                        (t_param , []) cs 
  foldM unifyResults
    ( s
    , SusT (s <$$> t_clause) (s <$$> ε'' , s <$$> ConsR label εl)
    , (s <$$> ε' , s <$$> εl'))
    xs >>= conclude

  where tcHandleClause :: String -> Type -> Type -> Type -> (Row , Row) -> (CPat , Expr) -> TC (Type , TCResult)
        tcHandleClause label t t_clause t_param _ (PRet x p , e) = do
          (s , u , ann) <- withEnv (bindT p t_param . bindT x t) (tc e)
          return (s <$$> t_param , (s , s <$$> u , ann)) 
        tcHandleClause label t t_clause t_param (ε , εl) (POp op args p k , e) = do
          checkDeclaredOperation op label 
          σ           <- (ask <&> typeContext) >>= resolve op
          opt         <- instantiate σ
          argBindings <- processOpArgs (argTypesOf opt) args
          let kt = FunT t_param (FunT (returnTypeOf opt) (SusT t_clause (ε , ConsR label εl)))
          (s , u , ann) <- withEnv
                           ( bindT k kt  
                           . bindT p t_param
                           . argBindings
                           ) (tc e)
          return (s <$$> t_param , (s , s <$$> u , ann))


        processOpArgs :: [Type] -> [String] -> TC Bindings 
        processOpArgs [] []         = return id
        processOpArgs (t:ts) (x:xs) = do
          bindings <- processOpArgs ts xs
          return (bindings . bindT x t)
        processOpArgs _      _      =
          throwError $ "Incorrect number of arguments in operation pattern"
         

-- Operations. Defined in terms of Var/App rules 
tc (Op x es) = tc (mkE x (reverse es))

  where mkE :: String -> [Expr] -> Expr
        mkE x [] = Var x
        mkE x (e:es) = App (mkE x es) e 


-- (Recursive) Let bindings
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

tc (Ann e σ) = do
  (s , t , ea) <- tc e
  if not ((ftv σ) == Set.empty) then
    throwError $ "Cannot annotate with " ++ show σ ++ ", because it contains free type variable(s)"
  else
    do σ'           <- generalize t 
       u            <- instantiate σ
       u `isInstanceOf` t 
       return (s , u , ea) 

tcDecl :: Decl -> TC (Maybe (String , TCResult))

-- Effect declarations 
tcDecl (Effect label ops) = do
  registerEffect (label , (\(op_name , _ , _) -> op_name) <$> ops)  
  ops' <- mapM (declareOp label) ops
  foldr (\(op , σ) f m -> f (withEnv (bindS op σ) m)) id ops' (return Nothing)

tcDecl (Datatype dname params cons) = do
  registerDatatype (dname , fst <$> cons) 
  cons' <- mapM (declareCons dname (fst <$> params)) cons
  foldr (\(con , σ) f m -> f (withEnv (bindS con σ) m )) id cons' (return Nothing)

tcDecl (Function fname Nothing [] e) = do
  result <- tc e
  return (Just (fname , result))
tcDecl (Function fname (Just t) [] e) = do
  σ      <- generalize t 
  result <- tc (Ann e σ)
  return (Just (fname , result)) 
tcDecl (Function fname sig _  e) = throwError "Type checking for pattern matching functions is not yet implemented (use labda's and match instead)" 


tcProgram :: Program -> TC [Maybe (String , TCResult)]
tcProgram = fmap reverse . foldM (\acc decl -> tcDecl decl >>= \r -> return (r:acc)) [] . decls

type Result = Either String (Scheme , (Row , Row)) 

-- Infers the type of an expression, returning either an error string, or the
-- inferred type scheme.
infer :: Expr -> Result
infer e = (\(σ , ann) -> (normalizeAlpha σ , normalizeAnn ann))  <$> 
  ( fst $ runTC $
      tc e >>= \(s , t , ann) -> generalize (apply s t) >>= \σ -> return (σ , ann))

check :: Expr -> Scheme -> Result
check e σ = infer (Ann e σ)

checkProgram :: Program -> Either String [Maybe (String , TCResult)] 
checkProgram p = fst $ runTC (tcProgram p)
