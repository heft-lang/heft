module Heft.Interpreter where

import Heft.AST
--import Debug.Trace

{- Contexts

E ::= E e | v E | E!
    | handle cases with E in e | handle cases with v in E
    | op f (E...e) | ... | op f (v...E)
    | ho f (E...e) es | ... | ho f (v...E) es | ho f vs (E...e) | ho f vs (v...E)

-}

data Ctx
  = CtxMt
  | CtxApp0 Ctx Expr
  | CtxApp1 Val Ctx
  | CtxRun Ctx
  | CtxCon String [Val] Ctx [Expr]
  | CtxMatch Ctx [(Pat,Expr)]
  | CtxHandle0 [(CPat, Expr)] Ctx Expr
  | CtxHandle1 [(CPat, Expr)] Val Ctx
  | CtxOp0 Name [Val] Ctx [Expr] [Expr]
  | CtxOp1 Name [Val] [Val] Ctx [Expr]
  | CtxBOp0 Ctx BinOp Expr
  | CtxBOp1 Val BinOp Ctx
  deriving Show

{- Semantics (selected rules):

e |-> e'
------------------
E[ e ] --> E[ e' ]


{e}! |-> e 


(lam x e) v |-> e[x/v]


letrec x = e1 in e2 |-> e2[ x/e[ x/(letrec x = e1 in e2) ] ]


(return x p = e) ∈ cases
--------------------------------------------
handle cases with vp in v |-> e[ x/v, p/vp ]


there are no closer handlers that match f in E
(op f xs ms p k = e) ∈ cases
----------------------------------------------------------------------------
handle cases with vp in E[ op f vsv vsm ]
  |-> e[ xs/vsv , ms/vsm , p/vp , k/(λ y q . handle cases with q in E[y!]) ]

-}

{- Notion of potential redex -}

data PR
  = PRNum Int
  | PRLam String Expr
  | PRApp String Expr Val
  | PRSusp Expr
  | PRRun Expr
  | PRCon String [Val]
  | PRMatch Name [Val] [(Pat, Expr)]
  | PRRet [(CPat,Expr)] Val Val
  | PROp Name [Val] [Val]
  | PRLetrec String Expr Expr
  | PRBOp Val BinOp Val


{- Notion of decomposition -}

data Decomp = VD Val                  -- value decomposition
            | RD Ctx PR               -- redex decomposition

{- Decomposition, Composition, Recomposition -}

decompose :: Expr -> Ctx -> Decomp
decompose (V v)                       c = decompose_aux c v
decompose (Num i)                     c = decompose_aux c (VNum i)
decompose (Lam x e)                   c = decompose_aux c (VLam x e)
decompose (Susp e)                    c = decompose_aux c (VSusp e)
decompose (Var x)                     _ = error $ "Error: free variable " ++ x
decompose (App e1 e2)                 c = decompose e1 (CtxApp0 c e2)
decompose (Run e)                     c = decompose e (CtxRun c)
decompose (Con f es)                  c = case es of
  []     -> decompose_aux c (VCon f [])
  (e:es) -> decompose e (CtxCon f [] c es)
decompose (Match e pes)               c = decompose e (CtxMatch c pes)
decompose (Handle cases ep e)         c = decompose ep (CtxHandle0 cases c e)
decompose (Op f esv esm)              c = case esv of
  []     -> case esm of
    []      -> RD c (PROp f [] [])
    (e:esm) -> decompose e (CtxOp1 f [] [] c esm)
  (e:es) -> decompose e (CtxOp0 f [] c es esm)
decompose (Letrec x e1 e2)            c = RD c (PRLetrec x e1 e2)
decompose (BOp e1 bop e2)             c = decompose e1 (CtxBOp0 c bop e2)

decompose_aux :: Ctx -> Val -> Decomp
decompose_aux CtxMt                  v  = VD v
decompose_aux (CtxApp0 c e2)         v1 = decompose e2 (CtxApp1 v1 c)
decompose_aux (CtxApp1 v1 c)         v2 = case v1 of
  (VLam x e) -> RD c (PRApp x e v2)
  _          -> error $ "Type error: cannot apply non-function value " ++ show v1 ++ " to the value " ++ show v2
decompose_aux (CtxRun c)              v  = case v of
  (VSusp e) -> RD c (PRRun e)
  _         -> error $ "Type error: cannot run non-suspension value " ++ show v
decompose_aux (CtxMatch c pes)        v  = case v of
  (VCon x vs) -> RD c (PRMatch x vs pes)
  _           -> error $ "Type error: cannot match on non-constructor value " ++ show v
decompose_aux (CtxHandle0 cases c e)  v  = decompose e (CtxHandle1 cases v c)
decompose_aux (CtxHandle1 cases vp c) v  = RD c (PRRet cases vp v)
decompose_aux (CtxOp0 f vs c es esm)  v  = case es of
  []     -> case esm of
    []      -> RD c (PROp f (vs ++ [v]) [])
    (e:esm) -> decompose e (CtxOp1 f (vs ++ [v]) [] c esm)
  (e:es) -> decompose e (CtxOp0 f (vs ++ [v]) c es esm)
decompose_aux (CtxOp1 f vs vsm c esm) v  = case esm of
  []      -> RD c (PROp f vs (vsm ++ [v]))
  (e:esm) -> decompose e (CtxOp1 f vs (vsm ++ [v]) c esm)
decompose_aux (CtxCon f vs c es)      v  = case es of
  []     -> RD c (PRCon f (vs ++ [v]))
  (e:es) -> decompose e (CtxCon f (vs ++ [v]) c es)
decompose_aux (CtxBOp0 c bop e2)      v  = decompose e2 (CtxBOp1 v bop c)
decompose_aux (CtxBOp1 v1 bop c)      v  = RD c (PRBOp v1 bop v)


compose :: Ctx -> Ctx -> Ctx
compose CtxMt                     c2 = c2
compose (CtxApp0 c1 e)            c2 = CtxApp0 (compose c1 c2) e
compose (CtxApp1 v c1)            c2 = CtxApp1 v (compose c1 c2)
compose (CtxRun c1)               c2 = CtxRun (compose c1 c2)
compose (CtxCon f vs c1 es)       c2 = CtxCon f vs (compose c1 c2) es
compose (CtxMatch c1 pes)         c2 = CtxMatch (compose c1 c2) pes
compose (CtxHandle0 cases c1 e)   c2 = CtxHandle0 cases (compose c1 c2) e
compose (CtxHandle1 cases v c1)   c2 = CtxHandle1 cases v (compose c1 c2)
compose (CtxOp0 x vsv c1 esv esm) c2 = CtxOp0 x vsv (compose c1 c2) esv esm
compose (CtxOp1 x vsv vsm c1 esm) c2 = CtxOp1 x vsv vsm (compose c1 c2) esm
compose (CtxBOp0 c1 bop e2)       c2 = CtxBOp0 (compose c1 c2) bop e2
compose (CtxBOp1 v1 bop c1)       c2 = CtxBOp1 v1 bop (compose c1 c2)


recompose :: Ctx -> Expr -> Expr
recompose CtxMt                    e = e
recompose (CtxApp0 c e2)           e = recompose c (App e e2)
recompose (CtxApp1 v c)            e = recompose c (App (V v) e)
recompose (CtxRun c)               e = recompose c (Run e)
recompose (CtxCon f vs c es)       e = recompose c (Con f (map V vs ++ e:es))
recompose (CtxMatch c pes)         e = recompose c (Match e pes)
recompose (CtxHandle0 cases c e1)  e = recompose c (Handle cases e    e1)
recompose (CtxHandle1 cases v c)   e = recompose c (Handle cases (V v) e)
recompose (CtxOp0 f vs c es0 es1)  e = recompose c (Op f (map V vs ++ e : es0) es1)
recompose (CtxOp1 f vs0 vs1 c es1) e = recompose c (Op f (map V vs0) (map V vs1 ++ e : es1))
recompose (CtxBOp0 c bop e2)       e = recompose c (BOp e bop e2)
recompose (CtxBOp1 v1 bop c)       e = recompose c (BOp (V v1) bop e)


{- Substitution -}

subst :: Expr -> Expr -> String -> Expr
subst (V v)          _ _ = V v
subst (Num i)        _ _ = Num i
subst (Lam y e)      v x | x == y    = Lam y e
                         | otherwise = Lam y (subst e v x)
subst (Var y)        v x | x == y    = v
                         | otherwise = Var y
subst (App e1 e2)    v x = App (subst e1 v x) (subst e2 v x)
subst (Susp e)       v x = Susp (subst e v x)
subst (Run e)        v x = Run (subst e v x)
subst (Con c es)     v x = Con c (map (\ e -> subst e v x) es)
subst (Match e pes)  v x = Match (subst e v x) (map (\ (p, e) ->
                                                      if elem x (bindingsOfPat p) then (p, e)
                                                      else (p, subst e v x)) pes)
subst (Handle cases e1 e2) v x = Handle (map (\ (p,e) ->
                                                if elem x (bindingsOfCPat p) then (p, e)
                                                else (p, subst e v x)) cases)
                                        (subst e1 v x)
                                        (subst e2 v x)
subst (Op f evs ems) v x = Op f (map (\ e -> subst e v x) evs) (map (\ e -> subst e v x) ems)
subst (Letrec y e1 e2) v x | x == y = Letrec y e1 e2
                           | otherwise = Letrec y (subst e1 v x) (subst e2 v x)
subst (BOp e1 bop e2) v x = BOp (subst e1 v x) bop (subst e2 v x)


{- Computing fresh names -}

freshC :: Ctx -> String -> String
freshC CtxMt              x = x
freshC (CtxApp0 c e)      x = freshC c (freshE e x)
freshC (CtxApp1 _ c)      x = freshC c x
freshC (CtxRun c)         x = freshC c x
freshC (CtxCon _ _ c es)  x = freshC c (foldr freshE x es)
freshC (CtxMatch c pes)   x = freshC c (foldr (\ (p, e) x -> if (elem x (bindingsOfPat p)) then freshE e ("." ++ x)
                                                             else freshE e x)
                                              x pes)
freshC (CtxHandle0 cases c e) x = freshC c (foldr (\ (p, e) x -> if (elem x (bindingsOfCPat p)) then freshE e ("." ++ x)
                                                                 else freshE e x)
                                                  (freshE e x)
                                                  cases)
freshC (CtxHandle1 cases _ c) x = freshC c (foldr (\ (p, e) x -> if (elem x (bindingsOfCPat p)) then freshE e ("." ++ x)
                                                                 else freshE e x)
                                                  x
                                                  cases)
freshC (CtxOp0 _ _ c esv esm) x = freshC c (foldr freshE (foldr freshE x esv) esm)
freshC (CtxOp1 _ _ _ c esm) x = freshC c (foldr freshE x esm)
freshC (CtxBOp0 c _ e1) x = freshC c (freshE e1 x)
freshC (CtxBOp1 _ _ c) x = freshC c x


freshE :: Expr -> String -> String
freshE (V _)         x = x
freshE (Num _)       x = x
freshE (Lam y e)     x | y == x    = freshE e ("." ++ x)
                       | otherwise = freshE e x
freshE (Var y)       x | y == x    = "." ++ x
                       | otherwise = x
freshE (App e1 e2)   x = freshE e2 (freshE e1 x)
freshE (Susp e)      x = freshE e x
freshE (Run e)       x = freshE e x
freshE (Con _ es)    x = foldr freshE x es
freshE (Match e pes) x = foldr (\ (p, e) x -> if (elem x (bindingsOfPat p)) then freshE e ("." ++ x)
                                              else freshE e x)
                               (freshE e x)
                               pes
freshE (Handle cases ep e) x = foldr (\ (p, e) x -> if (elem x (bindingsOfCPat p)) then freshE e ("." ++ x)
                                                    else freshE e x)
                                     (freshE e (freshE ep x))
                                     cases
freshE (Op _ esv esm) x = foldr freshE (foldr freshE x esv) esm
freshE (Letrec y e1 e2) x | x == y = freshE e2 (freshE e1 ("." ++ x))
                          | otherwise = freshE e2 (freshE e1 x)
freshE (BOp e1 _ e2) x = freshE e2 (freshE e1 x)

{- Contraction -}

contract :: PR -> Ctx -> (Expr, Ctx)
contract (PRNum i) c = (V $ VNum i, c)
contract (PRLam x e) c = (V $ VLam x e, c)
contract (PRApp x e v) c = (subst e (V v) x, c)
contract (PRSusp e) c = (V $ VSusp e, c)
contract (PRRun e) c = (e, c)
contract (PRCon f vs) c = (V $ VCon f vs, c)
contract (PRMatch f vs pes) c = case match (VCon f vs) pes of
  Just (r, e) -> (foldr (\ (x,v) e -> subst e (V v) x) e r, c)
  Nothing -> error $ "Pattern match failure on value " ++ (show (VCon f vs))
  where
    match v           ((PVar x, e):_)      = Just ([(x,v)], e)
    match (VCon f vs) ((PCon g ps, e):pes) | f == g && length vs == length ps
                                             = foldr (\ (v,p) m -> do
                                                         (r, e) <- m
                                                         (r', e) <- match v [(p, e)]
                                                         return (r ++ r', e))
                                                     (Just ([], e))
                                                     (zip vs ps)
                                           | otherwise
                                             = match (VCon f vs) pes
    match _ _ = Nothing
contract (PRRet cases vp v) c = case retOf cases of
  Just (xv, xp, e) -> (subst (subst e (V vp) xp) (V v) xv, c)
  Nothing -> error "Handler is missing return case!"
  where
    retOf :: [(CPat,Expr)] -> Maybe (String, String, Expr)
    retOf []                  = Nothing
    retOf ((PRet xv xp, e):_) = Just (xv, xp, e)
    retOf (_:cases)           = retOf cases
contract (PROp f vs vsm) c = let x = freshC c "x" in case unwind c f vs vsm x (Run (Var x)) of
  Just (e', c') -> (e', c')
  Nothing -> error $ "Unhandled op error: " ++ f ++ " is unhandled"
  where
    unwind :: Ctx -> String -> [Val] -> [Val] -> String -> Expr -> Maybe (Expr, Ctx)
    unwind CtxMt _ _ _ _ _ = Nothing
    unwind (CtxApp0 c e2) f vs vsm x e = unwind c f vs vsm x (App e e2)
    unwind (CtxApp1 v c) f vs vsm x e = unwind c f vs vsm x (App (V v) e)
    unwind (CtxRun c) f vs vsm x e = unwind c f vs vsm x (Run e)
    unwind (CtxCon g ws c es) f vs vsm x e = unwind c f vs vsm x (Con g (map V ws ++ e:es))
    unwind (CtxMatch c pes) f vs vsm x e = unwind c f vs vsm x (Match e pes)
    unwind (CtxHandle0 cases c e1) f vs vsm x e = unwind c f vs vsm x (Handle cases e e1)
    unwind (CtxHandle1 cases vp c) f vs vsm x e = case matchOp f vs vsm cases of
      Nothing -> unwind c f vs vsm x (Handle cases (V vp) e)
      Just (xsv, xsm, xp, xk, e') ->
        let q = freshE e "q" in
        Just ( foldr (\ (x,v) e -> subst e (V v) x)
                     (subst (subst e' (V vp) xp)
                            (Lam x
                               (Lam q
                                  (Handle cases (Var q) e)))
                            xk)
                     (zip xsv vs ++ zip xsm vsm)
             , c )
    unwind (CtxOp0 g ws c es0 es1) f vs vsm x e = unwind c f vs vsm x (Op g (map V ws ++ e:es0) es1)
    unwind (CtxOp1 g ws vs0 c es1) f vs vsm x e = unwind c f vs vsm x (Op g (map V ws) (map V vs0 ++ e:es1))
    unwind (CtxBOp0 c bop e2) f vs vsm x e = unwind c f vs vsm x (BOp e bop e2)
    unwind (CtxBOp1 v1 bop c) f vs vsm x e = unwind c f vs vsm x (BOp (V v1) bop e)

    matchOp :: String -> [Val] -> [Val] -> [(CPat, Expr)] -> Maybe ([String], [String], String, String, Expr)
    matchOp f vsv vsm ((POp g xsv xsm xp xk, e):cases)
      | f == g && length vsv == length xsv && length vsm == length xsm
        = Just (xsv, xsm, xp, xk, e)
      | otherwise
        = matchOp f vsv vsm cases
    matchOp f vsv vsm (_:cases) = matchOp f vsv vsm cases
    matchOp _ _ _ _ = Nothing
contract (PRLetrec x e1 e2) c =
  (subst e2 (subst e1 (Letrec x e1 (Var x)) x) x, c)
contract (PRBOp v1 Eq v2) c =
  (if v1 == v2 then Con "True" [] else Con "False" [], c)
contract (PRBOp v1 Plus v2) c = case (v1, v2) of
  (VNum i1, VNum i2) -> (V $ VNum (i1 + i2), c)
  p -> error $ "Bad plus expression. Expected sub-expressions to yield numbers, but found: " ++ show p
contract (PRBOp v1 Times v2) c = case (v1, v2) of
  (VNum i1, VNum i2) -> (V $ VNum (i1 * i2), c)
  p -> error $ "Bad times expression. Expected sub-expressions to yield numbers, but found: " ++ show p
contract (PRBOp v1 Minus v2) c = case (v1, v2) of
  (VNum i1, VNum i2) -> (V $ VNum (i1 - i2), c)
  p -> error $ "Bad minus expression. Expected sub-expressions to yield numbers, but found: " ++ show p


{- Drive -}

drive :: Expr -> Val
drive e = --trace (show e ++ "\n") $ 
  case decompose e CtxMt of
    VD v -> v
    RD c r -> case contract r c of
      (e', c') -> drive (recompose c' e')

{-

Parsed Expression:
Letrec "add" (Lam "x" (Lam "y" (Match (Var "x") [(PCon "S" [PVar "z"],Con "S" [App (App (Var "add") (Var "z")) (Var "y")]),(PCon "Z" [],Var "y")]))) (Letrec "fib" (Lam "x" (Match (Var "x") [(PCon "S" [PVar "y"],Match (Var "y") [(PCon "S" [PVar "z"],App (App (Var "add") (App (Var "fib") (Var "y"))) (App (Var "fib") (Var "z"))),(PCon "Z" [],Var "x")]),(PCon "Z" [],Var "x")])) (App (App (Var "add") (Con "S" [Con "Z" []])) (Con "S" [Con "Z" []])))
-}
