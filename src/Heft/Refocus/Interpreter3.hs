module Heft.Refocus.Interpreter3 where

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
  | CtxOp0 Name [Val] Ctx [Expr]
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
(op f xs p k = e) ∈ cases
----------------------------------------------------------------------------
handle cases with vp in E[ op f vsv ]
  |-> e[ xs/vsv , p/vp , k/(λ y q . handle cases with q in E[y!]) ]

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
  | PROp Name [Val]
  | PRLetrec String Expr Expr
  | PRBOp Val BinOp Val


{- Notion of decomposition -}

data Decomp
  = VD Val                  -- value decomposition
  | RD Ctx PR               -- redex decomposition


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
subst (Op f evs) v x = Op f (map (\ e -> subst e v x) evs)
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
freshC (CtxOp0 _ _ c es) x = freshC c (foldr freshE x es)
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
freshE (Op _ esv) x = foldr freshE x esv
freshE (Letrec y e1 e2) x | x == y = freshE e2 (freshE e1 ("." ++ x))
                          | otherwise = freshE e2 (freshE e1 x)
freshE (BOp e1 _ e2) x = freshE e2 (freshE e1 x)



{- Refocused iteration -}

-- refunctionalization

eval :: Expr -> (Expr -> (Val -> Val) -> String -> [Val] -> String -> Val) -> (Val -> Val) -> Val
eval (V v) _ c = c v
eval (Num i) _ c = c (VNum i)
eval (Lam x e) _ c = c (VLam x e)
eval (Susp e) _ c = c (VSusp e)
eval (Var x) _ _ = error $ "Error: free variable " ++ x
eval (App e1 e2) h c =
  eval e1
    (\ e -> h (App e e2))
    (\ v1 ->
       eval e2
         (\ e -> h (App (V v1) e))
         (\ v2 -> case v1 of
            (VLam x e) -> eval (subst e (V v2) x) h c
            _          -> error $ "Type error: cannot apply non-function value " ++ show v1 ++ " to the value " ++ show v2))
-- eval (Run e) c = eval e (CtxRun c)
-- eval (Con f es) c = case es of
--   []     -> cont c (VCon f [])
--   (e:es) -> eval e (CtxCon f [] c es)
-- eval (Match e pes) c = eval e (CtxMatch c pes)
-- eval (Handle cases ep e) c = eval ep (CtxHandle0 cases c e)
-- eval (Op f esv) c = case esv of
--   []     -> let x = freshC c "x" in unwind c f [] x (Run (Var x))
--   (e:es) -> eval e (CtxOp0 f [] c es)
-- eval (Letrec x e1 e2) c = eval (subst e2 (subst e1 (Letrec x e1 (Var x)) x) x) c
-- eval (BOp e1 bop e2) c = eval e1 (CtxBOp0 c bop e2)


-- cont :: Ctx -> Val -> Val
-- cont CtxMt v = v
-- cont (CtxApp0 c e2) v1 = eval e2 (CtxApp1 v1 c)
-- cont (CtxApp1 v1 c) v2 = case v1 of
--   (VLam x e) -> eval (subst e (V v2) x) c
--   _          -> error $ "Type error: cannot apply non-function value " ++ show v1 ++ " to the value " ++ show v2
-- cont (CtxRun c) v = case v of
--   (VSusp e) -> eval e c
--   _         -> error $ "Type error: cannot run non-suspension value " ++ show v
-- cont (CtxMatch c pes) v  = case v of
--   (VCon f vs) -> case match (VCon f vs) pes of
--     Just (r, e) -> eval (foldr (\ (x,v) e -> subst e (V v) x) e r) c
--     Nothing     -> error $ "Pattern match failure on value " ++ (show (VCon f vs))
--   _           -> error $ "Type error: cannot match on non-constructor value " ++ show v
--   where
--     match v           ((PVar x, e):_)      = Just ([(x,v)], e)
--     match (VCon f vs) ((PCon g ps, e):pes) | f == g && length vs == length ps
--                                              = foldr (\ (v,p) m -> do
--                                                          (r, e) <- m
--                                                          (r', e) <- match v [(p, e)]
--                                                          return (r ++ r', e))
--                                                      (Just ([], e))
--                                                      (zip vs ps)
--                                            | otherwise
--                                              = match (VCon f vs) pes
--     match _ _ = Nothing
-- cont (CtxHandle0 cases c e) v = eval e (CtxHandle1 cases v c)
-- cont (CtxHandle1 cases vp c) v = case retOf cases of
--   Just (xv, xp, e) -> eval (subst (subst e (V vp) xp) (V v) xv) c
--   Nothing -> error "Handler is missing return case!"
--   where
--     retOf :: [(CPat,Expr)] -> Maybe (String, String, Expr)
--     retOf []                  = Nothing
--     retOf ((PRet xv xp, e):_) = Just (xv, xp, e)
--     retOf (_:cases)           = retOf cases
-- cont (CtxOp0 f vs c es)  v  = case es of
--   []     -> let x = freshC c "x" in unwind c f (vs ++ [v]) x (Run (Var x))
--   (e:es) -> eval e (CtxOp0 f (vs ++ [v]) c es)
-- cont (CtxCon f vs c es)      v  = case es of
--   []     -> cont c (VCon f (vs ++ [v]))
--   (e:es) -> eval e (CtxCon f (vs ++ [v]) c es)
-- cont (CtxBOp0 c bop e2)      v  = eval e2 (CtxBOp1 v bop c)
-- cont (CtxBOp1 v1 bop c)      v  = case bop of
--   Eq -> if v1 == v
--     then cont c (VCon "True" [])
--     else cont c (VCon "False" [])
--   Plus -> case (v1, v) of
--     (VNum i1, VNum i2) -> cont c (VNum (i1 + i2))
--     p -> error $ "Bad plus expression. Expected sub-expressions to yield numbers, but got: " ++ show p
--   Times -> case (v1, v) of
--     (VNum i1, VNum i2) -> cont c (VNum (i1 * i2))
--     p -> error $ "Bad times expression. Expected sub-expressions to yield numbers, but got: " ++ show p
--   Minus -> case (v1, v) of
--     (VNum i1, VNum i2) -> cont c (VNum (i1 - i2))
--     p -> error $ "Bad minus expression. Expected sub-expressions to yield numbers, but got: " ++ show p


-- -- helpers

-- unwind :: Ctx -> String -> [Val] -> String -> Expr -> Val
-- unwind CtxMt f _ _ _ = error $ "Unhandled op error: " ++ f ++ " is unhandled"
-- unwind (CtxApp0 c e2) f vs x e = unwind c f vs x (App e e2)
-- unwind (CtxApp1 v c) f vs x e = unwind c f vs x (App (V v) e)
-- unwind (CtxRun c) f vs x e = unwind c f vs x (Run e)
-- unwind (CtxCon g ws c es) f vs x e = unwind c f vs x (Con g (map V ws ++ e:es))
-- unwind (CtxMatch c pes) f vs x e = unwind c f vs x (Match e pes)
-- unwind (CtxHandle0 cases c e1) f vs x e = unwind c f vs x (Handle cases e e1)
-- unwind (CtxHandle1 cases vp c) f vs x e = case matchOp f vs cases of
--   Nothing -> unwind c f vs x (Handle cases (V vp) e)
--   Just (xsv, xp, xk, e') ->
--     let q = freshE e "q" in
--     eval ( foldr (\ (x,v) e -> subst e (V v) x)
--                  (subst (subst e' (V vp) xp)
--                         (Lam x
--                            (Lam q
--                               (Handle cases (Var q) e)))
--                         xk)
--                  (zip xsv vs) )
--          c
-- unwind (CtxOp0 g ws c es) f vs x e = unwind c f vs x (Op g (map V ws ++ e:es))
-- unwind (CtxBOp0 c bop e2) f vs x e = unwind c f vs x (BOp e bop e2)
-- unwind (CtxBOp1 v1 bop c) f vs x e = unwind c f vs x (BOp (V v1) bop e)

-- matchOp :: String -> [Val] -> [(CPat, Expr)] -> Maybe ([String], String, String, Expr)
-- matchOp f vsv ((POp g xsv xp xk, e):cases)
--   | f == g && length vsv == length xsv
--     = Just (xsv, xp, xk, e)
--   | otherwise
--     = matchOp f vsv cases
-- matchOp f vsv (_:cases) = matchOp f vsv cases
-- matchOp _ _ _ = Nothing


-- -- run

-- run :: Expr -> Val
-- run e = eval e CtxMt


