module Heft.Interpreter where

import Heft.AST

{- Contexts

E ::= E e | v E | E!
    | handle cases with E in e | handle cases with v in E
    | op f (E...e) | ... | op f (v...E)
    | ho f (E...e) es | ... | ho f (v...E) es | ho f vs (E...e) | ho f vs (v...E)

-}

data Ctx = CtxMt
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
-----------------------------------------------------------------
handle cases with vp in E[ op f vsv vsm ]
  |-> e[ xs/vsv , ms/vsm , p/vp , k/(λ y q . handle cases with q in E[y!]) ]

-}

{- Notion of potential redex -}

data PR = PRNum Int
        | PRLam String Expr
        | PRApp String Expr Val
        | PRSusp Expr
        | PRRun Expr
        | PRCon String [Val]
        | PRMatch Name [Val] [(Pat, Expr)]
        | PRRet [(CPat,Expr)] Val Val
        | PROp Name [Val] [Val] [(CPat,Expr)] Val Ctx
        | PRLetrec String Expr Expr
        | PRBOp Val BinOp Val

{- Notion of decomposition -}

data Decomp = VD Val                  -- value decomposition
            | RD Ctx PR               -- redex decomposition
            | OD Ctx Name [Val] [Val] -- op decomposition

{- Decomposition, Composition, Recomposition -}

decompose :: Expr -> Ctx -> Decomp
decompose (V v)                      CtxMt = VD v
decompose (V v)                      c@CtxRun{} 
  = error $ "Cannot decompose value: " ++ show v ++ "\nin: " ++ show c ++ "\nperhaps you forgot to thunk a value?"
decompose (Num i)                     c     = RD c (PRNum i)
decompose (Lam x e)                   c     = RD c (PRLam x e)
decompose (Var x)                     c     = error $ "Error: free variable " ++ x
decompose (App (V (VLam x e)) (V v2)) c     = RD c (PRApp x e v2)
decompose (App (V v) e2)              c     = decompose e2 (CtxApp1 v c)
decompose (App e1 e2)                 c     = decompose e1 (CtxApp0 c e2)
decompose (Susp e)                    c     = RD c (PRSusp e)
decompose (Run (V (VSusp e)))         c     = RD c (PRRun e)
decompose (Run e)                     c     = decompose e (CtxRun c)
decompose (Con f es)                  c     = case partition es of
  Left vs -> RD c (PRCon f vs)
  Right (vs, e, es) -> decompose e (CtxCon f vs c es)
decompose (Match (V (VCon x vs)) pes) c     = RD c (PRMatch x vs pes)
decompose (Match e pes)               c     = decompose e (CtxMatch c pes)
decompose (Handle cases (V p) (V v))  c     = RD c (PRRet cases p v)
decompose (Handle cases (V p) e    )  c     = case decompose e CtxMt of
  OD c' f' vsv vsm -> if elem f' (concat $ map (namesOf . fst) cases)
    then RD c (PROp f' vsv vsm cases p c')
    else OD (compose c' (CtxHandle1 cases p c)) f' vsv vsm
  RD c' pr -> RD (compose c' (CtxHandle1 cases p c)) pr
decompose (Handle cases ep e)         c     = decompose ep (CtxHandle0 cases c e)
decompose (Op f esv esm)              c     = case partition esv of
  Left vsv -> case partition esm of
    Left vsm -> OD c f vsv vsm
    Right (vsm, e, esm) -> decompose e (CtxOp1 f vsv vsm c esm)
  Right (vsv, e, esv) -> decompose e (CtxOp0 f vsv c esv esm)
decompose (Letrec x e1 e2)            c     = RD c (PRLetrec x e1 e2)
decompose (BOp (V v1) bop (V v2))     c     = RD c (PRBOp v1 bop v2)
decompose (BOp (V v1) bop e2)         c     = decompose e2 (CtxBOp1 v1 bop c)
decompose (BOp e1 bop e2)             c     = decompose e1 (CtxBOp0 c bop e2)
decompose e c = error $ "Cannot decompose: " ++ show e ++ "\nin: " ++ show c


partition :: [Expr] -> Either [Val] ([Val], Expr, [Expr])
partition []     = Left []
partition (V v:es) = case partition es of
  Left vs -> Left (v:vs)
  Right (vs, e, es) -> Right (v:vs, e, es)
partition (e:es) = case partition es of
  Left vs -> Right ([], e, map V vs)
  Right (vs, e', es) -> Right ([], e, map V vs ++ e':es)


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
freshC (CtxCon f vs c es) x = freshC c (foldr freshE x es)
freshC (CtxMatch c pes)   x = freshC c (foldr (\ (p, e) x -> if (elem x (bindingsOfPat p)) then freshE e ("." ++ x)
                                                             else freshE e x)
                                              x pes)
freshC (CtxHandle0 cases c e) x = freshC c (foldr (\ (p, e) x -> if (elem x (bindingsOfCPat p)) then freshE e ("." ++ x)
                                                                 else freshE e x)
                                                  (freshE e x)
                                                  cases)
freshC (CtxHandle1 cases v c) x = freshC c (foldr (\ (p, e) x -> if (elem x (bindingsOfCPat p)) then freshE e ("." ++ x)
                                                                 else freshE e x)
                                                  x
                                                  cases)
freshC (CtxOp0 f vs c esv esm) x = freshC c (foldr freshE (foldr freshE x esv) esm)
freshC (CtxOp1 f vs vsm c esm) x = freshC c (foldr freshE x esm)
freshC (CtxBOp0 c bop e1) x = freshC c (freshE e1 x)
freshC (CtxBOp1 v1 bop c) x = freshC c x


freshE :: Expr -> String -> String
freshE (V v)         x = x
freshE (Num i)       x = x
freshE (Lam y e)     x | y == x    = freshE e ("." ++ x)
                       | otherwise = freshE e x
freshE (Var y)       x | y == x    = "." ++ x
                       | otherwise = x
freshE (App e1 e2)   x = freshE e2 (freshE e1 x)
freshE (Susp e)      x = freshE e x
freshE (Run e)       x = freshE e x
freshE (Con f es)    x = foldr freshE x es
freshE (Match e pes) x = foldr (\ (p, e) x -> if (elem x (bindingsOfPat p)) then freshE e ("." ++ x)
                                              else freshE e x)
                               (freshE e x)
                               pes
freshE (Handle cases ep e) x = foldr (\ (p, e) x -> if (elem x (bindingsOfCPat p)) then freshE e ("." ++ x)
                                                    else freshE e x)
                                     (freshE e (freshE ep x))
                                     cases
freshE (Op f esv esm) x = foldr freshE (foldr freshE x esv) esm
freshE (Letrec y e1 e2) x | x == y = freshE e2 (freshE e1 ("." ++ x))
                          | otherwise = freshE e2 (freshE e1 x)
freshE (BOp e1 bop e2) x = freshE e2 (freshE e1 x)

{- Contraction -}

contract :: PR -> Expr
contract (PRNum i) = V (VNum i)
contract (PRLam x e) = V (VLam x e)
contract (PRApp x e v) = subst e (V v) x
contract (PRSusp e) = V (VSusp e)
contract (PRRun e) = e
contract (PRCon f vs) = V (VCon f vs)
contract (PRMatch f vs pes) = case match (VCon f vs) pes of
  Just (r, e) -> foldr (\ (x,v) e -> subst e (V v) x) e r
  Nothing -> error $ "Pattern match failure on value " ++ (show (VCon f vs))
  where
    match v           ((PVar x, e):pes)      = Just ([(x,v)], e)
    match (VCon f vs) ((PCon g ps, e):pes) | f == g && length vs == length ps
                                             = foldr (\ (v,p) m -> do
                                                         (r, e) <- m
                                                         (r', e) <- match v [(p, e)]
                                                         return (r ++ r', e))
                                                     (Just ([], e))
                                                     (zip vs ps)
                                           | otherwise
                                             = match (VCon f vs) pes
    match _ [] = Nothing
contract (PRRet cases vp v) = case retOf cases of
  Just (PRet xv xp, e) -> subst (subst e (V vp) xp) (V v) xv
  Nothing -> error "Handler is missing return case!"
  where
    retOf []                  = Nothing
    retOf ((PRet xv xp, e):_) = Just (PRet xv xp, e)
    retOf (_:cases)           = retOf cases
contract (PROp f vsv vsm cases vp c) =
  let y = freshC c "x"
      q = freshC c "p"
  in case matchOp f vsv vsm cases of
    Just (POp f' xsv xsm xp xk, e) ->
      foldr (\ (x,v) e -> subst e (V v) x)
            (subst (subst e (V vp) xp)
                   (Lam y
                      (Lam q
                         (Handle cases (Var q)
                            (recompose c (Run (Var y))))))
                   xk)
            (zip xsv vsv ++ zip xsm vsm)
    Nothing -> error $ "Bad redex: the op " ++ f ++ " is unhandled"
  where
    matchOp f vsv vsm ((POp g xsv xsm xp xk, e):cases)
      | f == g && length vsv == length xsv && length vsm == length xsm
        = Just (POp g xsv xsm xp xk, e)
      | otherwise
        = matchOp f vsv vsm cases
    matchOp f vsv vsm (_:cases) = matchOp f vsv vsm cases
    matchOp _ _ _ _ = Nothing
contract (PRLetrec x e1 e2) =
  subst e2 (subst e1 (Letrec x e1 e2) x) x
contract (PRBOp v1 Eq v2) =
  if v1 == v2 then Con "True" [] else Con "False" []
contract (PRBOp v1 Plus v2) = case (v1, v2) of
  (VNum i1, VNum i2) -> V $ VNum (i1 + i2)
  p -> error $ "Bad plus expression. Expected sub-expressions to yield numbers, but found: " ++ show p
contract (PRBOp v1 Times v2) = case (v1, v2) of
  (VNum i1, VNum i2) -> V $ VNum (i1 * i2)
  p -> error $ "Bad times expression. Expected sub-expressions to yield numbers, but found: " ++ show p
contract (PRBOp v1 Minus v2) = case (v1, v2) of
  (VNum i1, VNum i2) -> V $ VNum (i1 - i2)
  p -> error $ "Bad minus expression. Expected sub-expressions to yield numbers, but found: " ++ show p


{- Drive -}

drive :: Expr -> Val
drive e = --trace (show e ++ "\n") $ 
  case decompose e CtxMt of
    VD v -> v
    RD c r -> drive (recompose c (contract r))
    OD _ f _ _ -> error $ "Unhandled op: " ++ f
