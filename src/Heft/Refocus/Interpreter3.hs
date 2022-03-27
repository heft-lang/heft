module Heft.Refocus.Interpreter3 where

import Heft.AST
--import Debug.Trace



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
subst (Handle' cases e1 e2) v x = Handle' (map (\ (p,e) ->
                                                  if elem x (bindingsOfCPat p) then (p, e)
                                                  else (p, subst e v x)) cases)
                                          (subst e1 v x)
                                          (subst e2 v x)
subst (Op f evs) v x = Op f (map (\ e -> subst e v x) evs)
subst (Letrec y e1 e2) v x | x == y = Letrec y e1 e2
                           | otherwise = Letrec y (subst e1 v x) (subst e2 v x)
subst (BOp e1 bop e2) v x = BOp (subst e1 v x) bop (subst e2 v x)



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
freshE (Handle' cases ep e) x = foldr (\ (p, e) x -> if (elem x (bindingsOfCPat p)) then freshE e ("." ++ x)
                                                     else freshE e x)
                                      (freshE e (freshE ep x))
                                      cases
freshE (Op _ esv) x = foldr freshE x esv
freshE (Letrec y e1 e2) x | x == y = freshE e2 (freshE e1 ("." ++ x))
                          | otherwise = freshE e2 (freshE e1 x)
freshE (BOp e1 _ e2) x = freshE e2 (freshE e1 x)



{- Refocused iteration -}

-- refunctionalization

eval :: Expr
     -> (Expr -> String -> [Val] -> String -> Val) -- unwind cont
     -> (String -> String)                                         -- fresh cont
     -> (Val -> Val)                                               -- plain cont
     -> Val
eval (V v) _ _ c = c v
eval (Num i) _ _ c = c (VNum i)
eval (Lam x e) _ _ c = c (VLam x e)
eval (Susp e) _ _ c = c (VSusp e)
eval (Var x) _ _ _ = error $ "Error: free variable " ++ x
eval (App e1 e2) h r c =
  eval e1
    (\ e -> h (App e e2))
    (r . freshE e2)
    (\ v1 ->
       eval e2
         (\ e -> h (App (V v1) e))
         r
         (\ v2 -> case v1 of
            (VLam x e) -> eval (subst e (V v2) x) h r c
            _          -> error $ "Type error: cannot apply non-function value " ++
                                  show v1 ++ " to the value " ++ show v2))
eval (Run e) h r c =
  eval e
    (\ e -> h (Run e))
    r
    (\ v -> case v of
        (VSusp e) -> eval e h r c
        _ -> error $ "Type error: cannot run non-suspension value " ++ show v)
eval (Con f es) h r c =
  (foldr
     (\ e c' vs ->
        eval e
          (\ e' -> h (Con f (map V vs ++ e':drop (length vs+1) es)))
          r
          (\ v' -> c' (vs ++ [v'])))
     (\ vs -> c (VCon f vs))
     es) []
eval (Match e pes) h r c =
  eval e
    (\ e -> h (Match e pes))
    (\ x ->
       r (foldr (\ (p, e) x -> if (elem x (bindingsOfPat p)) then freshE e ("." ++ x)
                               else freshE e x)
           x pes))
    (\ v -> case v of
        (VCon f vs) -> case match (VCon f vs) pes of
          Just (r', e) -> eval (foldr (\ (x,v) e -> subst e (V v) x) e r') h r c
          Nothing     -> error $ "Pattern match failure on value " ++ (show (VCon f vs))
        _           -> error $ "Type error: cannot match on non-constructor value " ++ show v)
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
eval (Handle cases ep e) _ _ c =
  c (VSusp $ Handle' cases ep e)
eval (Handle' cases ep e) h r c =
  eval ep
    (\ ep' -> h (Handle' cases ep' e))
    (\ x ->
      r (foldr (\ (p, e) x -> if (elem x (bindingsOfCPat p)) then freshE e ("." ++ x)
                              else freshE e x)
           (freshE e x)
           cases))
    (\ vp ->
       eval e
         (\ e f vs x -> case matchOp f vs cases of
             Nothing -> h (Handle' cases (V vp) e) f vs x 
             Just (xsv, xp, xk, e') ->
               let q = freshE e "q" in
               eval ( foldr (\ (x,v) e -> subst e (V v) x)
                            (subst (subst e' (V vp) xp)
                                   (Lam q
                                      (Lam x
                                         (Handle' cases (Var q) e)))
                                   xk)
                            (zip xsv vs) )
                 h
                 r
                 c)
         (\ x ->
            r (foldr (\ (p, e) x -> if (elem x (bindingsOfCPat p)) then freshE e ("." ++ x)
                                    else freshE e x)
                 (freshE e x)
                 cases))
         (\ v -> case retOf cases of
             Just (xv, xp, e) ->
               eval (subst (subst e (V vp) xp) (V v) xv)
                 h
                 r
                 c
             Nothing -> error "Handler is missing return case!"))
  where
    matchOp :: String -> [Val] -> [(CPat, Expr)] -> Maybe ([String], String, String, Expr)
    matchOp f vsv ((POp g xsv xp xk, e):cases)
      | f == g && length vsv == length xsv
        = Just (xsv, xp, xk, e)
      | otherwise
        = matchOp f vsv cases
    matchOp f vsv (_:cases) = matchOp f vsv cases
    matchOp _ _ _ = Nothing

    retOf :: [(CPat,Expr)] -> Maybe (String, String, Expr)
    retOf []                  = Nothing
    retOf ((PRet xv xp, e):_) = Just (xv, xp, e)
    retOf (_:cases)           = retOf cases
eval (Op f es) h r _ =
  (foldr
     (\ e c' vs' ->
        eval e
          (\ e' -> h (Op f (map V vs' ++ e':drop (length vs'+1) es)))
          r
          (\ v' ->
             c' (vs' ++ [v'])))
     (\ vs ->
        let x = r "x" in h (Run (Var x)) f vs x)
     es) []
eval (Letrec x e1 e2) h r c =
  eval e1
    (\ e' -> h (Letrec x e' e2))
    (\ x' -> if x == x' then ("." ++ x') else x')
    (\ v -> case v of
       VLam y e -> let e' = subst e (Letrec x (V v) (Var x)) x in
         eval (subst e2 (V $ VLam y e') x)
           h
           r
           c
       VSusp e -> let e' = subst e (Letrec x (V v) (Var x)) x in
         eval (subst e2 (V $ VSusp e') x)
           h
           r
           c
       v ->
         eval (subst e2 (V v) x)
           h
           r
           c)
eval (BOp e1 bop e2) h r c =
  eval e1
    (\ e' -> h (BOp e' bop e2))
    r
    (\ v1 ->
       eval e2
         (\ e' -> h (BOp (V v1) bop e'))
         r
         (\ v2 -> case bop of
            Eq -> if v1 == v2
              then c (VCon "True" [])
              else c (VCon "False" [])
            Plus -> case (v1, v2) of
              (VNum i1, VNum i2) -> c (VNum (i1 + i2))
              p -> error $ "Bad plus expression. Expected sub-expressions to yield numbers, but got: " ++ show p
            Times -> case (v1, v2) of
              (VNum i1, VNum i2) -> c (VNum (i1 * i2))
              p -> error $ "Bad times expression. Expected sub-expressions to yield numbers, but got: " ++ show p
            Minus -> case (v1, v2) of
              (VNum i1, VNum i2) -> c (VNum (i1 - i2))
              p -> error $ "Bad minus expression. Expected sub-expressions to yield numbers, but got: " ++ show p))


-- run

run :: Expr -> Val
run e =
  eval e
    (\ _ f _ _ -> error $ "Unhandled op error: " ++ f ++ " is unhandled")
    id
    id


