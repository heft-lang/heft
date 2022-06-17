module Heft.Syntax.Expr where

import Heft.Syntax.Misc
import Heft.Syntax.Type 

{- Syntax:

e ::= v
    | lam x e
    | e e
    | {e}
    | x
    | e!
    | match e with patcase*
    | con x e*
    | handle e e { case* }
    | op f e*
    | letrec x = e in e          -- Assumes that e is pure (returns a value without any side-effects)
    | e ⊕ e


⊕ ∈ +,-,=,...


v ::= vlam x e
    | v{e}
    | vcon x v*
    | c


case ::= return x p = e
       | op f x* p k = e


patcase ::= pcon x p* | pvar x

-}

data BinOp = Eq | Plus | Minus | Times
  deriving Show

{-
type Program = [Decl]

data Decl = DDecl ...
          | EDecl ...
          | FDecl Name (Maybe Type) [Pat] Expr 
-} 


newtype Program = Program { decls :: [Decl] }
  deriving Show

data Decl = Function Name (Maybe Type) [Pat] Expr          
          | Datatype Name
              [(Name , Kind)]   -- Parameters 
              [ ( Name          -- constructor name 
                , [Type]        -- Argument Types
                )
              ]
          | Effect Name
              [ ( Name                 -- op name 
                , Type                 -- Return Type (including suspension)
                , [Type]               -- Argument Types 
                )
              ]
  deriving Show

data Expr = V Val      -- Internal syntax     
          | Num Int
          | Lam String Expr
          | Var String
          | App Expr Expr
          | Susp Expr
          | Run Expr
          | Con String [Expr]
          | Match Expr [(Pat, Expr)]
          | Handle Name [(CPat,Expr)] Expr Expr
          | Op Name [Expr]
          | Letrec String Expr Expr
          | BOp Expr BinOp Expr
          | Ann Expr Scheme 
  deriving Show

data Pat = PCon String [Pat]
         | PVar String
  deriving Show

data Val  = VLam String Expr
          | VSusp Expr
          | VNum Int
          | VCon String [Val]

instance Eq Val where
  VNum i1 == VNum i2 = i1 == i2
  VCon f vs == VCon g ws | length vs == length ws = f == g && vs == ws
                         | otherwise = False
  _ == _ = False

instance Show Val where -- built-in support for list  show (VLam x e) = "(λ " ++ x ++ " . " ++ show e ++ ")"
  show (VSusp e)  = "{" ++ show e ++ "}"
  show (VNum i)   = show i
  show (VCon "[]" []) = "[]"
  show (VCon "::" [h,t]) = show h ++ " :: " ++ show t
  show (VCon "," [a,b]) = "(" ++ show a ++ ", " ++ show b ++ ")"
  
  show (VCon f []) = f
  show (VCon f vs) = "(" ++ f ++ " " ++ unwords (map show' vs) ++ ")"

  show (VLam x e) = "(\\" ++ x ++ " -> " ++ show e ++ ")"

show' :: Val -> [Char]
show' v@(VCon "::" [_, _]) = "(" ++ show v ++ ")"
show' v = show v

data CPat = PRet String String
          | POp Name [String] String String
  deriving Show

bindingsOfPat :: Pat -> [String]
bindingsOfPat (PVar x)    = [x]
bindingsOfPat (PCon _ ps) = concatMap bindingsOfPat ps

namesOf :: CPat -> [Name]
namesOf (PRet _ _) = []
namesOf (POp f _ _ _) = [f]

bindingsOfCPat :: CPat -> [String]
bindingsOfCPat (PRet x p)       = [x,p]
bindingsOfCPat (POp _ xs xp xk) = xs ++ [xp, xk]
