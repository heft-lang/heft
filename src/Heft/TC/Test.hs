module Heft.TC.Test where

import Heft.Syntax.Type 
import Heft.Syntax.Expr
import Heft.TC.TC 

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

expr19 = LetData "Unit" [] [("TT" , [])] (Var "TT")

expr20 = LetData "Nat" [] [("Zero" , []) , ("Suc" , [VarT "Nat"])] (Con "Suc" [(Con "Zero" [])])

expr21 = LetData "Nat" [] [("Zero" , []) , ("Suc" , [VarT "Nat"])] (App (Var "Suc") (Var "Suc"))

expr22 = LetData "Maybe" [("a" , Star)] [("Just" , [VarT "a"]), ("Nothing" , [])] (Con "Just" [])   

expr23 = LetData "Maybe" [("a" , Star)] [("Just" , [VarT "a"]), ("Nothing" , [])] (Con "Just" [Con "Nothing" []])   

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
    , expr19
    , expr20
    , expr21
    , expr22
    , expr23
    ]
  where runTest e = putStrLn ("Term:\t\t " ++ show e) >> printResult (infer e) >> putStr "\n" 

