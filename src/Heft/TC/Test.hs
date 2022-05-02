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

expr24 = LetData "Unit" [] [("TT" , [])] (Lam "x" (Match (Var "x") [(PCon "TT" [] , Num 0)]))

expr25 =
  LetData "Maybe" [("a" , Star)] [("Just" , [VarT "a"]), ("Nothing" , [])] $
    Letrec "maybe"
      (Lam "f" (Lam "z" (Lam "x"
        (Match (Var "x")
           [ (PCon "Nothing" []      , Var "z")
           , (PCon "Just" [PVar "y"] , App (Var "f") (Var "y"))]
        ))))

      (Var "maybe") 

printResult :: Result -> IO ()
printResult (Left err) = do
  putStrLn err
printResult (Right (σ , (ε , εl))) = do
  putStrLn $ "Inferred:\t " ++ show σ ++ " | " ++ show ε ++ " * " ++ show εl 

runTest :: Expr -> IO () 
runTest e = putStrLn ("Term:\t\t " ++ show e) >> printResult (infer e) >> putStr "\n" 

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
    , expr24
    , expr25
    ]

matchTest = mapM_ runTest
  [ expr24
  , expr25
  ]


hexpr1 =
  LetEff "Abort"
    [ ("abort" , "r" , (VarT "a") , [])
    ] $
  Handle "Abort"
    [(PRet "x" "p" , Susp (BOp (Var "x") Plus (Var "p")))
    ]
    (Num 0)
  (Num 1)

hexpr2 =
  LetEff "Abort"
    [ ("abort" , "r" , (VarT "a") , [])
    ] $
  LetData "Maybe" [("a" , Star)]
    [ ("Just"    , [VarT "a"])
    , ("Nothing" , [])
    ] $
  Lam "n" $ 
  Handle "Abort"
    [(PRet "x" "p" , Susp (Con "Just" [BOp (Var "x") Plus (Var "p")]))
    ]
    (Var "n")
  (Run $ Op "abort" [])

hexpr3 =
  LetEff "Abort"
    [ ("abort" , "r" , (VarT "a") , [])
    ] $
  LetData "Maybe" [("a" , Star)]
    [ ("Just"    , [VarT "a"])
    , ("Nothing" , [])
    ] $
  LetData "Unit" []
    [ ("TT" , [])
    ] $ 
  Run $ Handle "Abort"
    [ (POp "abort" [] "p" "k" , Susp (Con "Nothing" [])) 
    , (PRet "x" "p" , Susp (Con "Just" [Var "x"]))
    ]
    (Con "TT" [])
  (Run $ Op "abort" [])

hexpr4 =
  LetData "Unit" []
    [ ("TT" , [])
    ] $
  LetData "Pair" [("a" , Star) , ("b" , Star)]
    [ ("MkPair" , [VarT "a",VarT "b"])
    ] $ 
  LetEff "State"
    [ ("get" , "r" , NumT , [])
    , ("put" , "r" , VarT "Unit", [NumT])
    ] $
  Lam "term" $ Lam "s" $ 
  Handle "State"
   [ (PRet "x" "s" , Susp (Con "MkPair" [Var "x", Var"s"]))
   , (POp "get" []       "s" "k" , App (App (Var "k") (Var "s")) (Susp (Var "s")))
   , (POp "put" ["sNew"] "s" "k" , App (App (Var "k") (Var "sNew")) (Susp (Con "TT" [])))
   ]
   (Var "s") $ 
  Run (Var "term")

optest =
  LetData "Unit" []
    [ ("TT" , [])
    ] $
  LetEff "State"
    [ ("get" , "r" , NumT , [])
    , ("put" , "r" , VarT "Unit", [NumT])
    ] $ Run $ Op "put" [(Num 10)]

handleTest = mapM_ runTest
  [ hexpr1
  , hexpr2
  , hexpr3
  , hexpr4
  , optest
  ]

fib :: Expr
fib =
  LetData "Nat" []
    [("Zero" , [])
    ,("Suc" , [VarT "Nat"])] $
  Letrec "add"
    (Lam "n" (Lam "m" $
      Match (Var "n")
        [ (PCon "Zero" []        , Var "m")
        , (PCon "Suc" [PVar "k"] , Con "Suc" [App (App (Var "add") (Var "k")) (Var "m")])
        ] 
    )) $
  Letrec "fib"
     (Lam "n"
       (Match (Var "n")
        [ (PCon "Zero" []                      , Con "Zero" [])
        , (PCon "Suc"  [PCon "Zero" []]        , Con "Suc" [Con "Zero" []])
        , (PCon "Suc"  [PCon "Suc" [PVar "n"]] , App (App (Var "add") (Con "Suc" [Var "n"])) (Var "n"))
        ]))
  (Var "fib")
  
fibTest = runTest fib 
