module Main where

import Heft.Interpreter (eval)
import Heft.Parser (pProgram, runParser)
import Heft.Util (letify)
import Heft.Syntax.Expr (Expr (Var, Run))
import System.Environment (getArgs)

main :: IO ()
main = do
  x : _ <- getArgs
  runFile x

runFile :: String -> IO ()
runFile x = do
  xs <- readFile x
  let prog = runParser x pProgram xs
  putStrLn "Parsed Expression:"
  print prog
  putStrLn "Result Value:"
  print (eval (letify prog (Run (Var "main"))))
