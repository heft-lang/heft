module Main where

import Heft.Interpreter (eval)
import Heft.Parser (pExpr, runParser)
import System.Environment (getArgs)

main :: IO ()
main = do
  x : _ <- getArgs
  runFile x

runFile :: String -> IO ()
runFile x = do
  xs <- readFile x
  let expr = runParser x pExpr xs
  putStrLn "Parsed Expression:"
  print expr
  putStrLn "Result Value:"
  print (eval expr)