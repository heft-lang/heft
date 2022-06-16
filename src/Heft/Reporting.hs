module Heft.Reporting where

--import System.Console.Pretty

data LogType = INFO | WARNING | ERROR

typeStr :: LogType -> String
typeStr INFO    = "[-INFO----]"
typeStr WARNING = {- colorize Foreground Yellow -} "[-WARNING-]"
typeStr ERROR   = {- colorize Foreground Red -} "[-ERROR---]"

reportStr :: LogType -> String -> String
reportStr t str = typeStr t ++ " " ++ str 

report :: LogType -> String -> IO ()
report t str = putStrLn (reportStr t str) 

