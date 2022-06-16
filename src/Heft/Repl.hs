module Heft.Repl where

import Control.Monad.Trans
import Control.Monad.State
import Control.Exception (throwIO)
import Data.List (isPrefixOf , delete)
import Data.Char (isSpace)
import Data.Monoid

import System.Console.Haskeline (Interrupt (..) , Completion (..))
import System.Console.Repline
import System.Exit
import System.FilePath
import System.Directory

import Heft.Parser
import Heft.TC.TC

import System.Console.Pretty

data LogType = INFO | WARNING | ERROR

typeStr :: LogType -> String
typeStr INFO    =  style Bold $ "[INFO]   "
typeStr WARNING =  style Bold $ colorize Foreground Yellow "[WARNING]"
typeStr ERROR   =  style Bold $ colorize Foreground Red  "[ERROR]  "

reportStr :: LogType -> String -> String
reportStr t str = typeStr t ++ " " ++ str 

report :: LogType -> String -> IO ()
report t str = putStrLn (reportStr t str) 


data ReplState = ReplState { wd :: FilePath -- working directory
                           } 

type Repl a = HaskelineT (StateT ReplState IO) a

-- Evaluation : handle each line user inputs
cmd :: String -> Repl ()
cmd = run -- liftIO $ print input

-- Commands
help :: [String] -> Repl ()
help args = liftIO $ print $ "Help: " ++ show args

load :: FilePath -> Repl ()
load path = do

  st <- get

  let qpath = filter (not . isSpace) (wd st </> path) 
  
  -- Read and parce source file 
  src <- liftIO $ readFile qpath
  let program = runParser qpath pProgram src

  -- Run type checker
  let tcOutput = checkProgram program

  case tcOutput of
    (Left  err) -> liftIO $ report ERROR   $ "Failed to load " ++ qpath ++ ": " ++ err
    (Right _)   -> liftIO $ report WARNING $ "Loaded " ++ qpath ++ ", but only ran the typechecker."

  -- TODO: actually load the contents of the file 

run :: String -> Repl ()
run name = liftIO $ report WARNING "Running isn't implemented yet" 

cd :: String -> Repl ()
cd path = do
  qpath <- liftIO $ canonicalizePath $ path
  liftIO $ setCurrentDirectory qpath
  st <- get
  put (st { wd = qpath })

-- Show current working directory
cwd :: Repl ()
cwd = do
  st <- get
  liftIO $ putStrLn (wd st)

ls :: Repl ()
ls = do
  st    <- get 
  paths <- liftIO $ getDirectoryContents (wd st)
  liftIO $ mapM_ putStrLn (filter ((/='.') . head) paths) 


quitMessage = "Goodbye."

quit :: Repl ()
quit = do
  _ <- final
  liftIO $ throwIO Interrupt



-- Options
opts :: [(String, String -> Repl ())]
opts = 
  [ ("load"   , load) 
  , ("run"    , run) 
  , ("cd"     , cd)
  , ("cwd"    , const cwd) 
  , ("quit"   , const quit)
  , ("dir"    , const ls ) 
  ] 

fileCompleter' :: (Monad m , MonadIO m) => [String] -> CompletionFunc m
fileCompleter' exts i = do
  (r , paths) <- fileCompleter i
  return (r , filter (endsWith exts . replacement) paths)

  where endsWith :: [String] -> FilePath -> Bool
        endsWith exts path = any ((flip isExtensionOf) path) exts

-- Completer
defaultMatcher :: (MonadIO m) => [([Char], CompletionFunc m)]
defaultMatcher =
  [ -- Commands
    (":load"   , fileCompleter' [".heft"])
  , (":run"    , wordCompleter $ const $ return [])
  , (":cd"     , fileCompleter)
  , (":cwd"    , wordCompleter $ const $ return [])
  , (":quit"   , wordCompleter $ const $ return [])
  , (":dir"     , wordCompleter $ const $ return []) 
  ]

byWord :: Monad m => WordCompleter m
byWord n = do
  let names = fmap ((":" <>) . fst) opts
  return $ filter (isPrefixOf n) names

-- Initialiser function

ini :: Repl ()
ini = liftIO $ putStrLn "Welcome!"

-- Finaliser function
final :: Repl ExitDecision
final = do
   liftIO $ putStrLn quitMessage
   return Exit

customBanner :: MultiLine -> Repl String
customBanner SingleLine = pure "h> "
customBanner MultiLine = pure "| "

initialState :: ReplState
initialState = ReplState { wd = "." } 

repl :: IO () 
repl = fmap fst $ flip runStateT initialState $ evalReplOpts $
  ReplOpts
      { banner           = customBanner
      , command          =  cmd
      , options          =  opts
      , prefix           =  Just ':'
      , multilineCommand =  Just "paste"
      , tabComplete      =  (Prefix (wordCompleter byWord) defaultMatcher)
      , initialiser      =  ini
      , finaliser        =  final
      }

