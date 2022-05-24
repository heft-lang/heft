module Heft.Repl where

import Control.Monad.Trans
import Control.Monad.State
import Control.Exception (throwIO)
import Data.List (isPrefixOf , delete)
import Data.Monoid
import qualified Data.Text.IO as T
import qualified Data.Map as M 

import System.Console.Haskeline (Interrupt (..) , Completion (..))
import System.Console.Repline
import System.Process 
import System.Exit
import System.FilePath
import System.Directory
import GHC.IO.Handle
import Control.Concurrent (threadDelay)

import Data.Text (pack, strip, unpack)

import Heft.Reporting

type Repl a = HaskelineT IO a

-- Evaluation : handle each line user inputs
cmd :: String -> Repl ()
cmd = run -- liftIO $ print input

-- Commands
help :: [String] -> Repl ()
help args = liftIO $ print $ "Help: " ++ show args

load :: FilePath -> Repl ()
load path = liftIO $ report WARNING "Loading isn't implemented yet" 

run :: String -> Repl ()
run name = liftIO $ report WARNING "Running isn't implemented yet" 

cd :: String -> Repl ()
cd path = do
  qpath <- liftIO $ canonicalizePath $ path
  liftIO $ setCurrentDirectory qpath
  liftIO $ report WARNING "Changing directories doesn't affect the internal state!" 


quitMessage = "Goodbye."

quit :: Repl ()
quit = do
  _ <- final
  liftIO $ throwIO Interrupt


check :: String -> Repl ()
check _ = liftIO $ report ERROR "Type checking is not yet implemented"


-- Options
opts :: [(String, String -> Repl ())]
opts =
  [ ("load"   , load) 
  , ("run"    , run) 
  , ("cd"     , cd)
  , ("check"  , check) 
  , ("quit"   , const quit)
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
  , (":dump"   , wordCompleter $ const $ return [])
  , (":quit"   , wordCompleter $ const $ return [])
  , (":core"   , fileCompleter' [".stc"])
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
customBanner SingleLine = pure ">>> "
customBanner MultiLine = pure "| "

repl :: IO ()
repl =
  evalReplOpts $
    ReplOpts
      { banner           = customBanner
      , command          = cmd
      , options          = opts
      , prefix           = Just ':'
      , multilineCommand = Just "paste"
      , tabComplete      = (Prefix (wordCompleter byWord) defaultMatcher)
      , initialiser      = ini
      , finaliser        = final
      }

