module Main where

import Parser
import Prettyprint
import Modules
import Core

import System.Environment 
import Control.Monad.RWS

{-
TODO:
- elaborator:
  - insert constraints
  - generate fresh metavariables
  - generate guarded constants
  - build choice constraints
- constraint solver
  - reduce with metavariables
  - simplify use-env trees
  - detect and solve pattern constraints
  - solve choice constraints

de-blockify structure of definitions and data?
if termination/positivity is to be checked, we'll need a visited list,
but otherwise, the checks might become simpler
-}

main :: IO ()
main = getArgs >>= openFiles >>= checkFiles where

  openFiles :: [String] -> IO [(String,String)]
  openFiles = mapM (\name -> do file <- readFile name; pure (name,file))

  checkFiles :: [(String,String)] -> IO ()
  checkFiles files = case mapM (uncurry parse) files of
    Left err -> putStrLn err
    Right asts -> case checkModules asts of
      Left err -> putStrLn (showError err)
      Right _ -> putStrLn "ok"

