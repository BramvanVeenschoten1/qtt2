module Main where

import Parser
import Prettyprint
import Modules
import Core

import System.Environment 
import Control.Monad.RWS

{-
TODO:
- fix equations
- fix parser messages
- fix error messages

- do multiplicity checks
- restore and improve termination checks
- do positivity checks, also for indexed data

the atrocious error list:
- non covering split
- intro non-function

roadmap:
  - allow splitting on bottom
  - allow defaulting branches.
    - for non-linear types, this can be done by just replacing the defaulting pattern by
      wildcard patterns
  - do inference for minimal cic
  - have liftable constants
  - full inference for universes and multiplicities with subtyping
  - disambiguation
  - relax singleton criterion for absurd clauses
  - enable non-strict splits
  - enable alternative split order
  - optimize split liftover
  - split on Eq
  - patternmatching for minimal cic
  - general splitting on inductive families

note to self: don't work too hard to make linearity work,
  its not as valuable when you language can have separation logic for stateful computations

Q: have special case split computation for multiplicities?
pros:
- type a few more programs, in particular, linear let-bound variables can be
  outside cases and retain their definitional equality within
- simplify liftover in case expressions
cons:
- complicate kernel. Keep in mind that Agda can be implemented without this feature.
=> for now, keep this burden in the kernel, but re-evaluate

Q: have primitive default branches?
pros:
- improve naive compilation, reduce term size (possibly compiler performance)
cons:
- complication
=> term sizes can be kept reasonably small by defining branches in let-expressions
=> recovering default branches and projections is a nice job for the compiler

Q: one can go even further and have primitive faculty for @-patterns, to accommodate linearity and conversion
=> no, just no
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

