module Modules where

import Control.Monad
import Control.Monad.State.Lazy as S
import Core
import Data.Either
import Data.Function
import Data.List as L
import Data.Map as M
import Data.Maybe
import Debug.Trace
import Elaborator
import Declaration
import Lexer (Loc)
import Parser
import Prettyprint
import Error

import Control.Monad.RWS

modName (n, _, _) = n

sortDependencies :: [Module] -> Either Error [Module]
sortDependencies mods = fmap reverse (topological [] [] mods)
  where
    findModule name =
      maybe
        (Left (UnknownModule name))
        pure
        (find ((== name) . modName) mods)

    topological exploring explored [] = pure explored
    topological exploring explored (mod@(name, children, _) : mods)
      | name `elem` exploring = Left (CircularImports exploring)
      | name `elem` fmap modName explored = topological exploring explored mods
      | otherwise = do
        children' <- mapM findModule children
        explored' <- topological (name : exploring) explored children'
        topological exploring (mod : explored') mods

checkModules :: [Module] -> Either Error ()
checkModules mods = do
  runStateT
    (S.lift (sortDependencies mods) >>= mapM_ checkModule)
    (mempty, Signature mempty mempty mempty, 0)

  pure ()

checkModule :: Module -> StateT (Map Name NameSpace, Signature, Int) (Either Error) ()
checkModule (name, imports, decls) = do
  (names, sig, nextb) <- get

  let 
      st =
        DeclState
          { moduleName = name,
            nextBlock = nextb,
            importedNames = L.foldl (\acc imp -> mergeNameSpace acc (names ! imp)) mempty imports,
            internalNames = mempty,
            Declaration.signature = sig
          }

  (_, st') <- S.lift (runStateT (S.lift (groupDecls decls) >>= checkBlocks) st)

  put
    ( M.insert name (internalNames st') names,
      signature st',
      nextBlock st'
    )
