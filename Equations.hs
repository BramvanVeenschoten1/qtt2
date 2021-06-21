module Equations where

import Lexer (Loc)
import Parser
import Core
import Elaborator
import Data.Map as M
import Data.List as L
import Data.Maybe
import Data.Function
import Control.Monad

-- todo : add variables bound in the type to the constraints, for computing clearer motives
--        also multiplicities
data Problem = Problem {
  problemConstraints :: [(Pattern,Term)],
  problemPatterns :: [Pattern],
  problemRhs :: Expr}

mkProblem (pats,rhs) = Problem [] pats rhs

mkCtx :: [(Pattern,Term)] -> Context
mkCtx = fmap f where
  f (PApp _ _ head [], ty) = Hyp head ty Nothing
  f (_,ty) = Hyp "" ty Nothing

{-

number 1 also prompt the question on how to deal with forcing, unification and indices
- due to forcing, variables deeper in the context may also need type updates
- for free variable indices, a similar mechanism to simple pattern matching can be used
- unifiable indexes will require help from equalities
- alternatively, we can leave the updating of contexts strictly to equalities.
  This might be a simpler solution for indexed types, and it might improve naive compilation
  of caseTerms, but the caseTerms will be larger and more confusing.
-}

compileEquations :: ElabState -> [Problem] -> Term -> Either Error Term
compileEquations  _ [] _ = error "non-covering split should have been detected earlier"
compileEquations st (probs @ (problem : _)) returnType =
  L.foldl checkSplittable tryIntro (zip [0..] constrs) where
    sig = signature st
    constrs = problemConstraints problem
    ctx = mkCtx constrs
    
    checkSplittable :: Either Error Term -> (Int,(Pattern,Term)) -> Either Error Term
    checkSplittable noSplit (k, (pat, ty)) = case pat of
      PIgnore -> noSplit
      PAbsurd loc -> checkEmpty k ty loc
      PApp loc _ head args -> checkCtorPattern k loc head args ty noSplit
    
    checkEmpty :: Int -> Term -> Loc -> Either Error Term
    checkEmpty k ty loc =
      case unrollApp (whnf sig ctx ty) of
      --(Pi _ _ (Type _) (Var 0),_) -> Case One k [] Nothing
      -- abstract over linear arguments
      -- ensure correct eliminee usage
        (Top (Ind blockno defno _),_) ->
          if Prelude.null (indCtors ((sigData sig ! blockno) !! defno))
          then let
            motive = Lam Many "" ty (Core.lift 1 returnType)
            in pure (Case Zero (Var k False) motive [] Nothing)
          else Left (RefuteNonEmpty loc)
    
    checkCtorPattern :: Int -> Loc -> String -> [Pattern] -> Term -> Either Error Term -> Either Error Term
    checkCtorPattern k loc head args ty noSplit =
      case unrollApp (whnf sig ctx ty) of
        (Top (Ind blockno datano _), args) -> let
          ctors = indCtors ((sigData sig ! blockno) !! datano)
          in splitAt k loc blockno datano ctors args
        _ ->
          if Prelude.null args
          then noSplit
          else Left (SplitNonData loc)
    
    splitAt :: Int -> Loc -> Int -> Int -> [(String,Term)] -> [Term] -> Either Error Term
    splitAt k loc blockno defno ctors args = do
      let
        (ctorNames,ctorTypes) = unzip ctors
        ctorTypes' = fmap (instantiateCtor args) ctorTypes
        tags = zip ctorNames (zip (fmap countDomains ctorTypes') [0..])
      probs2 <- mapM (matchProblem k tags) probs
      let
        (brs,dfs) =
          L.partition (isJust . fst) $
          fmap (\xs -> (fst (head xs), fmap snd xs)) $
          groupBy ((==) `on` fst) $
          sortOn fst probs2
        brs2 = fmap (\(tag,prob) -> (fromJust tag, prob)) brs
        brs3 = fmap (\(tag,prob) -> (tag, ctorTypes !! tag, prob)) brs2
        dfs2 = snd (head dfs)
        checkCoverage tag =
          maybe (Left (NonCoveringSplit loc (ctorNames !! tag))) (const (pure ())) (L.lookup tag brs2)
      when (Prelude.null dfs2) (mapM_ checkCoverage [0 .. length ctors - 1])
      let
        motive = Core.lift (k + 1) (computeMotive k constrs returnType)
      branches <- mapM (computeBranch k args motive blockno defno) brs3
      defbr <- (if Prelude.null dfs2 
        then pure Nothing
        else Just <$> computeDefaultBranch k motive dfs2)
      let
        cargs = reverse (fmap (flip Var False) [0 .. k - 1])
        cased = Case Many (Var k False) motive branches defbr
      pure (mkApp cased cargs)
      
    computeBranch :: Int -> [Term] -> Term -> Int -> Int -> (Int,Term,[Problem]) -> Either Error (Int,Term)
    computeBranch k args motive blockno datano (tag, ctorType, problems) =
      (,) tag <$> compileEquations st newProblems newType where
        newProblems = fmap (pushConstrs k) problems
        
        pushConstrs 0 (Problem ((PApp _ _ _ args, _) : constrs) pats rhs) =
          Problem constrs (args ++ pats) rhs
        pushConstrs k (Problem ((pat,_): constrs) pats rhs) =
          pushConstrs (k - 1) (Problem constrs (pat : pats) rhs)
        
        newType = computeBranchType args motive (blockno,datano,tag,ctorType)
    
    computeDefaultBranch :: Int -> Term -> [Problem] -> Either Error Term
    computeDefaultBranch k motive problems =
      compileEquations st newProblems newType where
        newProblems = fmap (pushConstrs k) problems
        
        pushConstrs 0 (Problem ((pat,_): constrs) pats rhs) =
          Problem constrs (pat:pats) rhs
        pushConstrs k (Problem ((pat,_): constrs) pats rhs) =
          pushConstrs (k - 1) (Problem constrs (pat : pats) rhs)

        newType = let Lam mult name src dst = motive in Pi mult name src dst
      
    computeMotive :: Int -> [(Pattern,Term)] -> Term -> Term
    computeMotive 0 (c:cs) = Lam Many "" (snd c)
    computeMotive n (c:cs) = Pi Many "" (snd c) . computeMotive (n - 1) cs
    computeMotive _ [] = error "computeMotive"
    
    matchProblem :: Int -> [(String,(Int,Int))] -> Problem -> Either Error (Maybe Int,Problem)
    matchProblem k ctors problem @ (Problem constrs pats rhs) =
      case fst (constrs !! k) of
        PIgnore -> pure (Nothing, problem)
        PAbsurd loc -> Left (RefuteNonEmpty loc)
        PApp loc nloc head args ->
          case L.lookup head ctors of
            Nothing ->
              if Prelude.null args
              then pure (Nothing,problem)
              else Left (ConstructorMismatch loc head ctx (Core.lift (k + 1) (hypType (ctx !! k)))) 
            Just (argc,tag) ->
              if argc == length args
              then pure (Just tag, problem)
              else Left (ArityMismatch loc (length args) argc)

    tryIntro
      | all (Prelude.null . problemPatterns) probs = do
        (body,uses) <- check st ctx (problemRhs problem) returnType
        -- do something with uses
        pure body
      | all (not . Prelude.null . problemPatterns) probs =
        case whnf sig ctx returnType of
          Pi mult name src dst -> let
            
            introProblem (Problem constrs (pat:pats) rhs) = 
              Problem ((pat,src):constrs) pats rhs
            
            probs2 = fmap introProblem probs
            
            in Lam mult name src <$> compileEquations st probs2 dst
          _ -> Left IntroNonFunction
      | otherwise = Left UnevenPatterns





