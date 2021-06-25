module Equations where

import Lexer (Loc)
import Parser
import Core
import Error
import Elaborator
import Data.Map as M
import Data.List as L
import Data.Maybe
import Data.Function
import Control.Monad
import Debug.Trace
import Prettyprint
import Reduction

-- todo : add variables bound in the type to the constraints, for computing clearer motives
data Problem = Problem {
  problemConstraints :: [(Pattern,Mult,Term)],
  problemPatterns :: [Pattern],
  problemRhs :: Expr}

mkProblem (pats,rhs) = Problem [] pats rhs

mkCtx :: [(Pattern,Mult,Term)] -> Context
mkCtx = fmap f where
  f (PApp _ _ head [], m, ty) = Hyp head ty Nothing
  f (_,m,ty) = Hyp "" ty Nothing

showPattern (PAbsurd _) = "()"
showPattern PIgnore = "_"
showPattern (PApp _ _ hd []) = hd
showPattern (PApp _ _ hd args) = "(" ++ hd ++ " " ++ unwords (fmap showPattern args) ++ ")"

showProblem (Problem constrs pats rhs) = 
  unwords (fmap (\(pat,m,ty) -> showPattern pat) (reverse constrs)) ++ " | " ++
  unwords (fmap showPattern pats)

{-

number 1 also prompt the question on how to deal with forcing, unification and indices
- due to forcing, variables deeper in the context may also need type updates
- for free variable indices, a similar mechanism to simple pattern matching can be used
- unifiable indexes will require help from equalities
- alternatively, we can leave the updating of contexts strictly to equalities.
  This might be a simpler solution for indexed types, and it might improve naive compilation
  of caseTerms, but the caseTerms will be larger and more confusing.
-}

-- check multiplicities
compileEquations :: ElabState -> Context -> [Problem] -> Term -> Either Error Term
compileEquations  _ _ [] _ = error "non-covering split should have been detected earlier"
compileEquations st ctx (probs @ (problem : _)) returnType =
  --trace (unlines (fmap showProblem probs) ++ ": " ++ showTerm ctx' returnType ++ "\n") $
  L.foldl checkSplittable tryIntro (zip [0..] constrs) where
    sig = snd st
    constrs = problemConstraints problem
    ctx' = mkCtx constrs ++ ctx
    
    checkSplittable :: Either Error Term -> (Int,(Pattern,Mult,Term)) -> Either Error Term
    checkSplittable noSplit (k, (pat, mult, ty)) = -- trace ("checkSplittable: " ++ show k) $
     case pat of
      PIgnore -> noSplit
      PAbsurd loc -> checkEmpty k mult ty loc
      PApp loc _ hd args -> checkCtorPattern k mult loc hd args ty noSplit
    
    checkEmpty :: Int -> Mult -> Term -> Loc -> Either Error Term
    checkEmpty k mult ty loc =
      case unrollApp (whnf sig ctx' ty) of
      --(Pi _ _ (Type _) (Var 0),_) -> Case One k [] Nothing
      -- abstract over linear arguments
      -- ensure correct eliminee usage
        (Top _ (Ind blockno defno _),_) ->
          if Prelude.null (snd ((sigData sig ! blockno) !! defno))
          then let
            motive = Lam Many "" ty (Core.lift 1 returnType)
            in pure (Case mult (Var k False) motive [])
          else Left (RefuteNonEmpty ctx' loc ty)
        _ -> Left (RefuteNonEmpty ctx' loc ty)
    
    checkCtorPattern :: Int -> Mult -> Loc -> String -> [Pattern] -> Term -> Either Error Term -> Either Error Term
    checkCtorPattern k mult loc hd args ty noSplit =
      case unrollApp (whnf sig ctx' ty) of
        (Top _ (Ind blockno datano _), data_args) -> let
          ctors = snd ((sigData sig ! blockno) !! datano)
          in case L.lookup hd ctors of
            Nothing ->
              if Prelude.null args
              then noSplit
              else Left (ConstructorMismatch loc ('#' : hd) ctx' ty)
            Just _ -> splitAt k mult loc blockno datano ctors data_args
        _ ->
          if Prelude.null args
          then noSplit
          else Left (SplitNonData loc)
    
    splitAt :: Int -> Mult -> Loc -> Int -> Int -> [(String,Term)] -> [Term] -> Either Error Term
    splitAt k mult loc blockno defno ctors args = do
      let
        (ctorNames,ctorTypes) = unzip ctors
        ctorTypes' = fmap (instantiateCtor args) ctorTypes
        tags = zip ctorNames (zip (fmap countDomains ctorTypes') [0..])
      probs2 <- mapM (matchProblem k tags) probs
      
      let
        brs =
          fmap (\xs -> (fst (head xs), fmap snd xs)) $
          groupBy ((==) `on` fst) $
          sortOn fst probs2
        brs2 = fmap (\(tag,prob) -> (tag, ctorNames !! tag, ctorTypes' !! tag, prob)) brs
        checkCoverage tag =
          maybe (Left (NonCoveringSplit loc (ctorNames !! tag))) (const (pure ())) (L.lookup tag brs)
      
      mapM_ checkCoverage [0 .. length ctors - 1]
      
      let
        motive = Core.lift (k + 1) (computeMotive k constrs returnType)
        
      branches <- mapM (computeBranch k mult args motive blockno defno) brs2
        
      let
        cargs = reverse (fmap (flip Var False) [0 .. k - 1])
        cased = Case mult (Var k False) motive branches
      pure (mkApp cased cargs)
      
    computeBranch :: Int -> Mult -> [Term] -> Term -> Int -> Int -> (Int,String,Term,[Problem]) -> Either Error Term
    computeBranch k mult args motive blockno datano (tag, ctorName, ctorType, problems) =
      compileEquations st ctx newProblems newType where
        newProblems = fmap (pushConstrs k) problems
        
        pushConstrs k (Problem constrs pats rhs) = Problem constrs' pats' rhs
          where
            (subsequent, (PApp _ _ _ args, m, ty) : previous) = L.splitAt k constrs
            pats' = args ++ L.foldl (\acc (pat,_,_) -> pat : acc) pats subsequent
            constrs' = (fmap (\(_,m,ty) -> (PIgnore,m,ty)) subsequent) ++ (PIgnore,m,ty) : previous 
        
        newType = computeBranchType mult (length args) motive (ctorName,blockno,datano,tag,ctorType)
      
    computeMotive :: Int -> [(Pattern,Mult,Term)] -> Term -> Term
    computeMotive 0 ((_,_,ty):cs) = Lam Many "" ty
    computeMotive n ((_,_,ty):cs) = Pi Many "" ty . computeMotive (n - 1) cs
    computeMotive _ [] = error "computeMotive"
    
    matchProblem :: Int -> [(String,(Int,Int))] -> Problem -> Either Error (Int,Problem)
    matchProblem k ctors problem @ (Problem constrs pats rhs) =
      case constrs !! k of
        (PIgnore,_,_) -> Left (Msg "non-strict split")
        (PAbsurd loc,_,_) -> Left (RefuteNonEmpty ctx' loc (Type 0))
        (PApp loc nloc hd args,_,_) ->
          case L.lookup hd ctors of
            Nothing -> Left (ConstructorMismatch loc ('$' : hd) ctx' (Core.lift (k + 1) (hypType (ctx' !! k)))) 
            Just (argc,tag) ->
              if argc == length args
              then pure (tag, problem)
              else Left (ArityMismatch loc (length args) argc)

    tryIntro
      | all (Prelude.null . problemPatterns) probs = do
        (body,uses) <- check st ctx' (problemRhs problem) returnType
        -- do something with uses
        pure body
      | all (not . Prelude.null . problemPatterns) probs =
        case whnf sig ctx' returnType of
          Pi mult name src dst -> let
            
            introProblem (Problem constrs (pat:pats) rhs) = 
              Problem ((pat,mult,src):constrs) pats rhs
            
            probs2 = fmap introProblem probs
            
            in Lam mult name src <$> compileEquations st ctx probs2 dst
          _ -> Left IntroNonFunction
      | otherwise = Left UnevenPatterns





