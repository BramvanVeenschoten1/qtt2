module Equations where

import Lexer
import Parser
import Core
import Error
import Elaborator
import Data.Map as M
import Data.List as L
import Data.Maybe
import Data.Function
import Control.Monad
--import Debug.Trace
import Prettyprint
import Reduction

type Result = Either Error (Term,Uses)

data Problem = Problem {
  problemConstraints :: [(Pattern,String,Mult,Term)],
  problemPatterns :: [Pattern],
  problemRhs :: Expr}

mkProblem (pats,rhs) = Problem [] pats rhs

mkCtx :: [(Pattern,String,Mult,Term)] -> Context
mkCtx = fmap f where
  f (PApp _ _ head [], _, m, ty) = Hyp head ty Nothing
  f (_,s,m,ty) = Hyp s ty Nothing

showPattern (PAbsurd _) = "()"
showPattern (PIgnore _) = "_"
showPattern (PApp _ _ hd []) = hd
showPattern (PApp _ _ hd args) = "(" ++ hd ++ " " ++ unwords (fmap showPattern args) ++ ")"

showProblem (Problem constrs pats rhs) = 
  unwords (fmap (\(pat,s,m,ty) -> showPattern pat) (reverse constrs)) ++ " | " ++
  unwords (fmap showPattern pats)

{-
considering the distinct advantages of primitive case trees, also consider the challenges in
making them work. In particular, it is hard to equip them with semantics for
instantiating variables, deleting variables from contexts, reordering contexts, etcetera.
-}

-- check multiplicities
compileEquations :: ElabState -> Context -> [Problem] -> Term -> Result
compileEquations  _ _ [] _ = error "non-covering split should have been detected earlier"
compileEquations st ctx (probs @ (problem : _)) returnType =
  --trace (unlines (fmap showProblem probs) ++ ": " ++ showTerm ctx' returnType ++ "\n") $
  L.foldl checkSplittable tryIntro (zip [0..] constrs) where
    sig = snd st
    constrs = problemConstraints problem
    ctx' = mkCtx constrs ++ ctx
    
    checkSplittable :: Result -> (Int,(Pattern,String,Mult,Term)) -> Result
    checkSplittable noSplit (k, (pat, s, mult, ty)) = -- trace ("checkSplittable: " ++ show k) $
     case pat of
      PIgnore _ -> noSplit
      PAbsurd loc -> checkEmpty k mult ty loc
      PApp loc _ hd args -> checkCtorPattern k mult loc hd args ty noSplit
    
    checkEmpty :: Int -> Mult -> Term -> Loc -> Result
    checkEmpty k mult ty loc =
      case unrollApp (whnf sig ctx' ty) of
      --(Pi _ _ (Type _) (Var 0),_) -> Case One k [] Nothing
      -- abstract over linear arguments
      -- ensure correct eliminee usage
        (Top _ (Ind blockno defno _),_) ->
          if Prelude.null (snd ((sigData sig ! blockno) !! defno))
          then let
            motive = Lam Many "" ty (Core.lift 1 returnType)
            in pure (Case mult (Var k False) motive [], noUses)
          else Left (RefuteNonEmpty ctx' loc ty)
        _ -> Left (RefuteNonEmpty ctx' loc ty)
    
    checkCtorPattern :: Int -> Mult -> Loc -> String -> [Pattern] -> Term -> Result -> Result
    checkCtorPattern k mult loc hd args ty noSplit =
      case unrollApp (whnf sig ctx' ty) of
        (Top _ (Ind blockno datano _), data_args) -> let
          ctors = snd (sigData sig ! blockno !! datano)
          in case L.lookup hd ctors of
            Nothing ->
              if Prelude.null args
              then noSplit
              else Left (ConstructorMismatch loc hd ctx' ty)
            Just _ -> splitAt k mult loc blockno datano ctors data_args
        _ ->
          if Prelude.null args
          then noSplit
          else Left (SplitNonData loc)
    
    splitAt :: Int -> Mult -> Loc -> Int -> Int -> [(String,Term)] -> [Term] -> Result
    splitAt k mult loc blockno defno ctors args = do
      let (ctorNames,ctorTypes) = unzip ctors
          argc = length args
          matchInfo = zipWith3 (\name tag ty -> (name,(countDomains ty - argc,tag))) ctorNames [0..] ctorTypes
      probs2 <- mapM (matchProblem k matchInfo) probs
      let brs =
            fmap (\xs -> (fst (head xs), fmap snd xs)) $
            groupBy ((==) `on` fst) $
            sortOn fst probs2
          checkCovered tag = maybe
            (Left (NonCoveringSplit loc (ctorNames !! tag)))
            (const (pure ()))
            (L.lookup tag brs)
      mapM_ checkCovered [0 .. length ctors - 1]
      let motive = Core.lift (k + 1) (computeMotive k constrs returnType)
      branches <- zipWithM (computeBranch k mult args motive blockno defno) brs ctors
      let (branches', bUses) = unzip branches
          elimUses = replicate k Nouse ++ [Oneuse One emptyLoc] ++ repeat Nouse
          branchUses' = branchUses emptyLoc bUses
          cargs = reverse (fmap (flip Var False) [0 .. k - 1])
          cased = Case mult (Var k False) motive branches'
      pure (mkApp cased cargs, plusUses elimUses branchUses')
      
    computeBranch :: Int -> Mult -> [Term] -> Term -> Int -> Int -> (Int,[Problem]) -> (String,Term) -> Result
    computeBranch k mult args motive blockno datano (tag,problems) (ctorName,ctorType) =
      --trace ("split " ++ show k ++ ", branch " ++ show tag ++ ":") $
      --trace (unlines (fmap showProblem newProblems)) $
      --trace ("new type:") $
      --trace (showTerm ctx newType) $
      --trace ""
      compileEquations st ctx newProblems newType where
        newProblems = fmap (pushConstrs k) problems
        
        pushConstrs k (Problem constrs pats rhs) = Problem constrs' pats' rhs
          where
            (subsequent, (PApp loc _ _ args, s, m, ty) : previous) = L.splitAt k constrs
            pats' = args ++ L.foldl (\acc (pat,_,_,_) -> pat : acc) pats subsequent
            constrs' = (fmap (\(_,s,m,ty) -> (PIgnore loc,s,m,ty)) subsequent) ++ (PIgnore loc,s,m,ty) : previous 
        
        -- args may need to be lifted over the thingies
        newType = computeBranchType mult blockno datano
          (fmap (Core.lift (k + 1)) args) motive tag (ctorName,ctorType)
      
    computeMotive :: Int -> [(Pattern,String,Mult,Term)] -> Term -> Term
    computeMotive 0 ((_,s,_,ty):cs) = Lam Many s ty
    computeMotive n ((_,s,m,ty):cs) = computeMotive (n - 1) cs . Pi m s ty
    computeMotive _ [] = error "computeMotive"
    
    matchProblem :: Int -> [(String,(Int,Int))] -> Problem -> Either Error (Int,Problem)
    matchProblem k ctors problem @ (Problem constrs pats rhs) =
      case constrs !! k of
        (PIgnore _,_,_,_) -> Left (Msg "non-strict split")
        (PAbsurd loc,_,_,_) -> Left (RefuteNonEmpty ctx' loc (Type 0))
        (PApp loc nloc hd args,_,_,_) ->
          case L.lookup hd ctors of
            Nothing -> Left (ConstructorMismatch loc hd ctx' (Core.lift (k + 1) (hypType (ctx' !! k)))) 
            Just (argc,tag) ->
              if argc == length args
              then pure (tag, problem)
              else Left (ArityMismatch loc (length args) argc)

    tryIntro :: Result
    tryIntro
      | all (Prelude.null . problemPatterns) probs = do
        check st ctx' (problemRhs problem) returnType
      | all (not . Prelude.null . problemPatterns) probs =
        case whnf sig ctx' returnType of
          Pi mult name src dst -> let
            
            name'
              | Prelude.null name = "%x" ++ show (length ctx')
              | otherwise = '%' : name
            
            introProblem (Problem constrs (pat:pats) rhs) = 
              Problem ((pat,name',mult,src):constrs) pats rhs
            
            probs2 = fmap introProblem probs
            
            in do
              (term,uses) <- compileEquations st ctx probs2 dst
              let (use : uses') = uses
              checkArgMult emptyLoc mult use
              pure (Lam mult name' src term, uses')
          _ -> Left IntroNonFunction
      | otherwise = Left UnevenPatterns





