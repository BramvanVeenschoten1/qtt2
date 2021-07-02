module Termination where

import Data.Set as S
import Data.Map as M
import Data.List as L
import Data.Maybe
import Control.Monad
import Control.Applicative

--import Debug.Trace
import Core
import Reduction
import Prettyprint

-- idea: allow user to provide decreasing path explicitly?

{-
a distinct advantage of agda/idris style case-trees is that termination is guaranteed,
even if it does not depend on a single argument, due the matching evaluating the full tree.
to get similar behaviour in these fixpoints, we need a set of recargs and their lexical relation

new equation compiler will require a new strategy, as match branches are no longer required
to fully abstract over the constructor arguments.
additionally, we would like to handle liftover arguments

- variables referring to recursive calls can be tracked by depth, as recursive functions are
  always in the bottom of the context
- it might be useful to have a notion of a subterm stack as well as a subterm context,
  to accommodate liftovers and the sort. it would work like so:
  
  1. at the beginning of the function, seeds are pushed to the stack.
  2. when introducing a lambda, if there is a seed on the stack, pop it and push it to the env
  3. in a case, if the eliminee is a seed, push subs on the stack for the constructor arguments
  4. Pi appears to just introduce an irrelevant argument in the context
  5. if a let contains a recursive call, reduce it to avoid shenanigans. Otherwise, proceed
  6. Applications are interesting.
    - first of all, the substack does not apply to the application arguments.
    - if the application head is a lambda (it shouldn't be), push the seed values of the arguments
      to the stack before proceeding. remember to collect rec_calls from the argumetns
    - if the app head is a case, ditto
    - if the app head is a var, one of 2 scenarios apply:
      1. it is a recursive function, make a reccall.
      2. it is a variable, acquire reccalls from arguments.
    - it is a definition, acquire reccalls from arguments.
      if an argument is an underapplied function, reduce and check again
    - it is a fixpoint, acquire reccalls from arguments.
      if an argument is an underapplied function, do the thing and the hoohaa

useful things to have:
- maximum arity of the function, to check underappliedness
- an occurrence check for the recursive functions
-}

data Subdata
  = Recursive Int -- a recursive occurrence and its number
  | Seed Int -- an argument to the function and its number
  | Sub Int -- a term smaller than an argument and the number of said argument
  | Other -- a variable that is neither recursive nor smaller
  deriving Show

-- information on which debruijn indices are possibly recursive arguments
-- with regular inference, all top-level lambda arguments are possibly recursive
-- with nested inference, the recursive argument is already known
data RecArg
  = Past
  | Unknown Int
  | Known Int Int Int
  deriving Show

argSucc :: RecArg -> RecArg
argSucc Past = Past
argSucc (Unknown x) = Unknown (x + 1)
argSucc (Known x recpno unipno) = Known (x + 1) recpno unipno

isRecArg :: RecArg -> Subdata
isRecArg Past = Other
isRecArg (Unknown x) = Seed x
isRecArg (Known x recpno unipno)
  | x == recpno - unipno = Seed recpno
  | otherwise = Other

type RecCall = (Int,[Maybe Int]) -- callee defno, [(caller argno, callee argno)]
{-
  returns a list of recursive calls, with for each callee argument whether it is a subdatum and
  which caller argument it is derived from if so
-}
getRecursiveCalls :: Signature -> Context -> Term -> [RecCall]
getRecursiveCalls sig ctx = getRecCalls ctx (fmap Recursive [0 .. blockSize - 1]) (Unknown 0) where
  blockSize = length ctx

  isUnderApplied = undefined
  {-
  getRecCalls2 :: Int -> Context -> [Subdata] -> Term -> [Subdata] -> [RecCall]
  getRecCalls2 k ctx env t stack = let
    (hd,args) = unrollApp t
    smallerArgs = fmap (isSmaller ctx env t) args
    argRecCalls = fmap (getRecCalls2 ctx env t (repeat Other)) args
    in case hd of
      Var n _ -> case env !! n of
        Recursive m -> (m,smallerArgs) : argRecCalls
        _ -> argRecCalls
      Lam m name src dst ->
        getRecCalls2
          (k + 1)
          (Hyp name src Nothing : ctx)
          (head stack : env)
          dst
          (tail stack) ++ argRecCalls
      Pi m namre src dst ->
        getRecCalls2
          (k + 1)
          (Hyp name src Nothing : ctx)
          (Other : env)
          dst
          (repeat Other) ++ argRecCalls
      Let m name ta a b ->
        (if occurs (blocksize + k) k a
         then getRecCalls2 k ctx env (psubst [a] b) stack
         else
          getRecCalls2
            (k + 1)
            (Hyp name ta (Just a) : ctx)
            (Other : env)
            b
            stack) ++ argRecCalls
      Case mult eliminee motive branches -> let
        
        (obj_id,defno,data_argc) =  case unrollApp (whnf sig ctx (typeOf sig ctx eliminee)) of
          (Top _ (Ind obj_id defno _), args) -> (obj_id,defno,length args)
          (x,_) -> error (showTerm ctx x)
        
        (_,ctors) = sigData sig ! obj_id !! defno
        
        ctor_arities = fmap (\(_,ty) -> countDomains ty - data_argc) ctors
        
        elimSub = case unrollApp eliminee of
          (Var n _, _) -> case env !! n of
            Seed m -> Sub m
            Sub m -> Sub m
            _ -> Other
          _ -> Other
        
        elimCall = getRecCalls2 k ctx env eliminee (repeat Other)
        
        branchCalls = concat (zipWith
          (\arity branch ->
            getRecCalls2 k ctx env branch (replicate arity elimSub ++ stack))
          ctor_arities
          branches)
        
        in elimCall : (branchCalls ++ argRecCalls)
      Top _ (Def blockno height) -> undefined
      Top _ (Fix blockno defno recparamno height uniparamno) -> undefined
      _ -> argRecCalls
  -}    
  
  -- check whether some match branches are all subterms of some seed
  isCaseSmaller :: [Maybe Int] -> Maybe Int
  isCaseSmaller (Just n : xs)
    | all ((==) (Just n)) xs = Just n
  isCaseSmaller _ = Nothing
  
  -- find if a term is smaller and if so, return argument number
  -- case branches need to have lambda's stripped
  isSmaller :: Context -> [Subdata] -> Term -> Maybe Int
  isSmaller ctx subs t = case whnf sig ctx t of
    Var n _ -> case subs !! n of
      Sub m -> Just m
      _ -> Nothing
    App f x -> isSmaller ctx subs f
    Case _ _ _ branches -> isCaseSmaller (fmap (isSmaller ctx subs) branches)
    _ -> Nothing
  
  -- traverse the body of a fixpoint function and gather recursive path information
  getRecCalls :: Context -> [Subdata] -> RecArg -> Term -> [RecCall]
  getRecCalls ctx subs argc t = let
    (fun,args) = unrollApp (whnf sig ctx t)
    arg_calls = concatMap (getRecCalls ctx subs Past) args
    small_args = fmap (isSmaller ctx subs) args
    in {-
     trace "hmm:"
     trace (showContext ctx) $
     trace (showTerm ctx t) $
     trace (showTerm ctx (whnf sig ctx t)) $ 
     trace "" $ -- -}
     (++) arg_calls $ case fun of
      Var n _ -> case subs !! n of
        Recursive defno -> [(defno, small_args)]
        _ -> arg_calls
      Lam _ name ta b ->
        getRecCalls
          (  Hyp name ta Nothing  : ctx)
          (isRecArg argc : subs)
          (argSucc argc) b
      Let _ name ta a b ->
        getRecCalls
          (Hyp name ta (Just a) : ctx)
          (isRecArg argc : subs)
          (argSucc argc) b
      Pi _ name ta tb ->
        getRecCalls
          (Hyp name ta Nothing  : ctx)
          (Other : subs)
          Past tb
      Case mult eliminee motive branches -> let
        
        (obj_id,defno,data_argc) =  case unrollApp (whnf sig ctx (typeOf sig ctx eliminee)) of
          (Top _ (Ind obj_id defno _), args) -> (obj_id,defno,length args)
          (x,_) -> error (showTerm ctx x)
        
        block = fromJust (M.lookup obj_id (sigData sig))
        
        def = block !! defno
        
        (ctor_names,ctor_types) = unzip (snd def)
        
        ctor_arities = fmap (\(_,ty) -> countDomains ty - data_argc) (snd def)
        
        sub = (case unrollApp (whnf sig ctx eliminee) of
          (Var n _, _) -> case subs !! n of
            Seed m -> Sub m
            Sub m -> Sub m
            Other -> Other
          _ -> Other)
        
        unrollArgs :: Context -> [Subdata] -> Int -> Term -> [RecCall]
        unrollArgs ctx subs 0 branch = getRecCalls ctx subs argc branch
        unrollArgs ctx subs m (Lam _ name ta b) =
          unrollArgs (Hyp name ta Nothing : ctx) (sub : subs) (m - 1) b
            
        regular_calls = -- trace (unwords ctor_names) $
          concat (zipWith (unrollArgs ctx subs) ctor_arities branches)
        
        in regular_calls
      x -> []
      {-
      Top _ (Fix obj_id defno recparamno height uniparamno) -> let
        (left_args,right_args) = L.splitAt uniparamno args
        left_calls = concatMap (getRecCalls ctx subs Past) left_args
        right_calls = concatMap (getRecCalls ctx subs Past) right_args
        
        fix_bodies = fmap fixBody (fromJust (M.lookup obj_id (globalFix sig)))
        
        dummy_bodies = fmap (substWithDummy obj_id) fix_bodies
        
        applied_bodies = fmap (\fun -> App fun left_args) dummy_bodies
        
        expand = L.concatMap (getRecCalls ctx subs (Known 0 recparamno uniparamno)) applied_bodies 
        
        traceExpand = trace (
          show (fmap (showTerm ctx) dummy_bodies) ++ "\n" ++
          show (fmap (showTerm ctx . whnf sig ctx) applied_bodies) ++ "\n" ++
          show expand ++ "\n") expand
        
        in if Prelude.null left_calls
          then right_calls
          else traceExpand ++ right_calls
          -}

{-
  Given the recursive calls, check the totality of a fixpoint by computing recursive parameters of the mutually recursive functions.
  a fixpoint is guarded if in each recursive call, the recursive parameter of the callee is smaller than the
  recursive parameter of the caller. What exactly constitutes a smaller argument is defined in getRecursiveCalls.

  Finding the parameters is done by lazily traversing all possible configurations of recursive parameters,
  then returning the first that is completely guarded, if it exists.
-}
findRecparams :: [[RecCall]] -> Maybe [Int]
findRecparams rec_calls = let
  defcount = length rec_calls
  {-
    compute the possibly recursive parameters for the current definition.
    The candidates are constrained by 3 factors:
    - previous definitions in the same fixpoint will have been assigned a recursive parameter,
      so only the argument that guards these calls is allowed
    - The nth parameter passed to the recursive call is only guarded if it is
      smaller than the nth parameter of the function itself
    - Other definitions are not yet constrained, but serve as heuristic.
      so for each argument, if a term smaller than it is passed to a later function,
      it becomes a candidate.
  -}  
  allowed_args :: Int -> [RecCall] -> [Int] -> [Int]
  allowed_args defno calls recparams = let
    
    inter :: RecCall -> [Int] -> [Int]
    inter (defno',args) acc = let
      allowed :: [Int]
      allowed
          -- in calls to self, caller and callee recparamno have to be the same
        | defno == defno' =  [x | (x,y) <- zip [0..] args, Just x == y]
        | otherwise = case nth defno' recparams of
          -- in calls to previously constrained functions, 
          -- only the caller argument that the callees' recursive argument is derived from is allowed
          Just n -> maybe [] (:[]) (join (nth n args))
          -- other calls are only limited to smaller arguments
          Nothing -> L.nub (catMaybes args)
          
      -- we use a special intersection that works with an infinite list as acc
      in [x | x <- allowed, elem x acc]

    in L.foldr inter [0..] calls
  
  -- check recursive calls to defno in all previous definitions
  checkCalls :: Int -> Int -> [Int] -> Maybe ()
  checkCalls callee callee_recparamno recparams = zipWithM_ (mapM_ . checkCall) recparams rec_calls where
    --checkCall :: Int -> [RecCall] -> Maybe ()
    checkCall caller_paramno (defno,args)
      -- only calls to defno need to be checked, the argument in the given callee_recparamno position must be
      -- derived from the recursive argument of the caller
      | callee == defno = case join (nth callee_recparamno args) of
        Just argno -> if caller_paramno == argno then pure () else Nothing
        Nothing -> Nothing
      | otherwise = pure ()
  
  -- given the recursive calls, find an assignment of recursive parameters to definitions such that
  -- the fixpoint is guarded
  solve :: Int -> [Int] -> Maybe [Int]
  solve defno recparams
    | defno >= defcount = pure recparams
    | otherwise = let
      -- with the given constraints, get the possibly recursive arguments
      allowed = allowed_args defno (rec_calls !! defno) recparams
      
      -- for a given recursive argument, check the guardedness of its calls in previous definitions,
      -- then continue with the other definitions
      pick :: Int -> Maybe [Int]
      pick x = checkCalls defno x recparams *> solve (defno + 1) (recparams ++ [x])
      
      -- try every possibly allowed argument if necessary
      in L.foldr (<|>) Nothing (fmap pick allowed)
  
  in solve 0 []
