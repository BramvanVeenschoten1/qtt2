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
  for eliminators, the argument order is induction variable, arguments, equality proof
  for case-expressions, the induction variable and accessibility proof can be after the main arguments
  after compiling the dependent pattern matching, the subterms relation can be derived from the equality proof,
  which now has the arguments refined. A recursive call will construct the new induction term based on the arguments
  passed and the fact that the equality proof must be refl. the smaller than relation can be derived from the previous
  equality proof.
  
  The subterm relation for trees other that lists or natural numbers can probably best derived by computing the size
  of said tree. This method subsumes proper subexpressions and appears to be simpler. To derive the base intro rules,
  we'll need commutativity of plus, or a leq-relation on its operands. To define step introtules, we'll need something
  similar.
-}

data Subdata
  = Seed Int -- an argument to the function and its number
  | Sub Int -- a term smaller than an argument and the number of said argument
  | Other -- a variable that is neither recursive nor smaller
  deriving Show

type RecCall = (Int,[Maybe Int]) -- callee defno, [(caller argno, callee argno)]
{-
  returns a list of recursive calls, with for each callee argument whether it is a subdatum and
  which caller argument it is derived from if so
-}
getRecursiveCalls :: Signature -> Context -> Int -> [Int] -> Term -> [RecCall]
getRecursiveCalls sig ctx blockSize arities t =
  getRecCalls 0 ctx [] t (fmap Seed [0..]) where

  getRecCalls :: Int -> Context -> [Subdata] -> Term -> [Subdata] -> [RecCall]
  getRecCalls k ctx env t stack = let
    (hd,args) = unrollApp t
    smallerArgs = fmap (isSmaller ctx env) args
    argRecCalls = concatMap (\t -> getRecCalls k ctx env t (repeat Other)) args
    in case hd of
      Var n _ ->
        if n >= k
        then (k + blockSize - n - 1, smallerArgs) : argRecCalls
        else argRecCalls
      Lam m name src dst ->
        getRecCalls
          (k + 1)
          (Hyp name src Nothing : ctx)
          (head stack : env)
          dst
          (tail stack) ++ argRecCalls
      Pi m name src dst ->
        getRecCalls
          (k + 1)
          (Hyp name src Nothing : ctx)
          (Other : env)
          dst
          (repeat Other) ++ argRecCalls
      Let m name ta a b ->
        (if occurs (blockSize + k) k a
         then getRecCalls k ctx env (psubst [a] b) stack
         else
          getRecCalls
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
        
        elimCall = getRecCalls k ctx env eliminee (repeat Other)
        
        branchCalls = concat (zipWith
          (\arity branch ->
            getRecCalls k ctx env branch (replicate arity elimSub ++ stack))
          ctor_arities
          branches)
        
        in elimCall ++ branchCalls ++ argRecCalls
      Top _ (Def blockno height) ->
        if any (occursUnderapplied) args
        then getRecCalls k ctx env (whnf sig ctx t) stack
        else argRecCalls
      Top _ (Fix blockno defno recparamno height uniparamno) ->
        let (left_args,right_args) = L.splitAt uniparamno args
        in if any (occursUnderapplied) args
          then let
            fixs = sigFixs sig ! blockno
            -- replace recursive calls with dummy, then apply uni-args
            in undefined
          else argRecCalls
        -- if there are underapplied occurrences in the uniform arguments, do the hoohaa, otherwise, nothing
      _ -> argRecCalls
  
  -- find if a term is smaller and if so, return argument number
  -- case branches need to have lambda's stripped
  isSmaller :: Context -> [Subdata] -> Term -> Maybe Int
  isSmaller ctx subs t = case unrollApp t of
    (Var n _, _) -> case subs !! n of
      Sub m -> Just m
      _ -> Nothing
    _ -> Nothing
  
  occursUnderapplied = const False

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
