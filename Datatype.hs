module Datatype where

import Data.Set
import Data.Map
import Data.List as L
import Data.Maybe
import Control.Monad
import Control.Applicative hiding (Const)

import qualified Core as C
import Core
import Elaborator
import Reduction
import Error
import Parser
import Lexer(Loc)
--import Prettyprint
import Debug.Trace

assert :: Bool -> Error -> Either Error Int
assert True _ = pure maxBound
assert False msg = Left msg

allOccurrencesPositive :: Signature -> Context -> Loc -> Int -> Int -> Int -> Int -> Int -> Term -> Either Error Int
allOccurrencesPositive sig ctx loc defcount defno paramno n nn t = f (whnf sig ctx t) where
  f (Pi _ name ta tb) =
    min <$> strictlyPositive sig ctx loc defcount n nn ta
        <*> allOccurrencesPositive sig (Hyp name ta Nothing : ctx)
              loc defcount defno paramno (n+1)(nn+1) tb
  f tb =
    case unrollApp tb of
      (Var m, args) ->
        if m == length ctx - defno - 1
        then do
          u <- checkHomogeneousCall loc (length ctx) defcount n nn args
          if u >= paramno
          then pure u
          else Left (IllFormedConstructor loc)
        else Left (IllFormedConstructor loc)
      _ -> Left (IllFormedConstructor loc)

strictlyPositive :: Signature -> Context -> Loc -> Int -> Int -> Int -> Term -> Either Error Int
strictlyPositive sig ctx loc defcount n nn t = f (whnf sig ctx t) where
  f :: Term -> Either Error Int
  f t | not (occurs n nn t) = pure maxBound
  f (Pi _ name ta tb) = do
    assert (not (occurs n nn ta)) (IllegalOccurrence loc)
  
    strictlyPositive sig (Hyp name ta Nothing : ctx) loc defcount (n+1) (nn+1) tb
  f t = case unrollApp t of
    (Top _ (Ind block _ uniparamno), args) -> do
      let
        (left_params,right_params) = L.splitAt uniparamno args
        ctors = concatMap snd (sigData sig ! block) 
        ctors' = fmap (instantiateCtor left_params . snd) ctors
      assert (not (any (occurs n nn) right_params)) (IllegalOccurrence loc)
      if any (occurs n nn) left_params
      then foldM (\acc ctor -> min acc <$> weaklyPositive sig ctx loc defcount n nn block ctor) maxBound ctors'
      else pure maxBound
    (Var m, args) ->
      if m >= n && m <= nn
      then checkHomogeneousCall loc (length ctx) defcount n nn args
      else assert (not (any (occurs n nn) args)) (IllegalOccurrence loc)
    (_,args) -> assert (not (any (occurs n nn) args)) (IllegalOccurrence loc)
{- 
   why does matita:
   - disallow nesting in mutual types?
   - disallow deeper levels of nesting?
   - add the inspected type to the context?
   => we'll ignore these
-}
weaklyPositive :: Signature -> Context -> Loc -> Int -> Int -> Int -> Int -> Term -> Either Error Int
weaklyPositive sig ctx loc defcount n nn block_no t = f ctx n nn (substDummy block_no t) where
  f :: Context -> Int -> Int -> Term -> Either Error Int
  f ctx n nn te = case unrollApp (whnf sig ctx te) of
    (Type 0, args) ->
      assert (not (any (occurs n nn) args))
             (IllegalOccurrence loc)
    (Pi _ name ta tb,_) ->
      min <$> f (Hyp name ta Nothing : ctx) (n+1) (nn+1) tb
          <*> strictlyPositive sig ctx loc defcount n nn ta

checkHomogeneousCall :: Loc -> Int -> Int -> Int -> Int -> [Term] -> Either Error Int
checkHomogeneousCall loc depth defcount n nn args = do
  assert (not (any (occurs n nn) args))
    (IllegalOccurrence loc)

  pure (f (depth - defcount - 1) args)
  where
    f n (Var m : args)
      | n == m = 1 + f (n - 1) args
    f _ _ = 0
{-
doesNotOccur :: Context -> Int -> Int -> Term -> Bool
doesNotOccur ctx n nn t = f 0 t True where
  f _ _ False = False
  f k (Var m) _
    | m >= n + k && m <= nn + k = False
    | m < k && m > nn + k = True
    | otherwise = case nth (m - k) ctx >>= hypValue of
      Just bo -> f 0 (lift (m - k) bo) True
      Nothing -> True
  f k t _ = Core.fold (const (+1)) k f t True
-}
