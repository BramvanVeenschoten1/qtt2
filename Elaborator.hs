module Elaborator where

import Lexer(Loc)
import Parser
import Core
import Error
import Reduction

import Data.List
import Control.Monad
import Control.Monad.State.Lazy as S
import Control.Applicative hiding (Const)
import Data.Functor
import Data.Map as M
import Data.Either
import Data.Maybe
import Prettyprint

import Debug.Trace

data Use
  = Nouse
  | Oneuse Mult Loc
  | Adduse Use Use
  | CaseUse Loc [Use]

type Uses = [Use]

useSum :: Use -> Mult
useSum Nouse = Zero
useSum (Oneuse x _) = x
useSum (Adduse x y) = plus (useSum x)(useSum y)
useSum (CaseUse _ xs) = f (fmap useSum xs) where
  f xs
    | all (== Zero) xs = Zero
    | all (== One) xs = One
    | otherwise = Many

noUses :: Uses
noUses = repeat Nouse

plusUses :: Uses -> Uses -> Uses
plusUses = zipWith Adduse

timesUses :: Mult -> Uses -> Uses
timesUses Zero = const noUses
timesUses One  = id
timesUses Many = fmap f where
  f Nouse = Nouse
  f (Oneuse m x) = Oneuse (timesMany m) x
  f (Adduse x y) = Adduse (f x) (f y)
  f (CaseUse info xs) = CaseUse info (fmap f xs)

  timesMany Zero = Zero
  timesMany _    = Many

branchUses :: Loc -> [Uses] -> Uses
branchUses info [] = noUses
branchUses info xs = fmap (CaseUse info) (transpose xs)

type NameSpace = (Map Name [QName], Map QName (Loc, Ref))

type ElabState = (NameSpace,Signature)

lookupQName :: QName -> ElabState -> Maybe (Loc, Ref)
lookupQName qname st = M.lookup qname (snd (fst st))

lookupName :: Name -> ElabState -> Maybe [QName]
lookupName name st = M.lookup name (fst (fst st))

-- look up a qualified name in the symbol table
lookupQualified :: ElabState -> Loc -> QName -> Either Error (Term,Term,Uses)
lookupQualified st loc qname =
  case lookupQName qname st of
    Nothing -> Left (UndefinedName loc qname)
    Just (loc,ref) -> pure (Top (intercalate "." qname) ref, typeOfRef (snd st) ref, noUses)

-- look up a name in the symbol table and lookup Unqualified if appropriate
lookupUnqualified :: ElabState -> Loc -> Name -> Either Error (Term,Term,Uses)
lookupUnqualified st loc name = let
  in case lookupName name st of
    Nothing -> Left (UndefinedName loc [name])
    Just [qname] -> case lookupQName qname st of
      Nothing -> error "incomplete namespace"
      Just (loc,ref) -> pure (Top (intercalate "." qname) ref, typeOfRef (snd st) ref, noUses)
    Just xs -> Left (AmbiguousName loc name)

-- lookup a name in the context and return appropriate uses if present
lookupCtx :: Context -> Loc -> Name -> Maybe (Term,Term,Uses)
lookupCtx ctx loc name = f 0 ctx where
  f n [] = Nothing
  f n (hyp:hyps)
    | name == hypName hyp = pure (Var n (isJust (hypValue hyp)), Core.lift (n + 1) (hypType hyp), (Oneuse One loc) : noUses)
    | otherwise = fmap (\(t,ty,u) -> (t,ty,Nouse:u)) (f (n + 1) hyps)


-- check if a term is a valid sort
checkSort :: Signature -> Context -> Loc -> Term -> Either Error ()
checkSort sig ctx loc x = case whnf sig ctx x of
  Type _ -> pure ()
  _ -> Left (ExpectedSort ctx loc x)

ensureFunction :: Signature -> Context -> Loc -> Term -> Either Error (Mult,Name,Term,Term)
ensureFunction sig ctx loc t = case whnf sig ctx t of
  Pi m name src dst -> pure (m,name,src,dst)
  _ -> Left (ExpectedFunction ctx loc t)

-- check variable usage against given multiplicity
checkArgMult :: Loc -> Mult -> Use -> Either Error ()
checkArgMult _ Many _ = pure ()
checkArgMult _ Zero uses = f uses where
  f Nouse           = pure ()
  f (Oneuse Zero _) = pure ()
  f (Oneuse _ loc) = Left (LinearUsedUnrestricted loc)
  f (CaseUse loc xs) = mapM_ f xs
  f (Adduse x y) = f x *> f y
checkArgMult loc One uses = checkOne uses where

  checkOne Nouse = Left (LinearUnused loc)
  checkOne (Oneuse Zero _) = Left (LinearUnused loc)
  checkOne (Oneuse One _) = pure ()
  checkOne (Oneuse Many loc) = Left (LinearUsedUnrestricted loc)
  checkOne (Adduse x y) = do
    m <- checkMaybe x
    if m
    then checkNone y
    else checkOne y
  checkOne (CaseUse loc' xs) = mapM_ checkOne xs
  
  checkNone Nouse = pure ()
  checkNone (Oneuse Zero _) = pure ()
  checkNone (Oneuse One loc) = Left (LinearUsedAlready loc)
  checkNone (Oneuse Many loc) = Left (LinearUsedUnrestricted loc)
  checkNone (Adduse x y) = checkNone x *> checkNone y
  checkNone (CaseUse loc' xs) = mapM_ checkNone xs
  
  checkMaybe Nouse = pure False
  checkMaybe (Oneuse Zero _) = pure False
  checkMaybe (Oneuse One _) = pure True
  checkMaybe (Oneuse Many loc) = Left (LinearUsedUnrestricted loc)
  checkMaybe (Adduse x y) = do
    m <- checkMaybe x
    if m
    then checkNone y *> pure True
    else checkMaybe y
  checkMaybe (CaseUse loc' xs) = do
    uses <- mapM checkMaybe xs
    if and uses || not (or uses)
    then pure (or uses)
    else Left (LinearCase loc')

-- check or synthesise the binding of a let expression
checkLetBinding :: ElabState -> Context -> Expr -> Expr -> Either Error (Term,Term,Uses)
checkLetBinding st ctx (EHole _) a = synth st ctx a
checkLetBinding st ctx ta a = do
  let la = exprLoc ta
  (ta,ka,_) <- synth st ctx ta
  checkSort (snd st) ctx la ka
  (a,ua) <- check st ctx a ta
  pure (a,ta,ua)

-- for the given expression, compute its corresponding core term, its type and the usage environment
synth :: ElabState -> Context -> Expr -> Either Error (Term,Term,Uses)
synth st ctx expr = case expr of
  EHole  loc -> Left (Msg "Holes are not implemented")
  EType  loc l -> pure (Type l, Type (l + 1), noUses)
  ELift  loc l -> pure (liftTy l, Type (l + 1), noUses)
  EName  loc qname -> lookupQualified st loc qname
  EVar   loc name -> maybe (lookupUnqualified st loc name) pure (lookupCtx ctx loc name)
  EApply loc _ f arg -> do
    (f,tf,uf) <- synth st ctx f
    (m,name,ta,tb) <- ensureFunction (snd st) ctx loc tf
    (a,ua) <- check st ctx arg ta
    pure (App f a, psubst [a] tb, plusUses (timesUses m ua) uf)
  ELet loc mloc name ta a b -> do
    (a,ta,ua) <- checkLetBinding st ctx ta a
    let hyp = Hyp name ta (Just a)
    (b,tb,ub0) <- synth st (hyp : ctx) b
    let ux : ub = ub0
        u = useSum ux
    pure (Let u name ta a b, psubst [a] tb, plusUses (timesUses u ua) ub)
  ELam loc mloc _ _ _ (EHole _) _ -> Left (InferLambda ctx loc)
  ELam loc mloc p m name ta b -> do
    let la = exprLoc ta
    (ta,ka,_) <- synth st ctx ta
    checkSort (snd st) ctx la ka
    let hyp = Hyp {
          hypName = name,
          hypType = ta,
          hypValue  = Nothing}
    (b,tb,ub0) <- synth st (hyp : ctx) b
    let ux : ub = ub0
    checkArgMult mloc m ux
    pure (Lam m name ta b, Pi m name ta tb, ub)
  EPi loc mloc p m name ta tb -> do
    let la = exprLoc ta
        lb = exprLoc tb
    (ta,ka,_) <- synth st ctx ta
    let hyp = Hyp {
          hypName = name,
          hypType = ta,
          hypValue  = Nothing}
    (tb,kb,_) <- synth st (hyp : ctx) tb
    checkSort (snd st) ctx la ka
    checkSort (snd st) ctx lb kb
    pure (Pi m name ta tb, kb, noUses)

-- check an expression agains a given type and compute the corresponding core term
check :: ElabState -> Context -> Expr -> Term -> Either Error (Term,Uses)
check st ctx expr ty = case expr of
  ELam loc mloc p _ name (EHole _) b -> do
    (m, _, ta, tb) <- ensureFunction (snd st) ctx loc ty
    let hyp = Hyp {
            hypName = name,
            hypType = ta,
            hypValue  = Nothing}
    (b,ub0) <- check st (hyp : ctx) b tb
    let ux : ub = ub0
    checkArgMult mloc m ux
    pure (Lam (useSum ux) name ta b, ub)
  ELam loc mloc p _ name ta b -> do
    (ta,_,_) <- synth st ctx ta
    let ty' = whnf (snd st) ctx ty
    (m, _, ta', tb) <- ensureFunction (snd st) ctx loc ty
    let hyp = Hyp {
            hypName = name,
            hypType = ta,
            hypValue  = Nothing}
    
    if convertible (snd st) ctx False ta' ta
    then pure ()
    else
      Left (AnnotError ctx loc ta' ta)

    (b,ub0) <- check st (hyp : ctx) b tb
    
    let ux : ub = ub0
    checkArgMult mloc m ux
    pure (Lam (useSum ux) name ta b, ub)
  ELet loc mloc name ta a b -> do
    (a,ta,ua) <- checkLetBinding st ctx ta a
    let hyp = Hyp name ta (Just a)
    (b,ub0) <- check st (hyp : ctx) b (Core.lift 1 ty)
    let ux : ub = ub0
        u = useSum ux
    pure (Let u name ta a b, plusUses (timesUses u ua) ub)
  x -> do
    (a,ta,ua) <- synth st ctx x
    
    let ty' = whnf (snd st) ctx ty
        ta' = whnf (snd st) ctx ta
    
    if convertible (snd st) ctx False ta ty
    then pure ()
    else 
      --trace (showTerm ctx ty') $
      --trace (showTerm ctx ta') $
      Left (TypeError ctx (exprLoc x) ty a ta)
    
    pure (a,ua)

