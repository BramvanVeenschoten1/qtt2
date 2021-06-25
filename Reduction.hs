module Reduction where

import Core
import Prettyprint
import Data.Function
import Data.Map as M
import Debug.Trace
import Data.List

data Config = Config Int [Config] Term [Config]

showConf ctx (Config k e t s) =
  "{" ++ intercalate ", " (fmap (showConf ctx) e) ++ "} " ++
   showTerm ctx t ++
   " [" ++ intercalate ", " (fmap (showConf ctx) s) ++ "]"

mkConf t = Config 0 [] t []

unwind (Config k e t s) = mkApp (psubst (fmap unwind e) t) (fmap unwind s)

reduce :: Signature -> Context -> Int -> Config -> (Config,Bool)
reduce sig ctx delta config @ (Config k e t s) = fkets where
  --one = ">> " ++ showConf ctx config
  --two = "~> " ++ showConf ctx (fst (fkets)) ++ "\n"
  
  fkets = f k e t s

  f :: Int -> [Config] -> Term -> [Config] -> (Config,Bool)
  --f k e t s
  --  | trace (">> " ++ showConf ctx (Config k e t s)) False = undefined
  f k e t @ (Var n b) s
    | n < k = let Config k' e' t' s' = e !! n in f k' e' t' (s' ++ s)
    | b = let Just x = hypValue (ctx !! (n - k)) in
      f 0 [] (Core.lift (n - k + 1) x) s
  f k e (Let _ _ _ x y) s =
    f (k + 1) (fst (f k e x []) : e) y s
  f k e (Lam _ _ _ dst) (x:s) =
    f (k + 1) (x : e) dst s
  f k e (App fun arg) s =
    f k e fun (fst (f k e arg []) : s)
  f k e (Lift l) (a:x:y:e':p:px:s)
    | convertible sig ctx True (unwind x) (unwind y) =
      let Config k' e' t' s' = px in f k' e' t' (s' ++ s)
  f k e t @ (Top _ (Def blockno height)) s
    | delta >= height = (Config k e t s, False)
    | otherwise = f 0 [] (snd (sigDefs sig ! blockno)) s
  f k e t @ (Top _ (Fix blockno defno recparamno height _)) s =
    case fmap (fst . reduce sig ctx 0) (nth recparamno s) of
      Just (Config _ _ (Top _ (Con {})) _) ->
        if delta >= height
        then (Config k e t s, False)
        else f 0 [] (snd ((sigFixs sig ! blockno) !! defno)) s
      _ -> (Config k e t s, True)
  f k e t @ (Case mult eliminee motive branches) s =
    case fst (reduce sig ctx 0 (Config k e eliminee [])) of
      Config _ _ (Top _ (Con _ _ tag paramno)) args ->
        f k e (branches !! tag) (Prelude.drop paramno args ++ s)
      c -> (Config k e t s, True)
  f k e t s = (Config k e t s, True)

whnf sig ctx t = unwind (fst (reduce sig ctx 0 (mkConf t)))
 
typeOf :: Signature -> Context -> Term -> Term
typeOf sig ctx t = case t of
  Type n -> Type (n + 1)
  Var n b -> Core.lift (n + 1) (hypType (ctx !! n))
  Lift l -> liftTy l
  Lam mult name src dst -> Pi mult name src (typeOf sig (Hyp name src Nothing : ctx) dst)
  Pi mult name src dst -> let
    ksrc = typeOf sig ctx src
    kdst = typeOf sig (Hyp name src Nothing : ctx) dst
    in case (ksrc,kdst) of
      (Type l0,Type l1) -> Type (if l1 == 0 then 0 else (max l0 l1))
  Let mult name ta a b -> psubst [a] (typeOf sig (Hyp name ta (Just a) : ctx) b)
  App fun arg -> case whnf sig ctx (typeOf sig ctx fun) of
    Pi _ name src dst -> psubst [arg] dst
    x -> error (showTerm ctx x)
  Top _ ref -> typeOfRef sig ref
  Case _ eliminee motive _ -> App motive eliminee

convertible sig ctx flag t0 t1 =
  --trace ("== " ++ showTerm ctx t0 ++ "\n== " ++ showTerm ctx t1 ++ "\n") $ 
  irrelevant ctx t0 ||
  alpha ctx flag t0 t1 ||
  machine flag (beta (mkConf t0)) (beta (mkConf t1)) where
  irrelevant ctx t = False
    --case whnf sig ctx (typeOf sig ctx (typeOf sig ctx t)) of
      --Type 0 -> True
      --_ -> False
  
  alpha ctx flag (Type l0) (Type l1) = l0 == l1 || (not flag && l0 <= l1)
  alpha ctx flag (Var n0 _) (Var n1 _) = n0 == n1
  alpha ctx flag (Lam _ name src0 dst0) (Lam _ _ _ dst1) =
    convertible sig (Hyp name src0 Nothing : ctx) flag dst0 dst1
  alpha ctx flag (Pi m0 name src0 dst0) (Pi m1 _ src1 dst1) =
    (m0 == m1 || not flag && m1 == Many) &&
    convertible sig ctx flag src1 src0 &&
    convertible sig (Hyp name src0 Nothing : ctx) flag dst0 dst1
  alpha ctx flag (Let _ name ta0 a0 b0) (Let _ _ ta1 a1 b1) =
    convertible sig ctx True ta0 ta1 &&
    convertible sig ctx True a0 a1 &&
    convertible sig (Hyp name ta0 (Just a0):ctx) flag b0 b1
  alpha ctx flag (App f0 x0) (App f1 x1) =
    convertible sig ctx True f0 f1 &&
    convertible sig ctx True x0 x1
  alpha ctx flag (Case _ e0 m0 b0) (Case _ e1 m1 b1) =
    convertible sig ctx True e0 e1 &&
    convertible sig ctx True m0 m1 &&
    and (zipWith (convertible sig ctx True) b0 b1)
  alpha ctx flag (Top _ r0) (Top _ r1) = r0 == r1
  alpha ctx flag t0 t1 = False
  
  beta = reduce sig ctx maxBound
  
  deltaStep flag (m0 @ ((Config _ _ t0 _), norm0)) (m1 @ ((Config _ _ t1 _), norm1)) = let
    heightOf (Top _ (Def _ h)) = h
    heightOf (Top _ (Fix _ _ _ h _)) = h
    heightOf t @ (App fun _) = error (showTerm ctx t ++ " heightOf app")
    heightOf _ = 0
  
    h0 = heightOf t0
    h1 = heightOf t1
    
    delta
      | norm0     = h1 - 1
      | norm1     = h0 - 1
      | h0 == h1  = max 0 (h0 - 1)
      | otherwise = min h0 h1
      
    m0' = reduce sig ctx delta (fst m0)
    m1' = reduce sig ctx delta (fst m1)
    
    proceed
      | norm0     = machine flag m0  m1'
      | norm1     = machine flag m0' m1
      | otherwise = machine flag m0' m1'
    in proceed
  
  machine flag m0 @ (Config k0 e0 t0 s0, norm0) m1 @ (Config k1 e1 t1 s1, norm1) =
    --trace ("~~ " ++ show norm0 ++ " " ++ show norm1 ++ " (" ++
      --showConf ctx (fst m0) ++ ") (" ++
      --showConf ctx (fst m1) ++ ")") $
    (alpha ctx flag (unwind (Config k0 e0 t0 [])) (unwind (Config k1 e1 t1 [])) &&
     and (zipWith (on (machine True) beta) s0 s1)) ||
      (not (norm0 && norm1) && deltaStep flag m0 m1)