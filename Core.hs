module Core where

import Data.Map as M
import Data.List as L
import Data.Maybe

data Mult
  = Zero
  | One
  | Many
  deriving Eq

times :: Mult -> Mult -> Mult
times Zero _ = Zero
times _ Zero = Zero
times One x  = x
times x  One = x
times _  _   = Many

plus :: Mult -> Mult -> Mult
plus Zero x   = x
plus One Zero = One
plus _   _    = Many

data Plicity
  = Explicit
  | Implicit
  | Class

-- Lift : Pi (a : Type l)(x y : a), (Pi P : a -> Prop, P x -> P y) -> Pi P : a -> Type l, P x -> P y

data Ref
  = Ind Int Int Int     -- block number, data number, uniparams number
  | Def Int Int Int Int -- block number, def number, height, uniparams number
  | Con Int Int Int Int -- block number, data number, ctor number, params number
  deriving Eq

-- consider Type 0 = Prop
-- pros : simplify some things
-- cons : complicate level polymorphism, which may not quantify over prop
data Term
  = Type Int
  | Lift Int
  | Var Int Bool
  | Lam Mult String Term Term
  | Pi  Mult String Term Term
  | Let Mult String Term Term Term
  | App Term Term
  | Top Ref
  | Case Mult Term Term [(Int,Term)] (Maybe Term)

data Inductive = Inductive {
  indName  :: String,
  indArity :: Term,
  indCtors :: [(String,Term)]}

data Function = Function {
  funName :: String,
  funType :: Term,
  funBody :: Term}
  
data Signature = Signature {
  sigData :: Map Int [Inductive],
  sigDefs :: Map Int [Function]}

data Hyp = Hyp {
  hypName     :: String,
  hypType     :: Term,
  hypValue    :: Maybe Term}

type Context = [Hyp]

nth 0 (x : _) = Just x
nth n (_ : xs) = nth (n - 1) xs
nth _ [] = Nothing

liftTy l = 
    Pi Zero "a" (Type l) $
    Pi Zero "x" (Var 0 False) $
    Pi Zero "y" (Var 1 False) $
    Pi Zero ""  (
      Pi Zero "P" (Pi Many "" (Var 4 False) (Type 0)) $
      Pi One  ""  (App (Var 0 False) (Var 2 False)) $
                  (App (Var 1 False) (Var 3 False))) $
    Pi Zero "P" (Pi Many "" (Var 3 False) (Type l)) $
    Pi One  ""  (App (Var 0 False) (Var 3 False)) $
                (App (Var 1 False) (Var 4 False))

fold push ctx f t = case t of
  App fun arg -> f ctx fun . f ctx arg
  Pi  mult name src dst -> f ctx src . f (push (Hyp name src Nothing) ctx) dst
  Lam mult name src dst -> f ctx src . f (push (Hyp name src Nothing) ctx) dst
  Let mult name ty t body -> f ctx ty . f ctx t . f (push (Hyp name ty (Just t)) ctx) body
  Case mult eliminee motive branches defbr ->
    f ctx eliminee .
    f ctx motive .
    L.foldr (f ctx . snd) branches .
    maybe id (f ctx) defbr 
  _ -> id

map push ctx f t = case t of
  App fun arg -> App (f ctx fun) (f ctx arg)
  Pi  mult name src dst -> Pi mult name (f ctx src) (f (push (Hyp name src Nothing) ctx) dst)
  Lam mult name src dst -> Lam mult name (f ctx src) (f (push (Hyp name src Nothing) ctx) dst)
  Let mult name ty t body -> Let mult name (f ctx ty) (f ctx t) (f (push (Hyp name ty (Just t)) ctx) body)
  Case mult eliminee motive branches defbr ->
    Case mult (f ctx eliminee) (f ctx motive) (fmap (\(l,t) -> (l, f ctx t)) branches) (fmap (f ctx) defbr)
  t -> t

lift n = f 0 where
  f k (Var m b)
    | m >= k = Var (m + n) b
  f k t = Core.map (const (+1)) k f t

mkApp = L.foldl App

unrollApp (App fun arg) = let (fun',args) = unrollApp fun in (fun',arg:args)
unrollApp t = (t,[])

psubst args = f 0 where
  nargs = length args
  
  f k t @ (Var n b)
    | n >= k + nargs = Var (n - nargs) b -- free
    | n < k = t -- local
    | otherwise = lift k (args !! (n - k)) -- in bounds
  f k (App fun arg) = beta (f k fun) (f k arg)
  f k t = Core.map (const (+1)) k f t
  
  beta (Lam _ _ _ dst) arg = psubst [arg] dst
  beta t s = App t s

countDomains :: Term -> Int
countDomains (Pi _ _ _ dst) = 1 + countDomains dst
countDomains _ = 0

dropDomains :: Int -> Term -> Term
dropDomains 0 t = t
dropDomains n (Pi m name src dst) = dropDomains (n - 1) dst
dropDomains _ _ = undefined

instantiateCtor :: [Term] -> Term -> Term
instantiateCtor params = psubst (reverse params) . dropDomains (length params)

data Config = Config Int [Config] Term [Config]

mkConf t = Config 0 [] t []

unwind (Config k e t s) = mkApp (psubst (fmap unwind e) t) (fmap unwind s)

reduce :: Signature -> Context -> Int -> Config -> Config
reduce sig ctx delta config @ (Config k e t s) = f k e t s where
  f :: Int -> [Config] -> Term -> [Config] -> Config
  f k e t @ (Var n b) s
    | n < k = let Config k e t s' = e !! n in f k e t (s' ++ s)
    | b = let Just x = hypValue (ctx !! (n - k)) in f k e x s
  f k e (Let _ _ _ x y) s =
    f (k + 1) (f k e x [] : e) y s
  f k e (Lam _ _ _ dst) (x:s) =
    f (k + 1) (reduce sig ctx delta x : e) dst s
  f k e (App fun arg) s =
    f k e fun (mkConf arg : s)
  f k e (Lift l) (a:x:y:e':p:px:s)
    | convertible sig ctx True (unwind x) (unwind y) =
      let Config k' e' t' s' = px in f k' e' t' (s' ++ s)
  f k e (Top (Def blockno defno height _)) s
    | height >= delta = let
      fun = funBody ((sigDefs sig ! blockno) !! defno)
      in f 0 [] fun s
    | otherwise = Config k e t s
  f k e (Case mult eliminee motive branches defbr) s =
    let c = reduce sig ctx 0 (mkConf eliminee)
    in case c of
      Config _ _ (Top (Con _ _ ctorno paramno)) args ->
        case L.lookup ctorno branches of
          Just branch ->
            f k e branch (Prelude.drop paramno args ++ s)
          Nothing ->
            f k e (fromJust defbr) (c : s)
      _ -> Config k e (Case mult (unwind c) motive branches defbr) s
  f k e t s = Config k e t s

whnf sig ctx t = unwind (reduce sig ctx 0 (mkConf t))

typeOfRef :: Signature -> Ref -> Term
typeOfRef sig ref = case ref of
  Con blockno datano ctorno _ ->
    snd (indCtors ((sigData sig ! blockno) !! datano) !! ctorno)
  Ind blockno datano _ ->
    indArity ((sigData sig ! blockno) !! datano)
  Def blockno defno _ _ ->
    funType ((sigDefs sig ! blockno) !! defno)

{-
  requires:
    args, motive, constructor type, tag, blockno defno
-}

computeBranchType :: [Term] -> Term -> (Int,Int,Int,Term) -> Term
computeBranchType args motive (blockno,datano,ctorno,ctorType) =
  undefined

typeOf :: Signature -> Context -> Term -> Term
typeOf sig ctx t = case t of
  Type n -> Type (n + 1)
  Var n b -> Core.lift (n + 1) (hypType (ctx !! n))
  Lift l -> liftTy l
  Lam mult name src dst -> Pi mult name src (typeOf sig ctx dst)
  Pi mult name src dst -> let
    ksrc = typeOf sig ctx src
    kdst = typeOf sig (Hyp name src Nothing : ctx) dst
    in case (ksrc,kdst) of
      (Type l0,Type l1) -> Type (if l1 == 0 then 0 else (max l0 l1))
  Let mult name ta a b -> psubst [a] (typeOf sig ctx b)
  App fun arg -> let
    Pi _ name src dst = whnf sig ctx (typeOf sig ctx fun)
    in psubst [arg] dst
  Top ref -> typeOfRef sig ref
  Case _ eliminee motive _ _ -> App motive eliminee

{-
It seems there is a choice to make between an optimal, handwritten decision tree
and compact code. keep in mind that the matita kernel uses reference equality, and so
has reason to compare before doing any reduction at all.

Interesting idea: compare configs without unwinding. Will require some way to 
move envs under binders. consider:

ctx = z : a
env = y : b
t   = \(x : a), $0 $1 $2

$0 refers to x in scope, $1 refers to y in env, $2 refers to a variable in the context at large.

to move an env under the lambda expresison (\x, t), add x to the context at large, and a reference
to x ($0) to the env. This is easily invertible

advantage: replace substitutions by constant time operations in typechecking and conversion checking
can increase space use, by failing to discard terms that are substituted in terms they don't occur in,
needs attention
-}


convertible sig ctx flag t0 t1 =
  irrelevant ctx t0 ||
  alpha ctx flag t0 t1 ||
  machine ctx flag 
    (reduce sig ctx maxBound (mkConf t0))
    (reduce sig ctx maxBound (mkConf t1)) where
      irrelevant ctx t = case whnf sig ctx (typeOf sig ctx (typeOf sig ctx t)) of
        Type 0 -> True
        _ -> False
      
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
      alpha ctx flag (Case _ e0 m0 b0 d0) (Case _ e1 m1 b1 d1) =
        convertible sig ctx True e0 e1 &&
        convertible sig ctx True m0 m1 &&
        and (zipWith (\(l0,t0)(l1,t1) -> l0 == l1 && convertible sig ctx True t0 t1) b0 b1) &&
        fromMaybe False (convertible sig ctx True <$> d0 <*> d1)
      alpha ctx flag (Top r0) (Top r1) = r0 == r1
      
      alpha ctx flag t0 t1 = False
      
      machine ctx flag c0 @ (Config _ _ t0 _) c1 @ (Config _ _ t1 _) =
        case (t0,t1) of
          (Top (Def _ _ h0 _), Top (Def _ _ h1 _)) ->
            case compare h0 h1 of
              LT -> machine ctx flag c0 (reduce sig ctx h1 c1)
              EQ -> machine ctx flag (reduce sig ctx (h0 - 1) c0) (reduce sig ctx (h0 - 1) c1)
              GT -> machine ctx flag (reduce sig ctx h0 c0) c1
          (Top (Def _ _ h _), _) ->
            machine ctx flag (reduce sig ctx h c0) c1
          (_, Top (Def _ _ h _)) ->
            machine ctx flag c0 (reduce sig ctx h c1)
          _ -> alpha ctx flag (unwind c0) (unwind c1)
  


