module Core where

import Data.Map as M
import Data.List as L
import Data.Maybe
import Data.Function

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

data Ref
  = Ind !Int !Int !Int           -- blockno, defno, uniparamno
  | Con !Int !Int !Int !Int      -- blockno, defno, ctortag, paramno
  | Fix !Int !Int !Int !Int !Int -- blockno, defno, recparamno, height, uniparamno
  | Def !Int !Int                -- declno, height
  deriving Eq

data Term
  = Type !Int
  | Lift !Int
  | Var  !Int 
  | Lam  !Mult !String !Term !Term
  | Pi   !Mult !String !Term !Term
  | Let  !Mult !String !Term !Term !Term
  | App  !Term !Term
  | Top  !String !Ref
  | Case !Mult !Term !Term ![Term]

type Inductive = (Term,[(String,Term)])
type Definition = (Term,Term) -- ty, body

data Signature = Signature {
  sigFixs :: !(Map Int [Definition]),
  sigDefs :: !(Map Int Definition),
  sigData :: !(Map Int [Inductive])}

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
    Pi Zero "x" (Var 0) $
    Pi Zero "y" (Var 1) $
    Pi Zero ""  (
      Pi Zero "P" (Pi Many "" (Var 2) (Type 0)) $
      Pi One  ""  (App (Var 0) (Var 2)) $
                  (App (Var 1) (Var 2))) $
    Pi Zero "P" (Pi Many "" (Var 3) (Type l)) $
    Pi One  ""  (App (Var 0) (Var 3)) $
                (App (Var 1) (Var 3))

fold :: (Hyp -> k -> k) -> k -> (k -> Term -> a -> a) -> Term -> a -> a
fold push ctx f t = case t of
  App fun arg -> f ctx fun . f ctx arg
  Pi  mult name src dst -> f ctx src . f (push (Hyp name src Nothing) ctx) dst
  Lam mult name src dst -> f ctx src . f (push (Hyp name src Nothing) ctx) dst
  Let mult name ty t body -> f ctx ty . f ctx t . f (push (Hyp name ty (Just t)) ctx) body
  Case mult eliminee motive branches ->
    f ctx eliminee . f ctx motive . flip (L.foldr (f ctx)) branches
  _ -> id

map push ctx f t = case t of
  App fun arg -> App (f ctx fun) (f ctx arg)
  Pi  mult name src dst -> Pi mult name (f ctx src) (f (push (Hyp name src Nothing) ctx) dst)
  Lam mult name src dst -> Lam mult name (f ctx src) (f (push (Hyp name src Nothing) ctx) dst)
  Let mult name ty t body -> Let mult name (f ctx ty) (f ctx t) (f (push (Hyp name ty (Just t)) ctx) body)
  Case mult eliminee motive branches ->
    Case mult (f ctx eliminee) (f ctx motive) (fmap (f ctx) branches)
  t -> t

lift n = f 0 where
  f k (Var m)
    | m >= k = Var (m + n)
  f k t = Core.map (const (+1)) k f t

mkApp = L.foldl App

unrollApp t = f t [] where
  f (App fun arg) acc = f fun (arg : acc)
  f t acc = (t,acc)

psubst args = f 0 where
  nargs = length args
  
  f k t @ (Var n)
    | n >= k + nargs = Var (n - nargs) -- free
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

computeBranchType :: Mult -> Int -> Int -> [Term] -> Term -> Int -> (String,Term) -> Term
computeBranchType mult blockno datano args motive ctorno (name,ctorType) =
  f 0 (instantiateCtor args ctorType) where
    argc = length args
    f k (Pi m' name src dst) = Pi (times mult m') name src (f (k + 1) dst)
    f k t = App (Core.lift k motive) (mkApp
          (Top name (Con blockno datano ctorno argc))
          (fmap (Core.lift k) args ++
          fmap Var (reverse [0 .. k - 1])))
  
typeOfRef :: Signature -> Ref -> Term
typeOfRef sig ref = case ref of
  Ind blockno defno _ -> fst (sigData sig ! blockno !! defno)
  Con blockno defno ctorno _ -> snd (snd (sigData sig ! blockno !! defno) !! ctorno)
  Fix blockno defno _ _ _ -> fst (sigFixs sig ! blockno !! defno)
  Def blockno _ -> fst (sigDefs sig ! blockno)

heightOf :: Term -> Int
heightOf t = f () t 0 where
  f :: () -> Term -> Int -> Int
  f _ (Top _ (Fix _ _ _ h _)) = max h
  f _ (Top _ (Def _ h)) = max h
  f _ t = Core.fold (const id) () f t

occurs :: Int -> Int -> Term -> Bool
occurs deep shallow t = f 0 t False where
  f k (Var n)
    | n <= deep + k && n >= shallow + k = const True
    | otherwise = id
  f k t = Core.fold (const (+1)) k f t

substDummy :: Int -> Term -> Term
substDummy block t = f () t where
  f _ app @ App {} = case unrollApp app of
    (hd @ (Top _ (Ind blockno _ uniparamno)), args) ->
      if block == blockno
      then mkApp (Type 0) (fmap (f ()) (L.drop uniparamno args))
      else mkApp hd (fmap (f ()) args)
    (hd @ (Top _ (Fix blockno _ _ _ uniparamno)), args) ->
      if block == blockno
      then mkApp (Type 0) (fmap (f ()) (L.drop uniparamno args))
      else mkApp hd (fmap (f ()) args)
    (hd, args) -> mkApp hd (fmap (f ()) args)
  f _ t = Core.map (const id) () f t
    



