module Prettyprint where

import Core
import Error
import Lexer (Loc)
import Debug.Trace

import Data.List as L
import Data.Map as M
import Control.Monad.RWS

dbiName :: Int -> Context -> String
dbiName n ctx = f n ctx where
  f m [] = '$' : show n
  f 0 (Hyp "" _ _:ctx) = '$' : show n
  f 0 (Hyp name _ _:ctx) = name
  f m (_ : ctx) = f (m - 1) ctx

embrace :: String -> String
embrace x = '(' : x ++ ")"

bracePi :: Term -> String -> String
bracePi Pi {} = embrace
bracePi _     = id

braceApp :: Term -> String -> String
braceApp App {}  = embrace
braceApp Lam {}  = embrace
braceApp Pi {}   = embrace
braceApp Case {} = embrace
braceApp Let {}  = embrace
braceApp _       = id

showArg :: Context -> Term -> String
showArg  ctx t = braceApp t (showTerm  ctx t)

showLam :: Context -> String -> Term -> String
showLam  ctx acc (Lam m name ta tb) = showLam  (Hyp name ta Nothing:ctx) (acc ++ showDomain  ctx m name ta) tb
showLam  ctx acc tb = "\\" ++ acc ++ ", " ++ showTerm  ctx tb

showPi :: Context -> String -> Term -> String
showPi  ctx acc (Pi m name ta tb) = showPi  (Hyp name ta Nothing:ctx) (acc ++ showDomain  ctx m name ta) tb
showPi  ctx acc tb = "Pi " ++ acc ++ ", " ++ showTerm  ctx tb

showMult :: Mult -> String
showMult Zero = "0 "
showMult One = "1 "
showMult _ = ""

showDomain :: Context -> Mult -> String -> Term -> String
showDomain  ctx m n t
  | Prelude.null n = '(' : showMult m ++ "_ : " ++ showTerm  ctx t ++ ")"
  | otherwise = '(' : showMult m ++ n ++ " : " ++ showTerm  ctx t ++ ")"

showTerm :: Context -> Term -> String
showTerm  ctx (Type 0)     = "Prop"
showTerm  ctx (Type 1)     = "Type"
showTerm  ctx (Type l)     = "Type " ++ show (l - 1)
showTerm  ctx (Var n _)    = dbiName n ctx
showTerm  ctx (Top s _)    = s
showTerm  ctx app @ App {} = unwords (fmap (showArg  ctx) (f : xs)) where (f,xs) = unrollApp app
showTerm  ctx pi  @ Pi {}  = showPi  ctx [] pi
showTerm  ctx lam @ Lam {} = showLam  ctx [] lam
showTerm  ctx (Let m name ta a b) =
  "let " ++ name ++ " = " ++ showTerm ctx a ++ " in " ++ showTerm ctx b
showTerm  ctx (Case m eliminee motive branches) =
  "case " ++ showTerm ctx eliminee ++ " return " ++ showTerm ctx motive ++ " of " ++ intercalate "; " (fmap (showTerm ctx) branches)

showContext :: Context -> String
showContext  [] = ""
showContext  (Hyp name ty _ :ctx) = showContext  ctx ++ name ++ " : " ++ showTerm  ctx ty ++ "\n"

errHeader :: Loc -> Context -> String
errHeader loc ctx = show loc ++ "\nin context:\n" ++ showContext ctx

showQName = intercalate "."

showError :: Error -> String
showError e = case e of
  TypeError ctx loc expected term given ->
    errHeader loc ctx ++
    "\ngot term:\n" ++
    showTerm ctx term ++
    "\nof type:\n" ++
    showTerm ctx given ++
    "\nbut expected type was:\n" ++
    showTerm ctx expected
  AnnotError ctx loc pi annot ->
    errHeader loc ctx ++
    "\nexpected a function with domain:\n" ++
    showTerm ctx pi ++
    "\nbut lamda annotation is:\n" ++
    showTerm ctx annot
  ExpectedFunction ctx loc t ->
    errHeader loc ctx ++
    "\nexpected a function, but got a term of type:\n" ++
    showTerm ctx t
  ExpectedSort ctx loc t ->
    errHeader loc ctx ++
    "\nexpected a type, but got a term of type:\n" ++
    showTerm ctx t
  InferLambda ctx loc ->
    errHeader loc ctx ++
    "cannot infer type of un-annotated lambda expression"
  
  UnknownModule name ->
    "Unknown module: " ++ name
  CircularImports names ->
    "circular imports:\n" ++ unlines names
  NameAlreadyDefined loc qname ->
    show loc ++
    "\nname already defined: " ++ showQName qname
  UndefinedName loc qname ->
    show loc ++
    "\nundefined name: " ++ showQName qname
    
  RefuteNonEmpty ctx loc t ->
    errHeader loc ctx ++
    "cannot refute non-empty type:\n" ++
    showTerm ctx t 
  SplitNonData _ -> "split non data"
  ArityMismatch _ _ _ -> " arity mismatch"
  ConstructorMismatch loc hd ctx t ->
    errHeader loc ctx ++
    hd ++ " is not a constructor of type:\n" ++
    showTerm ctx t 
  NonCoveringSplit _ _ -> "non covering split"
  IntroNonFunction -> "intro non function"
  UnevenPatterns -> "uneven patterns"
  
  Msg s -> s
  
  _ -> "some error"

{-
showError :: Error -> String
showError e = case e of
  ExpectedSort ctx t -> "in context:\n" ++ showContext ctx ++ "expected a sort, but got:\n" ++ showTerm ctx t
  ExpectedFunction ctx t -> "in context:\n" ++ showContext ctx ++ "expected a function, but got a term of type:\n" ++ showTerm ctx t
  ExpectedType ctx expected term ty -> "in context:\n" ++ showContext ctx ++ "Type error:\ngot term:\n" ++ showTerm ctx term ++ "\nof type:\n" ++ showTerm ctx ty ++ "\nbut expected a term of type:\n" ++ showTerm ctx expected
  NameNotDefined name -> "undefined name: " ++ name
  NameAlreadyDefined name -> "name was already defined: " ++ name
  IllFormedTypeConstructor name -> "type constructor " ++ name ++ " is ill-formed"
  IllFormedDataConstructor name -> "data constructor " ++ name ++ " is ill-formed"
  OccurrenceInIndex name -> "datatype " ++ name ++ " occurs in an illegal index"
  NegativeOccurrence name -> "datatype " ++ name ++ " occurs negatively in its constructor"
-}
