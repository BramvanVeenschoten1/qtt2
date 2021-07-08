module Prettyprint where

import Core
import Error
import Lexer (Loc)
import Debug.Trace

import Data.List as L
import Data.Map as M
import Control.Monad.RWS

{-
interesting flags:
- print flatly
- show lambda domains
- show case motives
-}
type SE = (Bool,Bool,Int)

dbiName :: Int -> Context -> ShowS
dbiName n ctx = f n ctx where
  f m [] = ('$' :) . showsPrec 0 n
  f 0 (Hyp "" _ _:ctx) = ('$' :) . showsPrec 0 n
  f 0 (Hyp name _ _:ctx) = (name ++)
  f m (_ : ctx) = f (m - 1) ctx

indent :: SE -> ShowS
indent (True,_,n) = ('\n':) . (replicate n ' ' ++)
indent (False,_,n) = id

embrace :: ShowS -> ShowS
embrace x = ('(' :) . x . (')':)

bracePi :: Term -> ShowS -> ShowS
bracePi Pi {} = embrace
bracePi _     = id

braceFun :: Term -> ShowS -> ShowS
braceFun Lam {}  = embrace
braceFun Pi {}   = embrace
braceFun Case {} = embrace
braceFun Let {}  = embrace
braceFun _       = id

braceArg :: Term -> ShowS -> ShowS
braceArg App {}  = embrace
braceArg Lam {}  = embrace
braceArg Pi {}   = embrace
braceArg Case {} = embrace
braceArg Let {}  = embrace
braceArg _       = id

showApp :: Context -> SE -> Term -> ShowS
showApp ctx se t = braceFun t (showSTerm ctx se t)

showArg :: Context -> SE -> Term -> ShowS
showArg ctx se t = braceArg t (showSTerm ctx se t)

showPi :: Context -> SE -> Term -> ShowS -> ShowS
showPi ctx se (Pi m name ta tb) acc =
  showPi (Hyp name ta Nothing:ctx) se tb (acc . showPiDomain ctx se m name ta)
showPi ctx se tb acc = ("Π" ++) . acc . (", " ++) . showSTerm ctx se tb

showLam :: Context -> SE -> Term -> ShowS -> ShowS
showLam ctx se (Lam m name ta tb) acc =
  showLam (Hyp name ta Nothing:ctx) se tb (acc . showDomain ctx se m name ta) 
showLam ctx se tb acc = ("λ" ++) . acc . (", " ++) . showSTerm ctx se tb

showLet :: Context -> SE -> Term -> ShowS -> ShowS
showLet ctx se t acc = case t of
  Let m name ta a body ->
    showLet (Hyp name ta (Just a) : ctx) se body
      (acc .
       indent se .
       (name ++) .
       (" : " ++) .
       showSTerm ctx se ta .
       (" = " ++) .
       showSTerm ctx se a)
  t -> ("let" ++) . acc . indent se . ("in " ++) . showSTerm ctx se t

showMult :: Mult -> ShowS
showMult Zero = ("0 " ++)
showMult One = ("1 " ++)
showMult _ = id

showPiDomain :: Context -> SE -> Mult -> String -> Term -> ShowS
showPiDomain ctx se m n t
  | Prelude.null n = ('(' :) . showMult m . ("_ : " ++) . showSTerm ctx se t . (')':)
  | otherwise = ('(' :) . showMult m . (n ++) . (" : " ++) . showSTerm ctx se t . (')':)

showDomain :: Context -> SE -> Mult -> String -> Term -> ShowS

showDomain ctx (b0,b1,i) m n t
  | b1 = ('(':) . showMult m . showName . (" : " ++) . showSTerm ctx (b0,b1,i) t . (')':)
  | otherwise = (' ':) . showName
  where
    showName
      | Prelude.null n = ('_':)
      | otherwise = (n ++)


showTerm ctx t = showSTerm ctx (True,True,0) t ""

showSTerm :: Context -> SE -> Term -> String -> String
showSTerm ctx se @ (b0,b1,i) t = case t of
  Type 0 -> ("Prop" ++)
  Type 1 -> ("Type" ++)
  Type l -> ("Type " ++) . showsPrec 0 (l - 1)
  Lift l -> ("Lift " ++) . showsPrec 0 l
  Var n _ -> dbiName n ctx
  Top s _ -> (s ++)
  App fun arg -> showApp ctx se fun . (' ':) . showArg ctx (b1,False,i) arg
  Case mult eliminee motive branches ->
    let se' j = (b0,False,i + j) in
      indent (se' 2).
      ("case " ++) .
      (showSTerm ctx (se' 6) eliminee) .
      (" return " ++) .
      (showSTerm ctx (se' 6) motive) .
      (" of" ++) .
      L.foldl (\acc branch -> acc .  indent (se' 4) . showSTerm ctx (se' 4) branch) id branches 
  pi @ Pi {} -> showPi ctx se pi id
  lam @ Lam {} -> showLam ctx se lam id
  lt @ Let {} -> showLet ctx se lt id

showSContext :: Context -> ShowS
showSContext [] = id
showSContext (Hyp name ty _ : ctx) =
  showSContext ctx .
  (name ++) .
  (" : " ++) .
  showSTerm ctx (True,True,length name + 3) ty .
  ('\n':)

showContext :: Context -> String
showContext ctx = showSContext ctx ""

errHeader :: Loc -> Context -> String
errHeader loc ctx = show loc ++ "\nin context:\n" ++ showContext ctx

showQName = intercalate "."

showError :: Error -> String
showError e = case e of
  Msg s -> "bad error message:\n" ++ s
  
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
  AmbiguousName loc name ->
    show loc ++
    "\nambiguous name: " ++ name
  
  DeclWithoutBody loc ->
    show loc ++ "\ndeclaration without body"
  BodyWithoutDecl loc ->
    show loc ++ "\ndefinition without type signature"
    
  LinearUnused loc name ->
    show loc ++ "\nLinear variable `" ++ name ++ "' is unused"
  LinearUsedAlready loc name ->
    show loc ++ "\nLinear variable `" ++ name ++ "' was already used"
  LinearUsedUnrestricted loc name ->
    show loc ++ "\nLinear variable `" ++ name ++ "' is used in unrestricted context"
  LinearCase loc name ->
    show loc ++ "\nLinear variable `" ++ name ++ "' is used inconsistently accross case branches"
  ErasedUsedRelevant loc name ->
    show loc ++ "\nErased variable `" ++ name ++ "' is used in irrelevant position"
    
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
  
  InductiveProp loc ->
    show loc ++ "\ndatatypes may not inhabit prop"
  
  
  -- _ -> "some error"

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
