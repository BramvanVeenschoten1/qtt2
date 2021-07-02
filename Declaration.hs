module Declaration where

import Control.Monad.RWS.Lazy
import Control.Monad.State.Lazy as S
import Control.Monad.Trans
import Core
import Data.Function
import Data.List as L
import Data.Map as M
import Debug.Trace
import Elaborator
import Lexer (Loc, emptyLoc)
import Parser
import Prettyprint
import Equations
import Error
import Termination
import Reduction

{-
TODO:
- compute function heights
-}

type Clause = ([Pattern], Expr)

data Block
  = DataBlock [(Loc, Name, [Param], Expr, [Ctor])]
  | FunBlock [(Loc, Name, Expr, [Clause])]


data DeclState = DeclState {
  nextBlock :: Int,
  moduleName :: Name,
  importedNames :: NameSpace,
  internalNames :: NameSpace,
  signature :: Signature}

mergeNameSpace :: NameSpace -> NameSpace -> NameSpace
mergeNameSpace (n0,q0) (n1,q1) = (M.unionWith (++) n0 n1, M.union q0 q1)

emptyNameSpace :: NameSpace
emptyNameSpace = (M.empty,M.empty)

emptySignature = Signature M.empty M.empty

type DeclElab = StateT DeclState (Either Error)

insertName :: (QName, Loc, Ref) -> DeclElab ()
insertName (qname,loc,ref) = do
  (shorts,longs) <- gets internalNames
  case M.lookup qname longs of
    Nothing -> do
      traceM (showQName qname ++ " defined")
      
      modify (\st -> st {
        internalNames =
          (insertWith (++) (last qname) [qname] shorts,
           M.insert qname (loc, ref) longs)})
    Just (loc, _) -> S.lift $ Left $ NameAlreadyDefined loc qname

runTypechecker :: (ElabState -> Either Error a) -> DeclElab a
runTypechecker x = do
  DeclState _ modname imported internal sig <- get
  case x (mergeNameSpace imported internal, sig) of
    Left err -> S.lift (Left err)
    Right x -> pure x

groupDecls :: [Decl] -> Either Error [Block]
groupDecls = coupleGroups . groupBy sameDeclKind
  where
    head (x:_) = x
    head _ = error "decl head"
    
    sameDeclKind DataDecl {} DataDecl {} = True
    sameDeclKind DataDef {} DataDef {} = True
    sameDeclKind FunDecl {} FunDecl {} = True
    sameDeclKind Clause {} Clause {} = True
    sameDeclKind _ _ = False

    declName :: Decl -> String
    declName (DataDecl _ n _ _) = n
    declName (DataDef _ n _) = n
    declName (FunDecl _ n _) = n
    declName (Clause _ n _ _) = n

    declLoc :: Decl -> Loc
    declLoc (DataDecl x _ _ _) = x
    declLoc (DataDef x _ _) = x
    declLoc (FunDecl x _ _) = x
    declLoc (Clause x _ _ _) = x

    findDefs :: [Decl] -> [Decl] -> Either Error [(Loc, Name, [Param], Expr, [Ctor])]
    findDefs [] [] = pure []
    findDefs (DataDef loc _ _ : _) [] = Left (BodyWithoutDecl loc)
    findDefs defs (decl@(DataDecl loc name params arity) : decls) = case find ((name ==) . declName) defs of
      Just (DataDef _ _ ctors) -> do
        block <- findDefs (deleteBy ((==) `on` declName) decl defs) decls
        pure ((loc, name, params, arity, ctors) : block)
      Nothing -> Left (DeclWithoutBody loc)

    findClauses :: [[Decl]] -> [Decl] -> Either Error [(Loc, Name, Expr, [Clause])]
    findClauses [] [] = pure []
    findClauses ((Clause loc _ _ _ : _) : _) [] = Left (BodyWithoutDecl loc)
    findClauses clauses (decl@(FunDecl loc name ty) : decls) = case find ((name ==) . declName . head) clauses of
      Just c -> do
        let clauses' = fmap (\(Clause _ _ pats rhs) -> (pats, rhs)) c
        block <- findClauses (deleteBy ((==) `on` (declName . head)) c clauses) decls
        pure ((loc, name, ty, clauses') : block)
      Nothing -> Left (DeclWithoutBody loc)

    coupleGroups :: [[Decl]] -> Either Error [Block]
    coupleGroups [] = pure []
    coupleGroups (decls : defs : groups) = case (head decls, head defs) of
      (DataDecl {}, DataDef {}) -> do
        block <- findDefs defs decls
        blocks <- coupleGroups groups
        pure (Declaration.DataBlock block : blocks)
      (FunDecl {}, Clause {}) -> do
        block <- findClauses (groupBy ((==) `on` declName) defs) decls
        blocks <- coupleGroups groups
        pure (FunBlock block : blocks)
      (FunDecl loc _ _, _) -> Left (DeclWithoutBody loc)
      (DataDecl loc _ _ _, _) -> Left (DeclWithoutBody loc)
      (DataDef loc _ _, _) -> Left (BodyWithoutDecl loc)
      (Clause loc _ _ _, _) -> Left (BodyWithoutDecl loc)

checkBlocks :: [Block] -> DeclElab ()
checkBlocks = mapM_ f
  where
    f (Declaration.DataBlock defs) = checkData defs
    f (FunBlock defs) = checkFunctions defs

checkFunctions :: [(Loc, Name, Expr, [Clause])] -> DeclElab ()
checkFunctions defs = do
  modname <- gets moduleName

  block <- gets nextBlock

  let (deflocs, defnames, deftys, clauses) = unzip4 defs

      qnames = fmap (\name -> [modname, name]) defnames

  tys <- runTypechecker $
    \st -> flip mapM deftys $ \ty -> do
      (ty, k, _) <- synth st [] ty
      checkSort (snd st) [] emptyLoc k
      pure ty

  let ctx = zipWith (\name ty -> Hyp name ty Nothing) defnames tys
  
      checkBody :: ElabState -> Term -> [Clause] -> Either Error Term
      checkBody st t cs = compileEquations st ctx (fmap mkProblem cs) t
  
  bodies <- runTypechecker $ \st -> zipWithM (checkBody st) tys clauses

  sig <- gets signature

  let rec_calls = fmap (getRecursiveCalls sig ctx) bodies
      height = 1 + maximum (fmap heightOf bodies)
  
  case rec_calls of
    [[]] -> do
      
      let qname = head qnames
          loc = head deflocs
          ref = Def block height
          top = Top (showQName qname) ref
          ty = head tys
          body = psubst [top] (head bodies)
      
      insertName (qname,loc,ref)
      
      --traceM (showTerm [] body)
      --traceM ""
      
      modify (\st -> st {
        nextBlock = block + 1,
        signature = Signature
          (sigFixs (signature st))
          (M.insert block (ty,body) (sigDefs (signature st)))
          (sigData (signature st))})
      
      sig <- gets signature
      unless (convertible sig [] False (typeOf sig [] body) ty)
        (error ("ill-formed function: " ++ head defnames ++ "\n" ++ showTerm [] body))
    _ -> do
      
      rec_args <- S.lift $ maybe
        (Left (Msg (show rec_calls ++ "\ncannot infer decreasing path in fixpoint:\n" ++
          concatMap show deflocs))) Right (findRecparams rec_calls)
      
      let makeRef defno rec_arg = Fix block defno rec_arg height 0    
          refs = zipWith makeRef [0..] rec_args
          tops = zipWith Top (fmap showQName qnames) refs
          bodies' = fmap (psubst tops) bodies
          typed_bodies = zip tys bodies'
          name_loc_refs = zip3 qnames deflocs refs
      
      mapM_ insertName name_loc_refs
      
      --traceM (unlines (fmap (showTerm []) (fmap snd typed_bodies))) 
      
      modify (\st -> st {
        nextBlock = block + 1,
        signature = Signature
          (M.insert block typed_bodies (sigFixs (signature st)))
          (sigDefs (signature st))
          (sigData (signature st))})
      
      sig <- gets signature
      sequence_ (zipWith3 (\name ty body ->
        unless (convertible sig [] False (typeOf sig [] body) ty)
          (error ("ill-formed function: " ++ head defnames ++ "\n" ++ showTerm [] body)))
        defnames tys bodies')

checkData :: [(Loc, Name, [Param], Expr, [Ctor])] -> DeclElab ()
checkData defs = do
  modname <- gets Declaration.moduleName

  block <- gets nextBlock

  let defcount = length defs
      (def_locs, names, paramss, arities, ctorss) = unzip5 defs

      qnames = fmap (\name -> [modname, name]) names

      ctor_names = fmap (fmap (\(_, n, _) -> n)) ctorss

      ctor_qnames = concat (zipWith (\qname ctor_names -> fmap (\name -> qname ++ [name]) ctor_names) qnames ctor_names)

  let checkParams :: ElabState -> Context -> [Param] -> Expr -> Either Error  (Context, Term)
      checkParams st ctx [] e = case e of
          EType loc 0 -> Left (InductiveProp loc)
          EType loc l -> pure (ctx, Type l)
          _ -> Left (Msg "indices not supported")
      checkParams st ctx ((_, p, m, name, ty) : params) e = do
        (ty, _, _) <- synth st ctx ty
        checkParams st (Hyp name ty Nothing : ctx) params e

  (paramss, arities) <- unzip <$> runTypechecker (\st -> zipWithM (checkParams st []) paramss arities)

  let paramnos = fmap length paramss
      indexnos = fmap countDomains arities

      extendArity :: Term -> Context -> Term
      extendArity = L.foldl (\acc (Hyp name ty _) -> Pi Zero name ty acc)

      -- arities extended with parameters
      extended_arities = zipWith extendArity arities paramss

      ctx_with_arities = reverse (zipWith (\name ty -> Hyp name ty Nothing) names extended_arities)

      checkCtor :: ElabState -> Context -> Int -> Int -> Ctor -> Either Error (Int, Term)
      checkCtor st ctx defno pno (loc, name, expr) = do
        (t, _, _) <- synth st ctx expr
        --u <- allOccurrencesPositive loc defcount defno pno pno (pno + defcount) t
        pure (0,t)

      checkCtorBlock :: ElabState -> Context ->  (Int, Context, [Ctor]) -> Either Error (Int, [Term])
      checkCtorBlock st ctx (defno, params, ctors) = do
        (us, ctors) <- unzip <$> mapM (checkCtor st (params ++ ctx_with_arities) defno (length params)) ctors
        pure (minimum (maxBound : us), ctors)

  (us, ctor_tys) <-
    runTypechecker $ \st ->
      unzip <$> mapM (checkCtorBlock st ctx_with_arities) (zip3 [0 ..] paramss ctorss)

  let -- abstracted ctors explicitly quantify over the datatype parameters
      abstractCtors :: Context -> [Term] -> [Term]
      abstractCtors params ctors =
        fmap (\acc -> L.foldl
                (\acc (Hyp name ty _) -> Pi Zero name ty acc) acc params) ctors

      abstracted_ctors = zipWith abstractCtors paramss ctor_tys

      upno = minimum us

      def_refs = fmap (\datano -> Ind block datano upno) [0 ..]

      def_consts = zipWith (\qname -> Top (intercalate "." qname)) qnames def_refs

      def_name_loc_refs = zip3 qnames def_locs def_refs

      ctor_instances = fmap (fmap (psubst (reverse def_consts))) abstracted_ctors

      ctor_refs =
        concat
          ( zipWith3
              ( \ctors params defno ->
                  fmap
                    (\ctorno -> Con block defno ctorno (length params))
                    [0 .. length ctors - 1]
              )
              ctor_instances
              paramss
              [0 ..]
          )

      ctor_locs = concatMap (fmap (\(loc, _, _) -> loc)) ctorss

      ctor_name_loc_refs = zip3 ctor_qnames ctor_locs ctor_refs

      name_loc_refs = ctor_name_loc_refs ++ def_name_loc_refs

  let objects = zipWith3 (\arity ctor_names ctor_types ->
        (arity, zip ctor_names ctor_types))
        extended_arities
        ctor_names
        ctor_instances
  --when (names == ["Acc"]) $ do
  --  traceM (unlines (concat (fmap (fmap (showTerm [])) ctor_tys)))
  --  traceM (unlines (concat (fmap (fmap (showTerm [])) abstracted_ctors)))
  --  traceM (unlines (concat (fmap (fmap (showTerm [])) ctor_instances)))
  
  --traceM (unlines (concat (fmap (fmap (showTerm [])) ctor_instances)))
  
  mapM_ insertName name_loc_refs

  modify (\st -> st {
    nextBlock = block + 1,
    signature = Signature
      (sigFixs (signature st))
      (sigDefs (signature st))
      (M.insert block objects (sigData (signature st)))})
  
{-
  let computeAux compute name defno dat = do
        def <- runTypechecker $ compute block defno dat

        runTypechecker $ runCore (showTerm def) >>= traceM >> traceM ""

        ty <- runTypechecker $ fst <$> runCore (infer def)
        block' <- gets nextBlock
        let qname = dataName dat
            ref = Fun block' 0 1 True
            name' = qname ++ [name]
            nlr = (name', emptyLoc, ref)
            fun = Function ty def
            obj = FunctionBlock maxBound True True [fun]

        modify
          ( \st ->
              st
                { nextBlock = block' + 1,
                  internalNames = updateNameSpace [nlr] (internalNames st),
                  Declaration.signature = second (M.insert block' obj) (Declaration.signature st)
                }
          )

  traceM $ show qnames ++ " defined"
-}

