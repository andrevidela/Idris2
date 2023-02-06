module TTImp.ProcessDef

import Core.Case.CaseBuilder
import Core.Case.CaseTree
import Core.Case.CaseTree.Pretty
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Coverage
import Core.Env
import Core.Hash
import Core.LinearCheck
import Core.Metadata
import Core.Normalise
import Core.Termination
import Core.Transform
import Core.Value
import Core.UnifyState

import Idris.REPL.Opts
import Idris.Syntax
import Idris.Pretty.Annotations

import TTImp.BindImplicits
import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Elab.Utils
import TTImp.Impossible
import TTImp.PartialEval
import TTImp.TTImp
import TTImp.TTImp.Functor
import TTImp.ProcessType
import TTImp.Unelab
import TTImp.WithClause
import TTImp.ProcessWith
import TTImp.CheckLHS

import Data.Either
import Data.List
import Libraries.Data.NameMap
import Data.String
import Data.Maybe
import Libraries.Text.PrettyPrint.Prettyprinter

%default covering

mutual
  mismatchNF : {auto c : Ref Ctxt Defs} ->
               {vars : _} ->
               Defs -> NF vars -> NF vars -> Core Bool
  mismatchNF defs (NTCon _ xn xt _ xargs) (NTCon _ yn yt _ yargs)
      = if xn /= yn
           then pure True
           else anyM (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs)
  mismatchNF defs (NDCon _ _ xt _ xargs) (NDCon _ _ yt _ yargs)
      = if xt /= yt
           then pure True
           else anyM (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs)
  mismatchNF defs (NPrimVal _ xc) (NPrimVal _ yc) = pure (xc /= yc)
  mismatchNF defs (NDelayed _ _ x) (NDelayed _ _ y) = mismatchNF defs x y
  mismatchNF defs (NDelay _ _ _ x) (NDelay _ _ _ y)
      = mismatchNF defs !(evalClosure defs x) !(evalClosure defs y)

  -- NPrimVal is apart from NDCon, NTCon, NBind, and NType
  mismatchNF defs (NPrimVal _ _) (NDCon _ _ _ _ _) = pure True
  mismatchNF defs (NDCon _ _ _ _ _) (NPrimVal _ _) = pure True
  mismatchNF defs (NPrimVal _ _) (NBind _ _ _ _) = pure True
  mismatchNF defs (NBind _ _ _ _) (NPrimVal _ _) = pure True
  mismatchNF defs (NPrimVal _ _) (NTCon _ _ _ _ _) = pure True
  mismatchNF defs (NTCon _ _ _ _ _) (NPrimVal _ _) = pure True
  mismatchNF defs (NPrimVal _ _) (NType _ _) = pure True
  mismatchNF defs (NType _ _) (NPrimVal _ _) = pure True

-- NTCon is apart from NBind, and NType
  mismatchNF defs (NTCon _ _ _ _ _) (NBind _ _ _ _) = pure True
  mismatchNF defs (NBind _ _ _ _) (NTCon _ _ _ _ _) = pure True
  mismatchNF defs (NTCon _ _ _ _ _) (NType _ _) = pure True
  mismatchNF defs (NType _ _) (NTCon _ _ _ _ _) = pure True

-- NBind is apart from NType
  mismatchNF defs (NBind _ _ _ _) (NType _ _) = pure True
  mismatchNF defs (NType _ _) (NBind _ _ _ _) = pure True

  mismatchNF _ _ _ = pure False

  mismatch : {auto c : Ref Ctxt Defs} ->
             {vars : _} ->
             Defs -> (Closure vars, Closure vars) -> Core Bool
  mismatch defs (x, y)
      = mismatchNF defs !(evalClosure defs x) !(evalClosure defs y)

-- If the terms have the same type constructor at the head, and one of
-- the argument positions has different constructors at its head, then this
-- is an impossible case, so return True
export
impossibleOK : {auto c : Ref Ctxt Defs} ->
               {vars : _} ->
               Defs -> NF vars -> NF vars -> Core Bool
impossibleOK defs (NTCon _ xn xt xa xargs) (NTCon _ yn yt ya yargs)
    = if xn /= yn
         then pure True
         else anyM (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs)
-- If it's a data constructor, any mismatch will do
impossibleOK defs (NDCon _ _ xt _ xargs) (NDCon _ _ yt _ yargs)
    = if xt /= yt
         then pure True
         else anyM (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs)
impossibleOK defs (NPrimVal _ x) (NPrimVal _ y) = pure (x /= y)

-- NPrimVal is apart from NDCon, NTCon, NBind, and NType
impossibleOK defs (NPrimVal _ _) (NDCon _ _ _ _ _) = pure True
impossibleOK defs (NDCon _ _ _ _ _) (NPrimVal _ _) = pure True
impossibleOK defs (NPrimVal _ _) (NBind _ _ _ _) = pure True
impossibleOK defs (NBind _ _ _ _) (NPrimVal _ _) = pure True
impossibleOK defs (NPrimVal _ _) (NTCon _ _ _ _ _) = pure True
impossibleOK defs (NTCon _ _ _ _ _) (NPrimVal _ _) = pure True
impossibleOK defs (NPrimVal _ _) (NType _ _) = pure True
impossibleOK defs (NType _ _) (NPrimVal _ _) = pure True

-- NTCon is apart from NBind, and NType
impossibleOK defs (NTCon _ _ _ _ _) (NBind _ _ _ _) = pure True
impossibleOK defs (NBind _ _ _ _) (NTCon _ _ _ _ _) = pure True
impossibleOK defs (NTCon _ _ _ _ _) (NType _ _) = pure True
impossibleOK defs (NType _ _) (NTCon _ _ _ _ _) = pure True

-- NBind is apart from NType
impossibleOK defs (NBind _ _ _ _) (NType _ _) = pure True
impossibleOK defs (NType _ _) (NBind _ _ _ _) = pure True

impossibleOK defs x y = pure False

export
impossibleErrOK : {auto c : Ref Ctxt Defs} ->
                  Defs -> Error -> Core Bool
impossibleErrOK defs (CantConvert fc gam env l r)
    = do let defs = { gamma := gam } defs
         impossibleOK defs !(nf defs env l)
                           !(nf defs env r)
impossibleErrOK defs (CantSolveEq fc gam env l r)
    = do let defs = { gamma := gam } defs
         impossibleOK defs !(nf defs env l)
                           !(nf defs env r)
impossibleErrOK defs (BadDotPattern _ _ ErasedArg _ _) = pure True
impossibleErrOK defs (CyclicMeta _ _ _ _) = pure True
impossibleErrOK defs (AllFailed errs)
    = anyM (impossibleErrOK defs) (map snd errs)
impossibleErrOK defs (WhenUnifying _ _ _ _ _ err)
    = impossibleErrOK defs err
impossibleErrOK defs _ = pure False

-- If it's a clause we've generated, see if the error is recoverable. That
-- is, if we have a concrete thing, and we're expecting the same concrete
-- thing, or a function of something, then we might have a match.
export
recoverable : {auto c : Ref Ctxt Defs} ->
              {vars : _} ->
              Defs -> NF vars -> NF vars -> Core Bool
-- Unlike the above, any mismatch will do

-- TYPE CONSTRUCTORS
recoverable defs (NTCon _ xn xt xa xargs) (NTCon _ yn yt ya yargs)
    = if xn /= yn
         then pure False
         else pure $ not !(anyM (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs))
-- Type constructor vs. primitive type
recoverable defs (NTCon _ _ _ _ _) (NPrimVal _ _) = pure False
recoverable defs (NPrimVal _ _) (NTCon _ _ _ _ _) = pure False
-- Type constructor vs. type
recoverable defs (NTCon _ _ _ _ _) (NType _ _) = pure False
recoverable defs (NType _ _) (NTCon _ _ _ _ _) = pure False
-- Type constructor vs. binder
recoverable defs (NTCon _ _ _ _ _) (NBind _ _ _ _) = pure False
recoverable defs (NBind _ _ _ _) (NTCon _ _ _ _ _) = pure False

recoverable defs (NTCon _ _ _ _ _) _ = pure True
recoverable defs _ (NTCon _ _ _ _ _) = pure True

-- DATA CONSTRUCTORS
recoverable defs (NDCon _ _ xt _ xargs) (NDCon _ _ yt _ yargs)
    = if xt /= yt
         then pure False
         else pure $ not !(anyM (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs))
-- Data constructor vs. primitive constant
recoverable defs (NDCon _ _ _ _ _) (NPrimVal _ _) = pure False
recoverable defs (NPrimVal _ _) (NDCon _ _ _ _ _) = pure False

recoverable defs (NDCon _ _ _ _ _) _ = pure True
recoverable defs _ (NDCon _ _ _ _ _) = pure True

-- FUNCTION CALLS
recoverable defs (NApp _ (NRef _ f) fargs) (NApp _ (NRef _ g) gargs)
    = pure True -- both functions; recoverable

-- PRIMITIVES
recoverable defs (NPrimVal _ x) (NPrimVal _ y) = pure (x == y)
-- primitive vs. binder
recoverable defs (NPrimVal _ _) (NBind _ _ _ _) = pure False
recoverable defs (NBind _ _ _ _) (NPrimVal _ _) = pure False

-- OTHERWISE: no
recoverable defs x y = pure False

export
recoverableErr : {auto c : Ref Ctxt Defs} ->
                 Defs -> Error -> Core Bool
recoverableErr defs (CantConvert fc gam env l r)
  = do let defs = { gamma := gam } defs
       l <- nf defs env l
       r <- nf defs env r
       log "coverage.recover" 10 $ unlines
         [ "Recovering from CantConvert?"
         , "Checking:"
         , "  " ++ show l
         , "  " ++ show r
         ]
       recoverable defs l r

recoverableErr defs (CantSolveEq fc gam env l r)
  = do let defs = { gamma := gam } defs
       recoverable defs !(nf defs env l)
                        !(nf defs env r)
recoverableErr defs (BadDotPattern _ _ ErasedArg _ _) = pure True
recoverableErr defs (CyclicMeta _ _ _ _) = pure False
recoverableErr defs (AllFailed errs)
    = anyM (recoverableErr defs) (map snd errs)
recoverableErr defs (WhenUnifying _ _ _ _ _ err)
    = recoverableErr defs err
recoverableErr defs _ = pure False

-- Return whether any of the pattern variables are in a trivially empty
-- type, where trivally empty means one of:
--  * No constructors
--  * Every constructor of the family has a return type which conflicts with
--    the given constructor's type
hasEmptyPat : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              Defs -> Env Term vars -> Term vars -> Core Bool
hasEmptyPat defs env (Bind fc x b sc)
   = pure $ !(isEmpty defs env !(nf defs env (binderType b)))
            || !(hasEmptyPat defs (b :: env) sc)
hasEmptyPat defs env _ = pure False


-- Check a pattern clause, returning the component of the 'Case' expression it
-- represents, or Nothing if it's an impossible clause
export
checkClause : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
              (mult : RigCount) -> (vis : Visibility) ->
              (totreq : TotalReq) -> (hashit : Bool) ->
              Int -> List ElabOpt -> NestedNames vars -> Env Term vars ->
              ImpClause -> Core (Either RawImp Clause)
checkClause mult vis totreq hashit n opts nest env (ImpossibleClause fc lhs)
    = do lhs_raw <- lhsInCurrentNS nest lhs
         handleUnify
           (do autoimp <- isUnboundImplicits
               setUnboundImplicits True
               (_, lhs) <- bindNames False lhs_raw
               setUnboundImplicits autoimp

               log "declare.def.clause.impossible" 5 $ "Checking " ++ show lhs
               logEnv "declare.def.clause.impossible" 5 "In env" env
               (lhstm, lhstyg) <-
                           elabTerm n (InLHS mult) opts nest env
                                      (IBindHere fc PATTERN lhs) Nothing
               defs <- get Ctxt
               lhs <- normaliseHoles defs env lhstm
               if !(hasEmptyPat defs env lhs)
                  then pure (Left lhs_raw)
                  else throw (ValidCase fc env (Left lhs)))
           (\err =>
              case err of
                   ValidCase _ _ _ => throw err
                   _ => do defs <- get Ctxt
                           if !(impossibleErrOK defs err)
                              then pure (Left lhs_raw)
                              else throw (ValidCase fc env (Right err)))
checkClause {vars} mult vis totreq hashit n opts nest env (PatClause fc lhs_in rhs)
    = do (_, (vars'  ** (sub', env', nest', lhstm', lhsty'))) <-
             checkLHS False mult n opts nest env fc lhs_in
         let rhsMode = if isErased mult then InType else InExpr
         log "declare.def.clause" 5 $ "Checking RHS " ++ show rhs
         logEnv "declare.def.clause" 5 "In env" env'

         rhstm <- logTime 3 ("Check RHS " ++ show fc) $
                    wrapErrorC opts (InRHS fc !(getFullName (Resolved n))) $
                       checkTermSub n rhsMode opts nest' env' env sub' rhs (gnf env' lhsty')
         clearHoleLHS

         logTerm "declare.def.clause" 3 "RHS term" rhstm
         when hashit $
           do addHashWithNames lhstm'
              addHashWithNames rhstm
              log "module.hash" 15 "Adding hash for def."

         -- If the rhs is a hole, record the lhs in the metadata because we
         -- might want to split it interactively
         case rhstm of
              Meta _ _ _ _ =>
                 addLHS (getFC lhs_in) (length env) env' lhstm'
              _ => pure ()

         pure (Right (MkClause env' lhstm' rhstm))
checkClause {vars} mult vis totreq hashit n opts nest env
    (WithClause ifc lhs_in rig wval_raw mprf flags cs)
    = processWith {vars} mult vis totreq hashit n opts nest env
                  ifc lhs_in rig wval_raw mprf flags cs

nameListEq : (xs : List Name) -> (ys : List Name) -> Maybe (xs = ys)
nameListEq [] [] = Just Refl
nameListEq (x :: xs) (y :: ys) with (nameEq x y)
  nameListEq (x :: xs) (x :: ys) | (Just Refl) with (nameListEq xs ys)
    nameListEq (x :: xs) (x :: xs) | (Just Refl) | Just Refl= Just Refl
    nameListEq (x :: xs) (x :: ys) | (Just Refl) | Nothing = Nothing
  nameListEq (x :: xs) (y :: ys) | Nothing = Nothing
nameListEq _ _ = Nothing

-- Calculate references for the given name, and recursively if they haven't
-- been calculated already
calcRefs : {auto c : Ref Ctxt Defs} ->
           (runtime : Bool) -> (aTotal : Name) -> (fn : Name) -> Core ()
calcRefs rt at fn
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact fn (gamma defs)
              | _ => pure ()
         let PMDef r cargs tree_ct tree_rt pats = definition gdef
              | _ => pure () -- not a function definition
         let refs : Maybe (NameMap Bool)
                  = if rt then refersToRuntimeM gdef else refersToM gdef
         let Nothing = refs
              | Just _ => pure () -- already done
         let tree : CaseTree cargs = if rt then tree_rt else tree_ct
         let metas = CaseTree.getMetas tree
         traverse_ addToSave (keys metas)
         let refs_all = addRefs at metas tree
         refs <- ifThenElse rt
                    (dropErased (keys refs_all) refs_all)
                    (pure refs_all)
         ignore $ ifThenElse rt
            (addDef fn ({ refersToRuntimeM := Just refs } gdef))
            (addDef fn ({ refersToM := Just refs } gdef))
         traverse_ (calcRefs rt at) (keys refs)
  where
    dropErased : List Name -> NameMap Bool -> Core (NameMap Bool)
    dropErased [] refs = pure refs
    dropErased (n :: ns) refs
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => dropErased ns refs
             if multiplicity gdef /= erased
                then dropErased ns refs
                else dropErased ns (delete n refs)

-- Compile run time case trees for the given name
mkRunTime : {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto o : Ref ROpts REPLOpts} ->
            FC -> Name -> Core ()
mkRunTime fc n
    = do log "compile.casetree" 5 $ "Making run time definition for " ++ show !(toFullNames n)
         defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | _ => pure ()
         let cov = gdef.totality.isCovering
         -- If it's erased at run time, don't build the tree
         when (not (isErased $ multiplicity gdef)) $ do
           let PMDef r cargs tree_ct _ pats = definition gdef
                | _ => pure () -- not a function definition
           let ty = type gdef
           -- Prepare RHS of definitions, by erasing 0-multiplicities, and
           -- finding any applications to specialise (partially evaluate)
           pats' <- traverse (toErased (location gdef) (getSpec (flags gdef)))
                             pats

           let clauses_init = map (toClause (location gdef)) pats'
           let clauses = case cov of
                              MissingCases _ => addErrorCase clauses_init
                              _ => clauses_init

           (rargs ** (tree_rt, _)) <- getPMDef (location gdef) RunTime n ty clauses
           logC "compile.casetree" 5 $ do
             tree_rt <- toFullNames tree_rt
             pure $ unlines
               [ show cov ++ ":"
               , "Runtime tree for " ++ show (fullname gdef) ++ ":"
               , show (indent 2 $ prettyTree tree_rt)
               ]
           log "compile.casetree" 10 $ show tree_rt
           log "compile.casetree.measure" 15 $ show (measure tree_rt)

           let Just Refl = nameListEq cargs rargs
                   | Nothing => throw (InternalError "WAT")
           ignore $ addDef n $
                       { definition := PMDef r rargs tree_ct tree_rt pats
                       } gdef
           -- If it's a case block, and not already set as inlinable or forced
           -- to not be inlinable, check if it's safe to inline
           when (caseName !(toFullNames n) && noInline (flags gdef)) $
             do inl <- canInlineCaseBlock n
                when inl $ do
                  log "compiler.inline.eval" 5 "Marking \{show !(toFullNames n)} for inlining in runtime case tree."
                  setFlag fc n Inline
  where
    -- check if the flags contain explicit inline or noinline directives:
    noInline : List DefFlag -> Bool
    noInline (Inline :: _)   = False
    noInline (NoInline :: _) = False
    noInline (x :: xs) = noInline xs
    noInline _ = True

    caseName : Name -> Bool
    caseName (CaseBlock _ _) = True
    caseName (NS _ n) = caseName n
    caseName _ = False

    mkCrash : {vars : _} -> String -> Term vars
    mkCrash msg
       = apply fc (Ref fc Func (NS builtinNS (UN $ Basic "idris_crash")))
               [Erased fc Placeholder, PrimVal fc (Str msg)]

    matchAny : Term vars -> Term vars
    matchAny (App fc f a) = App fc (matchAny f) (Erased fc Placeholder)
    matchAny tm = tm

    makeErrorClause : {vars : _} -> Env Term vars -> Term vars -> Clause
    makeErrorClause env lhs
        = MkClause env (matchAny lhs)
             (mkCrash ("Unhandled input for " ++ show n ++ " at " ++ show fc))

    addErrorCase : List Clause -> List Clause
    addErrorCase [] = []
    addErrorCase [MkClause env lhs rhs]
        = MkClause env lhs rhs :: makeErrorClause env lhs :: []
    addErrorCase (x :: xs) = x :: addErrorCase xs

    getSpec : List DefFlag -> Maybe (List (Name, Nat))
    getSpec [] = Nothing
    getSpec (PartialEval n :: _) = Just n
    getSpec (x :: xs) = getSpec xs

    toErased : FC -> Maybe (List (Name, Nat)) ->
               (vars ** (Env Term vars, Term vars, Term vars)) ->
               Core (vars ** (Env Term vars, Term vars, Term vars))
    toErased fc spec (_ ** (env, lhs, rhs))
        = do lhs_erased <- linearCheck fc linear True env lhs
             -- Partially evaluate RHS here, where appropriate
             rhs' <- applyTransforms env rhs
             rhs' <- applySpecialise env spec rhs'
             rhs_erased <- linearCheck fc linear True env rhs'
             pure (_ ** (env, lhs_erased, rhs_erased))

    toClause : FC -> (vars ** (Env Term vars, Term vars, Term vars)) -> Clause
    toClause fc (_ ** (env, lhs, rhs))
        = MkClause env lhs rhs

compileRunTime : {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 FC -> Name -> Core ()
compileRunTime fc atotal
    = do defs <- get Ctxt
         traverse_ (mkRunTime fc) (toCompileCase defs)
         traverse_ (calcRefs True atotal) (toCompileCase defs)

         update Ctxt { toCompileCase := [] }

toPats : Clause -> (vs ** (Env Term vs, Term vs, Term vs))
toPats (MkClause {vars} env lhs rhs)
    = (_ ** (env, lhs, rhs))

warnUnreachable : {auto c : Ref Ctxt Defs} ->
                  Clause -> Core ()
warnUnreachable (MkClause env lhs rhs)
    = recordWarning (UnreachableClause (getLoc lhs) env lhs)

isAlias : RawImp -> Maybe ((FC, Name)                -- head symbol
                          , List (FC, (FC, String))) -- pattern variables
isAlias lhs
  = do let (hd, apps) = getFnArgs lhs []
       hd <- isIVar hd
       args <- traverse (isExplicit >=> bitraverse pure isIBindVar) apps
       pure (hd, args)

lookupOrAddAlias : {vars : _} ->
                   {auto m : Ref MD Metadata} ->
                   {auto c : Ref Ctxt Defs} ->
                   {auto u : Ref UST UState} ->
                   {auto s : Ref Syn SyntaxInfo} ->
                   {auto o : Ref ROpts REPLOpts} ->
                   List ElabOpt -> NestedNames vars -> Env Term vars -> FC ->
                   Name -> List ImpClause -> Core (Maybe GlobalDef)
lookupOrAddAlias eopts nest env fc n [cl@(PatClause _ lhs _)]
  = do defs <- get Ctxt
       log "declare.def.alias" 20 $ "Looking at \{show cl}"
       Nothing <- lookupCtxtExact n (gamma defs)
         | Just gdef => pure (Just gdef)
       -- No prior declaration:
       --   1) check whether it has the shape of an alias
       let Just (hd, args) = isAlias lhs
         | Nothing => pure Nothing
       --   2) check whether it could be a misspelling
       log "declare.def" 5 $
         "Missing type declaration for the alias "
         ++ show n
         ++ ". Checking first whether it is a misspelling."
       [] <- do -- get the candidates
                Just (str, kept) <- getSimilarNames n
                   | Nothing => pure []
                -- only keep the ones that haven't been defined yet
                decls <- for kept $ \ (cand, weight) => do
                    Just gdef <- lookupCtxtExact cand (gamma defs)
                      | Nothing => pure Nothing -- should be impossible
                    let None = definition gdef
                      | _ => pure Nothing
                    pure (Just (cand, weight))
                pure $ showSimilarNames (currentNS defs) n str $ catMaybes decls
          | (x :: xs) => throw (MaybeMisspelling (NoDeclaration fc n) (x ::: xs))
       --   3) declare an alias
       log "declare.def" 5 "Not a misspelling: go ahead and declare it!"
       processType eopts nest env fc top Public []
          $ MkImpTy fc fc n $ holeyType (map snd args)
       defs <- get Ctxt
       lookupCtxtExact n (gamma defs)

  where
    holeyType : List (FC, String) -> RawImp
    holeyType [] = Implicit fc False
    holeyType ((xfc, x) :: xs)
      = let xfc = virtualiseFC xfc in
        IPi xfc top Explicit (Just (UN $ Basic x)) (Implicit xfc False)
      $ holeyType xs

lookupOrAddAlias _ _ _ fc n _
  = do defs <- get Ctxt
       lookupCtxtExact n (gamma defs)

||| Process a top-level definition
||| @ fc the position of the definition
||| @ n_in the name of the definition
||| @ cs_in the list of clauses associated with the definition
export
processDef : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto o : Ref ROpts REPLOpts} ->
             List ElabOpt -> NestedNames vars -> Env Term vars -> FC ->
             Name -> List ImpClause -> Core ()
processDef opts nest env fc n_in cs_in
    = do n <- inCurrentNS n_in
         defs <- get Ctxt
         Just gdef <- lookupOrAddAlias opts nest env fc n cs_in
           | Nothing => noDeclaration fc n
         let None = definition gdef
              | _ => throw (AlreadyDefined fc n)
         let ty = type gdef
         -- a module's interface hash (what determines when the module has changed)
         -- should include the definition (RHS) of anything that is public (available
         -- at compile time for elaboration) _or_ inlined (dropped into destination definitions
         -- during compilation).
         let hashit = visibility gdef == Public || (Inline `elem` gdef.flags)
         let mult = if isErased (multiplicity gdef)
                       then erased
                       else linear
         nidx <- resolveName n

         -- Dynamically rebind default totality requirement to this function's totality requirement
         -- and use this requirement when processing `with` blocks
         log "declare.def" 5 $ "Traversing clauses of " ++ show n ++ " with mult " ++ show mult
         let treq = fromMaybe !getDefaultTotalityOption (findSetTotal (flags gdef))
         cs <- withTotality treq $
               traverse (checkClause mult (visibility gdef) treq
                                     hashit nidx opts nest env) cs_in

         let pats = map toPats (rights cs)

         (cargs ** (tree_ct, unreachable)) <-
             logTime 3 ("Building compile time case tree for " ++ show n) $
                getPMDef fc (CompileTime mult) n ty (rights cs)

         traverse_ warnUnreachable unreachable

         logC "declare.def" 2 $
                 do t <- toFullNames tree_ct
                    pure ("Case tree for " ++ show n ++ ": " ++ show t)

         -- check whether the name was declared in a different source file
         defs <- get Ctxt
         let pi = case lookup n (userHoles defs) of
                        Nothing => defaultPI
                        Just e => { externalDecl := e } defaultPI
         -- Add compile time tree as a placeholder for the runtime tree,
         -- but we'll rebuild that in a later pass once all the case
         -- blocks etc are resolved
         ignore $ addDef (Resolved nidx)
                  ({ definition := PMDef pi cargs tree_ct tree_ct pats
                   } gdef)

         when (visibility gdef == Public) $
             do let rmetas = getMetas tree_ct
                log "declare.def" 10 $ "Saving from " ++ show n ++ ": " ++ show (keys rmetas)
                traverse_ addToSave (keys rmetas)
         when (isUserName n && visibility gdef /= Private) $
             do let tymetas = getMetas (type gdef)
                traverse_ addToSave (keys tymetas)
         addToSave n

         -- Flag this name as one which needs compiling
         update Ctxt { toCompileCase $= (n ::) }

         atotal <- toResolvedNames (NS builtinNS (UN $ Basic "assert_total"))
         logTime 3 ("Building size change graphs " ++ show n) $
           when (not (InCase `elem` opts)) $
             do calcRefs False atotal (Resolved nidx)
                sc <- calculateSizeChange fc n
                setSizeChange fc n sc
                checkIfGuarded fc n

         md <- get MD -- don't need the metadata collected on the coverage check

         cov <- logTime 3 ("Checking Coverage " ++ show n) $ checkCoverage nidx ty mult cs
         setCovering fc n cov
         put MD md

         -- If we're not in a case tree, compile all the outstanding case
         -- trees.
         when (not (elem InCase opts)) $
              compileRunTime fc atotal
  where
    -- Move `withTotality` to Core.Context if we need it elsewhere
    ||| Temporarily rebind the default totality requirement (%default total/partial/covering).
    withTotality : TotalReq -> Lazy (Core a) -> Core a
    withTotality tot c = do
         defaultTotality <- getDefaultTotalityOption
         setDefaultTotalityOption tot
         x <- catch c (\error => do setDefaultTotalityOption defaultTotality
                                    throw error)
         setDefaultTotalityOption defaultTotality
         pure x


    simplePat : forall vars . Term vars -> Bool
    simplePat (Local _ _ _ _) = True
    simplePat (Erased _ _) = True
    simplePat (As _ _ _ p) = simplePat p
    simplePat _ = False

    -- Is the clause returned from 'checkClause' a catch all clause, i.e.
    -- one where all the arguments are variables? If so, no need to do the
    -- (potentially expensive) coverage check
    catchAll : Clause -> Bool
    catchAll (MkClause env lhs _)
       = all simplePat (getArgs lhs)

    -- Return 'Nothing' if the clause is impossible, otherwise return the
    -- checked clause (with implicits filled in, so that we can see if they
    -- match any of the given clauses)
    checkImpossible : Int -> RigCount -> ClosedTerm ->
                      Core (Maybe ClosedTerm)
    checkImpossible n mult tm
        = do itm <- unelabNoPatvars [] tm
             let itm = map rawName itm
             handleUnify
               (do ctxt <- get Ctxt
                   log "declare.def.impossible" 3 $ "Checking for impossibility: " ++ show itm
                   autoimp <- isUnboundImplicits
                   setUnboundImplicits True
                   (_, lhstm) <- bindNames False itm
                   setUnboundImplicits autoimp
                   (lhstm, _) <- elabTerm n (InLHS mult) [] (MkNested []) []
                                    (IBindHere fc COVERAGE lhstm) Nothing
                   defs <- get Ctxt
                   lhs <- normaliseHoles defs [] lhstm
                   if !(hasEmptyPat defs [] lhs)
                      then do log "declare.def.impossible" 5 "Some empty pat"
                              put Ctxt ctxt
                              pure Nothing
                      else do log "declare.def.impossible" 5 "No empty pat"
                              empty <- clearDefs ctxt
                              rtm <- closeEnv empty !(nf empty [] lhs)
                              put Ctxt ctxt
                              pure (Just rtm))
               (\err => do defs <- get Ctxt
                           if not !(recoverableErr defs err)
                              then pure Nothing
                              else pure (Just tm))
      where
        closeEnv : Defs -> NF [] -> Core ClosedTerm
        closeEnv defs (NBind _ x (PVar _ _ _ _) sc)
            = closeEnv defs !(sc defs (toClosure defaultOpts [] (Ref fc Bound x)))
        closeEnv defs nf = quote defs [] nf

    getClause : Either RawImp Clause -> Core (Maybe Clause)
    getClause (Left rawlhs)
        = catch (do lhsp <- getImpossibleTerm env nest rawlhs
                    log "declare.def.impossible" 3 $ "Generated impossible LHS: " ++ show lhsp
                    pure $ Just $ MkClause [] lhsp (Erased (getFC rawlhs) Impossible))
                (\e => do log "declare.def" 5 $ "Error in getClause " ++ show e
                          pure Nothing)
    getClause (Right c) = pure (Just c)

    checkCoverage : Int -> ClosedTerm -> RigCount ->
                    List (Either RawImp Clause) ->
                    Core Covering
    checkCoverage n ty mult cs
        = do covcs' <- traverse getClause cs -- Make stand in LHS for impossible clauses
             log "declare.def" 5 $ unlines
               $ "Using clauses :"
               :: map (("  " ++) . show) !(traverse toFullNames covcs')
             let covcs = mapMaybe id covcs'
             (_ ** (ctree, _)) <-
                 getPMDef fc (CompileTime mult) (Resolved n) ty covcs
             log "declare.def" 3 $ "Working from " ++ show !(toFullNames ctree)
             missCase <- if any catchAll covcs
                            then do log "declare.def" 3 $ "Catch all case in " ++ show n
                                    pure []
                            else getMissing fc (Resolved n) ctree
             logC "declare.def" 3 $
                     do mc <- traverse toFullNames missCase
                        pure ("Initially missing in " ++
                                 show !(getFullName (Resolved n)) ++ ":\n" ++
                                showSep "\n" (map show mc))
             -- Filter out the ones which are impossible
             missImp <- traverse (checkImpossible n mult) missCase
             -- Filter out the ones which are actually matched (perhaps having
             -- come up due to some overlapping patterns)
             missMatch <- traverse (checkMatched covcs) (mapMaybe id missImp)
             let miss = catMaybes missMatch
             if isNil miss
                then do [] <- getNonCoveringRefs fc (Resolved n)
                           | ns => toFullNames (NonCoveringCall ns)
                        pure IsCovering
                else pure (MissingCases miss)
