-- Module to elaborate with clauses used in `TTImp.ProcessDef`
module TTImp.ProcessWith

import Core.Context
import Core.Core
import Core.Env
import Core.FC
import Core.Metadata
import Core.Name
import Core.TT
import Core.UnifyState
import Core.Value

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.BindImplicits
import TTImp.TTImp
import TTImp.CheckLHS
import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Elab.Utils
import TTImp.WithClause

-- For checking with blocks as nested names
applyEnv : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           Env Term vars -> Name ->
           Core (Name, (Maybe Name, List (Var vars), FC -> NameType -> Term vars))
applyEnv env withname
    = do n' <- resolveName withname
         pure (withname, (Just withname, reverse (allVarsNoLet env),
                  \fc, nt => applyTo fc
                         (Ref fc nt (Resolved n')) env))

export
processWith :
      {vars : List Name}
   -> {auto o : Ref ROpts REPLOpts}
   -> {auto s : Ref Syn SyntaxInfo}
   -> {auto u : Ref UST UState}
   -> {auto m : Ref MD Metadata}
   -> {auto c : Ref Ctxt Defs}
   -> (mult : ZeroOneOmega)
   -> (vis : Visibility)
   -> (totreq : TotalReq)
   -> (hashit : Bool)
   -> (n : Int)
   -> (opts : List ElabOpt)
   -> (nest : NestedNames vars)
   -> (env : Env Term vars)
   -> (ifc : FC)
   -> (lhs_in : RawImp' Name)
   -> (rig : ZeroOneOmega)
   -> (wval_raw : RawImp' Name)
   -> (mprf : Maybe Name)
   -> (flags : List WithFlag)
   -> (cs : List (ImpClause' Name))
   -> Core (Either (RawImp' Name) Clause)
processWith {vars} mult vis totreq hashit n opts nest env
    ifc lhs_in rig wval_raw mprf flags cs
    = do (lhs, (vars'  ** (sub', env', nest', lhspat, reqty))) <-
             checkLHS False mult n opts nest env ifc lhs_in
         let wmode
               = if isErased mult || isErased rig then InType else InExpr

         (wval, gwvalTy) <- wrapErrorC opts (InRHS ifc !(getFullName (Resolved n))) $
                elabTermSub n wmode opts nest' env' env sub' wval_raw Nothing
         clearHoleLHS

         logTerm "declare.def.clause.with" 5 "With value (at quantity \{show rig})" wval
         logTerm "declare.def.clause.with" 3 "Required type" reqty
         wvalTy <- getTerm gwvalTy
         defs <- get Ctxt
         wval <- normaliseHoles defs env' wval
         wvalTy <- normaliseHoles defs env' wvalTy

         let (wevars ** withSub) = keepOldEnv sub' (snd (findSubEnv env' wval))
         logTerm "declare.def.clause.with" 5 "With value type" wvalTy
         log "declare.def.clause.with" 5 $ "Using vars " ++ show wevars

         let Just wval = shrinkTerm wval withSub
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #1")
         let Just wvalTy = shrinkTerm wvalTy withSub
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #2")
         -- Should the env be normalised too? If the following 'impossible'
         -- error is ever thrown, that might be the cause!
         let Just wvalEnv = shrinkEnv env' withSub
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #3")

         -- Abstracting over 'wval' in the scope of bNotReq in order
         -- to get the 'magic with' behaviour
         (wargs ** (scenv, var, binder)) <- bindWithArgs rig wvalTy ((,wval) <$> mprf) wvalEnv

         let bnr = bindNotReq vfc 0 env' withSub [] reqty
         let notreqns = fst bnr
         let notreqty = snd bnr

         rdefs <- if Syntactic `elem` flags
                     then clearDefs defs
                     else pure defs
         wtyScope <- replace rdefs scenv !(nf rdefs scenv (weakenNs (mkSizeOf wargs) wval))
                            var
                            !(nf rdefs scenv
                                 (weakenNs (mkSizeOf wargs) notreqty))
         let bNotReq = binder wtyScope

         -- The environment has some implicit and some explcit args, potentially,
         -- which is inconvenient since we have to know which is which when
         -- elaborating the application of the rhs function. So it's easier
         -- if we just make them all explicit - this type isn't visible to
         -- users anyway!
         let env' = mkExplicit env'

         let Just (reqns, envns, wtype) = bindReq vfc env' withSub [] bNotReq
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #4")

         -- list of argument names - 'Just' means we need to match the name
         -- in the with clauses to find out what the pattern should be.
         -- 'Nothing' means it's the with pattern (so wargn)
         let wargNames
                 = map Just reqns ++
                   Nothing :: map Just notreqns

         logTerm "declare.def.clause.with" 3 "With function type" wtype
         log "declare.def.clause.with" 5 $ "Argument names " ++ show wargNames

         wname <- genWithName !(prettyName !(toFullNames (Resolved n)))
         widx <- addDef wname ({flags $= (SetTotal totreq ::)}
                                    (newDef vfc wname (if isErased mult then erased else top)
                                      vars wtype vis None))

         let toWarg : Maybe (PiInfo RawImp, Name) -> List (Maybe Name, RawImp)
               := flip maybe (\pn => [(Nothing, IVar vfc (snd pn))]) $
                    (Nothing, wval_raw) ::
                    case mprf of
                      Nothing => []
                      Just _  =>
                       let fc = emptyFC in
                       let refl = IVar fc (NS builtinNS (UN $ Basic "Refl")) in
                       [(mprf, INamedApp fc refl (UN $ Basic "x") wval_raw)]

         let rhs_in = gapply (IVar vfc wname)
                    $ map (\ nm => (Nothing, IVar vfc nm)) envns
                   ++ concatMap toWarg wargNames

         log "declare.def.clause.with" 3 $ "Applying to with argument " ++ show rhs_in
         rhs <- wrapErrorC opts (InRHS ifc !(getFullName (Resolved n))) $
             checkTermSub n wmode opts nest' env' env sub' rhs_in
                          (gnf env' reqty)

         -- Generate new clauses by rewriting the matched arguments
         cs' <- traverse (mkClauseWith 1 wname wargNames lhs) cs
         log "declare.def.clause.with" 3 $ "With clauses: " ++ show cs'

         -- Elaborate the new definition here
         nestname <- applyEnv env wname
         let nest'' = { names $= (nestname ::) } nest

         let wdef = IDef ifc wname cs'
         processDecl [] nest'' env wdef

         pure (Right (MkClause env' lhspat rhs))
  where
    vfc : FC
    vfc = virtualiseFC ifc

    mkExplicit : forall vs . Env Term vs -> Env Term vs
    mkExplicit [] = []
    mkExplicit (Pi fc c _ ty :: env) = Pi fc c Explicit ty :: mkExplicit env
    mkExplicit (b :: env) = b :: mkExplicit env

    bindWithArgs :
       (rig : RigCount) -> (wvalTy : Term xs) -> Maybe (Name, Term xs) ->
       (wvalEnv : Env Term xs) ->
       Core (ext : List Name
         ** ( Env Term (ext ++ xs)
            , Term (ext ++ xs)
            , (Term (ext ++ xs) -> Term xs)
            ))
    bindWithArgs {xs} rig wvalTy Nothing wvalEnv =
      let wargn : Name
          wargn = MN "warg" 0
          wargs : List Name
          wargs = [wargn]

          scenv : Env Term (wargs ++ xs)
                := Pi vfc top Explicit wvalTy :: wvalEnv

          var : Term (wargs ++ xs)
              := Local vfc (Just False) Z First

          binder : Term (wargs ++ xs) -> Term xs
                 := Bind vfc wargn (Pi vfc rig Explicit wvalTy)

      in pure (wargs ** (scenv, var, binder))

    bindWithArgs {xs} rig wvalTy (Just (name, wval)) wvalEnv = do
      defs <- get Ctxt

      let eqName = NS builtinNS (UN $ Basic "Equal")
      Just (TCon t ar _ _ _ _ _ _) <- lookupDefExact eqName (gamma defs)
        | _ => throw (InternalError "Cannot find builtin Equal")
      let eqTyCon = Ref vfc (TyCon t ar) !(toResolvedNames eqName)

      let wargn : Name
          wargn = MN "warg" 0
          wargs : List Name
          wargs = [name, wargn]

          wvalTy' := weaken wvalTy
          eqTy : Term (MN "warg" 0 :: xs)
               := apply vfc eqTyCon
                           [ wvalTy'
                           , wvalTy'
                           , weaken wval
                           , Local vfc (Just False) Z First
                           ]

          scenv : Env Term (wargs ++ xs)
                := Pi vfc top Implicit eqTy
                :: Pi vfc top Explicit wvalTy
                :: wvalEnv

          var : Term (wargs ++ xs)
              := Local vfc (Just False) (S Z) (Later First)

          binder : Term (wargs ++ xs) -> Term xs
                 := \ t => Bind vfc wargn (Pi vfc rig Explicit wvalTy)
                         $ Bind vfc name  (Pi vfc rig Implicit eqTy) t

      pure (wargs ** (scenv, var, binder))

    -- If it's 'KeepCons/SubRefl' in 'outprf', that means it was in the outer
    -- environment so we need to keep it in the same place in the 'with'
    -- function. Hence, turn it to KeepCons whatever
    keepOldEnv : {0 outer : _} -> {vs : _} ->
                 (outprf : SubVars outer vs) -> SubVars vs' vs ->
                 (vs'' : List Name ** SubVars vs'' vs)
    keepOldEnv {vs} SubRefl p = (vs ** SubRefl)
    keepOldEnv {vs} p SubRefl = (vs ** SubRefl)
    keepOldEnv (DropCons p) (DropCons p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** DropCons rest)
    keepOldEnv (DropCons p) (KeepCons p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** KeepCons rest)
    keepOldEnv (KeepCons p) (DropCons p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** KeepCons rest)
    keepOldEnv (KeepCons p) (KeepCons p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** KeepCons rest)

    -- Rewrite the clauses in the block to use an updated LHS.
    -- 'drop' is the number of additional with arguments we expect
    -- (i.e. the things to drop from the end before matching LHSs)
    mkClauseWith : (drop : Nat) -> Name ->
                   List (Maybe (PiInfo RawImp, Name)) ->
                   RawImp -> ImpClause ->
                   Core ImpClause
    mkClauseWith drop wname wargnames lhs (PatClause ploc patlhs rhs)
        = do log "declare.def.clause.with" 20 "PatClause"
             newlhs <- getNewLHS ploc drop nest wname wargnames lhs patlhs
             newrhs <- withRHS ploc drop wname wargnames rhs lhs
             pure (PatClause ploc newlhs newrhs)
    mkClauseWith drop wname wargnames lhs (WithClause ploc patlhs rig wval prf flags ws)
        = do log "declare.def.clause.with" 20 "WithClause"
             newlhs <- getNewLHS ploc drop nest wname wargnames lhs patlhs
             newwval <- withRHS ploc drop wname wargnames wval lhs
             ws' <- traverse (mkClauseWith (S drop) wname wargnames lhs) ws
             pure (WithClause ploc newlhs rig newwval prf flags ws')
    mkClauseWith drop wname wargnames lhs (ImpossibleClause ploc patlhs)
        = do log "declare.def.clause.with" 20 "ImpossibleClause"
             newlhs <- getNewLHS ploc drop nest wname wargnames lhs patlhs
             pure (ImpossibleClause ploc newlhs)
