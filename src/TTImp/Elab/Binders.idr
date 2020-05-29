module TTImp.Elab.Binders

import Data.Maybe

import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.TTImp

%default covering

-- Drop the name from the nested function declarations. We do this when
-- going into a new scope, so that we're resolving to the most recently
-- bound name.
export
dropName : Name -> NestedNames vars -> NestedNames vars
dropName n nest = record { names $= drop } nest
  where
    drop : List (Name, a) -> List (Name, a)
    drop [] = []
    drop ((x, y) :: xs)
        = if x == n then drop xs
             else (x, y) :: drop xs

checkPiInfo : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto e : Ref EST (EState vars)} ->
              RigCount -> ElabInfo -> NestedNames vars -> Env Term vars ->
              PiInfo RawImp -> (expTy : Maybe (Glued vars)) ->
              Core (PiInfo (Term vars))
checkPiInfo rig elabinfo nest env Explicit exp = pure Explicit
checkPiInfo rig elabinfo nest env Implicit exp = pure Implicit
checkPiInfo rig elabinfo nest env AutoImplicit exp = pure AutoImplicit
checkPiInfo rig elabinfo nest env (DefImplicit t) exp
    = do (tv, _) <- check rig elabinfo nest env t exp
         pure (DefImplicit tv)

export
checkPi : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          {auto e : Ref EST (EState vars)} ->
          RigCount -> ElabInfo ->
          NestedNames vars -> Env Term vars ->
          FC ->
          RigCount -> PiInfo RawImp -> (n : Name) ->
          (argTy : RawImp) -> (retTy : RawImp) ->
          (expTy : Maybe (Glued vars)) ->
          Core (Term vars, Glued vars)
checkPi rig elabinfo nest env fc rigf info n argTy retTy expTy
    = do let pirig = getRig (elabMode elabinfo)
         (tyv, tyt) <- check pirig elabinfo nest env argTy
                             (Just (gType fc))
         info' <- checkPiInfo rigf elabinfo nest env info (Just (gnf env tyv))
         let env' : Env Term (n :: _) = Pi rigf info' tyv :: env
         let nest' = weaken (dropName n nest)
         (scopev, scopet) <-
            inScope fc env' (\e' =>
              check {e=e'} pirig elabinfo nest' env' retTy (Just (gType fc)))
         checkExp rig elabinfo env fc (Bind fc n (Pi rigf info' tyv) scopev) (gType fc) expTy
  where
    -- Might want to match on the LHS, so use the context rig, otherwise
    -- it's always erased
    getRig : ElabMode -> RigCount
    getRig (InLHS _) = rig
    getRig _ = erased

findLamRig : {auto c : Ref Ctxt Defs} ->
             Maybe (Glued vars) -> Core RigCount
findLamRig Nothing = pure top
findLamRig (Just expty)
    = do tynf <- getNF expty
         case tynf of
              NBind _ _ (Pi c _ _) sc => pure c
              _ => pure top

inferLambda : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto e : Ref EST (EState vars)} ->
              RigCount -> ElabInfo ->
              NestedNames vars -> Env Term vars ->
              FC ->
              RigCount -> PiInfo RawImp -> (n : Name) ->
              (argTy : RawImp) -> (scope : RawImp) ->
              (expTy : Maybe (Glued vars)) ->
              Core (Term vars, Glued vars)
inferLambda rig elabinfo nest env fc rigl info n argTy scope expTy
    = do rigb_in <- findLamRig expTy
         let rigb = rigb_in `glb` rigl
         (tyv, tyt) <- check erased elabinfo nest env argTy (Just (gType fc))
         info' <- checkPiInfo rigl elabinfo nest env info (Just (gnf env tyv))
         let env' : Env Term (n :: _) = Lam rigb info' tyv :: env
         let nest' = weaken (dropName n nest)
         (scopev, scopet) <- inScope fc env' (\e' =>
                                check {e=e'} rig elabinfo
                                      nest' env' scope Nothing)
         let lamty = gnf env (Bind fc n (Pi rigb info' tyv) !(getTerm scopet))
         logGlue 5 "Inferred lambda type" env lamty
         maybe (pure ())
               (logGlueNF 5 "Expected lambda type" env) expTy
         checkExpP rig True elabinfo env fc
                  (Bind fc n (Lam rigb info' tyv) scopev)
                  lamty expTy

getTyNF : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          Env Term vars -> Term vars -> Core (Term vars)
getTyNF env x@(Bind _ _ _ _) = pure x
getTyNF env x
    = do defs <- get Ctxt
         xnf <- nf defs env x
         empty <- clearDefs defs
         quote empty env xnf

export
checkLambda : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto e : Ref EST (EState vars)} ->
              RigCount -> ElabInfo ->
              NestedNames vars -> Env Term vars ->
              FC ->
              RigCount -> PiInfo RawImp -> (n : Name) ->
              (argTy : RawImp) -> (scope : RawImp) ->
              (expTy : Maybe (Glued vars)) ->
              Core (Term vars, Glued vars)
checkLambda rig_in elabinfo nest env fc rigl info n argTy scope Nothing
    = let rig = if isErased rig_in then erased else linear in
          inferLambda rig elabinfo nest env fc rigl info n argTy scope Nothing
checkLambda rig_in elabinfo nest env fc rigl info n argTy scope (Just expty_in)
    = do let rig = the RigCount $ if isErased rig_in then erased else linear
         expty <- getTerm expty_in
         exptynf <- getTyNF env expty
         defs <- get Ctxt
         case exptynf of
              Bind bfc bn (Pi c _ pty) psc =>
                 do (tyv, tyt) <- check erased elabinfo nest env
                                        argTy (Just (gType fc))
                    info' <- checkPiInfo rigl elabinfo nest env info (Just (gnf env tyv))
                    let rigb = rigl `glb` c
                    let env' : Env Term (n :: _) = Lam rigb info' tyv :: env
                    convertP True fc elabinfo env (gnf env tyv) (gnf env pty)
                    let nest' = weaken (dropName n nest)
                    (scopev, scopet) <-
                       inScope fc env' (\e' =>
                          check {e=e'} rig elabinfo nest' env' scope
                                (Just (gnf env' (renameTop n psc))))
                    logTermNF 10 "Lambda type" env exptynf
                    logGlueNF 10 "Got scope type" env' scopet
                    checkExpP rig True elabinfo env fc
                             (Bind fc n (Lam rigb info' tyv) scopev)
                             (gnf env
                                  (Bind fc n (Pi rigb info' tyv) !(getTerm scopet)))
                             (Just (gnf env
                                       (Bind fc bn (Pi c info' pty) psc)))
              _ => inferLambda rig elabinfo nest env fc rigl info n argTy scope (Just expty_in)

weakenExp : {x, vars : _} ->
            Env Term (x :: vars) ->
            Maybe (Glued vars) -> Core (Maybe (Glued (x :: vars)))
weakenExp env Nothing = pure Nothing
weakenExp env (Just gtm)
    = do tm <- getTerm gtm
         pure (Just (gnf env (weaken tm)))

-- Branch on LinearMisuse when the expected rigCount is One, othewise take the other branch
matchLinearMisuse : (thenBr : a) -> (elseBr : a) -> Error -> a
matchLinearMisuse thenBr elseBr (LinearMisuse _ _ rig _) = branchOne thenBr elseBr rig
matchLinearMisuse thenBr elseBr _ = elseBr

printNameType : NameType -> String
printNameType (DataCon r _ _) = "Data constructor with rig " ++ show r
printNameType _ = ""

printTerm : {vars : List Name} -> Term vars -> String
printTerm (Local _ _ _ _) = "Local var"
printTerm (Ref _ tpe n) = "ref to something : " ++ show n ++ " " ++ printNameType tpe
printTerm (Bind _ n _ _) = "binder : " ++ show n
printTerm (Meta _ n _ _) = "meta : " ++ show n
printTerm (App _ (Ref _ nametype name) _) = "applying ref : " ++ printNameType nametype ++ ", " ++ show name
printTerm (As _ _ _ _) = "As"
printTerm _ = ""

||| If rigcount is different from rig of DataCon, replace it, otherwise nothing
lineariseDataCon : RigCount -> Term vars -> Maybe (Term vars)
lineariseDataCon rig (App fc (Ref fc' (DataCon r tag ary) name) arg) =
  toMaybe (rig /= r) (App fc (Ref fc' (DataCon rig tag ary) name) arg)
lineariseDataCon _ _ = Nothing

export
checkLet : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           RigCount -> ElabInfo ->
           NestedNames vars -> Env Term vars ->
           FC ->
           RigCount -> (n : Name) ->
           (nTy : RawImp) -> (nVal : RawImp) -> (scope : RawImp) ->
           (expTy : Maybe (Glued vars)) ->
           Core (Term vars, Glued vars)
checkLet rigc_in elabinfo nest env fc rigl n nTy nVal scope expty {vars}
    = do let rigc = the RigCount $ if isErased rigc_in then erased else linear
         coreLift $ putStrLn ("checking let with name " ++ show n)
         (tyv, tyt) <- check erased elabinfo nest env nTy (Just (gType fc))
         -- Try checking at the given multiplicity; if that doesn't work,
         -- try checking at Rig1 (meaning that we're using a linear variable
         -- so the resulting binding should be linear)
         -- Also elaborate any case blocks in the value via runDelays
         -- (0 is the highest priority delays only)
         (valv, valt, rigb) <- handle
              (do c <- runDelays 0 $ check (rigl |*| rigc)
                             (record { preciseInf = True } elabinfo)
                             nest env nVal (Just (gnf env tyv))
                  pure (fst c, snd c, rigl |*| rigc))
              (matchLinearMisuse (do c <- runDelays 0 $ check linear elabinfo
                                              nest env nVal (Just (gnf env tyv))
                                     pure (fst c, snd c, linear))
                                 (do c <- check (rigl |*| rigc)
                                              elabinfo -- without preciseInf
                                              nest env nVal (Just (gnf env tyv))
                                     pure (fst c, snd c, rigl |*| rigc)))
         let env' : Env Term (n :: _) = Lam rigb Explicit tyv :: env
         let nest' = weaken (dropName n nest)
         expScope <- weakenExp env' expty
         (scopev, gscopet) <-
            inScope fc env' (\e' => do
              check {e=e'} rigc elabinfo nest' env' scope expScope)
         coreLift $ printLn ("nVal " ++ show nVal)
         coreLift $ putStrLn $ case lineariseDataCon rigb valv of
           Nothing => "No replacement for : " ++ show n
           Just _ => "Replaced rig for: " ++ show n ++ " with " ++ show rigb
         coreLift $ putStrLn ("done checking " ++ show n)
         scopet <- getTerm gscopet

         -- No need to 'checkExp' here - we've already checked scopet
         -- against the expected type when checking the scope, so just
         -- build the term directly
         pure (Bind fc n (Let rigb valv tyv) scopev,
               gnf env (Bind fc n (Let rigb valv tyv) scopet))
