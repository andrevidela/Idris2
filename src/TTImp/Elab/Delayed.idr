module TTImp.Elab.Delayed

import Core.CaseTree
import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.TTImp

import Data.IntMap
import Data.List

%default covering

-- We run the elaborator in the given environment, but need to end up with a
-- closed term.
mkClosedElab : {vars : _} ->
               FC -> Env Term vars ->
               (Core (Term vars, Glued vars)) ->
               Core ClosedTerm
mkClosedElab fc [] elab
    = do (tm, _) <- elab
         pure tm
mkClosedElab {vars = x :: vars} fc (b :: env) elab
    = mkClosedElab fc env
          (do (sc', _) <- elab
              let b' = newBinder b
              pure (Bind fc x b' sc', gErased fc))
  where
    -- in 'abstractEnvType' we get a Pi binder (so we'll need a Lambda) for
    -- everything except 'Let', so make the appropriate corresponding binder
    -- here
    newBinder : Binder (Term vars) -> Binder (Term vars)
    newBinder (Let c val ty) = Let c val ty
    newBinder b = Lam (multiplicity b) Explicit (binderType b)

deeper : {auto e : Ref EST (EState vars)} ->
         Core a -> Core a
deeper elab
    = do est <- get EST
         let d = delayDepth est
         put EST (record { delayDepth = 1 + d } est)
         res <- elab
         est <- get EST
         put EST (record { delayDepth = d } est)
         pure res

-- Try the given elaborator; if it fails, and the error matches the
-- predicate, make a hole and try it again later when more holes might
-- have been resolved
export
delayOnFailure : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 FC -> RigCount -> Env Term vars ->
                 (expected : Glued vars) ->
                 (Error -> Bool) ->
                 (pri : Nat) ->
                 (Bool -> Core (Term vars, Glued vars)) ->
                 Core (Term vars, Glued vars)
delayOnFailure fc rig env expected pred pri elab
    = do est <- get EST
         handle (elab False)
          (\err =>
              do est <- get EST
                 if pred err
                    then
                      do nm <- genName "delayed"
                         (ci, dtm) <- newDelayed fc linear env nm !(getTerm expected)
                         logGlueNF 5 ("Postponing elaborator " ++ show nm ++
                                      " at " ++ show fc ++
                                      " for") env expected
                         log 10 ("Due to error " ++ show err)
                         ust <- get UST
                         put UST (record { delayedElab $=
                                 ((pri, ci, mkClosedElab fc env (deeper (elab True))) :: ) }
                                         ust)
                         pure (dtm, expected)
                    else throw err)

export
delayElab : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            FC -> RigCount -> Env Term vars ->
            (expected : Maybe (Glued vars)) ->
            (pri : Nat) ->
            Core (Term vars, Glued vars) ->
            Core (Term vars, Glued vars)
delayElab {vars} fc rig env exp pri elab
    = do est <- get EST
         nm <- genName "delayed"
         expected <- mkExpected exp
         (ci, dtm) <- newDelayed fc linear env nm !(getTerm expected)
         logGlueNF 5 ("Postponing elaborator " ++ show nm ++
                      " for") env expected
         ust <- get UST
         put UST (record { delayedElab $=
                 ((pri, ci, mkClosedElab fc env elab) :: ) }
                         ust)
         pure (dtm, expected)
  where
    mkExpected : Maybe (Glued vars) -> Core (Glued vars)
    mkExpected (Just ty) = pure ty
    mkExpected Nothing
        = do nm <- genName "delayTy"
             ty <- metaVar fc erased env nm (TType fc)
             pure (gnf env ty)

export
ambiguous : Error -> Bool
ambiguous (AmbiguousElab _ _ _) = True
ambiguous (AmbiguousName _ _) = True
ambiguous (AmbiguityTooDeep _ _ _) = True
ambiguous (InType _ _ err) = ambiguous err
ambiguous (InCon _ _ err) = ambiguous err
ambiguous (InLHS _ _ err) = ambiguous err
ambiguous (InRHS _ _ err) = ambiguous err
ambiguous (WhenUnifying _ _ _ _ err) = ambiguous err
ambiguous _ = False

mutual
  mismatchNF : {vars : _} ->
               Defs -> NF vars -> NF vars -> Core Bool
  mismatchNF defs (NTCon _ xn xt _ xargs) (NTCon _ yn yt _ yargs)
      = if xn /= yn
           then pure True
           else anyM (mismatch defs) (zip xargs yargs)
  mismatchNF defs (NDCon _ _ _ xt _ xargs) (NDCon _ _ _ yt _ yargs)
      = if xt /= yt
           then pure True
           else anyM (mismatch defs) (zip xargs yargs)
  mismatchNF defs (NPrimVal _ xc) (NPrimVal _ yc) = pure (xc /= yc)
  mismatchNF defs (NDelayed _ _ x) (NDelayed _ _ y) = mismatchNF defs x y
  mismatchNF defs (NDelay _ _ _ x) (NDelay _ _ _ y)
      = mismatchNF defs !(evalClosure defs x) !(evalClosure defs y)
  mismatchNF _ _ _ = pure False

  mismatch : {vars : _} ->
             Defs -> (Closure vars, Closure vars) -> Core Bool
  mismatch defs (x, y)
      = mismatchNF defs !(evalClosure defs x) !(evalClosure defs y)

contra : {vars : _} ->
               Defs -> NF vars -> NF vars -> Core Bool
-- Unlike 'impossibleOK', any mismatch indicates an unrecoverable error
contra defs (NTCon _ xn xt xa xargs) (NTCon _ yn yt ya yargs)
    = if xn /= yn
         then pure True
         else anyM (mismatch defs) (zip xargs yargs)
contra defs (NDCon _ _ _ xt _ xargs) (NDCon _ _ _ yt _ yargs)
    = if xt /= yt
         then pure True
         else anyM (mismatch defs) (zip xargs yargs)
contra defs (NPrimVal _ x) (NPrimVal _ y) = pure (x /= y)
contra defs (NDCon _ _ _ _ _ _) (NPrimVal _ _) = pure True
contra defs (NPrimVal _ _) (NDCon _ _ _ _ _ _) = pure True
contra defs x y = pure False

-- Errors that might be recoverable later if we try again. Generally -
-- ambiguity errors, type inference errors
export
recoverable : {auto c : Ref Ctxt Defs} ->
              Error -> Core Bool
recoverable (CantConvert _ env l r)
   = do defs <- get Ctxt
        pure $ not !(contra defs !(nf defs env l) !(nf defs env r))
recoverable (CantSolveEq _ env l r)
   = do defs <- get Ctxt
        pure $ not !(contra defs !(nf defs env l) !(nf defs env r))
recoverable (UndefinedName _ _) = pure False
recoverable (LinearMisuse _ _ _ _) = pure False
recoverable (InType _ _ err) = recoverable err
recoverable (InCon _ _ err) = recoverable err
recoverable (InLHS _ _ err) = recoverable err
recoverable (InRHS _ _ err) = recoverable err
recoverable (WhenUnifying _ _ _ _ err) = recoverable err
recoverable _ = pure True

data RetryError
     = RecoverableErrors
     | AllErrors

Show RetryError where
  show RecoverableErrors = "RecoverableErrors"
  show AllErrors = "AllErrors"

-- Try all the delayed elaborators. If there's a failure, we want to
-- show the ambiguity errors first (since that's the likely cause)
-- Return all the ones that need trying again
retryDelayed' : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto m : Ref MD Metadata} ->
                {auto u : Ref UST UState} ->
                {auto e : Ref EST (EState vars)} ->
                RetryError ->
                List (Nat, Int, Core ClosedTerm) ->
                List (Nat, Int, Core ClosedTerm) ->
                Core (List (Nat, Int, Core ClosedTerm))
retryDelayed' errmode acc [] = pure (reverse acc)
retryDelayed' errmode acc (d@(_, i, elab) :: ds)
    = do defs <- get Ctxt
         Just Delayed <- lookupDefExact (Resolved i) (gamma defs)
              | _ => retryDelayed' errmode acc ds
         handle
           (do est <- get EST
               log 5 (show (delayDepth est) ++ ": Retrying delayed hole " ++ show !(getFullName (Resolved i)))
               -- elab itself might have delays internally, so keep track of them
               ust <- get UST
               put UST (record { delayedElab = [] } ust)
               tm <- elab
               ust <- get UST
               let ds' = reverse (delayedElab ust) ++ ds

               updateDef (Resolved i) (const (Just
                    (PMDef (MkPMDefInfo NotHole True) [] (STerm 0 tm) (STerm 0 tm) [])))
               logTerm 5 ("Resolved delayed hole " ++ show i) tm
               logTermNF 5 ("Resolved delayed hole NF " ++ show i) [] tm
               removeHole i
               retryDelayed' errmode acc ds')
           (\err => do log 5 $ show errmode ++ ":Error in " ++ show !(getFullName (Resolved i))
                                ++ "\n" ++ show err
                       case errmode of
                         RecoverableErrors =>
                            if not !(recoverable err)
                               then throw err
                               else retryDelayed' errmode (d :: acc) ds
                         AllErrors => throw err)

export
retryDelayed : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               List (Nat, Int, Core ClosedTerm) ->
               Core ()
retryDelayed ds
    = do est <- get EST
         ds <- retryDelayed' RecoverableErrors [] ds -- try everything again
         retryDelayed' AllErrors [] ds -- fail on all errors
         pure ()

-- Run an elaborator, then all the delayed elaborators arising from it
export
runDelays : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            Nat -> Core a -> Core a
runDelays pri elab
    = do ust <- get UST
         let olddelayed = delayedElab ust
         put UST (record { delayedElab = [] } ust)
         tm <- elab
         ust <- get UST
         log 2 $ "Rerunning delayed in elaborator"
         handle (do retryDelayed' AllErrors []
                       (reverse (filter hasPri (delayedElab ust)))
                    pure ())
                (\err => do put UST (record { delayedElab = olddelayed } ust)
                            throw err)
         ust <- get UST
         put UST (record { delayedElab $= (++ olddelayed) } ust)
         pure tm
  where
    hasPri : (Nat, d) -> Bool
    hasPri (n, _) = natToInteger n <= natToInteger pri
