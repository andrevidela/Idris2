module TTImp.CheckLHS

import Core.Context
import Core.Core
import Core.Env
import Core.TT
import Core.Metadata
import Core.Normalise
import Core.UnifyState
import Core.Value

import TTImp.BindImplicits
import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Elab.Utils
import TTImp.TTImp

import Idris.REPL.Opts
import Idris.Syntax

-- Find names which are applied to a function in a Rig1/Rig0 position,
-- so that we know how they should be bound on the right hand side of the
-- pattern.
-- 'bound' counts the number of variables locally bound; these are the
-- only ones we're checking linearity of (we may be shadowing names if this
-- is a local definition, so we need to leave the earlier ones alone)
findLinear : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             Bool -> Nat -> RigCount -> Term vars ->
             Core (List (Name, RigCount))
findLinear top bound rig (Bind fc n b sc)
    = findLinear top (S bound) rig sc
findLinear top bound rig (As fc _ _ p)
    = findLinear top bound rig p
findLinear top bound rig tm
    = case getFnArgs tm of
           (Ref _ _ n, []) => pure []
           (Ref _ nt n, args)
              => do defs <- get Ctxt
                    Just nty <- lookupTyExact n (gamma defs)
                         | Nothing => pure []
                    findLinArg (accessible nt rig) !(nf defs [] nty) args
           _ => pure []
    where
      accessible : NameType -> RigCount -> RigCount
      accessible Func r = if top then r else erased
      accessible _ r = r

      findLinArg : {vars : _} ->
                   RigCount -> NF [] -> List (Term vars) ->
                   Core (List (Name, RigCount))
      findLinArg rig ty (As fc UseLeft _ p :: as)
          = findLinArg rig ty (p :: as)
      findLinArg rig ty (As fc UseRight p _ :: as)
          = findLinArg rig ty (p :: as)
      findLinArg rig (NBind _ x (Pi _ c _ _) sc) (Local {name=a} fc _ idx prf :: as)
          = do defs <- get Ctxt
               let a = nameAt prf
               if idx < bound
                 then do sc' <- sc defs (toClosure defaultOpts [] (Ref fc Bound x))
                         pure $ (a, rigMult c rig) ::
                                    !(findLinArg rig sc' as)
                 else do sc' <- sc defs (toClosure defaultOpts [] (Ref fc Bound x))
                         findLinArg rig sc' as
      findLinArg rig (NBind fc x (Pi _ c _ _) sc) (a :: as)
          = do defs <- get Ctxt
               pure $ !(findLinear False bound (c |*| rig) a) ++
                      !(findLinArg rig !(sc defs (toClosure defaultOpts [] (Ref fc Bound x))) as)
      findLinArg rig ty (a :: as)
          = pure $ !(findLinear False bound rig a) ++ !(findLinArg rig ty as)
      findLinArg _ _ [] = pure []

-- Combining multiplicities on LHS:
-- Rig1 + Rig1/W not valid, since it means we have repeated use of name
-- Rig0 + RigW = RigW
-- Rig0 + Rig1 = Rig1
combineLinear : FC -> List (Name, RigCount) ->
                Core (List (Name, RigCount))
combineLinear loc [] = pure []
combineLinear loc ((n, count) :: cs)
    = case lookupAll n cs of
           [] => pure $ (n, count) :: !(combineLinear loc cs)
           counts => do count' <- combineAll count counts
                        pure $ (n, count') ::
                               !(combineLinear loc (filter notN cs))
  where
    notN : (Name, RigCount) -> Bool
    notN (n', _) = n /= n'

    lookupAll : Name -> List (Name, RigCount) -> List RigCount
    lookupAll n [] = []
    lookupAll n ((n', c) :: cs)
       = if n == n' then c :: lookupAll n cs else lookupAll n cs

    -- Those combine rules are obtuse enough that they are worth investigating
    combine : RigCount -> RigCount -> Core RigCount
    combine l r = if l |+| r == top && not (isErased $ l `glb` r) && (l `glb` r) /= top
                     then throw (LinearUsed loc 2 n)
                     -- if everything is fine, return the linearity that has the
                     -- highest bound
                     else pure (l `lub` r)

    combineAll : RigCount -> List RigCount -> Core RigCount
    combineAll c [] = pure c
    combineAll c (c' :: cs)
        = do newc <- combine c c'
             combineAll newc cs

setLinear : List (Name, RigCount) -> Term vars -> Term vars
setLinear vs (Bind fc x b@(PVar _ _ _ _) sc)
    = case lookup x vs of
           Just c' => Bind fc x (setMultiplicity b c') (setLinear vs sc)
           _ => Bind fc x b (setLinear vs sc)
setLinear vs (Bind fc x b@(PVTy _ _ _) sc)
    = case lookup x vs of
           Just c' => Bind fc x (setMultiplicity b c') (setLinear vs sc)
           _ => Bind fc x b (setLinear vs sc)
setLinear vs tm = tm

-- Given a type checked LHS and its type, return the environment in which we
-- should check the RHS, the LHS and its type in that environment,
-- and a function which turns a checked RHS into a
-- pattern clause
-- The 'SubVars' proof contains a proof that refers to the *inner* environment,
-- so all the outer things are marked as 'DropCons'
extendEnv : {vars : _} ->
            Env Term vars -> SubVars inner vars ->
            NestedNames vars ->
            Term vars -> Term vars ->
            Core (vars' **
                    (SubVars inner vars',
                     Env Term vars', NestedNames vars',
                     Term vars', Term vars'))
extendEnv env p nest (Bind _ n (PVar fc c pi tmty) sc) (Bind _ n' (PVTy _ _ _) tysc) with (nameEq n n')
  extendEnv env p nest (Bind _ n (PVar fc c pi tmty) sc) (Bind _ n' (PVTy _ _ _) tysc) | Nothing
      = throw (InternalError "Can't happen: names don't match in pattern type")
  extendEnv env p nest (Bind _ n (PVar fc c pi tmty) sc) (Bind _ n (PVTy _ _ _) tysc) | (Just Refl)
      = extendEnv (PVar fc c pi tmty :: env) (DropCons p) (weaken nest) sc tysc
extendEnv env p nest (Bind _ n (PLet fc c tmval tmty) sc) (Bind _ n' (PLet _ _ _ _) tysc) with (nameEq n n')
  extendEnv env p nest (Bind _ n (PLet fc c tmval tmty) sc) (Bind _ n' (PLet _ _ _ _) tysc) | Nothing
      = throw (InternalError "Can't happen: names don't match in pattern type")
  -- PLet on the left becomes Let on the right, to give it computational force
  extendEnv env p nest (Bind _ n (PLet fc c tmval tmty) sc) (Bind _ n (PLet _ _ _ _) tysc) | (Just Refl)
      = extendEnv (Let fc c tmval tmty :: env) (DropCons p) (weaken nest) sc tysc
extendEnv env p nest tm ty
      = pure (_ ** (p, env, nest, tm, ty))

export -- also used by Transforms
checkLHS : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           Bool -> -- in transform
           (mult : RigCount) ->
           Int -> List ElabOpt -> NestedNames vars -> Env Term vars ->
           FC -> RawImp ->
           Core (RawImp, -- checked LHS with implicits added
                 (vars' ** (SubVars vars vars',
                           Env Term vars', NestedNames vars',
                           Term vars', Term vars')))
checkLHS {vars} trans mult n opts nest env fc lhs_in
    = do defs <- get Ctxt
         logRaw "declare.def.lhs" 30 "Raw LHS: " lhs_in
         lhs_raw <- if trans
                       then pure lhs_in
                       else lhsInCurrentNS nest lhs_in
         logRaw "declare.def.lhs" 30 "Raw LHS in current NS: " lhs_raw

         autoimp <- isUnboundImplicits
         setUnboundImplicits True
         (_, lhs_bound) <- bindNames False lhs_raw
         setUnboundImplicits autoimp
         logRaw "declare.def.lhs" 30 "Raw LHS with implicits bound" lhs_bound

         lhs <- if trans
                   then pure lhs_bound
                   else implicitsAs n defs vars lhs_bound

         logC "declare.def.lhs" 5 $ do pure $ "Checking LHS of " ++ show !(getFullName (Resolved n))
-- todo: add Pretty RawImp instance
--         logC "declare.def.lhs" 5 $ do pure $ show $ indent {ann = ()} 2 $ pretty lhs
         log "declare.def.lhs" 10 $ show lhs
         logEnv "declare.def.lhs" 5 "In env" env
         let lhsMode = if trans
                          then InTransform
                          else InLHS mult
         (lhstm, lhstyg) <-
             wrapErrorC opts (InLHS fc !(getFullName (Resolved n))) $
                     elabTerm n lhsMode opts nest env
                                (IBindHere fc PATTERN lhs) Nothing
         logTerm "declare.def.lhs" 5 "Checked LHS term" lhstm
         lhsty <- getTerm lhstyg

         defs <- get Ctxt
         let lhsenv = letToLam env
         -- we used to fully normalise the LHS, to make sure fromInteger
         -- patterns were allowed, but now they're fully normalised anyway
         -- so we only need to do the holes. If there's a lot of type level
         -- computation, this is a huge saving!
         lhstm <- normaliseHoles defs lhsenv lhstm
         lhsty <- normaliseHoles defs env lhsty
         linvars_in <- findLinear True 0 linear lhstm
         logTerm "declare.def.lhs" 10 "Checked LHS term after normalise" lhstm
         log "declare.def.lhs" 5 $ "Linearity of names in " ++ show n ++ ": " ++
                 show linvars_in

         linvars <- combineLinear fc linvars_in
         let lhstm_lin = setLinear linvars lhstm
         let lhsty_lin = setLinear linvars lhsty

         logTerm "declare.def.lhs" 3 "LHS term" lhstm_lin
         logTerm "declare.def.lhs" 5 "LHS type" lhsty_lin
         setHoleLHS (bindEnv fc env lhstm_lin)

         ext <- extendEnv env SubRefl nest lhstm_lin lhsty_lin
         pure (lhs, ext)
