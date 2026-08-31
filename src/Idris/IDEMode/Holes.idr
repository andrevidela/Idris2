module Idris.IDEMode.Holes

import Core.Env
import Core.Normalise

import Data.String

import Idris.Resugar
import Idris.Syntax
import Idris.Pretty

import Idris.IDEMode.Commands

%default covering

public export
record Premise where
  constructor MkHolePremise
  name         : Name
  type         : IPTerm
  multiplicity : RigCount
  isImplicit   : Bool

impBracket : Bool -> String -> String
impBracket False str = str
impBracket True str = "{" ++ str ++ "}"

export covering
Show Holes.Premise where
  show premise =
    " " ++ showCount premise.multiplicity ++ " "
    ++ impBracket premise.isImplicit (show premise.name ++ " : " ++ show premise.type)

prettyImpBracket : Bool -> Doc ann -> Doc ann
prettyImpBracket False = id
prettyImpBracket True = braces

export
prettyRigHole : RigCount -> Doc IdrisSyntax
prettyRigHole = elimSemi (keyword (pretty0 '0') <+> space)
                         (keyword (pretty0 '1') <+> space)
                         (const $ space <+> space)

export
Pretty IdrisSyntax Holes.Premise where
  pretty premise =
     prettyRigHole premise.multiplicity
     <+> prettyImpBracket premise.isImplicit (pretty0 premise.name <++> colon <++> pretty premise.type)

public export
record Data where
  constructor MkHoleData
  name : Name
  type : IPTerm
  context : List Holes.Premise
  ||| Set if we gave up normalising the hole's type or one of its premises,
  ||| in which case the types above are shown as they were stored.
  limitReached : Bool

export
prettyHoles : List Holes.Data -> Doc IdrisSyntax
prettyHoles holes = case holes of
  []  => "No holes"
  [x] => "1 hole" <+> colon <++> prettyHole x
  xs  => vcat $ (pretty0 (show $ length xs) <++> "holes" <+> colon)
              :: map (indent 2 . prettyHole) xs

  where

   prettyHole : Holes.Data -> Doc IdrisSyntax
   prettyHole x = pretty0 x.name <++> colon <++> pretty x.type


||| If input is a hole, return number of locals in scope at binding
||| point
export
isHole : GlobalDef -> Maybe Nat
isHole def
    = case definition def of
           Hole locs _ => Just locs
           PMDef pi _ _ _ _ =>
                 case holeInfo pi of
                      NotHole => Nothing
                      SolvedHole n => Just n
           None => Just 0
           _ => Nothing


-- Bring these back into REPL.idr
showName : Name -> Bool
showName (UN Underscore) = False
showName (MN {}) = False
showName _ = True

||| How far we normalise a type before showing it in a hole. A type which
||| mentions a non-total function has no normal form at all, so without a
||| limit the evaluator loops forever instead of answering.
|||
||| The fuel is what guarantees termination and is set high enough not to
||| interfere with real type level computation (it is a depth, and costs about
||| 2.5 per step of e.g. Nat addition). The application depth is what makes
||| the answer arrive quickly when a type really is diverging: reaching the
||| fuel limit on such a type takes tens of seconds, reaching this one takes
||| a fraction of a second.
holeNormaliseFuel : Nat
holeNormaliseFuel = 5000

holeNormaliseAppDepth : Nat
holeNormaliseAppDepth = 1000

||| Normalise a type for display, giving up and returning it unchanged (with
||| the flag set) if it looks like normalisation is not going to terminate.
normaliseForDisplay : {vars : _} ->
                      {auto c : Ref Ctxt Defs} ->
                      Defs -> Env Term vars -> Term vars ->
                      Core (Term vars, Bool)
normaliseForDisplay defs env tm
  = do Just tm' <- tryNormaliseLimited defs holeNormaliseFuel
                                       holeNormaliseAppDepth env tm
         | Nothing => do log "ide-mode.hole" 10 $
                            "Normalisation limit reached on: " ++ show !(toFullNames tm)
                         pure (tm, True)
       pure (tm', False)

export
extractHoleData : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto s : Ref Syn SyntaxInfo} ->
                  Defs -> Env Term vars -> Name -> Nat -> Term vars ->
                  Core Holes.Data
extractHoleData defs env fn (S args) (Bind fc x (Let _ c val ty) sc)
  = extractHoleData defs env fn args (subst val sc)
extractHoleData defs env fn (S args) (Bind fc x b sc)
  = do rest <- extractHoleData defs (b :: env) fn args sc
       let True = showName x
         | False => do log "ide-mode.hole" 10 $ "Not showing name: " ++ show x
                       pure rest
       log "ide-mode.hole" 10 $ "Showing name: " ++ show x
       (bty, limited) <- normaliseForDisplay defs env (binderType b)
       ity <- resugar env bty
       let premise = MkHolePremise x ity (multiplicity b) (isImplicit b)
       pure $ { context $= (premise ::)
              , limitReached $= (limited ||) } rest
extractHoleData defs env fn args ty
  = do (nty, limited) <- normaliseForDisplay defs env ty
       ity <- resugar env nty
       log "ide-mode.hole" 20 $
          "Return type: " ++ show !(toFullNames ty)
          ++ "\n  Evaluated to: " ++ show !(toFullNames nty)
          ++ "\n  Resugared to: " ++ show ity
       pure $ MkHoleData fn ity [] limited


export
holeData : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           Defs -> Env Term vars -> Name -> Nat -> Term vars ->
           Core Holes.Data

holeData gam env fn args ty
  = do hdata <- extractHoleData gam env fn args ty
       pp <- getPPrint
       pure $ if showImplicits pp
              then hdata
              else { context $= dropShadows } hdata
  where
    dropShadows : List Holes.Premise -> List Holes.Premise
    dropShadows [] = []
    dropShadows (premise :: rest)
        = if premise.name `elem` map name rest
             then            dropShadows rest
             else premise :: dropShadows rest

export
getUserHolesData :
  {auto c : Ref Ctxt Defs} ->
  {auto s : Ref Syn SyntaxInfo} ->
  Core (List Holes.Data)
getUserHolesData
    = do defs <- get Ctxt
         let ctxt = gamma defs
         ms  <- getUserHoles
         let globs = concat !(traverse (\n => lookupCtxtName n ctxt) ms)
         let holesWithArgs = mapMaybe (\(n, i, gdef) => do args <- isHole gdef
                                                           pure (n, gdef, args))
                                      globs
         traverse (\n_gdef_args =>
                     -- Inference can't deal with this for now :/
                     let (n, gdef, args) = the (Name, GlobalDef, Nat) n_gdef_args in
                     holeData defs Env.empty n args (type gdef))
                  holesWithArgs

||| Shown when we stopped normalising a hole's type early: the type above is
||| the one we started from, not its normal form.
export
limitWarning : String
limitWarning = "-- warning: normalisation stopped early, type shown unreduced"

export
showHole : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          Defs -> Env Term vars -> Name -> Nat -> Term vars ->
          Core String

showHole defs env fn args ty
    = do hdata <- holeData defs env fn args ty
         let warning = if hdata.limitReached
                          then "\n" ++ limitWarning
                          else ""
         case hdata.context of
           [] => pure $ show (hdata.name) ++ " : " ++ show hdata.type ++ warning
           _  => pure $
              unlines (map show hdata.context)
              ++ "-------------------------------------\n"
              ++ nameRoot (hdata.name) ++ " : " ++ show hdata.type ++ warning

export
prettyHole : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             Defs -> Env Term vars -> Name -> Nat -> Term vars ->
             Core (Doc IdrisSyntax)
prettyHole defs env fn args ty
  = do hdata <- holeData defs env fn args ty
       let warning = if hdata.limitReached
                        then hardline <+> pretty0 limitWarning
                        else neutral
       case hdata.context of
         [] => pure $ pretty0 hdata.name <++> colon <++> pretty hdata.type <+> warning
         _  => pure $ indent 1 (vsep $ map pretty hdata.context) <+> hardline
                  <+> (pretty0 $ replicate 30 '-') <+> hardline
                  <+> pretty0 (nameRoot $ hdata.name) <++> colon <++> pretty hdata.type
                  <+> warning


premiseIDE : Holes.Premise -> HolePremise
premiseIDE premise = IDE.MkHolePremise
  { name = " " ++ showCount premise.multiplicity ++ " "
               ++ (impBracket premise.isImplicit $
                  show premise.name)
  , type = show premise.type
  }

export
holeIDE : Holes.Data -> IDE.HoleData
holeIDE hole = IDE.MkHoleData
  { name = show hole.name
  , type = show hole.type
  , context = map premiseIDE hole.context
  }
