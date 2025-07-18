module Idris.Parser.Let

import Idris.Syntax
import Libraries.Text.Bounded

import Data.Either
import Data.List1

%default total

------------------------------------------------------------------------
-- Types

-- `let ... in ...` is used for two different notions:
-- * pattern-matching let binders to locally take an expression apart
-- * Local definitions that can be recursive

public export
record LetBinder where
  constructor MkLetBinder
  letUsage     : RigCount
  letPattern   : PTerm
  letBoundType : PTerm
  letBoundTerm : PTerm
  letUnhappy   : List PClause

public export
LetDecl : Type
LetDecl = List PDecl

------------------------------------------------------------------------
-- Let-binding functions

letFactory : (List (WithBounds LetBinder) -> a -> a) ->
             (WithBounds LetDecl -> a -> a) ->
             List1 (WithBounds (Either LetBinder LetDecl)) ->
             a -> a
letFactory letBind letDeclare blocks scope = foldr mkLet scope groups where

  LetBlock : Type
  LetBlock = Either (List1 (WithBounds LetBinder)) (List1 (WithBounds LetDecl))

  groups : List LetBlock
  groups = compress (forget $ map (\ b => bimap (<$ b) (<$ b) b.val) blocks)

  mkLet : LetBlock -> a -> a
  mkLet (Left  letBinds) = letBind (forget letBinds)
  mkLet (Right letDecls) =
    let bounds = mergeBounds (head letDecls) (last letDecls)
    in letDeclare (concatMap val letDecls <$ bounds)

export
mkLets : OriginDesc ->
         List1 (WithBounds (Either LetBinder LetDecl)) ->
         PTerm -> PTerm
mkLets origin = letFactory buildLets
  (\ decls, scope => MkFCVal (virtualiseFC $ boundToFC origin decls) (PLocal decls.val scope))

  where

    buildLets : List (WithBounds LetBinder) -> PTerm -> PTerm
    buildLets [] sc = sc
    buildLets (b :: rest) sc
      = let (MkLetBinder rig pat ty val alts) = b.val
            fc = virtualiseFC $ boundToFC origin b
         in MkFCVal fc $ PLet rig pat ty val (buildLets rest sc) alts --(buildLets rest sc) alts.val

export
mkDoLets : OriginDesc ->
           List1 (WithBounds (Either LetBinder LetDecl)) ->
           List PDo
mkDoLets origin lets = letFactory
    (\ binds, rest => buildDoLets binds ++ rest)
    (\ decls, rest => DoLetLocal (boundToFC origin decls) decls.val :: rest)
    lets
    []

  where

    buildDoLets : List (WithBounds LetBinder) -> List PDo
    buildDoLets [] = []
    buildDoLets (b :: rest) = let fc = boundToFC origin b in case b.val of
      (MkLetBinder rig b@(MkWithData _ $ PRef (UN un)) ty val []) =>
         (if isPatternVariable un
            then DoLet fc b.fc (UN un) rig ty val
            else DoLetPat fc b ty val []
         ) :: buildDoLets rest
      (MkLetBinder rig imp@(MkWithData _ PImplicit) ty val []) =>
        DoLet fc imp.fc (UN Underscore) rig ty val :: buildDoLets rest
      (MkLetBinder rig pat ty val alts) =>
        DoLetPat fc pat ty val alts :: buildDoLets rest
