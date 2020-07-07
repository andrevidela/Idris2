module Compiler.Mutate

import Core.CompileExpr
import Core.Context
import Core.Core
import Core.FC
import Core.Name

import Data.List

%hide Prelude.traverse

updateTag : (Int -> Int) -> (CConAlt vars) -> (CConAlt vars)
updateTag update (MkConAlt nm tag args rhs) = MkConAlt nm (update <$> tag) args rhs

interleave : List a -> List a -> List a
interleave [] ys = ys
interleave (x :: xs) ys = x :: (interleave2 xs ys)
  where
    interleave2 : List a -> List a -> List a
    interleave2 xs (y :: ys) = y :: (interleave xs ys)
    interleave2 xs [] = xs

mutual
  export
  mkMutating : {auto c : Ref Ctxt Defs} -> {vars : _} -> Name -> (tag : Maybe Int) -> CExp vars -> Core (CExp vars)
  mkMutating nm tag (CLam fc x body) =
    let mutating = (mkMutating nm tag body) in
        pure $ CLam fc x !mutating
  mkMutating nm tag (CLet fc n i rhs body) =
    let rhs' = mkMutating nm tag rhs
        body' = mkMutating nm tag body in
        pure $ CLet fc n i !rhs' !body'
  mkMutating nm tag (CApp fc fn args) = pure $ CApp fc !(mkMutating nm tag fn) !(traverse (mkMutating nm tag) args)
  -- if the constructor matches name and tag, replace it by mut, otherwise do nothing
  mkMutating nm tag con@(CCon fc nm' tag' args)  = do
    corePrint $ "looking to replace " ++ show !(getFullName nm) ++ " and we got " ++ show !(getFullName nm')
    pure $ if nm == nm' && tag == tag'
       then CMut fc nm args
       else con
  mkMutating nm tag (COp fc aty args) = pure $ COp fc aty !(traverseVect (mkMutating nm tag) args)
  mkMutating nm tag (CExtPrim fc n args) = pure $ CExtPrim fc n !(traverse (mkMutating nm tag) args)
  mkMutating nm tag (CForce fc body) = CForce fc <$> (mkMutating nm tag body)
  mkMutating nm tag (CDelay fc body) = CDelay fc <$> (mkMutating nm tag body)

  -- when we see a CConCase we need to expand it to allow mutating cases and then we
  -- modify each new case to allow the additional mutation from the enclosing scope
  -- this makes a redundant tree traversal, maybe we should do everything in 1 go
  mkMutating nm tag (CConCase fc sc clauses wc) = do
        -- add the mutating clauses for the current
        newClauses <- traverse mutateCaseAlt clauses
        pure $ CConCase fc sc !(traverse mutateClause newClauses) wc
    where
      -- mutate the clause but this time replace all `nm` and `tag` since nm' and tag'
      -- have already been added in the lines above
      mutateClause : CConAlt vars -> Core (CConAlt vars)
      mutateClause (MkConAlt nm' tag' args rhs) =
        pure $ MkConAlt nm' tag' args !(mkMutating nm tag rhs)
  mkMutating nm tag (CConstCase fc sc clauses wc) =
    let newClauses = traverse mapClauses clauses in
        pure $ CConstCase fc sc !newClauses wc
    where
      mapClauses : CConstAlt vars -> Core (CConstAlt vars)
      mapClauses (MkConstAlt c rhs) = pure $ MkConstAlt c !(mkMutating nm tag rhs)
  mkMutating nm tag other@(CCrash _ _) = pure other
  mkMutating nm tag other@(CErased _) = pure other
  mkMutating nm tag other@(CPrimVal _ _) = pure other
  mkMutating nm tag other@(CLocal _ _) = pure other
  mkMutating nm tag other@(CRef fc n) = pure other
  mkMutating nm tag other@(CMut _ _ _) = pure other

  ||| Given a name/tag for a constructor, replace all occurences of constructing that value
  ||| on the rhs of a case alternatuve.
  mutateCaseAlt : {auto c : Ref Ctxt Defs} -> {vars : _} -> CConAlt vars -> Core (CConAlt vars)
  mutateCaseAlt (MkConAlt nm tag args rhs) = MkConAlt nm tag args <$> (mkMutating nm tag rhs)

export
addMutatingCases : {auto c : Ref Ctxt Defs} -> Name -> Core ()
addMutatingCases n = do
  defs <- get Ctxt
  Just def <- lookupCtxtExact n (gamma defs)  | _ => pure ()
  let Just (MkFun fargs body) = compexpr def | _ => pure ()
  setCompiled n (MkFun fargs !(mkMutating (UN "") Nothing body))

export
updateMutating : {auto c : Ref Ctxt Defs} -> Name -> Core ()
updateMutating n = do
  defs <- get Ctxt
  Just def <- lookupCtxtExact n (gamma defs)  | _ => pure ()
  corePrint $ show !(getFullName n)
  corePrint $ show $ flags def
  corePrint $ show $ Mutating `elem` flags def
  if Mutating `elem` flags def
     then do corePrint "mutating flag found"
             let Just (MkFun fargs body) = compexpr def
               | _ => do corePrint "false alert" ; pure ()
             setCompiled n (MkFun fargs !(mkMutating (UN "") Nothing body))
     else pure ()

