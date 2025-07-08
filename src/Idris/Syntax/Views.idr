module Idris.Syntax.Views

import Idris.Syntax
import Idris.Syntax.Builtin

%default total

-- update this
public export
data Arg' nm
   = Explicit FC (PTerm' nm)
   | Auto     FC (PTerm' nm)
   | Named    FC Name (PTerm' nm)

export
unArg : Arg' nm -> PTerm' nm
unArg (Explicit _ t) = t
unArg (Auto _ t) = t
unArg (Named _ _ t) = t

export
getFnArgs : (Name -> nm) -> PTermBase nm -> (PTermBase nm, List (Arg' nm))
-- getFnArgs embed fts = go fts [] where
--
--   go : PTermBase nm -> List (Arg' nm) -> (PTermBase nm, List (Arg' nm))
--   go (PApp f t) = go f.val . (Explicit ?aa t ::)
--   go (PAutoApp f t) = go f.val . (Auto ?bb t ::)
--   go (PNamedApp f n t) = go f.val . (Named ?cc n t ::)
--   go (PBracketed f) = go f.val
--   -- we don't care about the binder info here
--   go (POp leftSide op r) =
--     (PRef op.val.toName,) . (Explicit ?loc leftSide.val.getLhs ::) . (Explicit ?fc r ::)
--   go (PEq l r) = (PRef $ embed eqName,) . (Explicit ?fc2 l ::) . (Explicit ?fc3 r ::)
--   -- ambiguous, picking the type constructor here
--   go (PPair l r) = (PRef $ embed pairname,) . (Explicit ?fc4 l ::) . (Explicit ?fc5 r ::)
--   go (PDPair fc l ty r)
--     = (PRef $ embed dpairname,)
--     . (Explicit ?fc6 l ::) . (Explicit ?fc7 ty ::) . (Explicit ?fc8 r ::)
--   go f = (f,)

export
underPis : PTerm' nm -> (List (Maybe Name, Binder (PTerm' nm)), PTerm' nm)
underPis abs = go abs [] where

  go : PTerm' nm -> List (Maybe Name, Binder (PTerm' nm)) ->
       (List (Maybe Name, Binder (PTerm' nm)), PTerm' nm)
  go pi@(MkWithData _ $ PPi rig pinfo mn a b) = go b . ((mn, Pi pi.fc rig pinfo a) ::)
  go (MkWithData _ $ PBracketed abs) = go abs
  go abs = (, abs)

export
underLams : PTerm' nm -> (List (PTerm' nm, Binder (PTerm' nm)), PTerm' nm)
underLams fs = go fs [] where

  go : PTerm' nm -> List (PTerm' nm, Binder (PTerm' nm)) ->
       (List (PTerm' nm, Binder (PTerm' nm)), PTerm' nm)
  go (MkWithData _ $ PBracketed f) = go f
  go lam@(MkWithData _ $ PLam rig pinfo pat a sc) = go sc . ((pat, Lam lam.fc rig pinfo a) ::)
  go fs = (,fs)
