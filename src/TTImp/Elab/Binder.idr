module TTImp.Elab.Binder

import Core.Core
import Core.TT
import Core.Context
import Core.Normalise
import TTImp.TTImp

export
checkCustomBinder : Name -> (info : BinderInformation Name) -> (scope : RawImp) -> Core (Term vars, Glued vars)
checkCustomBinder binder binderInfo scope = ?checkCustomBinder_rhs
