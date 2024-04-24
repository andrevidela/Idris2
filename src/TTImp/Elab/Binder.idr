module TTImp.Elab.Binder

import Core.Core
import Core.TT
import Core.Context
import Core.Normalise
import TTImp.TTImp

-- Elaborate expressions like `CLet (n : ty) | body`
-- where :
-- - `CLet` is the binder
-- - `n` is the name, stored inside "BinderInformation"
-- - `ty` is the type, stored inside "BinderInformation"
-- - `body` is the scope
export
checkCustomBinder : (binder : Name) -> (info : BinderInformation Name) -> (scope : RawImp) -> Core (Term vars, Glued vars)
checkCustomBinder binder binderInfo scope = do
  ?checkCustomBinder_rhs
