module Core.InitPrimitives

import Compiler.CompileExpr

import Core.Context
import Core.Primitives

%default covering

parameters {auto c : Ref Ctxt Defs}
           {auto w : AppendOnly Warn Warning}
  addPrim : Prim -> Core ()
  addPrim p
      = do addBuiltin (opName (fn p)) (type p) (totality p) (fn p)
           compileDef (opName (fn p))

  export
  addPrimitives : Core ()
  addPrimitives
      = traverse_ addPrim allPrimitives
