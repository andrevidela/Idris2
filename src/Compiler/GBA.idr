module Compiler.GBA

import Compiler.Common
import Core.Context

compileGBA : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String)
          -> ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileGBA c tmpDir outputDir tm outfile = do
  cdata <- getCompileData False ANF tm
  coreLift $ putStrLn "lol"
  ?compileGBA_rhs

export
codegenGBA : Codegen
codegenGBA =
  MkCG
    compileGBA
    ?runProgram
    Nothing
    Nothing
