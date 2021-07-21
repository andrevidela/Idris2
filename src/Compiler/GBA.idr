module Compiler.GBA

import Compiler.ANF
import Compiler.VMCode
import Compiler.Common
import Core.Context
import Core.Core
import Data.String
import Idris.Doc.String

corePutStrLn : String -> Core ()
corePutStrLn = coreLift . putStrLn

corePrint : Show a => a -> Core ()
corePrint = corePutStrLn . show

star : Doc ann
star = pretty '*'


namespace CDSL
  public export
  data Op = Plus
          | Times
          | Minus
          | Div

  public export
  data CType = Plain String
             | Ptr CType
             -- | FnPtr (List CType) CType -- I'll figure that one later

  public export
  data Expr = FCall String (List Expr)
            | BoolLit Bool
            | IntLit Int
            | While Expr (List Expr)
            | Var String
            | VarAssign String Expr
            | Deref Expr
            | Infix Expr Op Expr
            | Prefix Op Expr

  public export
  data TopDef : Type where
    Include : String -> TopDef
    ProtoDef : (return : CType) -> (name : String) -> (args : List (CType, String)) -> TopDef
    FnDef : (return : CType) -> (name : String) -> (args : List (CType, String)) -> (body : List Expr) -> TopDef
    VarDef : CType -> (name : String) -> (rhs : Expr) -> TopDef
    EnumDef : (name : String) -> (values : List String) -> TopDef
    StructDef : (name : String) -> (fields : List (CType, String)) -> TopDef

renderOp : Op -> Doc ann
renderOp Plus = pretty '+'
renderOp Times = star
renderOp Minus = pretty '-'
renderOp Div = pretty '/'


renderVarTy : CType -> String -> Doc String
renderVarTy y = ?renderVarTy_rhs

renderTy : CType -> Doc ann
renderTy (Plain x) = pretty x
renderTy (Ptr x) = renderTy x <+> star

renderExpr : Expr -> Doc String
renderExpr (FCall x xs) = pretty x <+> tupled (map renderExpr xs)
renderExpr (Var x) = pretty x
renderExpr (VarAssign x y) = pretty x <++> equals <++> renderExpr y
renderExpr (Deref x) = star <+> parens (renderExpr x)
renderExpr (Infix x y z) = parens (renderExpr x <++> renderOp y <++> renderExpr z)
renderExpr (Prefix x y) = ?renderExpr_rhs_6
renderExpr (While cond body) = pretty "while" <+> parens (renderExpr cond) <++> braces
    (hardline <+> indent 4 (vsep (map ((<+> semi) . renderExpr) body)) <+>
     hardline)
renderExpr (BoolLit True) = "1"
renderExpr (BoolLit False) = "0"
renderExpr (IntLit int) = pretty int

render : TopDef -> Doc String
render (Include x) = pretty "#include" <++> angles (pretty x)
render (ProtoDef return name args) = ?whu

-- FnDef : void fname(ty1 arg1, ty2 arg2) {
--             body;
--             ...
--         }
render (FnDef x name args body) =
  renderTy x <++> pretty name <+> tupled (map (uncurry renderVarTy) args) <+> braces (
    hardline <+> indent 4 (vsep (map ((<+> semi) . renderExpr) body)) <+>
    hardline)
render (VarDef ty name rhs) =
  renderTy ty <++> pretty name <++> equals <++> renderExpr rhs <+> semi
render (EnumDef name values) = ?rest_render_5
render (StructDef name fields) = ?rest_render_6

void : CType
void = Plain "void"

compileANF : Ref Ctxt Defs => Name -> ANFDef -> Core TopDef
compileANF name (MkAFun args x) = do
  nm <- toFullNames name
  corePutStrLn "printing function \{show nm}, with args \{show args}, and body \{show x}"
  let fn = FnDef (Ptr void) (show nm) ?args ?expt
  -- pure (FnDef (Ptr void)
  ?rest

compileANF name (MkACon tag arity nt) =
  throw (InternalError "constructor detected, nothing to write")
compileANF name (MkAForeign ccs fargs x) =
  ?compileANF_rhs_3
compileANF name (MkAError x) =
  throw (InternalError "MkError in ANF tree")

builtins : List (String, TopDef)
builtins = [("Main.loop", FnDef (Plain "int") "_while" [] [While (BoolLit True) []])]

compileVMCode : Ref Ctxt Defs => Name -> VMDef -> Core TopDef
compileVMCode nm code = do
  nm <- toFullNames nm
  corePutStrLn "printing function \{show nm} with code \{show code}"
  ?whut
  -- pure (FnDef (Plain "int") "main"  [] [])

var : Int -> String
var i = "var_\{show i}"

convertInstruction : VMInst -> List Expr
convertInstruction (DECLARE RVal) = []
convertInstruction (DECLARE (Loc x)) = [Var "var_\{show x}"]
convertInstruction (DECLARE Discard) = []
convertInstruction START = []
convertInstruction (ASSIGN (Loc x) y) = [VarAssign "var_\{show x}" ?exp]
convertInstruction (ASSIGN Discard y) = []
convertInstruction (ASSIGN RVal y) = []
convertInstruction (MKCON x tag args) = ?convertInstruction_rhs_4
convertInstruction (MKCLOSURE x y missing args) = ?convertInstruction_rhs_5
convertInstruction (MKCONSTANT x y) = ?convertInstruction_rhs_6
convertInstruction (APPLY (Loc x) (Loc f) a) = [VarAssign (var x) (FCall (var f) ?wsdhu)]
convertInstruction (CALL x tailpos y args) = ?convertInstruction_rhs_8
convertInstruction (OP x y xs) = ?convertInstruction_rhs_9
convertInstruction (EXTPRIM x y xs) = ?convertInstruction_rhs_10
convertInstruction (CASE x alts def) = ?convertInstruction_rhs_11
convertInstruction (CONSTCASE x alts def) = ?convertInstruction_rhs_12
convertInstruction (PROJECT x value pos) = ?convertInstruction_rhs_13
convertInstruction (NULL x) = ?convertInstruction_rhs_14
convertInstruction (ERROR x) = ?convertInstruction_rhs_15

compileBody : List (Name, VMDef) -> VMDef -> Core (List Expr)
compileBody xs (MkVMFun args []) = pure []
compileBody xs (MkVMFun args (x :: ys)) = ?compileBody_rhs_4
compileBody xs (MkVMError ys) = ?compileBody_rhs_2


compileGBA : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String)
          -> ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileGBA c tmpDir outputDir tm outfile = do
  cdata <- getCompileData False VMCode tm
  let code = cdata.vmcode
  let Just main = lookup (UN "Main.main")  code
    | Nothing => throw (InternalError "cannot find main")
  mainBody <- compileBody code main
  let finalProgram  = FnDef (Plain "int") "main" [] mainBody
  -- coreLift $ putStrLn (String.unlines (map (\(x, y) => "\{show x}: \{show y}") cdata.anf))
  -- coreLift $ putStrLn (String.unlines (map (\(x, y) => "\{show x}: \{show y}") cdata.vmcode))
  -- topDef <- traverse (\(n, code) => compileVMCode n code) code
  -- corePrint (vsep $ map render topDef)
  throw (InternalError "GBA Backend unfinished")

export
codegenGBA : Codegen
codegenGBA =
  MkCG
    compileGBA
    (\_,_,_ => throw (InternalError "Cannot execute GBA program"))
    Nothing
    Nothing


