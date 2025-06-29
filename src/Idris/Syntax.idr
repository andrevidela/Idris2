module Idris.Syntax

import public Core.Context
import public Core.Context.Log
import public Core.Core
import public Core.FC
import public Core.Normalise
import public Core.Options
import public Core.TT
import public Core.WithData

import TTImp.TTImp

import Data.List
import Data.Maybe
import Data.SnocList
import Data.String

import public Idris.Syntax.Pragmas

import Libraries.Data.ANameMap
import Libraries.Data.NameMap
import Libraries.Data.SortedMap
import Libraries.Data.String.Extra
import Libraries.Data.StringMap
import Libraries.Data.WithDefault
import public Libraries.Data.WithData
import Libraries.Text.PrettyPrint.Prettyprinter

import Parser.Lexer.Source

%default covering

public export
data OpStr' nm = OpSymbols nm | Backticked nm

-- Left: backticked, Right: operator symbols
export
opNameToEither : OpStr' nm -> Either nm nm
opNameToEither (Backticked nm) = Left nm
opNameToEither (OpSymbols nm) = Right nm

export
Functor OpStr' where
  map f (OpSymbols x) = OpSymbols (f x)
  map f (Backticked x) = Backticked (f x)

export
Foldable OpStr' where
  foldr f i (OpSymbols x) = f x i
  foldr f i (Backticked x) = f x i

export
traverseOp : (fn : Functor f) => (a -> f b) -> OpStr' a -> f (OpStr' b)
traverseOp f (OpSymbols x) = map OpSymbols (f x)
traverseOp f (Backticked x) = map Backticked (f x)


public export
Show nm => Show (OpStr' nm) where
  show (OpSymbols nm) = show nm
  show (Backticked nm) = "`\{show nm}`"

public export
(.toName) : OpStr' nm -> nm
(.toName) (OpSymbols nm) = nm
(.toName) (Backticked nm) = nm

public export
OpStr : Type
OpStr = OpStr' Name

public export
data HidingDirective = HideName Name
                     | HideFixity Fixity Name

-------------------------------------------------------------------------------

mutual

  ||| Source language as produced by the parser
  public export
  PTerm : Type
  PTerm = PTerm' Name

  ||| Internal PTerm
  ||| Source language as produced by the unelaboration of core Terms
  ||| KindedNames carry extra information about the nature of the variable
  public export
  IPTerm : Type
  IPTerm = PTerm' KindedName

  ||| The full high level source language
  ||| This gets desugared to RawImp (TTImp.TTImp),
  ||| then elaborated to Term (Core.TT)
  public export
  data PTermBase : Type -> Type where
       -- Direct (more or less) translations to RawImp

       PRef : nm -> PTermBase nm
       -- Pi-types with an arbitrary complex binder
       NewPi : WithFC (PBinderScope' nm) -> PTermBase nm
       Forall : WithFC (List1 (WithFC Name), PTerm' nm) -> PTermBase nm

       -- Simple pi-types, translates directly into IPi, this should be replace din favor of `NewPi`
       PPi : RigCount -> PiInfo (PTerm' nm) -> Maybe Name ->
             (argTy : PTerm' nm) -> (retTy : PTerm' nm) -> PTermBase nm
       PLam : RigCount -> PiInfo (PTerm' nm) -> (pat : PTerm' nm) ->
              (argTy : PTerm' nm) -> (scope : PTerm' nm) -> PTermBase nm
       PLet : RigCount -> (pat : PTerm' nm) ->
              (nTy : PTerm' nm) -> (nVal : PTerm' nm) -> (scope : PTerm' nm) ->
              (alts : List (PClause' nm)) -> PTermBase nm
       PCase : List (PFnOpt' nm) -> PTerm' nm -> List (PClause' nm) -> PTermBase nm
       PLocal : List (PDecl' nm) -> (scope : PTerm' nm) -> PTermBase nm
       PUpdate : List (PFieldUpdate' nm) -> PTermBase nm
       PApp : PTerm' nm -> PTerm' nm -> PTermBase nm
       PWithApp : PTerm' nm -> PTerm' nm -> PTermBase nm
       PNamedApp : PTerm' nm -> Name -> PTerm' nm -> PTermBase nm
       PBindingApp : (function : WithFC Name) -> (binder : WithFC (BindingInfo (PTerm' nm))) -> (scope : WithFC (PTerm' nm)) -> PTermBase nm
       PAutoApp : PTerm' nm -> PTerm' nm -> PTermBase nm

       PDelayed : LazyReason -> PTerm' nm -> PTermBase nm
       PDelay : PTerm' nm -> PTermBase nm
       PForce : PTerm' nm -> PTermBase nm

       PSearch : (depth : Nat) -> PTermBase nm
       PPrimVal : Constant -> PTermBase nm
       PQuote : PTerm' nm -> PTermBase nm
       PQuoteName : Name -> PTermBase nm
       PQuoteDecl : List (PDecl' nm) -> PTermBase nm
       PUnquote : PTerm' nm -> PTermBase nm
       PRunElab : PTerm' nm -> PTermBase nm
       PHole : (bracket : Bool) -> (holename : String) -> PTermBase nm
       PType : PTermBase nm
       PAs : WithFC Name -> (pattern : PTerm' nm) -> PTermBase nm
       PDotted : PTerm' nm -> PTermBase nm
       PImplicit : PTermBase nm
       PInfer : PTermBase nm

       -- Operators

       POp : (lhsInfo : WithFC (OperatorLHSInfo (PTerm' nm))) ->
             WithFC (OpStr' nm) -> (rhs : PTerm' nm) -> PTermBase nm
       PPrefixOp : WithFC (OpStr' nm) -> PTerm' nm -> PTermBase nm
       PSectionL : WithFC (OpStr' nm) -> PTerm' nm -> PTermBase nm
       PSectionR : PTerm' nm -> WithFC (OpStr' nm) -> PTermBase nm
       PEq : PTerm' nm -> PTerm' nm -> PTermBase nm
       PBracketed : PTerm' nm -> PTermBase nm

       -- Syntactic sugar
       PString : (hashtag : Nat) -> List (PStr' nm) -> PTermBase nm
       PMultiline : (hashtag : Nat) -> (indent : Nat) -> List (List (PStr' nm)) -> PTermBase nm
       PDoBlock : Maybe Namespace -> List (PDo' nm) -> PTermBase nm
       PBang : PTerm' nm -> PTermBase nm
       PIdiom : Maybe Namespace -> PTerm' nm -> PTermBase nm
       PList : (nilFC : FC) -> List (FC, PTerm' nm) -> PTermBase nm
                                        -- ^   v location of the conses/snocs
       PSnocList : (nilFC : FC) -> SnocList ((FC, PTerm' nm)) -> PTermBase nm
       PPair : PTerm' nm -> PTerm' nm -> PTermBase nm
       PDPair : (opFC : FC) -> PTerm' nm -> PTerm' nm -> PTerm' nm -> PTermBase nm
       PUnit : PTermBase nm
       PIfThenElse : PTerm' nm -> PTerm' nm -> PTerm' nm -> PTermBase nm
       PComprehension : PTerm' nm -> List (PDo' nm) -> PTermBase nm
       PRewrite : PTerm' nm -> PTerm' nm -> PTermBase nm
       -- A list range  [x,y..z]
       PRange : PTerm' nm -> Maybe (PTerm' nm) -> PTerm' nm -> PTermBase nm
       -- A stream range [x,y..]
       PRangeStream : PTerm' nm -> Maybe (PTerm' nm) -> PTermBase nm
       -- r.x.y
       PPostfixApp : PTerm' nm -> List (FC, Name) -> PTermBase nm
       -- .x.y
       PPostfixAppPartial : List (FC, Name) -> PTermBase nm

       -- Debugging
       PUnifyLog : LogLevel -> PTerm' nm -> PTermBase nm

       -- with-disambiguation
       PWithUnambigNames : List (FC, Name) -> PTerm' nm -> PTermBase nm

  public export
  PTerm' : Type -> Type
  PTerm' = WithFC . PTermBase

  export
  getPTermLoc : PTerm' nm -> FC
  getPTermLoc x = x.fc

  public export
  PFieldUpdate : Type
  PFieldUpdate = PFieldUpdate' Name

  public export
  data PFieldUpdate' : Type -> Type where
       PSetField : (path : List String) -> PTerm' nm -> PFieldUpdate' nm
       PSetFieldApp : (path : List String) -> PTerm' nm -> PFieldUpdate' nm

  public export
  PDo : Type
  PDo = PDo' Name

  public export
  data PDo' : Type -> Type where
       DoExp : FC -> PTerm' nm -> PDo' nm
       DoBind : FC -> (nameFC : FC) -> Name -> RigCount -> Maybe (PTerm' nm) -> PTerm' nm -> PDo' nm
       DoBindPat : FC -> PTerm' nm -> Maybe (PTerm' nm) -> PTerm' nm -> List (PClause' nm) -> PDo' nm
       DoLet : FC -> (lhs : FC) -> Name -> RigCount -> PTerm' nm -> PTerm' nm -> PDo' nm
       DoLetPat : FC -> PTerm' nm -> PTerm' nm -> PTerm' nm -> List (PClause' nm) -> PDo' nm
       DoLetLocal : FC -> List (PDecl' nm) -> PDo' nm
       DoRewrite : FC -> PTerm' nm -> PDo' nm

  public export
  PStr : Type
  PStr = PStr' Name

  public export
  data PStr' : Type -> Type where
       StrLiteral : FC -> String -> PStr' nm
       StrInterp : FC -> PTerm' nm -> PStr' nm

  public export
  PlainMultiBinder : Type
  PlainMultiBinder = PlainMultiBinder' Name

  ||| A plain binder without information about its use
  ||| plainBinder := name ':' term
  public export
  PlainMultiBinder' : (nm : Type) -> Type
  PlainMultiBinder' nm = List1 (WithName (PTerm' nm))

  public export
  PlainBinder : Type
  PlainBinder = PlainBinder' Name

  ||| A plain binder without information about its use
  ||| plainBinder := name ':' term
  public export
  PlainBinder' : (nm : Type) -> Type
  PlainBinder' nm  = WithName (PTerm' nm)

  public export
  BasicMultiBinder : Type
  BasicMultiBinder = BasicMultiBinder' Name

  ||| A binder with quantity information attached
  ||| basicBinder := qty plainBinder
  public export
  record BasicMultiBinder' (nm : Type) where
    constructor MkBasicMultiBinder
    rig : RigCount
    names : List1 (WithFC Name)
    type : PTerm' nm

  public export
  BasicBinder : Type
  BasicBinder = BasicBinder' Name

  ||| A binder with quantity information attached
  ||| basicBinder := qty plainBinder
  public export
  BasicBinder' : Type -> Type
  BasicBinder' = WithData [Rig', Name'] . PTerm'

  MkBasicBinder : RigCount -> WithFC Name -> PTerm' nm -> BasicBinder' nm
  MkBasicBinder rig nm term = Mk [rig, nm] term

  public export
  PBinder : Type
  PBinder = PBinder' Name

  ||| A binder with information about how it is binding
  ||| pbinder := '{' basicBinder '}'
  |||          | '{' auto basicBinder '}'
  |||          | '{' default term basicBinder '}'
  |||          | '(' basicBinder ')'
  public export
  record PBinder' (nm : Type) where
    constructor MkPBinder
    info : PiInfo (PTerm' nm)
    bind : BasicMultiBinder' nm

  public export
  PImpBinder' : (nm : Type) -> Type
  PImpBinder' = GenericBinder . PTerm'

  public export
  PBinderScope : Type
  PBinderScope = PBinderScope' Name

  public export
  record PBinderScope' (nm : Type) where
    constructor MkPBinderScope
    binder : PBinder' nm
    scope : PTerm' nm

  public export
  MkFullBinder : PiInfo (PTerm' nm) -> RigCount -> WithFC Name -> PTerm' nm -> PBinder' nm
  MkFullBinder info rig x y = MkPBinder info (MkBasicMultiBinder rig (singleton x) y)


  export
  getLoc : PDo' nm -> FC
  getLoc (DoExp fc _) = fc
  getLoc (DoBind fc _ _ _ _ _) = fc
  getLoc (DoBindPat fc _ _ _ _) = fc
  getLoc (DoLet fc _ _ _ _ _) = fc
  getLoc (DoLetPat fc _ _ _ _) = fc
  getLoc (DoLetLocal fc _) = fc
  getLoc (DoRewrite fc _) = fc

  export
  papply : FC -> PTerm' nm -> List (PTerm' nm) -> PTerm' nm
  papply fc f [] = f
  papply fc f (a :: as) = papply fc (MkFCVal fc $ PApp f a) as

  export
  applyArgs : PTerm' nm -> List (FC, PTerm' nm) -> PTerm' nm
  applyArgs f [] = f
  applyArgs f ((fc, a) :: args) = applyArgs (MkFCVal fc $ PApp f a) args

  export
  applyWithArgs : PTerm' nm -> List (FC, PTerm' nm) -> PTerm' nm
  applyWithArgs f [] = f
  applyWithArgs f ((fc, a) :: args) = applyWithArgs (MkFCVal fc $ PWithApp f a) args

  public export
  PTypeDecl : Type
  PTypeDecl = PTypeDecl' Name

  public export
  record PTypeDeclData' (nm : Type) where
      constructor MkPTy
      -- List of names and their associated documentation
      -- If no documentation is provided the first projection is `""`
      names : List1 (String, WithFC Name)
      doc: String
      type : PTerm' nm -- probably need `WithFC` here to fix #3408

  public export
  PTypeDecl' : Type -> Type
  PTypeDecl' nm = WithFC (PTypeDeclData' nm)

  export
  (.nameList) : PTypeDecl' nm -> List Name
  (.nameList) = forget . map (val . snd) . names . val

  public export
  PDataDecl : Type
  PDataDecl = PDataDecl' Name

  public export
  data PDataDecl' : Type -> Type where
       MkPData : FC -> (tyname : FCBind Name) ->
                 -- if we have already declared the type earlier using `MkPLater`,
                 -- we are allowed to leave the telescope out here
                 (tycon : Maybe (PTerm' nm)) ->
                 (opts : List DataOpt) ->
                 (datacons : List (AddMetadata Bind' (PTypeDecl' nm))) -> PDataDecl' nm
       MkPLater : FC -> (tyname : FCBind Name) -> (tycon : PTerm' nm) -> PDataDecl' nm

  public export
  data PRecordDecl' : Type -> Type where
       MkPRecord : (tyname : FCBind Name) ->
                   (params : List (PBinder' nm)) ->
                   (opts : List DataOpt) ->
                   (conName : Maybe (DocBindFC Name)) ->
                   (decls : List (PField' nm)) ->
                   PRecordDecl' nm
       MkPRecordLater : (tyname : FCBind Name) ->
                        (params : List (PBinder' nm)) ->
                        PRecordDecl' nm

  export
  getPDataDeclLoc : PDataDecl' nm -> FC
  getPDataDeclLoc (MkPData fc _ _ _ _) = fc
  getPDataDeclLoc (MkPLater fc _ _) = fc

  public export
  PWithProblem : Type
  PWithProblem = PWithProblem' Name


  public export
  record PWithProblem' (nm : Type) where
    constructor MkPWithProblem
    withRigCount : RigCount
    withRigValue : PTerm' nm
    withRigProof : Maybe (RigCount, Name) -- This ought to be a `Basic` username

  public export
  PClause : Type
  PClause = PClause' Name

  public export
  data PClauseBase : Type -> Type where
       MkPatClause : (lhs : PTerm' nm) -> (rhs : PTerm' nm) ->
                     (whereblock : List (PDecl' nm)) -> PClauseBase nm
       MkWithClause : (lhs : PTerm' nm) -> List1 (PWithProblem' nm) ->
                      List WithFlag -> List (PClause' nm) -> PClauseBase nm
       MkImpossible : (lhs : PTerm' nm) -> PClauseBase nm

  public export
  PClause' : Type -> Type
  PClause' = WithFC . PClauseBase

  export
  getPClauseLoc : PClause -> FC
  getPClauseLoc x = x.fc

  public export
  data Directive : Type where
       Hide : HidingDirective -> Directive
       Unhide : Name -> Directive
       Logging : Maybe LogLevel -> Directive
       LazyOn : Bool -> Directive
       UnboundImplicits : Bool -> Directive
       AmbigDepth : Nat -> Directive
       TotalityDepth: Nat -> Directive
       PairNames : Name -> Name -> Name -> Directive
       RewriteName : Name -> Name -> Directive
       PrimInteger : Name -> Directive
       PrimString : Name -> Directive
       PrimChar : Name -> Directive
       PrimDouble : Name -> Directive
       PrimTTImp : Name -> Directive
       PrimName : Name -> Directive
       PrimDecls : Name -> Directive
       CGAction : String -> String -> Directive
       Names : Name -> List String -> Directive
       StartExpr : PTerm' nm -> Directive
       Overloadable : Name -> Directive
       Extension : LangExt -> Directive
       DefaultTotality : TotalReq -> Directive
       PrefixRecordProjections : Bool -> Directive
       AutoImplicitDepth : Nat -> Directive
       NFMetavarThreshold : Nat -> Directive
       SearchTimeout : Integer -> Directive
       -- There is no nm on Directive
       ForeignImpl : Name -> List PTerm -> Directive


  public export
  record RecordField' (nm : Type) where
    constructor MkRecordField
    doc : String
    rig : RigCount
    piInfo : PiInfo (PTerm' nm)
    names : List Name -- See #3409
    type : PTerm' nm

  public export
  PField : Type
  PField = PField' Name

  public export
  PField' : Type -> Type
  PField' nm = WithFC (RecordField' nm)

  public export
  0 PRecordDeclLet : Type
  PRecordDeclLet = PRecordDeclLet' Name

  public export
  data PRecordDeclLet' : Type -> Type where
    RecordClaim : WithFC (PClaimData' nm) -> PRecordDeclLet' nm
    RecordClause : WithFC (PClause' nm) -> PRecordDeclLet' nm

  -- For noting the pass we're in when desugaring a mutual block
  -- TODO: Decide whether we want mutual blocks!
  public export
  data Pass = Single | AsType | AsDef

  export
  Eq Pass where
    Single == Single = True
    AsType == AsType = True
    AsDef == AsDef = True
    _ == _ = False

  export
  typePass : Pass -> Bool
  typePass p = p == Single || p == AsType

  export
  defPass : Pass -> Bool
  defPass p = p == Single || p == AsDef

  public export
  PFnOpt : Type
  PFnOpt = PFnOpt' Name

  public export
  data PFnOpt' : Type -> Type where
       IFnOpt : FnOpt' nm -> PFnOpt' nm
       PForeign : List (PTerm' nm) -> PFnOpt' nm
       PForeignExport : List (PTerm' nm) -> PFnOpt' nm

  public export
  PClaimData : Type
  PClaimData = PClaimData' Name

  public export
  record PClaimData' (nm : Type) where
    constructor MkPClaim
    qty : RigCount
    vis : Visibility
    opts : List (PFnOpt' nm)
    type : AddMetadata Bind' (PTypeDecl' nm)

  public export
  record PFixityData where
    constructor MkPFixityData
    exportModifier : WithDefault Visibility Export
    binding : BindingModifier
    fixity : Fixity
    precedence : Nat
    operators : List1 OpStr

  public export
  PDecl : Type
  PDecl = PDecl' Name

  public export
  data PDeclNoFC' : Type -> Type where
       PClaim : PClaimData' nm -> PDeclNoFC' nm
       PDef : List (PClause' nm) -> PDeclNoFC' nm
       PData : (doc : String) -> WithDefault Visibility Private ->
               Maybe TotalReq -> PDataDecl' nm -> PDeclNoFC' nm
       PParameters : Either (List1 (PlainBinder' nm))
                            (List1 (PBinder' nm)) ->
                     List (PDecl' nm) -> PDeclNoFC' nm
       PUsing : List (Maybe Name, PTerm' nm) ->
                List (PDecl' nm) -> PDeclNoFC' nm
       PInterface : WithDefault Visibility Private ->
                    (constraints : List (Maybe Name, PTerm' nm)) ->
                    (typeName : Name) -> -- Those two should be merged into
                    (doc : String) ->    --  WithData [Doc', FC'] Name
                    (params : List (BasicMultiBinder' nm)) ->
                    (det : Maybe (List1 Name)) ->
                    (conName : Maybe (DocBindFC Name)) ->
                    List (PDecl' nm) ->
                    PDeclNoFC' nm
       PImplementation : Visibility -> List PFnOpt -> Pass ->
                         (implicits : List (FC, RigCount, Name, PiInfo (PTerm' nm), PTerm' nm)) ->
                         (constraints : List (Maybe Name, PTerm' nm)) ->
                         Name ->
                         (params : List (PTerm' nm)) ->
                         (implName : Maybe Name) ->
                         (nusing : List Name) ->
                         Maybe (List (PDecl' nm)) ->
                         PDeclNoFC' nm
       PRecord : (doc : String) ->
                 WithDefault Visibility Private ->
                 Maybe TotalReq ->
                 PRecordDecl' nm ->
                 PDeclNoFC' nm

       -- TODO: PPostulate
       -- TODO: POpen (for opening named interfaces)
       ||| PFail is a failing block. The string must appear as a
       ||| substring of the error message raised when checking the block.
       PFail : Maybe String -> List (PDecl' nm) -> PDeclNoFC' nm

       PMutual : List (PDecl' nm) -> PDeclNoFC' nm
       PFixity : PFixityData -> PDeclNoFC' nm
       PNamespace : Namespace -> List (PDecl' nm) -> PDeclNoFC' nm
       PTransform : String -> PTerm' nm -> PTerm' nm -> PDeclNoFC' nm
       PRunElabDecl : PTerm' nm -> PDeclNoFC' nm
       PDirective : Directive -> PDeclNoFC' nm
       PBuiltin : BuiltinType -> Name -> PDeclNoFC' nm

  public export
  PDeclNoFC : Type
  PDeclNoFC = PDeclNoFC' Name

  public export
  PDecl' : Type -> Type
  PDecl' x = WithFC (PDeclNoFC' x)

  export
  getPDeclLoc : PDecl' nm -> FC
  getPDeclLoc x = x.fc

export
isStrInterp : PStr -> Maybe FC
isStrInterp (StrInterp fc _) = Just fc
isStrInterp (StrLiteral _ _) = Nothing

export
isStrLiteral : PStr -> Maybe (FC, String)
isStrLiteral (StrInterp _ _) = Nothing
isStrLiteral (StrLiteral fc str) = Just (fc, str)

export
isPDef : PDecl -> Maybe (WithFC (List PClause))
isPDef (MkWithData fc (PDef cs)) = Just (MkWithData fc cs)
isPDef _ = Nothing


definedInData : PDataDecl -> List Name
definedInData (MkPData _ n _ _ cons) = n.val :: concatMap ((.nameList) . drop) cons
definedInData (MkPLater _ n _) = [n.val]

export
definedIn : List PDeclNoFC -> List Name
definedIn [] = []
definedIn (PClaim claim :: ds) = claim.type.drop.nameList ++ definedIn ds
definedIn (PData _ _ _ d :: ds) = definedInData d ++ definedIn ds
definedIn (PParameters _ pds :: ds) = definedIn (map val pds) ++ definedIn ds
definedIn (PUsing _ pds :: ds) = definedIn (map val pds) ++ definedIn ds
definedIn (PNamespace _ ns :: ds) = definedIn (map val ns) ++ definedIn ds
definedIn (_ :: ds) = definedIn ds

public export
data REPLEval : Type where
     EvalTC : REPLEval -- Evaluate as if part of the typechecker
     NormaliseAll : REPLEval -- Normalise everything (default)
     Execute : REPLEval -- Evaluate then pass to an executer
     Scheme : REPLEval -- Use the scheme evaluator

export
Show REPLEval where
  show EvalTC = "typecheck"
  show NormaliseAll = "normalise"
  show Execute = "execute"
  show Scheme = "scheme"

export
Pretty Void REPLEval where
  pretty EvalTC = pretty "typecheck"
  pretty NormaliseAll = pretty "normalise"
  pretty Execute = pretty "execute"
  pretty Scheme = pretty "scheme"

public export
data REPLOpt : Type where
     ShowImplicits : Bool -> REPLOpt
     ShowNamespace : Bool -> REPLOpt
     ShowMachineNames : Bool -> REPLOpt
     ShowTypes : Bool -> REPLOpt
     EvalMode : REPLEval -> REPLOpt
     Editor : String -> REPLOpt
     CG : String -> REPLOpt
     Profile : Bool -> REPLOpt
     EvalTiming : Bool -> REPLOpt

export
Show REPLOpt where
  show (ShowImplicits impl) = "showimplicits = " ++ show impl
  show (ShowNamespace ns) = "shownamespace = " ++ show ns
  show (ShowMachineNames mn) = "showmachinenames = " ++ show mn
  show (ShowTypes typs) = "showtypes = " ++ show typs
  show (EvalMode mod) = "eval = " ++ show mod
  show (Editor editor) = "editor = " ++ show editor
  show (CG str) = "cg = " ++ str
  show (Profile p) = "profile = " ++ show p
  show (EvalTiming p) = "evaltiming = " ++ show p

export
Pretty Void REPLOpt where
  pretty (ShowImplicits impl) = "showimplicits" <++> equals <++> pretty (show impl)
  pretty (ShowNamespace ns) = "shownamespace" <++> equals <++> pretty (show ns)
  pretty (ShowMachineNames mn) = "showmachinenames" <++> equals <++> pretty (show mn)
  pretty (ShowTypes typs) = "showtypes" <++> equals <++> pretty (show typs)
  pretty (EvalMode mod) = "eval" <++> equals <++> pretty mod
  pretty (Editor editor) = "editor" <++> equals <++> pretty editor
  pretty (CG str) = "cg" <++> equals <++> pretty str
  pretty (Profile p) = "profile" <++> equals <++> pretty (show p)
  pretty (EvalTiming p) = "evaltiming" <++> equals <++> pretty (show p)

public export
data EditCmd : Type where
     TypeAt : Int -> Int -> Name -> EditCmd
     CaseSplit : Bool -> Int -> Int -> Name -> EditCmd
     AddClause : Bool -> Int -> Name -> EditCmd
     Refine : Bool -> Int -> (hole : Name) -> (expr : PTerm) -> EditCmd
     Intro : Bool -> Int -> (hole : Name) -> EditCmd
     ExprSearch : Bool -> Int -> Name -> List Name -> EditCmd
     ExprSearchNext : EditCmd
     GenerateDef : Bool -> Int -> Name -> Nat -> EditCmd
     GenerateDefNext : EditCmd
     MakeLemma : Bool -> Int -> Name -> EditCmd
     MakeCase : Bool -> Int -> Name -> EditCmd
     MakeWith : Bool -> Int -> Name -> EditCmd

public export
data BracketType
  = IdiomBrackets
  | NameQuote
  | TermQuote
  | DeclQuote

public export
data DocDirective : Type where
  ||| A reserved keyword
  Keyword : String -> DocDirective
  ||| A reserved symbol
  Symbol  : String -> DocDirective
  ||| A type of brackets
  Bracket : BracketType -> DocDirective
  ||| An arbitrary PTerm
  APTerm  : PTerm -> DocDirective
  ||| A module name
  AModule : ModuleIdent -> DocDirective

public export
data HelpType : Type where
  GenericHelp : HelpType
  DetailedHelp : (details : String) -> HelpType

public export
data REPLCmd : Type where
     NewDefn : List PDecl -> REPLCmd
     Eval : PTerm -> REPLCmd
     Check : PTerm -> REPLCmd
     CheckWithImplicits : PTerm -> REPLCmd
     PrintDef : PTerm -> REPLCmd
     Reload : REPLCmd
     Load : String -> REPLCmd
     ImportMod : ModuleIdent -> REPLCmd
     Edit : REPLCmd
     Compile : PTerm -> String -> REPLCmd
     Exec : PTerm -> REPLCmd
     Help : HelpType -> REPLCmd
     TypeSearch : PTerm -> REPLCmd
     FuzzyTypeSearch : PTerm -> REPLCmd
     DebugInfo : Name -> REPLCmd
     SetOpt : REPLOpt -> REPLCmd
     GetOpts : REPLCmd
     CGDirective : String -> REPLCmd
     CD : String -> REPLCmd
     CWD: REPLCmd
     Missing : Name -> REPLCmd
     Total : Name -> REPLCmd
     Doc : DocDirective -> REPLCmd
     Browse : Namespace -> REPLCmd
     SetLog : Maybe LogLevel -> REPLCmd
     SetConsoleWidth : Maybe Nat -> REPLCmd
     SetColor : Bool -> REPLCmd
     Metavars : REPLCmd
     Editing : EditCmd -> REPLCmd
     RunShellCommand : String -> REPLCmd
     ShowVersion : REPLCmd
     Quit : REPLCmd
     NOP : REPLCmd
     ImportPackage : String -> REPLCmd

public export
record Import where
  constructor MkImport
  loc : FC
  reexport : Bool
  path : ModuleIdent
  nameAs : Namespace

export
Show Import where
  show (MkImport loc reexport path nameAs)
    = unwords $ catMaybes
      [ Just "import"
      , "public" <$ guard reexport
      , Just (show path)
      , ("as " ++ show nameAs) <$ guard (miAsNamespace path /= nameAs)
      ]

public export
record Module where
  constructor MkModule
  headerLoc : FC
  moduleNS : ModuleIdent
  imports : List Import
  documentation : String
  decls : List PDecl

parameters {0 nm : Type} (toName : nm -> Name)

  showAlt' : PClauseBase nm -> String
  showAlt : PClause' nm -> String
  showAlt x = showAlt' x.val
  showDo : PDo' nm -> String
  showPStr : PStr' nm -> String
  showUpdate : PFieldUpdate' nm -> String
  showPTermPrec' : Prec -> PTermBase nm -> String
  showPTermPrec : Prec -> PTerm' nm -> String
  showPTermPrec prec term = showPTermPrec' prec term.val
  showOpPrec : Prec -> OpStr' nm -> String
  showPBinder : Prec -> PBinder' nm -> String
  showBasicMultiBinder : BasicMultiBinder' nm -> String

  showPTerm : PTerm' nm -> String
  showPTerm term = showPTermPrec Open term

  showAlt' (MkPatClause lhs rhs _) =
    " | " ++ showPTerm lhs ++ " => " ++ showPTerm rhs ++ ";"
  showAlt' (MkWithClause lhs wps flags cs) = " | <<with alts not possible>>;"
  showAlt' (MkImpossible lhs) = " | " ++ showPTerm lhs ++ " impossible;"

  showDo (DoExp _ tm) = showPTerm tm
  showDo (DoBind _ _ n rig (Just ty) tm) = showCount rig ++ show n ++ " : " ++ showPTerm ty ++ " <- " ++ showPTerm tm
  showDo (DoBind _ _ n rig _ tm) = showCount rig ++ show n ++ " <- " ++ showPTerm tm
  showDo (DoBindPat _ l (Just ty) tm alts)
      = showPTerm l ++ " : " ++ showPTerm ty ++ " <- " ++ showPTerm tm ++ concatMap showAlt alts
  showDo (DoBindPat _ l _ tm alts)
      = showPTerm l ++ " <- " ++ showPTerm tm ++ concatMap showAlt alts
  showDo (DoLet _ _ l rig _ tm) = "let " ++ show l ++ " = " ++ showPTerm tm
  showDo (DoLetPat _ l _ tm alts)
      = "let " ++ showPTerm l ++ " = " ++ showPTerm tm ++ concatMap showAlt alts
  showDo (DoLetLocal _ ds)
      -- We'll never see this when displaying a normal form...
      = "let { << definitions >>  }"
  showDo (DoRewrite _ rule)
      = "rewrite " ++ showPTerm rule

  showPStr (StrLiteral _ str) = show str
  showPStr (StrInterp _ tm) = showPTerm tm

  showUpdate (PSetField p v) = showSep "." p ++ " = " ++ showPTerm v
  showUpdate (PSetFieldApp p v) = showSep "." p ++ " $= " ++ showPTerm v

  showBasicMultiBinder (MkBasicMultiBinder rig names type)
        = "\{showCount rig} \{showNames}: \{showPTerm type}"
        where
          showNames : String
          showNames = concat $ intersperse ", " $ map (show . val) (forget names)

  showPBinder d (MkPBinder Implicit bind) = "{\{showBasicMultiBinder bind}}"
  showPBinder d (MkPBinder Explicit bind) = "(\{showBasicMultiBinder bind})"
  showPBinder d (MkPBinder AutoImplicit bind) = "{auto \{showBasicMultiBinder bind}}"
  showPBinder d (MkPBinder (DefImplicit x) bind) = "{default \{showPTerm x} \{ showBasicMultiBinder bind}}"

  showPTermPrec' d (PRef n) = showPrec d (toName n)
  showPTermPrec' d (Forall (MkWithData _ (names, scope)))
        = "forall " ++ concat (intersperse ", " (map (show . val) (forget names))) ++ " . " ++ showPTermPrec d scope
  showPTermPrec' d (NewPi (MkWithData _ (MkPBinderScope binder scope)))
        = showPBinder d binder ++ " -> "  ++ showPTermPrec d scope
  showPTermPrec' d (PPi rig Explicit Nothing arg ret)
        = showPTermPrec d arg ++ " -> " ++ showPTermPrec d ret
  showPTermPrec' d (PPi rig Explicit (Just n) arg ret)
        = "(" ++ showCount rig ++ showPrec d n
         ++ " : " ++ showPTermPrec d arg ++ ") -> "
         ++ showPTermPrec d ret
  showPTermPrec' d (PPi rig Implicit Nothing arg ret) -- shouldn't happen
        = "{" ++ showCount rig ++ "_ : " ++ showPTermPrec d arg ++ "} -> "
          ++ showPTermPrec d ret
  showPTermPrec' d (PPi rig Implicit (Just n) arg ret)
        = "{" ++ showCount rig ++ showPrec d n ++ " : " ++ showPTermPrec d arg ++ "} -> " ++ showPTermPrec d ret
  showPTermPrec' d (PPi top AutoImplicit Nothing arg ret)
        = showPTermPrec d arg ++ " => " ++ showPTermPrec d ret
  showPTermPrec' d (PPi rig AutoImplicit (Just n) arg ret)
        = "{auto " ++ showCount rig ++ showPrec d n ++ " : " ++ showPTermPrec d arg ++ "} -> " ++ showPTermPrec d ret
  showPTermPrec' d (PPi rig (DefImplicit t) Nothing arg ret) -- shouldn't happen
        = "{default " ++ showPTermPrec App t ++ " " ++ showCount rig ++ "_ : " ++ showPTermPrec d arg ++ "} -> " ++ showPTermPrec d ret
  showPTermPrec' d (PPi rig (DefImplicit t) (Just n) arg ret)
        = "{default " ++ showPTermPrec App t ++ " " ++ showCount rig ++ showPrec d n ++ " : " ++ showPTermPrec d arg ++ "} -> " ++ showPTermPrec d ret
  showPTermPrec' d (PLam rig _ n (MkWithData _ PImplicit) sc)
        = "\\" ++ showCount rig ++ showPTermPrec d n ++ " => " ++ showPTermPrec d sc
  showPTermPrec' d (PLam rig _ n ty sc)
        = "\\" ++ showCount rig ++ showPTermPrec d n ++ " : " ++ showPTermPrec d ty ++ " => " ++ showPTermPrec d sc
  showPTermPrec' d (PLet rig n (MkWithData _ PImplicit) val sc alts)
        = "let " ++ showCount rig ++ showPTermPrec d n ++ " = " ++ showPTermPrec d val ++ " in " ++ showPTermPrec d sc
  showPTermPrec' d (PLet rig n ty val sc alts)
        = "let " ++ showCount rig ++ showPTermPrec d n ++ " : " ++ showPTermPrec d ty ++ " = "
                 ++ showPTermPrec d val ++ concatMap showAlt alts ++
                 " in " ++ showPTermPrec d sc
  showPTermPrec' _ (PCase _ tm cs)
        = "case " ++ showPTerm tm ++ " of { " ++
            showSep " ; " (map (showCase . val) cs) ++ " }"
      where
        showCase : PClauseBase nm -> String
        showCase (MkPatClause lhs rhs _) = showPTerm lhs ++ " => " ++ showPTerm rhs
        showCase (MkWithClause lhs _ flags _) = " | <<with alts not possible>>"
        showCase (MkImpossible lhs) = showPTerm lhs ++ " impossible"
  showPTermPrec' d (PLocal ds sc) -- We'll never see this when displaying a normal form...
        = "let { << definitions >>  } in " ++ showPTermPrec d sc
  showPTermPrec' d (PUpdate fs)
        = "record { " ++ showSep ", " (map showUpdate fs) ++ " }"
  showPTermPrec' d (PApp f a) =
      let catchall : Lazy String := showPTermPrec App f ++ " " ++ showPTermPrec App a in
      case f.val of
        PRef n =>
          if isJust (isRF (toName n))
          then showPTermPrec App a ++ " " ++ showPTermPrec App f
          else catchall
        _ => catchall
  showPTermPrec' d (PWithApp f a) = showPTermPrec d f ++ " | " ++ showPTermPrec d a
  showPTermPrec' d (PAutoApp f a)
        = showPTermPrec d f ++ " @{" ++ showPTermPrec d a ++ "}"
  showPTermPrec' d (PDelayed LInf ty)
        = showParens (d >= App) $ "Inf " ++ showPTermPrec App ty
  showPTermPrec' d (PDelayed _ ty)
        = showParens (d >= App) $ "Lazy " ++ showPTermPrec App ty
  showPTermPrec' d (PDelay tm)
        = showParens (d >= App) $ "Delay " ++ showPTermPrec App tm
  showPTermPrec' d (PForce tm)
        = showParens (d >= App) $ "Force " ++ showPTermPrec App tm
  showPTermPrec' d (PNamedApp f n (MkWithData _ $ PRef a))
        = if n == (toName a)
             then showPTermPrec d f ++ " {" ++ showPrec d n ++ "}"
             else showPTermPrec d f ++ " {" ++ showPrec d n ++ " = " ++ showPrec d (toName a) ++ "}"
  showPTermPrec' d (PNamedApp f n a)
        = showPTermPrec d f ++ " {" ++ showPrec d n ++ " = " ++ showPTermPrec d a ++ "}"

  showPTermPrec' d (PBindingApp fn bind scope)
        = ?TODO1
  showPTermPrec' _ (PSearch _) = "%search"
  showPTermPrec' d (PQuote tm) = "`(" ++ showPTermPrec d tm ++ ")"
  showPTermPrec' d (PQuoteName n) = "`{" ++ showPrec d n ++ "}"
  showPTermPrec' d (PQuoteDecl tm) = "`[ <<declaration>> ]"
  showPTermPrec' d (PUnquote tm) = "~(" ++ showPTermPrec d tm ++ ")"
  showPTermPrec' d (PRunElab tm) = "%runElab " ++ showPTermPrec d tm
  showPTermPrec' d (PPrimVal c) = showPrec d c
  showPTermPrec' _ (PHole _ n) = "?" ++ n
  showPTermPrec' _ (PType) = "Type"
  showPTermPrec' d (PAs n p) = showPrec d n.val ++ "@" ++ showPTermPrec d p
  showPTermPrec' d (PDotted p) = "." ++ showPTermPrec d p
  showPTermPrec' _ (PImplicit) = "_"
  showPTermPrec' _ (PInfer) = "?"
  showPTermPrec' d (POp (MkWithData _ $ NoBinder left) op right)
        = showPTermPrec d left ++ " " ++ showOpPrec d op.val ++ " " ++ showPTermPrec d right
  showPTermPrec' d (POp (MkWithData _ $ LHSBinder $ BindType nm left) op right)
        = "(" ++ showPTermPrec d nm ++ " : " ++ showPTermPrec d left ++ " " ++ showOpPrec d op.val ++ " " ++ showPTermPrec d right ++ ")"
  showPTermPrec' d (POp (MkWithData _ $ LHSBinder $ BindExpr nm left) op right)
        = "(" ++ showPTermPrec d nm ++ " := " ++ showPTermPrec d left ++ " " ++ showOpPrec d op.val ++ " " ++ showPTermPrec d right ++ ")"
  showPTermPrec' d (POp (MkWithData _ $ LHSBinder $ BindExplicitType nm ty left) op right)
        = "(" ++ showPTermPrec d nm ++ " : " ++ showPTermPrec d ty ++ ":=" ++ showPTermPrec d left ++ " " ++ showOpPrec d op.val ++ " " ++ showPTermPrec d right ++ ")"
  showPTermPrec' d (PPrefixOp op x) = showOpPrec d op.val ++ showPTermPrec d x
  showPTermPrec' d (PSectionL op x) = "(" ++ showOpPrec d op.val ++ " " ++ showPTermPrec d x ++ ")"
  showPTermPrec' d (PSectionR x op) = "(" ++ showPTermPrec d x ++ " " ++ showOpPrec d op.val ++ ")"
  showPTermPrec' d (PEq l r) = showPTermPrec d l ++ " = " ++ showPTermPrec d r
  showPTermPrec' d (PBracketed tm) = "(" ++ showPTermPrec d tm ++ ")"
  showPTermPrec' d (PString _ xs) = join " ++ " $ showPStr <$> xs
  showPTermPrec' d (PMultiline _ indent xs) = "multiline (" ++ (join " ++ " $ showPStr <$> concat xs) ++ ")"
  showPTermPrec' d (PDoBlock ns ds)
        = "do " ++ showSep " ; " (map showDo ds)
  showPTermPrec' d (PBang tm) = "!" ++ showPTermPrec d tm
  showPTermPrec' d (PIdiom Nothing tm) = "[|" ++ showPTermPrec d tm ++ "|]"
  showPTermPrec' d (PIdiom (Just ns) tm) = show ns ++ ".[|" ++ showPTermPrec d tm ++ "|]"
  showPTermPrec' d (PList _ xs)
        = "[" ++ showSep ", " (map (showPTermPrec d . snd) xs) ++ "]"
  showPTermPrec' d (PSnocList _ xs)
        = "[<" ++ showSep ", " (map (showPTermPrec d . snd) (xs <>> [])) ++ "]"
  showPTermPrec' d (PPair l r) = "(" ++ showPTermPrec d l ++ ", " ++ showPTermPrec d r ++ ")"
  showPTermPrec' d (PDPair _ l (MkWithData _ PImplicit) r) = "(" ++ showPTermPrec d l ++ " ** " ++ showPTermPrec d r ++ ")"
  showPTermPrec' d (PDPair _ l ty r) = "(" ++ showPTermPrec d l ++ " : " ++ showPTermPrec d ty ++
                                 " ** " ++ showPTermPrec d r ++ ")"
  showPTermPrec' _ (PUnit) = "()"
  showPTermPrec' d (PIfThenElse x t e) = "if " ++ showPTermPrec d x ++ " then " ++ showPTermPrec d t ++
                                 " else " ++ showPTermPrec d e
  showPTermPrec' d (PComprehension ret es)
        = "[" ++ showPTermPrec d (dePure ret) ++ " | " ++
                 showSep ", " (map (showDo . deGuard) es) ++ "]"
      where
        dePure : PTerm' nm -> PTerm' nm
        dePure tm@(MkWithData _ $ PApp (MkWithData _ $ PRef n) arg)
            = if dropNS (toName n) == UN (Basic "pure") then arg else tm
        dePure tm = tm

        deGuard : PDo' nm -> PDo' nm
        deGuard tm@(DoExp fc (MkWithData _ $ PApp (MkWithData _ $ PRef n) arg))
            = if dropNS (toName n) == UN (Basic "guard") then DoExp fc arg else tm
        deGuard tm = tm
  showPTermPrec' d (PRewrite rule tm)
        = "rewrite " ++ showPTermPrec d rule ++ " in " ++ showPTermPrec d tm
  showPTermPrec' d (PRange start Nothing end)
        = "[" ++ showPTermPrec d start ++ " .. " ++ showPTermPrec d end ++ "]"
  showPTermPrec' d (PRange start (Just next) end)
        = "[" ++ showPTermPrec d start ++ ", " ++ showPTermPrec d next ++ " .. " ++ showPTermPrec d end ++ "]"
  showPTermPrec' d (PRangeStream start Nothing)
        = "[" ++ showPTermPrec d start ++ " .. ]"
  showPTermPrec' d (PRangeStream start (Just next))
        = "[" ++ showPTermPrec d start ++ ", " ++ showPTermPrec d next ++ " .. ]"
  showPTermPrec' d (PUnifyLog _ tm) = showPTermPrec d tm
  showPTermPrec' d (PPostfixApp rec fields)
        = showPTermPrec d rec ++ concatMap (\n => "." ++ show n) fields
  showPTermPrec' d (PPostfixAppPartial fields)
        = concatMap (\n => "." ++ show n) fields
  showPTermPrec' d (PWithUnambigNames ns rhs)
        = "with " ++ show ns ++ " " ++ showPTermPrec d rhs

  showOpPrec d (OpSymbols op) = showPrec d (toName op)
  showOpPrec d (Backticked op) = "`\{showPrec d (toName op)}`"

export
covering
Show (PTermBase Name) where
  showPrec = showPTermPrec' id

export
covering
Show IPTerm where
  showPrec prec x = showPTermPrec rawName prec x

public export
Method : Type
Method = WithData [Tot', Name', Rig'] RawImp

export
covering
Show Method where
  show m
    = "[" ++ show m.totReq ++ "] " ++ show m.rig ++ " " ++ show m.name.val ++ " : " ++ show m.val

public export
record IFaceInfo where
  constructor MkIFaceInfo
  iconstructor : Name
  implParams : List Name
  params : List Name
  parents : List RawImp
  methods : List Method
     -- ^ name, whether a data method, and desugared type (without constraint)
  defaults : List (Name, List ImpClause)

-- If you update this, update 'extendSyn' in Desugar to keep it up to date
-- when reading imports
public export
record SyntaxInfo where
  constructor MkSyntax
  ||| Operators fixities as a map from their names to their fixity,
  ||| precedence, and the file context where that fixity was defined.
  fixities : ANameMap FixityInfo
  -- info about modules
  saveMod : List ModuleIdent -- current module name
  modDocstrings : SortedMap ModuleIdent String
  modDocexports : SortedMap ModuleIdent (List Import) -- keeping the imports that happen to be reexports
  -- info about interfaces
  saveIFaces : List Name -- interfaces defined in current session, to save
                         -- to ttc
  ifaces : ANameMap IFaceInfo
  -- info about definitions
  saveDocstrings : NameMap () -- names defined in current session
  defDocstrings : ANameMap String
  bracketholes : List Name -- hole names in argument position (so need
                           -- to be bracketed when solved)
                           -- TODO: use Set instead List
  usingImpl : List (Maybe Name, RawImp)
  startExpr : RawImp
  holeNames : List String -- hole names in the file

export
prefixes : SyntaxInfo -> ANameMap (FC, Nat)
prefixes = fromList
    . map (\(name, fx)=> (name, fx.fc, fx.precedence))
    . filter ((== Prefix) . fix . snd)
    . toList
    . fixities

export
infixes : SyntaxInfo -> ANameMap (FC, Fixity, Nat)
infixes = fromList
    . map (\(nm, fx) => (nm, fx.fc, fx.fix, fx.precedence))
    . filter ((/= Prefix) . fix . snd)
    . toList
    . fixities

HasNames IFaceInfo where
  full gam iface
      = do -- coreLift $ printLn (iconstructor iface)
           -- coreLift $ printLn (methods iface)
           pure iface

  resolved gam iface = pure iface

HasNames a => HasNames (ANameMap a) where
  full gam nmap
      = insertAll empty (toList nmap)
    where
      insertAll : ANameMap a -> List (Name, a) -> Core (ANameMap a)
      insertAll ms [] = pure ms
      insertAll ms ((k, v) :: ns)
          = insertAll (addName !(full gam k) !(full gam v) ms) ns

  resolved gam nmap
      = insertAll empty (toList nmap)
    where
      insertAll : ANameMap a -> List (Name, a) -> Core (ANameMap a)
      insertAll ms [] = pure ms
      insertAll ms ((k, v) :: ns)
          = insertAll (addName !(resolved gam k) !(resolved gam v) ms) ns

export
HasNames SyntaxInfo where
  full gam syn
      = pure $ { ifaces := !(full gam (ifaces syn))
               , bracketholes := !(traverse (full gam) (bracketholes syn))
               } syn
  resolved gam syn
      = pure $ { ifaces := !(resolved gam (ifaces syn))
               , bracketholes := !(traverse (resolved gam) (bracketholes syn))
               } syn

export
initSyntax : SyntaxInfo
initSyntax
    = MkSyntax initFixities
               []
               empty
               empty
               []
               empty
               initSaveDocStrings
               initDocStrings
               []
               []
               (IVar EmptyFC (UN $ Basic "main"))
               []

  where


    initFixities : ANameMap FixityInfo
    initFixities = fromList
      [ (UN $ Basic "-", MkFixityInfo EmptyFC Export NotBinding Prefix 10)
      , (UN $ Basic "negate", MkFixityInfo EmptyFC Export NotBinding Prefix 10) -- for documentation purposes
      , (UN $ Basic "=", MkFixityInfo EmptyFC Export NotBinding Infix 0)
      ]

    initDocStrings : ANameMap String
    initDocStrings = empty

    initSaveDocStrings : NameMap ()
    initSaveDocStrings = empty

-- A label for Syntax info in the global state
export
data Syn : Type where

export
withSyn : {auto s : Ref Syn SyntaxInfo} -> Core a -> Core a
withSyn = wrapRef Syn (\_ => pure ())

-- Add a list of reexports for a module name
export
addModDocInfo : {auto s : Ref Syn SyntaxInfo} ->
                ModuleIdent -> String -> List Import ->
                Core ()
addModDocInfo mi doc reexpts
    = update Syn { saveMod $= (mi ::)
                 , modDocexports $= insert mi reexpts
                 , modDocstrings $= insert mi doc }

||| Remove a fixity from the context
export
removeFixity :
  {auto s : Ref Syn SyntaxInfo} -> FC -> Fixity -> Name -> Core ()
removeFixity loc _ key = do
  fixityInfo <- fixities <$> get Syn
  if isJust $ lookupExact key fixityInfo
     then -- When the fixity is found, simply remove it
       update Syn ({ fixities $= removeExact key })
     else -- When the fixity is not found, find close matches
       let fixityNames : List Name = map fst (toList fixityInfo)
           closeNames = !(filterM (coreLift . closeMatch key) fixityNames)
           sameName : List Name = fst <$> lookupName (dropAllNS key) fixityInfo
           similarNamespaces = nub (closeNames ++ sameName)
       in if null similarNamespaces
             then
               throw $ GenericMsg loc "Fixity \{show key} not found"
             else
               throw $ GenericMsgSol loc "Fixity \{show key} not found" "Did you mean"
                 $ map printFixityHide similarNamespaces
  where
    printFixityHide : Name -> String
    printFixityHide nm = "%hide \{show nm}"

||| Return all fixity declarations for an operator name
export
getFixityInfo : {auto s : Ref Syn SyntaxInfo} -> String -> Core (List (Name, FixityInfo))
getFixityInfo nm = do
  syn <- get Syn
  pure $ lookupName (UN $ Basic nm) (fixities syn)

export
covering
Show PTypeDecl where
  show pty = unwords [show pty.nameList, ":", show pty.val.type.val]

export
covering
Show (PClauseBase Name) where
  show (MkPatClause lhs rhs []) = unwords [ show lhs.val, "=", show rhs.val ]
  show (MkPatClause _ _ _) = "MkPatClause"
  show (MkWithClause _ _ _ _) = "MkWithClause"
  show (MkImpossible lhs) = unwords [ show lhs.val, "impossible" ]

export
covering
Show PClaimData where
  show (MkPClaim rig _ _ sig) = showCount rig ++ show sig.drop

-- TODO: finish writing this instance
export
covering
Show PDeclNoFC where
  show (PClaim pclaim) = show pclaim
  show (PDef cls) = unlines (show <$> map val cls)
  show (PData{}) = "PData"
  show (PParameters{}) = "PParameters"
  show (PUsing{}) = "PUsing"
  show (PInterface{}) = "PInterface"
  show (PImplementation{}) = "PImplementation"
  show (PRecord{}) = "PRecord"
  show (PFail mstr ds) = unlines (unwords ("failing" :: maybe [] (pure . show) mstr) :: (show . val <$> ds))
  show (PMutual{}) = "PMutual"
  show (PFixity{}) = "PFixity"
  show (PNamespace{}) = "PNamespace"
  show (PTransform{}) = "PTransform"
  show (PRunElabDecl{}) = "PRunElabDecl"
  show (PDirective{}) = "PDirective"
  show (PBuiltin{}) = "PBuiltin"

