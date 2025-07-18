module Idris.Pretty

import Core.Metadata
import Data.List
import Data.SnocList
import Data.Maybe
import Data.String
import Libraries.Control.ANSI.SGR
import Libraries.Data.String.Extra

import Parser.Lexer.Source

import public Idris.Pretty.Annotations
import public Idris.Pretty.Render

import public Libraries.Text.PrettyPrint.Prettyprinter
import public Libraries.Text.PrettyPrint.Prettyprinter.Util

import Idris.REPL.Opts
import Idris.Syntax

%default covering

%hide Symbols.equals
%hide Symbols.semi

export
syntaxToDecoration : IdrisSyntax -> Maybe Decoration
syntaxToDecoration Hole     = Nothing
syntaxToDecoration (TCon{}) = pure Typ
syntaxToDecoration (DCon{}) = pure Data
syntaxToDecoration (Fun{})  = pure Function
syntaxToDecoration Bound    = pure Bound
syntaxToDecoration Keyword  = pure Keyword
syntaxToDecoration Pragma   = Nothing

export
kindAnn : KindedName -> Maybe IdrisSyntax
kindAnn (MkKindedName mcat fn nm) = do
    cat <- mcat
    pure $ case cat of
      Bound     => Bound
      Func      => Fun fn
      DataCon{} => DCon (Just fn)
      TyCon{}   => TCon (Just fn)

export
showCategory : (IdrisSyntax -> ann) -> GlobalDef -> Doc ann -> Doc ann
showCategory embed def = annotateM (embed <$> kindAnn (gDefKindedName def))

public export
data IdrisAnn
  = Warning
  | Error
  | ErrorDesc
  | FileCtxt
  | Code
  | Meta
  | Syntax IdrisSyntax
  | UserDocString

export
annToDecoration : IdrisAnn -> Maybe Decoration
annToDecoration (Syntax syn) = syntaxToDecoration syn
annToDecoration _ = Nothing

export
syntaxAnn : IdrisSyntax -> AnsiStyle
syntaxAnn Hole = color BrightGreen
syntaxAnn (TCon{}) = color BrightBlue
syntaxAnn (DCon{}) = color BrightRed
syntaxAnn (Fun{})  = color BrightGreen
syntaxAnn Bound    = italic
syntaxAnn Keyword  = color BrightWhite
syntaxAnn Pragma   = color BrightMagenta

export
colorAnn : IdrisAnn -> AnsiStyle
colorAnn Warning = color Yellow <+> bold
colorAnn Error = color BrightRed <+> bold
colorAnn ErrorDesc = bold
colorAnn FileCtxt = color BrightBlue
colorAnn Code = color Magenta
colorAnn Meta = color Green
colorAnn (Syntax syn) = syntaxAnn syn
colorAnn UserDocString = []

export
warning : Doc IdrisAnn -> Doc IdrisAnn
warning = annotate Warning

export
error : Doc IdrisAnn -> Doc IdrisAnn
error = annotate Error

export
errorDesc : Doc IdrisAnn -> Doc IdrisAnn
errorDesc = annotate ErrorDesc

export
fileCtxt : Doc IdrisAnn -> Doc IdrisAnn
fileCtxt = annotate FileCtxt

export
meta : Doc IdrisAnn -> Doc IdrisAnn
meta = annotate Meta

export
code : Doc IdrisAnn -> Doc IdrisAnn
code = annotate Code

export
Pretty i a => Pretty i (WithData fields a) where
  pretty x = pretty x.val

mutual

  prettyAlt : PClauseBase KindedName -> Doc IdrisSyntax
  prettyAlt (MkPatClause lhs rhs _) =
      space <+> pipe <++> pretty lhs <++> fatArrow <++> pretty rhs <+> semi
  prettyAlt (MkWithClause lhs wps flags cs) =
      space <+> pipe <++> angles (angles (reflow "with alts not possible")) <+> semi
  prettyAlt (MkImpossible lhs) =
      space <+> pipe <++> pretty lhs <++> impossible_ <+> semi

  prettyPClause : PClauseBase KindedName -> Doc IdrisSyntax
  prettyPClause (MkPatClause lhs rhs _) =
      pretty lhs <++> fatArrow <++> pretty rhs.val
  prettyPClause (MkWithClause lhs wps flags _) =
      space <+> pipe <++> angles (angles (reflow "with alts not possible"))
  prettyPClause (MkImpossible lhs) =
      pretty lhs <++> impossible_

  prettyPStr : PStr' KindedName -> Doc IdrisSyntax
  prettyPStr (StrLiteral str) = pretty0 str
  prettyPStr (StrInterp tm) = pretty tm.val

  prettyPDo : PDo' KindedName -> Doc IdrisSyntax
  prettyPDo (DoExp _ tm) = pretty tm.val
  prettyPDo (DoBind _ _ n rig (Just ty) tm) =
      prettyRig rig <+> pretty0 n <++> colon <++> pretty ty <++> keyword "<-" <++> pretty tm.val
  prettyPDo (DoBind _ _ n rig Nothing tm) =
      prettyRig rig <+> pretty0 n <++> keyword "<-" <++> pretty tm.val
  prettyPDo (DoBindPat _ l (Just ty) tm alts) =
      pretty l <++> colon <++> keyword "<-" <++> pretty tm <+> hang 4 (fillSep $ (prettyAlt . val) <$> alts)
  prettyPDo (DoBindPat _ l Nothing tm alts) =
      pretty l <++> keyword "<-" <++> pretty tm <+> hang 4 (fillSep $ (prettyAlt . val) <$> alts)
  prettyPDo (DoLet _ _ l rig _ tm) =
      let_ <++> prettyRig rig <+> pretty0 l <++> equals <++> pretty tm.val
  prettyPDo (DoLetPat _ l _ tm alts) =
      let_ <++> pretty l <++> equals <++> pretty tm <+> hang 4 (fillSep $ (prettyAlt . val) <$> alts)
  prettyPDo (DoLetLocal _ ds) =
      let_ <++> braces (angles (angles "definitions"))
  prettyPDo (DoRewrite _ rule) = rewrite_ <+> pretty rule.val

  export
  prettyFieldPath : List String -> Doc IdrisSyntax
  prettyFieldPath flds = concatWith (surround $ keyword "->") (pretty0 <$> flds)

  prettyPFieldUpdate : PFieldUpdate' KindedName -> Doc IdrisSyntax
  prettyPFieldUpdate (PSetField path v) =
      prettyFieldPath path <++> equals <++> pretty v.val
  prettyPFieldUpdate (PSetFieldApp path v) =
      prettyFieldPath path <++> keyword "$=" <++> pretty v.val

  prettyBinder : Name -> Doc IdrisSyntax
  prettyBinder = annotate Bound . pretty0

  startPrec : Prec
  startPrec = Open
  appPrec : Prec
  appPrec = App
  leftAppPrec : Prec
  leftAppPrec = Open

  prettyOp : KindedName -> Doc IdrisSyntax
  prettyOp op@(MkKindedName _ _ nm) = if isOpName nm
      then annotateM (kindAnn op) $ pretty0 nm
      else Chara '`' <+> annotateM (kindAnn op) (pretty0 nm) <+> Chara '`'

  Pretty IdrisSyntax (BasicMultiBinder' KindedName) where
    pretty (MkBasicMultiBinder rig names type)
      = prettyRig rig <++> commaSep (forget $ map (prettyBinder . val) names)
      <++> colon <++> pretty type

  export
  Pretty IdrisSyntax (PTermBase KindedName) where
    prettyPrec d (PRef nm) = annotateM (kindAnn nm) $ cast $ prettyOp False nm.rawName
    prettyPrec d (NewPi (MkPBinderScope (MkPBinder Implicit bind) scope)) =
      lcurly <+> pretty bind <+> rcurly <++> arrow <++> prettyPrec d scope.val
    prettyPrec d (NewPi (MkPBinderScope (MkPBinder Explicit bind) scope)) =
      lparen <+> pretty bind <+> rparen <++> arrow <++> prettyPrec d scope.val
    prettyPrec d (NewPi (MkPBinderScope (MkPBinder AutoImplicit bind) scope)) =
      lcurly <+> auto_ <++> pretty bind <+> rcurly <++> arrow <++> prettyPrec d scope.val
    prettyPrec d (NewPi (MkPBinderScope (MkPBinder (DefImplicit x) bind) scope)) =
      lcurly <+> default_ <++> prettyPrec appPrec x
      <++> pretty bind <+> rcurly <++> arrow <++> prettyPrec d scope.val
    prettyPrec d (Forall names scope) =
      parenthesise (d > startPrec) $ group $
        forall_ <++> commaSep (map (prettyBinder . val) (forget names)) <++> dot <++> pretty scope
    prettyPrec d (PPi rig Explicit Nothing arg ret) =
      parenthesise (d > startPrec) $ group $
        branchVal
          (pretty arg <++> arrow <++> pretty ret.val)
          (parens (prettyRig rig <+> "_" <++> colon <++> pretty arg)
                  <++> arrow <+> softline <+> pretty ret.val)
          rig
    prettyPrec d (PPi rig Explicit (Just n) arg ret) =
      parenthesise (d > startPrec) $ group $
        parens (prettyRig rig <+> prettyBinder n
             <++> colon <++> pretty arg)
             <++> arrow <+> softline <+> pretty ret.val
    prettyPrec d (PPi rig Implicit Nothing arg ret) =
      parenthesise (d > startPrec) $ group $
        braces (prettyRig rig <+> pretty0 Underscore
             <++> colon <++> pretty arg)
             <++> arrow <+> softline <+> pretty ret
    prettyPrec d (PPi rig Implicit (Just n) arg ret) =
      parenthesise (d > startPrec) $ group $
        braces (prettyRig rig <+> prettyBinder n
             <++> colon <++> pretty arg)
             <++> arrow <+> softline <+> pretty ret
    prettyPrec d (PPi rig AutoImplicit Nothing arg ret) =
      parenthesise (d > startPrec) $ group $
        branchVal
          (pretty arg <++> fatArrow <+> softline <+> pretty ret)
          (braces (auto_ <++> prettyRig rig <+> "_"
                <++> colon <++> pretty arg)
                <++> arrow <+> softline <+> pretty ret)
          rig
    prettyPrec d (PPi rig AutoImplicit (Just n) arg ret) =
      parenthesise (d > startPrec) $ group $
        braces (auto_ <++> prettyRig rig <+> prettyBinder n
             <++> colon <++> pretty arg)
             <++> arrow <+> softline <+> pretty ret
    prettyPrec d (PPi rig (DefImplicit t) Nothing arg ret) =
      parenthesise (d > startPrec) $ group $
        braces (default_ <++> prettyPrec appPrec t <++> prettyRig rig <+> "_"
             <++> colon <++> pretty arg)
             <++> arrow <+> softline <+> pretty ret
    prettyPrec d (PPi rig (DefImplicit t) (Just n) arg ret) =
      parenthesise (d > startPrec) $ group $
        braces (default_ <++> prettyPrec appPrec t
             <++> prettyRig rig <+> prettyBinder n
             <++> colon <++> pretty arg)
             <++> arrow <+> softline <+> pretty ret
    prettyPrec d (PLam rig _ n ty sc) =
      let (ns, sc) = getLamNames [(rig, n, ty)] sc in
          parenthesise (d > startPrec) $ group $
            backslash <+> prettyBindings ns <++> fatArrow <+> softline <+> pretty sc
      where
      getLamNames : List (RigCount, IPTerm, IPTerm) ->
                    IPTerm ->
                    (List (RigCount, IPTerm, PTermBase KindedName), IPTerm)
      -- getLamNames acc (MkWithData _ $ PLam rig _ n ty sc) = getLamNames ((rig, n, ty) :: acc) sc
      -- getLamNames acc sc = (reverse acc, sc)

      prettyBindings : List (RigCount, IPTerm, PTermBase KindedName) -> Doc IdrisSyntax
      prettyBindings [] = neutral
      prettyBindings [(rig, n, (PImplicit))] = prettyRig rig <+> pretty n
      prettyBindings [(rig, n, ty)] = prettyRig rig <+> pretty n <++> colon <++> pretty ty
      prettyBindings ((rig, n, (PImplicit)) :: ns) = prettyRig rig <+> pretty n
                                              <+> comma <+> line <+> prettyBindings ns
      prettyBindings ((rig, n, ty) :: ns) = prettyRig rig <+> pretty n <++> colon <++> pretty ty
                                              <+> comma <+> line <+> prettyBindings ns
    prettyPrec d (PLet rig n (aaa) val sc alts) =
      -- Hide uninformative lets
      -- (Those that look like 'let x = x in ...')
      -- Makes printing the types of names bound in where clauses a lot
      -- more readable
      fromMaybe fullLet $ do
        nName   <- getPRefName ?hauw
        valName <- getPRefName ?val2
        guard (show nName == show valName)
        pure continuation

     -- Hide lets that bind to underscore
     -- That is, 'let _ = x in ...'
     -- Those end up polluting the types of let bound variables in some
     -- occasions
      <|> do
        nName <- getPRefName ?nm1
        guard (isUnderscoreName nName)
        pure continuation

    where

      continuation : Doc IdrisSyntax
      continuation = pretty sc

      fullLet : Doc IdrisSyntax
      fullLet = parenthesise (d > startPrec) $ group $ align $
        let_ <++> (group $ align $ hang 2 $ prettyRig rig <+> pretty n <++> equals <+> line <+> pretty val) <+> line
          <+> in_ <++> (group $ align $ hang 2 $ continuation)

      getPRefName : PTermBase KindedName -> Maybe Name
      getPRefName (PRef n) = Just (rawName n)
      getPRefName _ = Nothing

    prettyPrec d (PLet rig n ty val sc alts) =
      parenthesise (d > startPrec) $ group $ align $ ?huh
        -- let_ <++> (group $ align $ hang 2 $
        --               prettyRig rig <+> pretty n <++> colon <++> pretty ty
        --               <++> equals <+> line <+> pretty val)
        -- <+> case alts of
        --      { [] => in_ <+> softline
        --      ; _ => hardline <+> indent 4 (vsep (prettyAlt <$> alts)) <+> hardline <+> in_
        --      }
        -- <+> group (align $ hang 2 $ pretty sc)
    prettyPrec d (PCase _ tm cs) =
      parenthesise (d > startPrec) $
        case_ <++> pretty tm <++> of_ <+> nest 2 (
        let punctuation = lcurly :: (semi <$ fromMaybe [] (tail' [1..length cs])) in
        line <+> (vsep $ zipWith (<++>) punctuation (prettyPClause . val <$> cs) ++ [rcurly]))
    prettyPrec d (PLocal ds sc) =
      parenthesise (d > startPrec) $ group $ align $
        let_ <++> braces (angles (angles "definitions")) <+> line <+> in_ <++> pretty sc
    prettyPrec d (PUpdate fs) =
      parenthesise (d > startPrec) $ group $
        record_ <++> braces (vsep $ punctuate comma (prettyPFieldUpdate <$> fs))
    prettyPrec d (PApp f a) =
      let catchall : Lazy (Doc IdrisSyntax)
           := prettyPrec leftAppPrec f <++> prettyPrec appPrec a

      in parenthesise (d >= appPrec) $ group $ case WithData.val f of
        (PRef n) =>
          if isJust (isRF $ rawName n)
          then prettyPrec leftAppPrec a <++> prettyPrec appPrec f
          else catchall
        _ => catchall
    prettyPrec d (PWithApp f a) = prettyPrec d f <++> pipe <++> prettyPrec d a
    prettyPrec d (PDelayed LInf ty) = parenthesise (d > startPrec) $ "Inf" <++> prettyPrec appPrec ty
    prettyPrec d (PDelayed _ ty) = parenthesise (d > startPrec) $ "Lazy" <++> prettyPrec appPrec ty
    prettyPrec d (PDelay tm) = parenthesise (d > startPrec) $ "Delay" <++> prettyPrec appPrec tm
    prettyPrec d (PForce tm) = parenthesise (d > startPrec) $ "Force" <++> prettyPrec appPrec tm
    prettyPrec d (PAutoApp f a) =
      parenthesise (d > startPrec) $ group $ prettyPrec leftAppPrec f <++> "@" <+> braces (pretty a)
    prettyPrec d (PBindingApp fn bind scope) = ?TODO2
    prettyPrec d (PNamedApp f n (MkWithData _ $ PRef a)) =
      parenthesise (d > startPrec) $ group $
        if n == rawName a
           then prettyPrec leftAppPrec f <++> braces (pretty0 n)
           else prettyPrec leftAppPrec f <++> braces (pretty0 n <++> equals <++> pretty0 a.rawName)
    prettyPrec d (PNamedApp f n a) =
      parenthesise (d > startPrec) $ group $
        prettyPrec leftAppPrec f <++> braces (pretty0 n <++> equals <++> prettyPrec d a)
    prettyPrec d (PSearch _) = pragma "%search"
    prettyPrec d (PQuote tm) = parenthesise (d > startPrec) $ "`" <+> parens (pretty tm)
    prettyPrec d (PQuoteName n) = parenthesise (d > startPrec) $ "`" <+> braces (pretty0 n)
    prettyPrec d (PQuoteDecl tm) =
      parenthesise (d > startPrec) $
         "`" <+> brackets (angles (angles "declaration"))
    prettyPrec d (PUnquote tm) = parenthesise (d > startPrec) $ "~" <+> parens (pretty tm)
    prettyPrec d (PRunElab tm) = parenthesise (d > startPrec) $ pragma "%runElab" <++> pretty tm
    prettyPrec d (PPrimVal c) = pretty c
    prettyPrec d (PHole _ n) = hole (pretty0 (strCons '?' n))
    prettyPrec d (PType) = annotate (TCon Nothing) "Type"
    prettyPrec d (PAs n p) = pretty0 n <+> "@" <+> prettyPrec d p
    prettyPrec d (PDotted p) = dot <+> prettyPrec d p
    prettyPrec d (PImplicit) = "_"
    prettyPrec d (PInfer) = annotate Hole $ "?"
    prettyPrec d (POp (MkWithData _ $ LHSBinder $ BindType nm left) op right) =
        group $ parens (prettyPrec d nm <++> ":" <++> pretty left)
           <++> prettyOp op.val.toName
           <++> pretty right
    prettyPrec d (POp (MkWithData _ $ LHSBinder $ BindExpr nm left) op right) =
        group $ parens (prettyPrec d nm <++> ":=" <++> pretty left)
           <++> prettyOp op.val.toName
           <++> pretty right
    prettyPrec d (POp (MkWithData _ $ LHSBinder $ BindExplicitType nm ty left) op right) =
        group $ parens (prettyPrec d nm <++> ":" <++> pretty ty <++> ":=" <++> pretty left)
           <++> prettyOp op.val.toName
           <++> pretty right
    prettyPrec d (POp (MkWithData _ $ NoBinder x) op y) =
      parenthesise (d >= App) $
        group $ pretty x
           <++> prettyOp op.val.toName
           <++> pretty y
    prettyPrec d (PPrefixOp op x) = parenthesise (d > startPrec) $ prettyOp op.val.toName <+> pretty x
    prettyPrec d (PSectionL op x) = parens (prettyOp op.val.toName <++> pretty x)
    prettyPrec d (PSectionR x op) = parens (pretty x <++> prettyOp op.val.toName)
    prettyPrec d (PEq l r) = parenthesise (d > startPrec) $ prettyPrec Equal l <++> equals <++> prettyPrec Equal r
    prettyPrec d (PBracketed tm) = parens (pretty tm)
    prettyPrec d (PString _ xs) = parenthesise (d > startPrec) $ hsep $ punctuate "++" (prettyPStr <$> xs)
    prettyPrec d (PMultiline _ indent xs) =
      "multiline" <++>
        (parenthesise (d > startPrec) $
           hsep $ punctuate "++" (prettyPStr <$> concat xs))
    prettyPrec d (PDoBlock ns ds) =
      parenthesise (d > startPrec) $ group $ align $ hang 2 $
        do_ <++> (vsep $ punctuate semi (prettyPDo <$> ds))
    prettyPrec d (PBang tm) = "!" <+> prettyPrec d tm
    prettyPrec d (PIdiom Nothing tm) = enclose (keyword "[|") (keyword "|]") (pretty tm)
    prettyPrec d (PIdiom (Just ns) tm) = enclose (pretty0 ns <+> keyword ".[|") (keyword "|]") (pretty tm)
    prettyPrec d (PList _ xs) = brackets (group $ align $ vsep $ punctuate comma (pretty . snd <$> xs))
    prettyPrec d (PSnocList _ xs)
      = brackets {ldelim = "[<"}
      $ group $ align $ vsep $ punctuate comma
      $ pretty . snd <$> (xs <>> [])
    prettyPrec d (PPair l r) = group $ parens (pretty l <+> comma <+> line <+> pretty r)
    prettyPrec d (PDPair _ l (MkWithData _ PImplicit) r)
      = group $ parens (pretty l <++> keyword "**" <+> line <+> pretty r)
    prettyPrec d (PDPair _ l ty r) =
      group $ parens (pretty l <++> colon <++> pretty ty <++> keyword "**" <+> line <+> pretty r)
    prettyPrec d (PUnit) = "()"
    prettyPrec d (PIfThenElse x t e) =
      parenthesise (d > startPrec) $ group $ align $ hang 2 $ vsep
        [ keyword "if" <++> pretty x
        , keyword "then" <++> pretty t
        , keyword "else" <++> pretty e]
    prettyPrec d (PComprehension ret es) =
      group $ brackets (pretty (dePure ret.val) <++> pipe <++> vsep (punctuate comma (prettyPDo . deGuard <$> es)))
      where
      dePure : PTermBase KindedName -> PTermBase KindedName
      dePure tm@(PApp (MkWithData _ $ PRef n) arg)
        = if dropNS (rawName n) == UN (Basic "pure") then arg.val else tm
      dePure tm = tm

      deGuard : PDo' KindedName -> PDo' KindedName
      deGuard tm@(DoExp fc (MkWithData _ $ PApp (MkWithData _ $ PRef n) arg))
        = if dropNS (rawName n) == UN (Basic "guard") then DoExp fc arg else tm
      deGuard tm = tm
    prettyPrec d (PRewrite rule tm) =
      parenthesise (d > startPrec) $ group $
        rewrite_ <++> pretty rule <+> line <+> in_ <++> pretty tm
    prettyPrec d (PRange start Nothing end) =
      brackets (pretty start <++> keyword ".." <++> pretty end)
    prettyPrec d (PRange start (Just next) end) =
      brackets (pretty start <+> comma <++> pretty next <++> keyword ".." <++> pretty end)
    prettyPrec d (PRangeStream start Nothing) = brackets (pretty start <++> keyword "..")
    prettyPrec d (PRangeStream start (Just next)) =
      brackets (pretty start <+> comma <++> pretty next <++> keyword "..")
    prettyPrec d (PUnifyLog lvl tm) = prettyPrec d tm
    prettyPrec d (PPostfixApp rec fields) =
      parenthesise (d > startPrec) $
        pretty rec <++> dot <+> concatWith (surround dot) (map (pretty0 . val) fields)
    prettyPrec d (PPostfixAppPartial fields) =
      parens (dot <+> concatWith (surround dot) (map (pretty0 . val) fields))
    prettyPrec d (PWithUnambigNames ns rhs) =
      parenthesise (d > startPrec) $ group $
        with_ <++> cast (prettyList $ map snd ns) <+> line <+> pretty rhs

export
render : {auto o : Ref ROpts REPLOpts} -> Doc IdrisAnn -> Core String
render = render colorAnn

export
renderWithDecorations :
  {auto o : Ref ROpts REPLOpts} ->
  (ann -> Maybe ann') ->
  Doc ann ->
  Core (String, List (Span ann'))
renderWithDecorations f doc =
  do (str, mspans) <- Render.renderWithSpans doc
     let spans = mapMaybe (traverse f) mspans
     pure (str, spans)

export
prettyImport : Import -> Doc IdrisSyntax
prettyImport (MkImport loc reexport path nameAs)
  = keyword "import"
    <+> ifThenElse reexport (space <+> keyword "public") ""
    <++> pretty0 path
    <+> ifThenElse (miAsNamespace path /= nameAs) (space <+> keyword "as" <++> pretty0 nameAs) ""
