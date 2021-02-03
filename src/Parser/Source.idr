module Parser.Source

import public Parser.Lexer.Source
import public Parser.Rule.Source
import public Parser.Unlit

import System.File
import Libraries.Utils.Either

%default total

export
runParserTo : {e : _} ->
              Maybe LiterateStyle -> -- (WithBounds Token -> Bool) ->
              String -> Grammar Token e ty -> Either (ParseError Token) ty
runParserTo lit str p
    = do str    <- mapError LitFail $ unlit lit str
         toks   <- mapError LexFail $ lexTo str
         parsed <- mapError toGenericParsingError $ parse p toks
         Right (fst parsed)

export
runParser : {e : _} ->
            Maybe LiterateStyle -> String -> Grammar Token e ty -> Either (ParseError Token) ty
runParser lit = runParserTo lit

export covering
parseFile : (fn : String) -> Rule ty -> IO (Either (ParseError Token) ty)
parseFile fn p
    = do Right str <- readFile fn
             | Left err => pure (Left (FileFail err))
         pure (runParser (isLitFile fn) str p)
