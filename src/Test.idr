module Test

data Token
    -- Single character tokens.
    = LEFT_PAREN
    | RIGHT_PAREN
    | WHILE
    -- Literals.
    | IDENTIFIER String
    | STRING String
    | NUMBER Int
    -- End of file.
    | EOF

record ContextToken where
    constructor ContextToken_
    token : Token
    line : Nat

record Error where
    constructor Error_
    line : Nat
    msg : String

record Errorable (ty : Type) where
    constructor Errorable_
    errors : List Error
    val : ty

scanTokens : (source : String) -> Errorable (List ContextToken)
scanTokens source =
    rec (unpack source) 0 (Errorable_ [] [])
    where
        rec : (chars : List Char) -> (line : Nat) -> Errorable (List ContextToken) -> Errorable (List ContextToken)
        rec [] _ eTokens = eTokens
        rec stream line (Errorable_ errors tokens) = ?wh
