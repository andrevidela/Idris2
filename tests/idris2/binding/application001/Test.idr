

-- typebind type constructor
typebind
record Exists (x : Type) (f : x -> Type) where
  constructor (#)
  fst : x
  snd : f fst

record Container  where
  -- typebind data constructor
  typebind
  constructor MKCont
  fst : Type
  snd : fst -> Type

-- typebind function definition
typebind
Sigma : (x : Type) -> (x -> Type) -> Type
-- Sigma x f = Exists (v : x) | f v


-- partially apply typebind function
Sigma' : (x : Type) -> (x -> Type) -> Type
Sigma' x f = (Exists x) f

-- autobind function
autobind
for : Applicative f => Traversable t => t a -> (a -> f b) -> f (t b)
for = flip traverse

-- autobind usage
-- test : List Integer -> Maybe (List Nat)
-- test ls = for (x : Integer := ls) | isNat x
--     where
--       isNat : Integer -> Maybe Nat
--       isNat x = if x > 0 then Just $ cast x
--                          else Nothing
