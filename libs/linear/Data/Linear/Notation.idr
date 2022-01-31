module Data.Linear.Notation

%default total

infixr 0 -@
||| Infix notation for linear implication
public export
(-@) : Type -> Type -> Type
a -@ b = (1 _ : a) -> b

||| Linear function composition
public export
(.) : (b -@ c) -@ (a -@ b) -@ (a -@ c)
(.) f g v = f (g v)

||| An interface for consumable types
public export
interface Consumable a where
  consume : a -@ ()

||| Void and the unit type are trivially consumable
export
Consumable Void where consume v impossible
export
Consumable () where consume u = u

||| Unions can be consumed by pattern matching
export
Consumable Bool where
  consume True = ()
  consume False = ()

||| We can cheat to make built-in types consumable
export
Consumable Int where
  consume = believe_me (\ 0 i : Int => ())

-- But crucially we don't have `Consumable World` or `Consumable Handle`.

infixr 5 `seq`
||| We can sequentially compose a computation returning a value that is
||| consumable with another computation. This is done by first consuming
||| the result of the first computation and then returning the second one.
export
seq : Consumable a => a -@ b -@ b
a `seq` b = let 1 () = consume a in b

public export
interface Duplicate a where
  dup : a -@ LPair a a

||| Comonoid is the dual of Monoid, it can consume a value linearly and duplicate a value linearly
public export
interface Comonoid a where
  counit : a -@ ()
  comult : a -@ LPair a a

export
Consumable a => Duplicate a => Comonoid a where
  counit = consume
  comult = dup

prefix 5 !*

||| Prefix notation for the linear unrestricted modality
public export
record (!*) (a : Type) where
  constructor MkBang
  unrestricted : a

export
Comonoid (!* a) where
  counit (MkBang _) = ()
  comult (MkBang v) = MkBang v # MkBang v

