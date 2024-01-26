module Language.Reflection.WithDefault

public export
data WithDefault : (a : Type) -> (def : a) -> Type where
     DefaultedValue : WithDefault a def
     SpecifiedValue : a -> WithDefault a def

export
specified : a -> WithDefault a def
specified = SpecifiedValue

export
defaulted : WithDefault a def
defaulted = DefaultedValue

export
isDefaulted : WithDefault a def -> Bool
isDefaulted DefaultedValue = True
isDefaulted _              = False

export
isSpecified : WithDefault a def -> Bool
isSpecified DefaultedValue = False
isSpecified _              = True

export
collapseDefault : {def : a} -> WithDefault a def -> a
collapseDefault DefaultedValue     = def
collapseDefault (SpecifiedValue a) = a

export
onWithDefault : (defHandler : Lazy b) -> (valHandler : a -> b) ->
                WithDefault a def -> b
onWithDefault defHandler _ DefaultedValue     = defHandler
onWithDefault _ valHandler (SpecifiedValue v) = valHandler v

public export
Eq a => Eq (WithDefault a def) where
  DefaultedValue   == DefaultedValue   = True
  DefaultedValue   == SpecifiedValue _ = False
  SpecifiedValue _ == DefaultedValue   = False
  SpecifiedValue x == SpecifiedValue y = x == y

public export
Ord a => Ord (WithDefault a def) where
  compare DefaultedValue   DefaultedValue       = EQ
  compare DefaultedValue   (SpecifiedValue _)   = LT
  compare (SpecifiedValue _) DefaultedValue     = GT
  compare (SpecifiedValue x) (SpecifiedValue y) = compare x y

public export
{def : a} -> (Show a) => Show (WithDefault a def) where
  show (SpecifiedValue x) = show x
  show DefaultedValue     = show def

