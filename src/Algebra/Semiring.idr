module Algebra.Semiring

%default total

infixl 8 |+|
infixl 9 |*|

||| A Semiring has two binary operations and an identity for each
public export
interface Semiring a where
  (|+|) : a -> a -> a
  plusNeutral : a
  plusAssociative : (x, y, z : a) -> x |+| (y |+| z) = (x |+| y) |+| z
  plusCommutative : (x, y : a) -> x |+| y = y |+| x
  plusIdentityLeft : (x : a) -> plusNeutral |+| x = x
  plusIdentityLeft x = rewrite plusCommutative plusNeutral x in plusIdentityRight x
  plusIdentityRight : (x : a) -> x |+| plusNeutral = x
  plusIdentityRight x = rewrite plusCommutative x plusNeutral in plusIdentityLeft x

  (|*|) : a -> a -> a
  timesNeutral : a
  timesAssociative : (x, y, z : a) -> x |*| (y |*| z) = (x |*| y) |*| z
  timesIdentityRight : (x : a) -> x |*| timesNeutral = x
  timesIdentityLeft : (x : a) -> timesNeutral |*| x = x
  timesDistributiveLeft : (x, y, z : a) -> x |*| (y |+| z) = (x |*| y) |+| (x |*| z)
  timesDistributiveRight : (x, y, z : a) -> (x |+| y) |*| z = (x |*| z) |+| (y |*| z)
  timesAnnihilationRight : (x : a) -> x |*| plusNeutral = plusNeutral
  timesAnnihilationLeft : (x : a) -> plusNeutral |*| x = plusNeutral

||| Erased linearity corresponds to the neutral for |+|
public export
erased : Semiring a => a
erased = plusNeutral

||| Purely linear corresponds to the neutral for |*|
public export
linear : Semiring a => a
linear = timesNeutral

||| A semiring eliminator
public export
elimSemi : (Semiring a, Eq a) => (zero : b) -> (one : b) -> (a -> b) -> a -> b
elimSemi zero one other r {a} =
  if r == Semiring.plusNeutral {a}
     then zero
     else if r == Semiring.timesNeutral {a}
             then one
             else other r

export
isErased : (Semiring a, Eq a) => a -> Bool
isErased = elimSemi True False (const False)

export
isLinear : (Semiring a, Eq a) => a -> Bool
isLinear = elimSemi False True (const False)

export
isRigOther : (Semiring a, Eq a) => a -> Bool
isRigOther = elimSemi False False (const True)

export
branchZero : (Semiring a, Eq a) => Lazy b -> Lazy b -> a -> b
branchZero yes no rig = if isErased rig then yes else no

export
branchOne : (Semiring a, Eq a) => Lazy b -> Lazy b -> a -> b
branchOne yes no rig = if isLinear rig then yes else no

export
branchVal : (Semiring a, Eq a) => Lazy b -> Lazy b -> a -> b
branchVal yes no rig = if isRigOther rig then yes else no
