module Algebra.ZeroOneOmega

import Decidable.Equality

import Algebra.Semiring
import Algebra.Preorder
import Algebra.Utils

%default total

public export
data ZeroOneOmega = Rig0 | Rig1 | RigW

data LTEZeroOneOmega : ZeroOneOmega -> ZeroOneOmega -> Type where
  LTEZero : LTEZeroOneOmega Rig0 y
  LTEOneOne : LTEZeroOneOmega Rig1 Rig1
  LTEOneOmega : LTEZeroOneOmega Rig1 RigW
  LTEOmegaOmega : LTEZeroOneOmega RigW RigW

Uninhabited (LTEZeroOneOmega Rig1 Rig0) where
  uninhabited LTEZero impossible
  uninhabited LTEOneOne impossible
  uninhabited LTEOneOmega impossible
  uninhabited LTEOmegaOmega impossible

Uninhabited (LTEZeroOneOmega RigW Rig0) where
  uninhabited LTEZero impossible
  uninhabited LTEOneOne impossible
  uninhabited LTEOneOmega impossible
  uninhabited LTEOmegaOmega impossible

Uninhabited (LTEZeroOneOmega RigW Rig1) where
  uninhabited LTEZero impossible
  uninhabited LTEOneOne impossible
  uninhabited LTEOneOmega impossible
  uninhabited LTEOmegaOmega impossible

export
Preorder ZeroOneOmega where
  LTE = LTEZeroOneOmega

  isLTE Rig0 y = Yes LTEZero
  isLTE Rig1 Rig0 = No uninhabited
  isLTE Rig1 Rig1 = Yes LTEOneOne
  isLTE Rig1 RigW = Yes LTEOneOmega
  isLTE RigW Rig0 = No uninhabited
  isLTE RigW Rig1 = No uninhabited
  isLTE RigW RigW = Yes LTEOmegaOmega

  preorderRefl Rig0 = LTEZero
  preorderRefl Rig1 = LTEOneOne
  preorderRefl RigW = LTEOmegaOmega

  preorderTrans LTEZero y = LTEZero
  preorderTrans LTEOneOne LTEOneOne = LTEOneOne
  preorderTrans LTEOneOne LTEOneOmega = LTEOneOmega
  preorderTrans LTEOneOmega LTEOmegaOmega = LTEOneOmega
  preorderTrans LTEOmegaOmega LTEOmegaOmega = LTEOmegaOmega

public export
Eq ZeroOneOmega where
  Rig0 == Rig0 = True
  Rig1 == Rig1 = True
  RigW == RigW = True
  _ == _ = False

public export
DecEq ZeroOneOmega where
  decEq Rig0 Rig0 = Yes Refl
  decEq Rig0 Rig1 = No (\case Refl impossible)
  decEq Rig0 RigW = No (\case Refl impossible)
  decEq Rig1 Rig0 = No (\case Refl impossible)
  decEq Rig1 Rig1 = Yes Refl
  decEq Rig1 RigW = No (\case Refl impossible)
  decEq RigW Rig0 = No (\case Refl impossible)
  decEq RigW Rig1 = No (\case Refl impossible)
  decEq RigW RigW = Yes Refl

export
Show ZeroOneOmega where
  show Rig0 = "Rig0"
  show Rig1 = "Rig1"
  show RigW = "RigW"

export
rigPlus : ZeroOneOmega -> ZeroOneOmega -> ZeroOneOmega
rigPlus Rig0 a = a
rigPlus a Rig0 = a
rigPlus Rig1 a = RigW
rigPlus a Rig1 = RigW
rigPlus RigW RigW = RigW

export
rigMult : ZeroOneOmega -> ZeroOneOmega -> ZeroOneOmega
rigMult Rig0 _ = Rig0
rigMult _ Rig0 = Rig0
rigMult Rig1 a = a
rigMult a Rig1 = a
rigMult RigW RigW = RigW

public export
Semiring ZeroOneOmega where
  (|+|) = rigPlus
  (|*|) = rigMult
  plusNeutral = Rig0
  timesNeutral = Rig1

  plusIdentityLeft Rig0 = Refl
  plusIdentityLeft Rig1 = Refl
  plusIdentityLeft RigW = Refl

  plusCommutative Rig0 y =
    rewrite plusIdentityRight y in Refl
  plusCommutative x Rig0 =
    rewrite plusIdentityRight x in Refl
  plusCommutative Rig1 Rig1 = Refl
  plusCommutative Rig1 RigW = Refl
  plusCommutative RigW Rig1 = Refl
  plusCommutative RigW RigW = Refl

  plusAssociative Rig0 y z = Refl
  plusAssociative x Rig0 z =
    rewrite plusIdentityRight x in Refl
  plusAssociative x y Rig0 =
    rewrite plusIdentityRight y in
    rewrite plusIdentityRight (x |+| y) in Refl
  plusAssociative Rig1 Rig1 Rig1 = Refl
  plusAssociative Rig1 Rig1 RigW = Refl
  plusAssociative Rig1 RigW Rig1 = Refl
  plusAssociative Rig1 RigW RigW = Refl
  plusAssociative RigW Rig1 Rig1 = Refl
  plusAssociative RigW Rig1 RigW = Refl
  plusAssociative RigW RigW Rig1 = Refl
  plusAssociative RigW RigW RigW = Refl

  timesIdentityLeft Rig0 = Refl
  timesIdentityLeft Rig1 = Refl
  timesIdentityLeft RigW = Refl

  timesIdentityRight Rig0 = Refl
  timesIdentityRight Rig1 = Refl
  timesIdentityRight RigW = Refl

  timesAnnihilationLeft Rig0 = Refl
  timesAnnihilationLeft Rig1 = Refl
  timesAnnihilationLeft RigW = Refl

  timesAnnihilationRight Rig0 = Refl
  timesAnnihilationRight Rig1 = Refl
  timesAnnihilationRight RigW = Refl

  timesAssociative Rig0 y z = Refl
  timesAssociative x Rig0 y =
    rewrite timesAnnihilationRight x in Refl
  timesAssociative x y Rig0 =
    rewrite timesAnnihilationRight y in
    rewrite timesAnnihilationRight x in
    rewrite timesAnnihilationRight (x |*| y) in Refl
  timesAssociative Rig1 y z =
    rewrite timesIdentityLeft y in
    rewrite timesIdentityLeft (y |*| z) in Refl
  timesAssociative x Rig1 y =
    rewrite timesIdentityLeft y in
    rewrite timesIdentityRight x in Refl
  timesAssociative x y Rig1 =
    rewrite timesIdentityRight y in
    rewrite timesIdentityRight (x |*| y) in Refl
  timesAssociative RigW RigW RigW = Refl

  timesDistributiveLeft Rig0 y z = Refl
  timesDistributiveLeft x Rig0 z =
    rewrite timesAnnihilationRight x in Refl
  timesDistributiveLeft x y Rig0 =
    rewrite timesAnnihilationRight x in
    rewrite plusIdentityRight y in
    rewrite plusIdentityRight (x |*| y) in Refl
  timesDistributiveLeft Rig1 y z =
    rewrite timesIdentityLeft y in
    rewrite timesIdentityLeft z in
    rewrite timesIdentityLeft (y |+| z) in Refl
  timesDistributiveLeft RigW Rig1 Rig1 = Refl
  timesDistributiveLeft RigW Rig1 RigW = Refl
  timesDistributiveLeft RigW RigW Rig1 = Refl
  timesDistributiveLeft RigW RigW RigW = Refl

  timesDistributiveRight Rig0 y z = Refl
  timesDistributiveRight x Rig0 z =
    rewrite plusIdentityRight x in
    rewrite plusIdentityRight (x |*| z) in Refl
  timesDistributiveRight x y Rig0 =
    rewrite timesAnnihilationRight (x |+| y) in
    rewrite timesAnnihilationRight x in
    rewrite timesAnnihilationRight y in Refl
  timesDistributiveRight Rig1 Rig1 Rig1 = Refl
  timesDistributiveRight Rig1 Rig1 RigW = Refl
  timesDistributiveRight Rig1 RigW Rig1 = Refl
  timesDistributiveRight Rig1 RigW RigW = Refl
  timesDistributiveRight RigW Rig1 Rig1 = Refl
  timesDistributiveRight RigW Rig1 RigW = Refl
  timesDistributiveRight RigW RigW Rig1 = Refl
  timesDistributiveRight RigW RigW RigW = Refl

||| The top value of a lattice
export
Top ZeroOneOmega where
  top = RigW

  topAbs Rig0 = LTEZero
  topAbs Rig1 = LTEOneOmega
  topAbs RigW = LTEOmegaOmega

export
AsNat ZeroOneOmega where
  toNat Rig0 = Just 0
  toNat Rig1 = Just 1
  toNat RigW = Nothing
  fromNat Z = Rig0
  fromNat 1 = Rig1
  fromNat _ = RigW

export
AdditiveInverse ZeroOneOmega where
  minus r Rig0 = r
  minus Rig0 _ = Rig0
  minus Rig1 Rig1 = Rig0
  minus Rig1 RigW = Rig0
  minus RigW _ = RigW
