module Algebra.Nats

import Data.Nat

import Algebra.Semiring
import Algebra.Preorder

%default total

public export
data InfNat = N Nat | Infinity

public export
data LTEInfNat : InfNat -> InfNat -> Type where
  LTENat : LTE n m -> LTEInfNat (N n) (N m)
  LTEInf : LTEInfNat n Infinity

export
Uninhabited (LTEInfNat Infinity (N n)) where
  uninhabited (LTENat x) impossible
  uninhabited LTEInf impossible

public export
Preorder InfNat where
  LTE = LTEInfNat

  isLTE x Infinity = Yes LTEInf
  isLTE (N n) (N m) with (isLTE n m)
    isLTE (N n) (N m) | Yes prf = Yes (LTENat prf)
    isLTE (N n) (N m) | No contra = No (\(LTENat prf) => contra prf)
  isLTE Infinity (N n) = No uninhabited

  preorderRefl (N k) = LTENat lteRefl
  preorderRefl Infinity = LTEInf

  preorderTrans (LTENat x) (LTENat y) = LTENat (lteTransitive x y)
  preorderTrans (LTENat x) LTEInf = LTEInf
  preorderTrans LTEInf LTEInf = LTEInf

public export
Eq InfNat where
  (N n) == (N m) = n == m
  Infinity == Infinity = True
  _ == _ = False

public export
natInjective : N n = N m -> n = m
natInjective Refl = Refl

public export
DecEq InfNat where
  decEq (N n) (N m) with (decEq n m)
    decEq (N n) (N m) | Yes prf = Yes (rewrite prf in Refl)
    decEq (N n) (N m) | No contra = No (contra . natInjective)
  decEq (N n) Infinity = No (\case Refl impossible)
  decEq Infinity (N m) = No (\case Refl impossible)
  decEq Infinity Infinity = Yes Refl

export
Show InfNat where
  show (N n) = show n
  show Infinity = "∞"

export
rigPlus : InfNat -> InfNat -> InfNat
rigPlus (N n) (N m) = N (n + m)
rigPlus Infinity m = Infinity
rigPlus n Infinity = Infinity

export
rigMult : InfNat -> InfNat -> InfNat
rigMult (N 0) m = N 0
rigMult n (N 0) = N 0
rigMult (N n) (N m) = N (n * m)
rigMult Infinity m = Infinity
rigMult n Infinity = Infinity

public export
Semiring InfNat where
  (|+|) = rigPlus
  (|*|) = rigMult
  plusNeutral = N 0
  timesNeutral = N 1

  plusIdentityLeft (N m) = Refl
  plusIdentityLeft Infinity = Refl

  plusAssociative Infinity y z = Refl
  plusAssociative (N x) Infinity z = Refl
  plusAssociative (N x) (N y) Infinity = Refl
  plusAssociative (N x) (N y) (N z) =
    rewrite Nat.plusAssociative x y z in Refl

  plusCommutative (N x) (N y) =
    rewrite Nat.plusCommutative x y in Refl
  plusCommutative (N k) Infinity = Refl
  plusCommutative Infinity (N y) = Refl
  plusCommutative Infinity Infinity = Refl

  timesIdentityLeft (N 0) = Refl
  timesIdentityLeft (N (S x)) =
    rewrite plusZeroRightNeutral x in Refl
  timesIdentityLeft Infinity = Refl

  timesIdentityRight (N 0) = Refl
  timesIdentityRight (N (S x)) =
    rewrite multOneRightNeutral x in Refl
  timesIdentityRight Infinity = Refl

  timesAnnihilationLeft (N x) = Refl
  timesAnnihilationLeft Infinity = Refl

  timesAnnihilationRight (N 0) = Refl
  timesAnnihilationRight (N (S x)) = Refl
  timesAnnihilationRight Infinity = Refl

  timesAssociative (N 0) y z = Refl
  timesAssociative (N (S x)) (N 0) z = Refl
  timesAssociative (N (S x)) (N (S y)) (N 0) = Refl
  timesAssociative (N (S x)) (N (S y)) (N (S z)) =
    rewrite sym $ Nat.plusAssociative z (y * (S z)) (x * S (z + y * (S z))) in
    rewrite multDistributesOverPlusLeft y (x * (S y)) (S z) in
    rewrite multAssociative x (S y) (S z) in Refl
  timesAssociative (N (S x)) (N (S y)) Infinity = Refl
  timesAssociative (N (S x)) Infinity (N 0) = Refl
  timesAssociative (N (S x)) Infinity (N (S z)) = Refl
  timesAssociative (N (S x)) Infinity Infinity = Refl
  timesAssociative Infinity (N 0) z = Refl
  timesAssociative Infinity (N (S y)) (N 0) = Refl
  timesAssociative Infinity (N (S y)) (N (S z)) = Refl
  timesAssociative Infinity (N (S y)) Infinity = Refl
  timesAssociative Infinity Infinity (N 0) = Refl
  timesAssociative Infinity Infinity (N (S z)) = Refl
  timesAssociative Infinity Infinity Infinity = Refl

  timesDistributiveLeft (N 0) (N y) z = Refl
  timesDistributiveLeft (N (S x)) (N 0) (N 0) = Refl
  timesDistributiveLeft (N (S x)) (N 0) (N (S z)) = Refl
  timesDistributiveLeft (N (S x)) (N (S y)) (N 0) =
    rewrite plusZeroRightNeutral y in
    rewrite plusZeroRightNeutral (y + (x * (S y))) in Refl
  timesDistributiveLeft (N (S x)) (N (S y)) (N (S z)) =
    rewrite sym $ Nat.plusAssociative y (S z) (x * (S (y + (S z)))) in
    rewrite sym $ Nat.plusAssociative y (x * (S y)) (S (z + (x * (S z)))) in
    rewrite sym $ plusSuccRightSucc (x * (S y)) (z + (x * (S z))) in
    rewrite Nat.plusCommutative (x * (S y)) (z + (x * (S z))) in
    rewrite sym $ Nat.plusAssociative z (x * (S z)) (x * (S y)) in
    rewrite Nat.plusCommutative y (S z) in
    rewrite sym $ multDistributesOverPlusRight x (S z) (S y) in
    rewrite sym $ plusSuccRightSucc z y in Refl
  timesDistributiveLeft (N (S x)) (N 0) Infinity = Refl
  timesDistributiveLeft (N (S x)) (N (S y)) Infinity = Refl
  timesDistributiveLeft (N 0) Infinity z = Refl
  timesDistributiveLeft (N (S x)) Infinity z = Refl
  timesDistributiveLeft Infinity (N 0) (N 0) = Refl
  timesDistributiveLeft Infinity (N 0) (N (S z)) = Refl
  timesDistributiveLeft Infinity (N (S y)) (N z) = Refl
  timesDistributiveLeft Infinity (N 0) Infinity = Refl
  timesDistributiveLeft Infinity (N (S y)) Infinity = Refl
  timesDistributiveLeft Infinity Infinity z = Refl

  timesDistributiveRight (N 0) (N 0) z = Refl
  timesDistributiveRight (N 0) (N (S y)) (N 0) = Refl
  timesDistributiveRight (N 0) (N (S y)) (N (S z)) = Refl
  timesDistributiveRight (N 0) (N (S y)) Infinity = Refl
  timesDistributiveRight (N 0) Infinity (N 0) = Refl
  timesDistributiveRight (N 0) Infinity (N (S z)) = Refl
  timesDistributiveRight (N 0) Infinity Infinity = Refl
  timesDistributiveRight (N (S x)) (N 0) (N 0) = Refl
  timesDistributiveRight (N (S x)) (N 0) (N (S z)) =
    rewrite plusZeroRightNeutral x in
    rewrite plusZeroRightNeutral (z + (x * (S z))) in Refl
  timesDistributiveRight (N (S x)) (N 0) Infinity = Refl
  timesDistributiveRight (N (S x)) (N (S y)) (N 0) = Refl
  timesDistributiveRight (N (S x)) (N (S y)) (N (S z)) =
    rewrite sym $ Nat.plusAssociative z (x * (S z)) (S (z + (y * (S z)))) in
    rewrite multDistributesOverPlusLeft x (S y) (S z) in
    cong N $ cong S $ cong (plus z) $ Refl
  timesDistributiveRight (N (S x)) (N (S y)) Infinity = Refl
  timesDistributiveRight (N (S x)) Infinity (N 0) = Refl
  timesDistributiveRight (N (S x)) Infinity (N (S z)) = Refl
  timesDistributiveRight (N (S x)) Infinity Infinity = Refl
  timesDistributiveRight Infinity (N 0) z =
    rewrite plusIdentityRight (Infinity |*| z) in Refl
  timesDistributiveRight Infinity (N (S y)) (N 0) = Refl
  timesDistributiveRight Infinity (N (S y)) (N (S z)) = Refl
  timesDistributiveRight Infinity (N (S y)) Infinity = Refl
  timesDistributiveRight Infinity Infinity (N 0) = Refl
  timesDistributiveRight Infinity Infinity (N (S z)) = Refl
  timesDistributiveRight Infinity Infinity Infinity = Refl

||| The top value of a lattice
export
Top InfNat where
  top = Infinity

  topAbs x = LTEInf

export
isNeitherZeroNorTop : InfNat -> Bool
isNeitherZeroNorTop (N 0) = False
isNeitherZeroNorTop (N _) = True
isNeitherZeroNorTop Infinity = False
