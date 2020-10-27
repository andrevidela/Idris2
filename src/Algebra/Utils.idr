module Algebra.Utils

public export
interface AsNat a where
  toNat : a -> Maybe Nat
  fromNat : Nat -> a

public export
interface AdditiveInverse r where
  minus : r -> r -> r

