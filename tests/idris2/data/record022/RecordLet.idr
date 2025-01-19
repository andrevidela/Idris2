record Monoid where
  constructor MkMon
  carrier : Type
  neutral : carrier
  op : carrier -> carrier -> Type

record MonLaws (mon : Monoid) where
  constructor MkMonLaws
  let (+) : mon.carrier -> mon.carrier -> Type
      (+) = mon.op
      i : mon.carrier
      i = mon.neutral
  neutralIdL : forall a . a + i = a
  neutralIdR : forall a . i + a = a
  opAssoc : forall a, b, c . a + (b + c) = (a + b) + c
