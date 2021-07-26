module Algebra.SkewLeft

import Algebra.Semiring
import Algebra.Preorder

||| A product of semirings which preorder is defined by the preorder
||| of its left component
export
Preorder a => Preorder b => Preorder (Pair a b) where
  (l, _) <= (l', _) = l <= l'
  preorderRefl = ?proofRefl
  preorderTrans = ?proofTrans

export
Semiring a => Semiring b => Semiring (Pair a b) where
  (l, r) |+| (l', r') = (l |+| l', r |+| r')
  (l, r) |*| (l', r') = (l |*| l', r |*| r')
  plusNeutral = (plusNeutral {a}, plusNeutral {a=b})
  timesNeutral = (timesNeutral {a}, timesNeutral {a=b})

export
Preorder (Pair a b) => Top a => Top b => Top (Pair a b) where
  top = (top {a}, top {a=b})
  topAbs = ?prfTop
