||| Products which are skewed one way or the other
module Algebra.SkewProduct

import Algebra.Semiring
import Algebra.Preorder

import Debug.Trace

infixl 7 <&&
infixl 7 &&>
infixl 7 *-
infixl 7 -*


namespace SkewLeft
  ||| a product that skews left
  public export
  record (-*) (a, b : Type) where
    constructor (<&&)
    fst : a
    snd : b

  ||| A product of semirings which preorder is defined by the preorder
  ||| of its left component
  export
  Preorder a => Preorder b => Preorder (a -* b) where
    (l <&& _) <= (l' <&& _) = l <= l'
    preorderRefl = ?proofRefl
    preorderTrans = ?proofTrans

  export
  Show a => Show b => Semiring a => Semiring b => Semiring (a -* b) where
    (l <&& r) |+| (l' <&& r') = (l |+| l' <&& r |+| r')
    (l <&& r) |*| (l' <&& r') = (l |*| l' <&& r |*| r')
    plusNeutral = (plusNeutral {a} <&& plusNeutral {a=b})
    timesNeutral = (timesNeutral {a} <&& timesNeutral {a=b})

  export
  Eq a => Eq (a -* b) where
    a == b = a.fst == b.fst

  export
  Preorder (a -* b) => Top a => Top b => Top (a -* b) where
    top = (top {a} <&& top {a=b})
    topAbs = ?notTopLeft

  export
  Show a => Show b => Show (a -* b) where
    show (a <&& b) = "\{show a} <&& \{show b}"

namespace SkewRight
  ||| a product that skews left
  public export
  record (*-) (a, b : Type) where
    constructor (&&>)
    fst : a
    snd : b

  export
  Preorder a => Preorder b => Preorder (a *- b) where
    (_ &&> r) <= (_ &&> r') = r <= r'
    preorderRefl = ?proofRefl
    preorderTrans = ?proofTrans

  export
  Show a => Show b => Semiring a => Semiring b => Semiring (a *- b) where
    (l &&> r) |+| (l' &&> r') =  (l |+| l' &&> r |+| r')
    (l &&> r) |*| (l' &&> r') =  (l |*| l' &&> r |*| r')
    plusNeutral = (plusNeutral {a} &&> plusNeutral {a=b})
    timesNeutral = (timesNeutral {a} &&> timesNeutral {a=b})

  export
  Eq b => Eq (a *- b) where
    a == b = a.snd == b.snd

  export
  Preorder (a *- b) => Top a => Top b => Top (a *- b) where
    top = (top {a} &&> top {a=b})
    topAbs = ?notTopRIght

  export
  Show a => Show b => Show (a *- b) where
    show (a &&> b) = "\{show a} &&> \{show b}"
