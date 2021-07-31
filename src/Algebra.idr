module Algebra

import public Algebra.ZeroOneOmega
import public Algebra.Semiring
import public Algebra.Preorder
import public Algebra.Staging
import public Algebra.SkewProduct

%default total

public export
RigCount : Type
RigCount = ZeroOneOmega -* Stage

export
showCount : RigCount -> String
showCount = show
