module Algebra.Staging

import Algebra.Semiring
import Algebra.Preorder

export
data Stage =
  -- ☐
  Compile |
  -- 1
  Runtime |
  -- 0
  Zero

||| Compile < Runtime < 0
export
Preorder Stage where
  Compile <= _ = True
  Runtime <= Runtime = True
  Runtime <= Zero = True
  _ <= Zero = True
  _ <= _ = False
  preorderTrans {x = Compile} a b = Refl
  preorderTrans {x = Runtime} {z} a b = ?stageTrans_2
  preorderTrans {x = Zero} a b = ?stageTrans_3
  preorderRefl {x = Compile} = Refl
  preorderRefl {x = Runtime} = Refl
  preorderRefl {x = Zero} = Refl

export
Eq Stage where
  Compile == Compile = True
  Runtime == Runtime = True
  Zero == Zero = True
  _ == _ = False

export
Show Stage where
  show Compile = "☐"
  show Runtime = "Runtime"
  show Zero = "Zero"

meet : Stage -> Stage -> Stage
meet x y = if x <= y then x else y

mult : Stage -> Stage -> Stage
mult Zero y = Zero
mult Compile Compile = Compile
mult _ _ = Runtime

public export
Semiring Stage where
  (|+|) = meet
  (|*|) = mult
  plusNeutral = Zero
  timesNeutral = Runtime

export
Top Stage where
  top = Zero
  topAbs {x = Compile} = Refl
  topAbs {x = Runtime} = Refl
  topAbs {x = Zero} = Refl
