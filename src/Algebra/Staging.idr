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

ordering : Stage -> Nat
ordering Compile = 0
ordering Runtime = 1
ordering Zero = 2

||| Compile < Runtime < 0
export
Preorder Stage where
  (<=) l r = ordering l <= ordering r
  preorderTrans {x = Compile} a b = ?dontcaretran
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

|||   *     │ Zero │ Runtime | Compile
||| ──────────────────────────────────
||| Zero    │ Zero │  Zero   │  Zero
||| Runtime │ Zero │ Runtime │ Runtime
||| Compile │ Zero │ Runtime │ Compile
mult : Stage -> Stage -> Stage
mult Zero y = Zero
mult x Zero = Zero
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
  top = Runtime
  --topAbs {x = Compile} = Refl
  --topAbs {x = Runtime} = Refl
  --topAbs {x = Zero} = Refl
