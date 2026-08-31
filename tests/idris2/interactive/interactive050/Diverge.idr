module Diverge

%default covering

-- No normal form: unfolding this never stops
loopy : Nat -> Nat
loopy n = loopy (S n)

-- The type of the hole mentions it, so normalising the goal diverges
diverging : loopy 0 = 0
diverging = ?diverging_rhs

-- ...but ordinary goals must still be shown in normal form
converging : plus 2 2 = 4
converging = ?converging_rhs
