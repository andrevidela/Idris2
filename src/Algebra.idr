module Algebra

import public Algebra.ZeroOneOmega
import public Algebra.Nats
import public Algebra.Product
import public Algebra.Semiring
import public Algebra.Preorder
import public Utils.Show
import public Algebra.Utils

%default total

public export
RigCount : Type
RigCount = ZeroOneOmega

export
elimRelevant : (Semiring a, Eq a, Top a) => (erased : b) -> (relevant : a -> b) -> (irrelevant : b) -> a -> b
elimRelevant erased rel irr val =
  if val == plusNeutral
     then erased
     else if val == top
             then irr
             else rel val

||| Relevant is everything except 0 and top
export
isRelevant : (Semiring a, Eq a, Top a) => a -> Bool
isRelevant val = val /= top && val /= erased

export
(Top r, Eq r, Show r) => ShowRing r where
  showAppendSpace = ifTop "" (\r => show r ++ " ")
  showSurroundSpace = ifTop "" (\r => " " ++ show r ++ " ")
  showInHole = ifTop "   " (\r => show r ++ " ")
