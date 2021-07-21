module Core.IdrSpace

import Core.Spaces

import Core.CaseTree
import Core.Context
import Core.TT

data Pattern : Type where
  PCon : Name -> (args : Pattern) -> (ty : ClosedTerm) -> Pattern
  PDelay : Pattern -> Pattern
  CConstant : Constant -> (ty : ClosedTerm) -> Pattern

Eq Pattern where
  PCon nm args ty == PCon nm' args' ty' =
    nm == nm' && args == args' && ty == ty'
  PDelay p == PDelay p' = p == p'
  CConstant c ty == CConstant c' ty' =
    c == c' && ty == ty'
  _ == _ = False

record InspectType where
  constructor MkInspectType
  type : Term []
  ||| List of
  constructors : List InspectType



toPattern : CaseAlt nm -> Core Pattern
toPattern x = ?toPattern_rhs

TypeSpace Core ClosedTerm Pattern where

  sameTy = (==)

  sameCs = (==)

  sig ty = pure $ ?whut

  dec ty = ?getDecx

  covers cs ty = ?coversImpl

-- TypeSpace ClosedTerm Clause where
--
--   sameTy t1 t2 = t1 == t2
--
--   sameCs (ConCase n tag _ _) (ConCase n' tag' _ _) = n == n' && tag == tag'
--   sameCs (DelayCase n _ _) (DelayCase n' _ _) = n == n'
--   sameCs (ConstCase c _) (ConstCase c' _) = c == c'
--   sameCs (DefaultCase _) (DefaultCase _) = True
--   sameCs _ _ = False
--
--   csFromTy cs ty = ?checkCon
--
--   sig ty = ?constructors
--
--   dec ty = ?getDecx
--
--   -- covers cs ty = ?coversImpl
