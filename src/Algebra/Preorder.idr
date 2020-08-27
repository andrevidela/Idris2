module Algebra.Preorder

import public Decidable.Equality

%default total

||| Preorder defines a binary relation using the `<=` operator
public export
interface Preorder a where
  LTE : a -> a -> Type
  isLTE : (x, y : a) -> Dec (LTE x y)
  preorderRefl : (x : a) -> LTE x x
  preorderTrans : {0 x, y, z : a} -> LTE x y -> LTE y z -> LTE x z

export
(<=) : Preorder a => a -> a -> Bool
(<=) x y with (isLTE x y)
  (<=) x y | Yes _ = True
  (<=) x y | No  _ = False

||| Least Upper Bound, replace max using only Preorder
export
lub : Preorder a => a -> a -> a
lub x y with (isLTE x y)
  lub x y | Yes _ = y
  lub x y | No  _ = x

||| Greatest Lower Bound, replaces min using only Preorder
export
glb : Preorder a => a -> a -> a
glb x y with (isLTE x y)
  glb x y | Yes _ = x
  glb x y | No  _ = y

||| Strict less-than using the relation from a preorder
public export
LT : (DecEq a, Preorder a) => a -> a -> Type
LT x y = (LTE x y, Not (x = y))

export
isLT : (DecEq a, Preorder a) => (x, y : a) -> Dec (LT x y)
isLT x y with (isLTE x y, decEq x y)
  isLT x y | (Yes lteprf, Yes eqprf) = No (\(_, contra) => contra eqprf)
  isLT x y | (Yes lteprf, No eqprf) = Yes (lteprf, eqprf)
  isLT x y | (No lteprf, _) = No (\(contra, _) => lteprf contra)

export
(<) : (DecEq a, Preorder a) => a -> a -> Bool
(<) x y with (isLT x y)
  (<) x y | Yes _ = True
  (<) x y | No  _ = False

||| The greatest bound of a bounded lattice, we only need to know about preorders however
public export
interface Preorder a => Top a where
   top : a
   topAbs : (x : a) -> LTE x top
