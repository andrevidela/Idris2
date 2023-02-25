data LinearList : Type -> Type where
  Nil : LinearList a
  (::) : (1 x : a) -> (1 xs : LinearList a) -> LinearList a

data LinearListView : LinearList a -> Type where
  IsNil : LinearListView []
  IsCons : {1 x, xs : _} -> LinearListView (x :: xs)

viewList : (1 ls : LinearList a) -> LinearListView ls
viewList [] = IsNil
viewList (x :: xs) = IsCons

%logging "declare.def.clause.with" 5
checkView : (1 ls : LinearList a) -> LinearList a
checkView ls with 1 (viewList ls)
  checkView [] | IsNil = ?rhs1
  checkView (x :: xs) | (IsCons {x} {xs}) = ?rhs2

