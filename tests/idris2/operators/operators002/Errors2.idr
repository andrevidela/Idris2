
private autobind infixr 0 =@

0 (=@) : (a : Type) -> (a -> Type) -> Type
(=@) a f = (1 x : a) -> f x

wrongId : {0 a : Type} -> a =@ a
wrongId x = x
