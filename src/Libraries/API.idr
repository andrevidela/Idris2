module Libraries.API

export typebind infixr 0 !>
export infixr 0 =&>
export infixr 0 :-
export prefix 9 !!
export infixr 8 $$
export infixr 1 &>
export infixr 1 |&>
export autobind infixr 0 @>

public export
record API where
  constructor (!>)
  message : Type
  response : message -> Type

public export
record Extension (a : API) (t : Type) where
  constructor (@>)
  msg : a.message
  cont : a.response msg -> t

public export %inline
Value : a.message -> Extension a ()
Value x = (_ <- x) @> ()

public export
(&>) : API -> API -> API
(&>) a b = (x : Extension a b.message) !>
           (y : a.response x.msg ** b.response (x.cont y))

public export
eitherElim :
  (m : Either a b -> Type) ->
  (left : (x : a) -> m (Left x)) ->
  (right : (y : b) -> m (Right y)) ->
  (e : Either a b) -> m e
eitherElim m left right (Left x) = left x
eitherElim m left right (Right x) = right x

public export
(+) : API -> API -> API
(+) a b = (x : Either a.message b.message)
      !> eitherElim (\_ => Type) a.response b.response x


public export
record (=&>) (a, b : API) where
  constructor (!!)
  cont : (x : a.message) ->
         Extension b (a.response x)

export
(|&>) : a =&> b -> b =&> c -> a =&> c


public export 0
(:-) : Type -> Type -> API
(:-) a b = (_ : a) !> b

-- send a message back
-- similar to the writer monad
public export 0
Send : Type -> API
Send a = () :- a

-- recieve a message from the outside
-- similar to the reader monad
public export 0
Recv : Type -> API
Recv a = a :- ()

public export 0
End : API
End = Unit :- Unit

public export
UExt : Extension End ()
UExt = (_ <- ()) @> ()


public export 0
Handler : API -> Type
Handler a = a =&> End

export
mkHandler : ((x : a.message) -> a.response x) -> Handler a
mkHandler f = !! \x => (@>) () (\_ => f x)

export
sendHandler : a -> Handler (Send a)
sendHandler x = !! \_ => (@>) () (\_ => x)

export
runHandler : Handler a -> ((x : a.message) -> a.response x)
runHandler m x = (m.cont x).cont ()

public export
($$) : (Type -> Type) -> API -> API
($$) f a = (x : a.message) !> f (a.response x)

namespace Lift
  export %inline
  map : (0 f : Type -> Type) -> Functor f => a =&> b -> f $$ a =&> f $$ b
  map f m  = !! \ x => let x1 @> x2 = m.cont x
                     in (x' <- x1) @> map x2 x'

public export
transform : {0 a : API} -> (forall x. n (a.response x) -> m (a.response x)) -> m $$ a =&> n $$ a
transform f = !! \x => (x' <- x) @> f x'

