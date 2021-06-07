module TTImp.InferShow

import Core.Core
import Core.Context
import Core.Env
import Core.GetType
import Core.Normalise
import Core.TT

show : Term vars -> Term vars

inferShow : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            Env Term vars -> Term vars -> Core (Term vars)
inferShow env (App fc (App fc1 (Ref fc3 y (UN "%_++_%")) left) right)
  = do
       typeLeft <- getType env left
       typeRight <- getType env right
       corePutStrLn "left type: \{show !typeLeft.term}"
       corePutStrLn "right type: \{show !typeRight.term}"
       pure (App fc (App fc1 (Ref fc3 y (NS typesNS (UN "++"))) !(inferShow env left))
                 !(inferShow env right))
inferShow env l@(Local fc isLet idx p) = pure l
inferShow env r@(Ref fc x name) = pure r
inferShow env (Meta fc x y xs) = Meta fc x y <$> traverse (inferShow env) xs
inferShow env (Bind fc x b scope) =  ?wat_4
inferShow env (App fc fn arg) =  ?wat_5
inferShow env (As fc x as pat) =  ?wat_6
inferShow env (TDelayed fc x y) =  ?wat_7
inferShow env (TDelay fc x ty arg) =  ?wat_8
inferShow env (TForce fc x y) =  ?wat_9
inferShow env (PrimVal fc x) =  ?wat_10
inferShow env (Erased fc imp) =  ?wat_11
inferShow env (TType fc) =  ?wat_12

data Free : (f : Type -> Type) -> (a : Type) -> Type where
  Pure : a -> Free f a
  Bind : f (Free f a) -> Free f a

Functor f => Functor (Free f) where
  map f m = assert_total $ case m of
    Pure x => Pure (f x)
    Bind x => Bind (map (map f) x)

Functor f => Applicative (Free f) where
  pure = Pure

  m <*> x = assert_total $ case m of
    Pure f => map f x
    Bind f => Bind (map (<*> x) f)

Functor f => Monad (Free f) where
  m >>= f = assert_total $ case m of
    Pure x => f x
    Bind x => Bind (map (>>= f) x)

liftFree : Functor f => f a -> Free f a
liftFree = assert_total $ Bind . map Pure

lowerFree : Monad f => Free f a -> f a
lowerFree m = assert_total $ case m of
  Pure x => pure x
  Bind f => join (map lowerFree f)

iterM : (Functor f) => (f (Core a) -> Core a) -> Free f a -> Core a
iterM f m = assert_total $ case m of
  Pure x => pure x
  Bind x => f (map (iterM f) x)


inferFree : Free (TermF vars) (Term vars) -> Core (Term vars)
inferFree = iterM go
  where
    go : TermF vars (Core (Term vars)) -> Core (Term vars)
    go x = ?go_rhs

