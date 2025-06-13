module Libraries.Pipeline

import Data.Vect
import Data.Vect.Quantifiers
import Control.Relation
import Core.Core

public export
interface Category (obj : Type) (arr : Rel obj) | arr where
  identity : {0 x : obj} -> arr x x
  (.andThen) : {0 x, y, z : obj} -> arr x y -> arr y z -> arr x z

public export
Pairup : Vect (S n) a -> Vect n (a, a)
Pairup (x :: []) = []
Pairup (x :: y :: xs) = (x, y) :: Pairup (y :: xs)

public export
Pipeline : Type -> Nat -> Type
Pipeline ty n = Vect (S n) ty

public export
Impl : Rel obj -> Pipeline obj n -> Type
Impl arr xs = All (uncurry arr) (Pairup xs)

GradedImpl : Monoid gr => (gr -> obj -> obj -> Type) -> Pipeline obj n -> Vect n gr -> Type
GradedImpl f [t1] [] = Unit
GradedImpl f (x :: (y :: xs)) (g :: gs)
  = Pair (f g x y) (GradedImpl f (y :: xs) gs)

export
runPipeline : {obj : Type} -> {arr : Rel obj} -> (cat : Category obj arr) =>
              (types : Pipeline obj n) -> Impl arr types -> head types `arr` last types
runPipeline (y :: []) x = identity @{cat}
runPipeline (y :: z :: ys) (x :: xs) = x.andThen (runPipeline (z :: ys) xs)

public export
Fn : Type -> Type -> Type
Fn a b = a -> b

export
runPipelineTypes : (types : Pipeline Type n) -> Impl Fn types -> head types -> last types
runPipelineTypes [_] _ x = x
runPipelineTypes (t1 :: t2 :: ts) (f :: fs) x
  = runPipelineTypes (t2 :: ts) fs (f x)

export
runPipelineCore : (types : Pipeline Type n) ->
               Impl (\a, b => a -> Core b) types -> head types -> Core (last types)
runPipelineCore [_] _ x = pure x
runPipelineCore (t1 :: t2 :: ts) (f :: fs) x
  = f x >>= runPipelineCore (t2 :: ts) fs

[CartesianProduct] Semigroup Type where
  (<+>) = Pair

[CartesianMonoid] Monoid Type using CartesianProduct where
  neutral = Unit

export
runPipelineCoreReader : (types : Pipeline Type n) -> (contexts : Vect n Type) ->
  GradedImpl @{CartesianMonoid} (\c, a, b => c -> a -> Core b) types contexts ->
  All Prelude.id contexts -> head types -> Core (last types)
runPipelineCoreReader [w] contexts x y z = pure z
runPipelineCoreReader (t1 :: t2 :: ts) (c :: cs) (f , fs) (cv :: cvs) arg
  = f cv arg >>= runPipelineCoreReader (t2 :: ts) cs fs cvs

