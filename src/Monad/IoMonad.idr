module Monad.IoMonad

import Basic.Category
import Basic.Functor
import Basic.NaturalTransformation
import Monad.Monad
import Idris.TypesAsCategory
import Utils

%access public export
%default total

postulate
ioId : (\x => (>>=) {m=IO} x pure) = id

postulate
ioCompose : (f : a -> b) -> (g : b -> c) ->
            (\x => (>>=) {m=IO} x (pure . g  . f)) = (\x => (>>=) {m=IO} ((>>=) {m=IO} x (pure . f)) (\b => pure (g b)))

ioFunctor : CFunctor TypesAsCategory.typesAsCategory TypesAsCategory.typesAsCategory
ioFunctor = MkCFunctor
  IO
  (\a, b => map)
  (\a => ioId)
  (\a,b,c,f,g => ioCompose f g)

postulate
ioCommutativity : (f : a -> b) -> (\x => (>>=) {m=IO} (pure x) (pure . f)) = pure . f

ioUnit : NaturalTransformation
           TypesAsCategory.typesAsCategory
           TypesAsCategory.typesAsCategory
           (idFunctor TypesAsCategory.typesAsCategory)
           Monad.IoMonad.ioFunctor
ioUnit = MkNaturalTransformation
           (\a => pure)
           (\a,b,f => ioCommutativity f)

unlawfulIO : UnlawfulMonad TypesAsCategory.typesAsCategory
unlawfulIO =
  MkUnlawfulMonad ioFunctor ioUnit ?wat2
