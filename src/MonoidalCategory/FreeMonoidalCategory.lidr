\iffalse
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `idris-ct` Category Theory in Idris library.

Copyright (C) 2019 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
\fi

> module FreeMonoidalCategory
>
> import Basic.Category
> import Basic.Functor
> import Data.List
> import Data.Fin
> import Discrete.DiscreteCategory
> import Monoid.FreeMonoid
> import Monoid.Monoid
> import MonoidalCategory.StrictMonoidalCategory
> import Product.ProductCategory
> import Syntax.PreorderReasoning
>
> %access public export
> %default total
>
> data FreeMorphism : (t : Type) -> (generatingMorphisms : List (List t, List t)) -> (domain : List t) -> (codomain : List t) -> Type where

-- >   MkUnitFreeMorphism : FreeMorphism t [] []
-- >   MkIdFreeMorphism : (x : t) -> FreeMorphism t [x] [x]

>   MkIdFreeMorphism            : (x : List t) -> FreeMorphism t generatingMorphisms x x
>   MkCompositionFreeMorphism   : FreeMorphism t generatingMorphisms a b
>                              -> FreeMorphism t generatingMorphisms b c
>                              -> FreeMorphism t generatingMorphisms a c
>   MkJuxtapositionFreeMorphism : FreeMorphism t generatingMorphisms a b
>                              -> FreeMorphism t generatingMorphisms c d
>                              -> FreeMorphism t generatingMorphisms (a ++ c) (b ++ d)
>   MkGeneratingFreeMorphism    : (l : List (List t, List t))
>                              -> (e : (List t, List t))
>                              -> Elem e l
>                              -> FreeMorphism t l (Basics.fst e) (Basics.snd e)
>
> freeIdentity : (ts : List t) -> FreeMorphism t generatingMorphisms ts ts
> freeIdentity = MkIdFreeMorphism

-- > freeIdentity []      = MkUnitFreeMorphism
-- > freeIdentity (x::xs) = MkJuxtapositionFreeMorphism (MkIdFreeMorphism x) (freeIdentity xs)

>
> freeComposition :
>      (as, bs, cs : List t)
>   -> (fm1 : FreeMorphism t generatingMorphisms as bs)
>   -> (fm2 : FreeMorphism t generatingMorphisms bs cs)
>   -> FreeMorphism t generatingMorphisms as cs
> freeComposition as bs cs fm1 fm2 = MkCompositionFreeMorphism fm1 fm2
>
> postulate
> freeLeftIdentity :
>      (as, bs : List t)
>   -> (fm : FreeMorphism t generatingMorphisms as bs)
>   -> MkCompositionFreeMorphism (freeIdentity as) fm = fm
>
> postulate
> freeRightIdentity :
>      (as, bs : List t)
>   -> (fm : FreeMorphism t generatingMorphisms as bs)
>   -> MkCompositionFreeMorphism fm (freeIdentity bs) = fm
>
> postulate
> freeAssociativity :
>      (as, bs, cs, ds : List t)
>   -> (fm1 : FreeMorphism t generatingMorphisms as bs)
>   -> (fm2 : FreeMorphism t generatingMorphisms bs cs)
>   -> (fm3 : FreeMorphism t generatingMorphisms cs ds)
>   -> MkCompositionFreeMorphism fm1 (MkCompositionFreeMorphism fm2 fm3)
>    = MkCompositionFreeMorphism (MkCompositionFreeMorphism fm1 fm2) fm3
>
> generateFreeCategory : (t : Type) -> List (List t, List t) -> Category
> generateFreeCategory t generatingMorphisms =
>   MkCategory
>     (List t)
>     (FreeMorphism t generatingMorphisms)
>     freeIdentity
>     freeComposition
>     freeLeftIdentity
>     freeRightIdentity
>     freeAssociativity
>
> freeTensorObject : (List t, List t) -> List t
> freeTensorObject pair = fst pair ++ snd pair
>
> freeTensorMorphism :
>      (a, b : (List t, List t))
>   -> ProductMorphism (generateFreeCategory t generatingMorphisms)
>                      (generateFreeCategory t generatingMorphisms)
>                      a b
>   -> FreeMorphism t generatingMorphisms (fst a ++ snd a) (fst b ++ snd b)
> freeTensorMorphism a b (MkProductMorphism f1 f2) = MkJuxtapositionFreeMorphism f1 f2
>
> freeTensor :
>      (t : Type)
>   -> (generatingMorphisms : List (List t, List t))
>   -> CFunctor (productCategory (generateFreeCategory t generatingMorphisms) (generateFreeCategory t generatingMorphisms))
>               (generateFreeCategory t generatingMorphisms)
> freeTensor t generatingMorphisms = MkCFunctor
>   freeTensorObject
>   freeTensorMorphism
>   ?preserveId
>   ?preserveCompose

-- >
-- > generateFreeMonoidalCategory : (t : Type) -> List (t, t) -> StrictMonoidalCategory
-- > generateFreeMonoidalCategory t generatingMorphisms = MkStrictMonoidalCategory
-- >   (generateFreeCategory t generatingMorphisms)
-- >   (freeTensor t generatingMorphisms)
-- >   []
-- >   ?leftUnitor
-- >   ?rightUnitor
-- >   ?associativeObj
-- >   ?associativeMor
