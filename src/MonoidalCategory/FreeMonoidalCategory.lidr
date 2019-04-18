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

finSetCategory : Nat -> Category
finSetCategory n = discreteCategory (set $ finSetToFreeMonoid n)

help : (ab : (List (Fin n), List (Fin n))) -> (cd : (List (Fin n), List (Fin n)))
   -> ProductMorphism (finSetCategory n) (finSetCategory n) ab cd
   -> fst ab ++ snd ab = fst cd ++ snd cd
help (c, d) (c, d) (MkProductMorphism Refl Refl) = Refl

finSetTensor : (n : Nat) -> CFunctor (productCategory (finSetCategory n) (finSetCategory n)) (finSetCategory n)
finSetTensor n =
 MkCFunctor
   (\ab => fst ab ++ snd ab)
   help
   (\(a, b) => Refl)
   (\(a, b), (c, d), (e, f), (MkProductMorphism Refl Refl), (MkProductMorphism Refl Refl) => Refl)

help2 : (a, b, c, d, e, f : List (Fin n)) ->
       (g : a = b) ->
       (h : c = d) ->
       (k : e = f) ->
       help (a, c ++ e) (b, d ++ f) (MkProductMorphism g (help (c, e) (d, f) (MkProductMorphism h k))) =
       help (a ++ c, e) (b ++ d, f) (MkProductMorphism (help (a, c) (b, d) (MkProductMorphism g h)) k)
help2 {n} b b d d f f Refl Refl Refl = really_believe_me (Refl {x=Refl {x=b ++ d ++ f}})  -- TODO figure out how to rewrite appendAssociative

finSetToFMC : Nat -> StrictMonoidalCategory
finSetToFMC n = MkStrictMonoidalCategory
                 (finSetCategory n)
                 (finSetTensor n)
                 []
                 (\a => Refl)
                 appendNilRightNeutral
                 appendAssociative
                 help2

data Path : (i -> i -> Type) -> i -> i -> Type where
Nil  : Path e i i
(::) : e i j -> Path e j k -> Path e i k

 l_1...l_m
 ()
a   b

generatorsToCat : (n:Nat) -> List ((Fin n, Fin n)) -> Category
generatorsToCat n gs =
  MkCategory
    (Fin n)
    (\m,p => Path ())
    ?ident
    ?comp
    ?lid
    ?rid
    ?assoc

 generatorsToFMC : (n:Nat) -> List ((finSetToFreeMonoid n, finSetToFreeMonoid n)) -> StrictMonoidalCategory
 generatorsToFMC n gs =
   MkStrictMonoidalCategory
     (finSetToFreeMonoid n)
     ?wat

> data FreeMorphism : (t : Type) -> (domain : List t) -> (codomain : List t) -> Type where
>   MkUnitFreeMorphism : FreeMorphism t [] []
>   MkIdFreeMorphism : (x : t) -> FreeMorphism t [x] [x]
>   MkCompositionFreeMorphism : FreeMorphism t a b -> FreeMorphism t b c -> FreeMorphism t a c
>   MkJuxtapositionFreeMorphism  : FreeMorphism t a b -> FreeMorphism t c d -> FreeMorphism t (a ++ c) (b ++ d)
>   MkGeneratingFreeMorphism : (l : List (List t, List t)) -> (e : (List t, List t)) -> Elem e l -> FreeMorphism t (Basics.fst e) (Basics.snd e)
>

> identitie : (ts : List t) -> FreeMorphism t ts ts
> identitie {t} []      = MkUnitFreeMorphism
> identitie {t} (x::xs) = MkJuxtapositionFreeMorphism (MkIdFreeMorphism x) (identitie xs)

> postulate
> lid : (as, bs : List t) -> (fm : FreeMorphism t as bs) -> MkCompositionFreeMorphism (identitie as) fm = fm

> postulate
> rid : (as, bs : List t) -> (fm : FreeMorphism t as bs) -> MkCompositionFreeMorphism fm (identitie bs) = fm

> postulate
> assoc : (as, bs, cs, ds : List t)
>      -> (fm1 : FreeMorphism t as bs)
>      -> (fm2 : FreeMorphism t bs cs)
>      -> (fm3 : FreeMorphism t cs ds)
>      -> MkCompositionFreeMorphism fm1 (MkCompositionFreeMorphism fm2 fm3) = MkCompositionFreeMorphism (MkCompositionFreeMorphism fm1 fm2) fm3

> generateFreeSymmetricMonoidalCategory : (t : Type) -> (List (t, t)) -> Category
> generateFreeSymmetricMonoidalCategory t generatingMorphisms =
>   MkCategory
>     (set (FreeMonoid t))
>     (FreeMorphism t)
>     (identitie)
>     (\as,bs,cs,fm1,fm2 => MkCompositionFreeMorphism fm1 fm2)
>     lid
>     rid
>     assoc
