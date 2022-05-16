open import Categories
open import Functors

{-

    ALGEBRAS DE UN FUNTOR

-}
module clase09.F-Algebra{a}{b}{C : Cat {a}{b}}(F : Fun C C) where

open import Library

--------------------------------------------------
-- Suponemos que trabajamos con una categoría C dada y
-- un endofunctor F sobre ella
--------------------------------------------------

record F-algebra : Set (a ⊔ b) where
   constructor falgebra
   open Cat C
   open Fun F
   field
      carrier : Obj
      algebra : Hom (OMap carrier) carrier 

{-
  Un F-Algebra captura la idea de un conjunto que soporta ciertas operaciones.
  El funtor hace las veces de firma (signature) de las operaciones.
-}
