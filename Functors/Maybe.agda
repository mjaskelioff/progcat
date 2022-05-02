
module Functors.Maybe where

open import Library
open import Functors
open import Categories.Sets
open import Data.Maybe.Base renaming (map to mapMaybe) public

Maybe-id : ∀{A : Set}{a : Maybe A} → mapMaybe id a ≅ a
Maybe-id {a = just x} = refl
Maybe-id {a = nothing} = refl

Maybe-comp : ∀{X Y Z : Set}{f : Y → Z}{g : X → Y}{a : Maybe X} →
             mapMaybe (f ∘ g) a ≅ mapMaybe f (mapMaybe g a)
Maybe-comp {a = just x} = refl
Maybe-comp {a = nothing} = refl

MaybeF : Fun Sets Sets
MaybeF = functor Maybe
                 mapMaybe
                 (ext (λ a → Maybe-id {a = a}))
                 (ext (λ a → Maybe-comp {a = a}))
