
module Functors.List where

open import Library
open import Functors
open import Categories.Sets

open import Data.List.Base renaming (map to mapList) public

ListF-id : ∀{A : Set}{a : List A} → mapList id a ≅ a
ListF-id {a = []} = refl
ListF-id {a = x ∷ a} = cong (_∷_ x) ListF-id

ListF-comp : ∀{X Y Z : Set}(f : Y → Z )(g : X → Y){a : List X}
          → mapList (f ∘ g) a ≅ mapList f (mapList g a)
ListF-comp f g {[]} = refl
ListF-comp f g {x ∷ a} = cong (_∷_ (f (g x))) (ListF-comp f g)

ListF : Fun Sets Sets
ListF = functor List
                mapList
                (ext (λ _ → ListF-id))
                (λ {_} {_} {_} {f} {g} → ext (λ _ → ListF-comp f g))
