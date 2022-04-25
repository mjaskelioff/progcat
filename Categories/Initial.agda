module Categories.Initial where

open import Library
open import Categories
open Cat

{- Objeto inicial en una categoría -}

record Initial {a b} (C : Cat {a}{b})(I : Obj C) : Set (a ⊔ b) where
  constructor init
  field i : ∀{X} → Hom C I X
        law : ∀{X}{f : Hom C I X} → i {X} ≅ f 


