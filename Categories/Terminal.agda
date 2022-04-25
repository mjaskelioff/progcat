module Categories.Terminal where

open import Library
open import Categories
open Cat

record Terminal {a b} (C : Cat {a}{b})(T : Obj C) : Set (a ⊔ b) where
  constructor term
  field t : ∀{X} → Hom C X T
        law : ∀{X}{f : Hom C X T} → t {X} ≅ f


