module Categories.Discrete where

open import Categories
open import Library

--------------------------------------------------
{- Categoría Discreta

   Una categoría discreta es una categoría en la que los únicos
morfismos son identidades. La composición y ecuaciones de coherencia
son triviales.
-}

open Cat

Discrete : ∀{a} → Set a → Cat
Discrete X = record
              { Obj = X
              ; Hom = λ X Y → X ≅ Y
              ; iden = refl
              ; _∙_ = λ f g → trans g f
              ; idl = λ {_}{_}{f} →  ir (trans f refl) f 
              ; idr = refl 
              ; ass = λ{_}{_}{_}{_}{f}{g}{h} → ir (trans h (trans g f)) (trans (trans h g) f) 
              }

∣_∣ : ∀{a b} → Cat {a} {b} → Cat
∣ C ∣ = Discrete (Obj C)

