module Categories.One where

open import Categories
open import Library

--------------------------------------------------
{- Categoría con un objeto y un morfismo (que necesariamente es la identidad) -}

open Cat

One : Cat
One = record
        { Obj = ⊤
        ; Hom = λ _ _ → ⊤
        ; iden = id tt
        ; _∙_ = λ _ _ → tt
        ; idl = refl
        ; idr = refl
        ; ass = refl
        }

