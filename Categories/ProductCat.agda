module Categories.ProductCat where

open import Library
open import Categories

--------------------------------------------------
{- Categoría Producto -}
{- Dadas dos categorías, podemos formar la categoría producto 
   Los objetos son el producto cartesiano de los objetos
   Los morfismos son pares de flechas.
-}

open Cat

_×C_ : ∀{a b c d} → Cat {a} {b} → Cat {c} {d} → Cat
C ×C D = record
           { Obj = Obj C × Obj D
           ; Hom = λ X Y → Hom C (fst X) (fst Y) × Hom D (snd X) (snd Y)
           ; iden = (iden C) , (iden D)
           ; _∙_ = λ { f g → _∙_ C (fst f) (fst g) , _∙_ D (snd f) (snd g)}
           ; idl = cong₂ _,_ (idl C) (idl D) 
           ; idr = cong₂ _,_ (idr C) (idr D)
           ; ass = cong₂ _,_ (ass C) (ass D)
           }
