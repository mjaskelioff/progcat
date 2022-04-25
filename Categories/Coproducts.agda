open import Data.Sum hiding ([_,_])
open import Library hiding (_,_)
open import Categories

module Categories.Coproducts {l}{m}(C : Cat {l} {m}) where

open Cat C

record Coproducts : Set (m ⊔ l) where
  constructor coproduct
  infixr 2 _+_
  field _+_   : Obj → Obj → Obj
        inl   : ∀{A B} → Hom A (A + B)
        inr   : ∀{A B} → Hom B (A + B)
        [_,_] : ∀{A B C} -> Hom A C -> Hom B C -> Hom (A + B) C
        law1  : ∀{A B C}{f : Hom A C}{g : Hom B C} →
                [ f , g ] ∙ inl ≅ f
        law2  : ∀{A B C}{f : Hom A C}{g : Hom B C} →
                [ f , g ] ∙ inr ≅ g
        law3  : ∀{A B C}{f : Hom A C}{g : Hom B C}{h : Hom (A + B) C} →
                h ∙ inl ≅ f → h ∙ inr ≅ g → h ≅ [ f , g ]
                
  copair : ∀{X Y Z W}(f : Hom X Z)(g : Hom Y W) → Hom (X + Y) (Z + W)
  copair f g = [ inl ∙ f , inr ∙ g ]

