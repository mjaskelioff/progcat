
module Functors.Hom where

open import Library
open import Functors
open import Categories
open import Categories.ProductCat
open import Categories.Sets

HomF : ∀{a b}{C : Cat {a}{b}} → Fun ((C Op) ×C C) Sets
HomF {C = C} = let open Cat C 
           in
           functor (λ {(X , Y) → Hom X Y})
                   (λ {(f , g) h → g ∙ h ∙ f})
                   (ext (λ a → trans idl idr))
                   (λ { {_} {_} {_} {f₁ , f₂} {g₁ , g₂} → ext (λ h → 
                          proof
                            (f₂ ∙ g₂) ∙ h ∙ (g₁ ∙ f₁) 
                          ≅⟨ ass ⟩
                          f₂ ∙ g₂ ∙ (h ∙ (g₁ ∙ f₁))
                          ≅⟨ cong (λ k → f₂ ∙ g₂ ∙ k) (sym ass) ⟩
                          f₂ ∙ g₂ ∙ ((h ∙ g₁) ∙ f₁)
                          ≅⟨ cong (λ k → f₂ ∙ k) (sym ass) ⟩
                          f₂ ∙ (g₂ ∙ h ∙ g₁) ∙ f₁
                          ∎
                         )})
