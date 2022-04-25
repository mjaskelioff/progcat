open import Library hiding (_×_ ; swap)
open import Categories

module Categories.Products {l}{m}(C : Cat {l}{m}) where

open Cat C

record Products : Set (l ⊔ m)
  where
  constructor prod
  infixr 3 _×_
  field _×_ : Obj → Obj → Obj
        π₁ : ∀{A B} → Hom (A × B) A
        π₂ : ∀{A B} → Hom (A × B) B
        ⟨_,_⟩ : ∀{A B C} →(f : Hom C A) → (g : Hom C B) → Hom C (A × B)
        law1 : ∀{A B C}{f : Hom C A}{g} → π₁ {A} {B} ∙ ⟨ f , g ⟩ ≅ f
        law2 : ∀{A B C}{f : Hom C A}{g} → π₂ {A} {B} ∙ ⟨ f , g ⟩ ≅ g
        law3 : ∀{A B C}{f : Hom C A}{g : Hom C B}{h : Hom C (A × B)} →
               π₁ ∙ h ≅ f → π₂ ∙ h ≅ g → h ≅ ⟨ f , g ⟩

  pair : ∀{A B C D}(f : Hom A B)(g : Hom C D) → Hom (A × C) (B × D)
  pair f g = ⟨ f ∙ π₁ , g ∙ π₂ ⟩


module ProductIso where

  open Products
  open import Categories.Iso

  ProductIso : ∀{A B} → (p q : Products)
           → Iso C (⟨_,_⟩ p {A} {B} (π₁ q) (π₂ q))
  ProductIso (prod _×p_ π₁p π₂p ⟨_,_⟩p law1p law2p law3p)
             (prod _×q_ π₁q π₂q ⟨_,_⟩q law1q law2q law3q) =
               iso ⟨ π₁p , π₂p ⟩q
                   (proof
                   ⟨ π₁q , π₂q ⟩p ∙ ⟨ π₁p , π₂p ⟩q
                   ≅⟨ law3p (trans (sym ass) (trans (cong₂ _∙_ law1p refl) law1q))
                            (trans (sym ass) (trans (cong₂ _∙_ law2p refl) law2q)) ⟩
                   ⟨ π₁p , π₂p ⟩p
                   ≅⟨ sym (law3p idr idr) ⟩
                   iden
                   ∎)
                   (proof
                     ⟨ π₁p , π₂p ⟩q ∙ ⟨ π₁q , π₂q ⟩p
                    ≅⟨ law3q (trans (sym ass) (trans (cong₂ _∙_ law1q refl) law1p))
                             (trans (sym ass) (trans (cong₂ _∙_ law2q refl) law2p)) ⟩
                     ⟨ π₁q , π₂q ⟩q
                    ≅⟨ sym (law3q idr idr) ⟩
                    iden
                    ∎)

open ProductIso public

module ProductMorphisms (p : Products) where

  open Products p
  
  ×-swap : ∀{A B} → Hom (A × B)  (B × A)
  ×-swap = ⟨ π₂ , π₁ ⟩

  ×-assoc : ∀{A B C} → Hom ((A × B) × C) (A × (B × C))
  ×-assoc = ⟨ (π₁ ∙ π₁) , ⟨ (π₂ ∙ π₁) , π₂ ⟩ ⟩

  --swap y assoc son isomorfismos.

open ProductMorphisms public

