
open import Library
open import Categories

module Categories.Iso {a}{b}(C : Cat {a}{b}) where

open Cat C

--------------------------------------------------
{- Isomorfismo en una categoría -}

record Iso {A B}(f : Hom A B) : Set b
  where
  constructor iso
  field inv  : Hom B A
        rinv : f ∙ inv ≅ iden {B}
        linv : inv ∙ f ≅ iden {A}

open Iso

--------------------------------------------------
{- La identidad es un isomorfismo -}

id-iso : ∀{X} → Iso (iden {X})
id-iso = iso iden idl idr

--------------------------------------------------
{- Los isomorfismos son cerrados bajo composición -}

comp-iso : ∀{X Y Z}{f : Hom Y Z}{g : Hom X Y} →
            Iso f → Iso g → Iso (f ∙ g)
comp-iso {f = f} {g} (iso inv law1 law2) (iso inv₁ law3 law4)
            =  
            iso (inv₁ ∙ inv)
                (proof
                  (f ∙ g) ∙ (inv₁ ∙ inv)
                  ≅⟨ trans ass (cong (_∙_ f) (sym ass)) ⟩
                   f ∙ (g ∙ inv₁) ∙ inv
                  ≅⟨ trans (cong (λ x → f ∙ x ∙ inv) law3) (cong (_∙_ f) idl) ⟩
                  f ∙ inv
                  ≅⟨ law1 ⟩
                  iden
                ∎)
                (proof
                  (inv₁ ∙ inv) ∙ f ∙ g
                  ≅⟨ trans ass (cong (_∙_ inv₁) (sym ass)) ⟩
                  inv₁ ∙ (inv ∙ f) ∙ g
                  ≅⟨ cong (λ x → _∙_ inv₁ (_∙_ x g)) law2 ⟩
                  inv₁ ∙ iden ∙ g
                  ≅⟨ cong (_∙_ inv₁) idl ⟩
                  inv₁ ∙ g
                  ≅⟨ law4 ⟩
                  iden
                ∎)

--------------------------------------------------
{-  Un componente de un isomorfismo
   sólo puede pertenecer a un único isomorfismo -}

iso-ir-aux :  ∀{A B}{f : Hom A B} →
         (p q : Iso f) → inv p ≅ inv q → p ≅ q
iso-ir-aux (iso inv₁ rinv₁ linv₁) (iso .inv₁ rinv₂ linv₂) refl = cong₂ (iso inv₁) (ir rinv₁ rinv₂) (ir linv₁ linv₂)
 
isoEq :  ∀{A B}{f : Hom A B} →
         (p q : Iso f) → p ≅ q
isoEq {f = f} p q = 
            iso-ir-aux p q (
                   proof
                   inv p
                   ≅⟨ sym idr ⟩
                   inv p ∙ iden
                   ≅⟨ cong (_∙_ (inv p)) (sym (rinv q)) ⟩
                   inv p ∙ (f ∙ inv q)
                   ≅⟨ sym ass ⟩
                   (inv p ∙ f) ∙ inv q
                   ≅⟨ cong (λ x → x ∙ (inv q)) (linv p) ⟩
                   iden ∙ inv q
                   ≅⟨ idl ⟩                   
                   inv q
                   ∎) 

