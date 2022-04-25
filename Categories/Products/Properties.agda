
open import Categories
open import Categories.Products


module Categories.Products.Properties {l m}{C : Cat {l}{m}}(p : Products C) where

open import Library hiding (_×_)
open Cat C
open Products p

π₁-pair : ∀{A B C D}{f : Hom A C}{g : Hom B D} → π₁ ∙ pair f g ≅ f ∙ π₁ {A} {B}
π₁-pair = law1


π₂-pair : ∀{A B C D}{f : Hom A C}{g : Hom B D} → π₂ ∙ pair f g  ≅ g ∙ π₂ {A} {B}
π₂-pair = law2


iden-pair : ∀{A B} →  pair (iden {A}) (iden {B}) ≅ iden {A × B}
iden-pair = sym (law3 (trans idr (sym idl)) (trans idr (sym idl)))


fusion : ∀{A B C D}{f : Hom C A}{g : Hom C B}{h : Hom D C}
        → ⟨ f , g ⟩ ∙ h ≅  ⟨ f ∙  h , g ∙ h ⟩
fusion {f = f}{g}{h} = law3 (trans (sym ass) (congl law1)) (trans (sym ass) (congl law2))

fusion-pair : ∀{A B C D E}{f : Hom B A}{g : Hom D C}{h : Hom E B}{i : Hom E D} 
          → pair f g ∙ ⟨ h , i ⟩ ≅ ⟨ f ∙ h , g ∙ i ⟩
fusion-pair {f = f}{g}{h}{i}= law3 (proof
                   π₁ ∙ ⟨ f ∙ π₁ , g ∙ π₂ ⟩ ∙ ⟨ h , i ⟩
                ≅⟨ congr fusion ⟩
                   π₁ ∙ ⟨ (f ∙ π₁) ∙ ⟨ h , i ⟩ , (g ∙ π₂) ∙ ⟨ h , i ⟩ ⟩
                ≅⟨ law1 ⟩
                   (f ∙ π₁) ∙ ⟨ h , i ⟩
                ≅⟨ ass ⟩
                  f ∙ π₁ ∙ ⟨ h , i ⟩
                ≅⟨ congr law1 ⟩
                  f ∙ h
                ∎)
                  (proof
                  π₂ ∙ ⟨ f ∙ π₁ , g ∙ π₂ ⟩ ∙ ⟨ h , i ⟩
                  ≅⟨ congr fusion ⟩
                  π₂ ∙ ⟨ (f ∙ π₁) ∙ ⟨ h , i ⟩ , (g ∙ π₂) ∙ ⟨ h , i ⟩ ⟩
                  ≅⟨ law2 ⟩
                  (g ∙ π₂) ∙ ⟨ h , i ⟩
                  ≅⟨ ass ⟩
                  g ∙ π₂ ∙ ⟨ h , i ⟩
                  ≅⟨ congr law2 ⟩
                  g ∙ i
                ∎)

comp-pair :  ∀{A B C A' B' C'}{f : Hom B C}{g : Hom A B}{h : Hom B' C'}{i : Hom A' B'}
          → pair (f ∙ g) (h ∙ i) ≅  pair f h ∙ pair g i
comp-pair {f = f}{g}{h}{i} = proof
                 ⟨ (f ∙ g) ∙ π₁ , (h ∙ i) ∙ π₂ ⟩
              ≅⟨ cong₂ ⟨_,_⟩ ass ass ⟩
                 ⟨ f ∙ g ∙ π₁ , h ∙ i ∙ π₂ ⟩
              ≅⟨ sym fusion-pair ⟩
                 pair f h ∙ pair g i
               ∎

