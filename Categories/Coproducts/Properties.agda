
open import Categories
open import Categories.Coproducts


module Categories.Coproducts.Properties {l m}{C : Cat {l}{m}}(c : Coproducts C) where

open import Library hiding (_,_)
open Cat C
open Coproducts c

inl-cop : ∀{A B C D}{f : Hom C A}{g : Hom D B} → copair f g ∙ inl ≅ inl {A} {B} ∙ f
inl-cop = law1

inr-cop : ∀{A B C D}{f : Hom C A}{g : Hom D B} → copair f g ∙ inr ≅ inr {A} {B} ∙ g
inr-cop = law2

iden-cop : ∀{A B} →  copair (iden {A}) (iden {B}) ≅ iden {A + B}
iden-cop = sym (law3 (trans idl (sym idr)) (trans idl (sym idr)))

fusion : ∀{A B C D}{f : Hom A C}{g : Hom B C}{h : Hom C D}
        → h ∙ [ f , g ] ≅ [ h ∙ f , h ∙ g ]
fusion {f = f}{g}{h} = law3 (trans ass (congr law1)) (trans ass (congr law2))


fusion-cop : ∀{A B C D E}{f : Hom A B}{g : Hom C D}{h : Hom B E}{i : Hom D E} 
          → [ h , i ] ∙ (copair f g) ≅ [ h ∙ f , i ∙ g ]
fusion-cop {f = f}{g}{h}{i}= law3 (proof
                   ([ h , i ] ∙ [ inl ∙ f , inr ∙ g ]) ∙ inl
                ≅⟨ congl fusion ⟩
                   [ [ h , i ] ∙ inl ∙ f , [ h , i ] ∙ inr ∙ g ] ∙ inl
                ≅⟨ law1 ⟩
                   [ h , i ] ∙ inl ∙ f
                ≅⟨ sym ass ⟩
                  ([ h , i ] ∙ inl) ∙ f
                ≅⟨ congl law1 ⟩
                  h ∙ f
               ∎)
                  (proof
                  ([ h , i ] ∙ [ inl ∙ f , inr ∙ g ]) ∙ inr
                ≅⟨ ass ⟩
                  [ h , i ] ∙ [ inl ∙ f , inr ∙ g ] ∙ inr
                ≅⟨ congr law2 ⟩
                 [ h , i ] ∙ inr ∙ g
                ≅⟨ sym ass ⟩
                 ([ h , i ] ∙ inr) ∙ g
                ≅⟨ congl law2 ⟩
                 i ∙ g
                 ∎)

comp-cop : ∀{A B C A' B' C'}{f : Hom B C}{g : Hom A B}{h : Hom B' C'}{i : Hom A' B'}
         → copair (f ∙ g) (h ∙ i) ≅ copair f h ∙ copair g i
comp-cop {f = f}{g}{h}{i} = proof
                  [ inl ∙ f ∙ g , inr ∙ h ∙ i ]
              ≅⟨ cong₂ [_,_] (sym ass) (sym ass) ⟩
                 [ (inl ∙ f) ∙ g , (inr ∙ h) ∙ i ]
              ≅⟨ sym fusion-cop ⟩
                  [ inl ∙ f , inr ∙ h ] ∙ [ inl ∙ g , inr ∙ i ]
               ∎





