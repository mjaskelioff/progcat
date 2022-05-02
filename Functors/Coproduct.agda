
open import Categories
open import Categories.Coproducts

module Functors.Coproduct {a b}{C : Cat {a}{b}}(cop : Coproducts C) where

open import Library

open import Functors
open import Categories.ProductCat

open Cat C
open Coproducts cop
open import Categories.Coproducts.Properties cop
open Fun

_+F_ : ∀{c d}{D : Cat {c} {d}} → Fun D C → Fun D C → Fun D C
_+F_ {D = D} F G = let open Cat D using () renaming (_∙_ to _∙D_)
                in functor (λ X →  OMap F X + OMap G X)
                (λ f → copair (HMap F f) (HMap G f))
                (proof
                  copair (HMap F (Cat.iden D)) (HMap G (Cat.iden D))
                ≅⟨ cong₂ copair (fid F) (fid G)  ⟩
                  copair iden iden
                ≅⟨ iden-cop ⟩
                  iden ∎)
                (λ {X Y Z f g} → proof
                  copair (HMap F (f ∙D g)) (HMap G (f ∙D g))
                  ≅⟨ cong₂ copair (fcomp F) (fcomp G) ⟩
                  copair (HMap F f ∙ HMap F g) (HMap G f ∙ HMap G g)
                  ≅⟨ cong₂ [_,_] (sym ass) (sym ass) ⟩
                   ([ ((inl ∙ HMap F f) ∙ HMap F g) , ((inr ∙ HMap G f) ∙ HMap G g) ])
                  ≅⟨ sym fusion-cop ⟩
                  copair (HMap F f) (HMap G f) ∙ copair (HMap F g) (HMap G g) 
                  ∎)

CoprodF : Fun (C ×C C) C
CoprodF =  functor (λ { (X , Y) → X + Y }) 
                   (λ { (f , g) → copair f g }) 
                   iden-cop 
                   comp-cop



