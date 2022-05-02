
open import Categories
open import Categories.Products

module Functors.Product {a b}{C : Cat {a}{b}}(p : Products C) where

open import Library hiding (_×_)

open import Functors

open import Categories.ProductCat


open Cat C
open Products p
open import Categories.Products.Properties p
open Fun

_×F_ : ∀{c d}{D : Cat {c} {d}} → Fun D C → Fun D C → Fun D C
_×F_ {D = D} F G = let open Cat D using () renaming (_∙_ to _∙D_ ; iden to idenD) in
            functor
                 (λ X → OMap F X × OMap G X)
                 (λ f → pair (HMap F f) (HMap G f))
                 (proof
                    pair (HMap F idenD) (HMap G idenD)
                 ≅⟨ cong₂ pair (fid F) (fid G) ⟩
                    pair iden iden
                 ≅⟨ iden-pair ⟩
                    iden
                 ∎)
                 (λ {X Y Z f g} → proof
                     pair (HMap F (f ∙D g)) (HMap G (f ∙D g))
                   ≅⟨ cong₂ pair (fcomp F) (fcomp G) ⟩
                    ⟨ (HMap F f ∙ HMap F g) ∙ π₁ , (HMap G f ∙ HMap G g) ∙ π₂ ⟩
                   ≅⟨ cong₂ ⟨_,_⟩ ass ass ⟩
                     ⟨ HMap F f ∙ HMap F g ∙ π₁ , HMap G f ∙ HMap G g ∙ π₂ ⟩
                   ≅⟨ sym fusion-pair ⟩
                     pair (HMap F f) (HMap G f) ∙ pair (HMap F g) (HMap G g)
                   ∎)

ProdF : Fun (C ×C C) C
ProdF =  functor (λ { (X , Y) → X × Y })
                 (λ { (f , g) → pair f g })
                 iden-pair
                 comp-pair
