module Categories.Sets where

open import Library
open import Categories

Sets : ∀{l} → Cat
Sets {l} = record{
  Obj  = Set l;
  Hom  = λ X Y → X → Y; 
  iden = id;
  _∙_ = λ f g → f ∘ g;
  idl  = refl; 
  idr  = refl; 
  ass  = refl}

--------------------------------------------------
open import Categories.Products

SetsHasProducts : ∀{l} → Products (Sets {l}) 
SetsHasProducts = prod _×_
                       fst
                       snd
                       (λ f g c → f c , g c)
                       refl
                       refl
                       (λ pf pg → ext (λ a → cong₂ _,_ (cong-app pf a)
                                                         (cong-app pg a)))

--------------------------------------------------
open import Categories.Coproducts

open import Data.Sum using (_⊎_) renaming (inj₁ to Inl ; inj₂ to Inr) 

SetsHasCoproducts : ∀{l} → Coproducts (Sets {l})
SetsHasCoproducts = record
                          { _+_ = _⊎_
                          ; inl = Inl
                          ; inr = Inr
                          ; [_,_] = λ f g  → λ { (Inl x) → f x; (Inr x) → g x  }
                          ; law1 = refl
                          ; law2 = refl
                          ; law3 = λ {_}{_}{_}{f} {g}{h} p q → ext
                              (λ { (Inl x) → cong-app p x ; (Inr x) → cong-app q x })
                          }

--------------------------------------------------
open import Categories.Initial

ZeroSet : Initial Sets ⊥
ZeroSet = record {i = λ(); law = ext λ()}


--------------------------------------------------
open import Categories.Terminal

OneSet : Terminal Sets ⊤
OneSet = record {t = λ _ → _; law = ext (λ _ → refl)}
