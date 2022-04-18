module Library where

open import Data.Unit public  using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality  
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) public
open import Function using (id; _∘_; _$_) public
open ≡-Reasoning renaming (begin_ to proof_) public
open import Level public renaming (suc to lsuc; zero to lzero) hiding (lift)

private
  variable
    a b c d : Level

{- extensionalidad -}
postulate ext : ∀ {A : Set a}{B : A → Set b}
                {f g : ∀ a → B a} → 
                (∀ a → f a ≡ g a) → f ≡ g


{- extensionalidad para funciones con argumento implícito -}
postulate iext : ∀ {A : Set a}{B : A → Set b}
             {f g : ∀ {a} → B a} → 
             (∀ a → f {a} ≡ g {a}) →
             (λ {a} → f {a}) ≡ (λ {a} → g {a})   
             

{- irrelevance proof -}
ir : ∀ {ℓ} {A : Set ℓ} {x y : A} (p q : x ≡ y) → p ≡ q
ir refl refl = refl


i2ir : ∀ {I J : Set a}{A : I → J → Set b}
       {x y : {i : I} → {j : J}→ A i j}
                    (p q : ∀{i j} → x {i} {j} ≡ y {i} {j}) →
                    (λ {i} {j} → p {i} {j}) ≡ (λ {i} {j} → q {i} {j})  
                    
i2ir p q = iext (λ i → iext ( λ j →  ir ( (p {i} {j}) ) ( (q {i} {j}) )  ))
 
