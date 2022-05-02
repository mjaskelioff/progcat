module Library where

open import Data.Empty public
open import Data.Unit public  using (⊤ ; tt)
open import Relation.Binary.HeterogeneousEquality hiding (Extensionality ; [_]) public 
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) public
open import Function using (id; _∘_; _$_ ; _$- ; λ-) public
open ≅-Reasoning renaming (begin_ to proof_) public
open import Level public renaming (suc to lsuc; zero to lzero) hiding (lift)

private
  variable
    a b c d : Level

Extensionality : (a b : Level) → Set _
Extensionality a b =
  {A : Set a} {B₁ B₂ : A → Set b}
  {f₁ : (x : A) → B₁ x} {f₂ : (x : A) → B₂ x} →
  (∀ x → f₁ x ≅ f₂ x) → f₁ ≅ f₂

postulate ext : Extensionality a b

{- extensionalidad para funciones con argumento implícito -}

{- extensionalidad para funciones con argumento implícito -}
postulate iext : ∀{a b}{A : Set a}{B B' : A → Set b}
             {f : ∀ {a} → B a}{g : ∀{a} → B' a} → 
             (∀ a → f {a} ≅ g {a}) → 
             (λ {x} → f {x}) ≅ (λ {x} → g {x})
--             _≅_ {_}{ {a : A} → B a} f { {a : A} → B' a} g

{-
ExtensionalityImplicit : (a b : Level) → Set _
ExtensionalityImplicit a b =  {A : Set a} {B B' : A → Set b} 
                              {f : {x : A} → B x}{g : {x : A} → B' x} →
                              (∀ x → f {x} ≅ g {x}) → 
                             (λ {x} → f {x}) ≅ (λ {x} → g {x})

implicit-extensionality : ∀ {a b} →
                          Extensionality a b →
                          ExtensionalityImplicit a b
implicit-extensionality ext f≅g = {! cong _$- !} --cong _$- (ext λ x → f≅g) 

iext : ExtensionalityImplicit a b
iext = implicit-extensionality ext
-}

{- irrelevance proof -}
ir : ∀ {ℓ} {A : Set ℓ}{B : Set ℓ} {x : A}{y : B} (p q : x ≅ y) → p ≅ q
ir refl refl = refl

iir : ∀ {a b} {I : Set a}{A B : I → Set b}{x : {i : I} → A i} {y : {i : I} → B i}
                    (p q : ∀{i} → x {i} ≅ y {i}) →
                    (λ {i} → p {i}) ≅ (λ {i} → q {i})
                   -- _≅_ {_} { {i : I} → _} p { {i : I} → _} q
iir p q = iext (λ i → ir (p {i}) (q {i})) 

i2ir : ∀ {I J : Set a}{A B : I → J → Set b}
       {x : {i : I} → {j : J}→ A i j}
       {y : {i : I} → {j : J}→ B i j}
       (p q : ∀{i j} → x {i} {j} ≅ y {i} {j}) →
       (λ {i} {j} → p {i} {j}) ≅ (λ {i} {j} → q {i} {j})                      
i2ir p q  =  iext (λ i → iext (λ j → ir p q))
 
