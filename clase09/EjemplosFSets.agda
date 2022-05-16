
module clase09.EjemplosFSets where

open import Categories.Iso
open import Categories.Sets
open import Categories.Products
open import Categories.Coproducts
open import Categories.Terminal
open import Categories.Initial
open import Functors
open import Functors.Constant
open import Library hiding (_×_)

open Products (SetsHasProducts {lzero})
open Coproducts (SetsHasCoproducts {lzero}) 
open Terminal OneSet
open Initial ZeroSet

open import Functors.Product (SetsHasProducts {lzero})
open import Functors.Coproduct (SetsHasCoproducts {lzero})

open import Data.Sum renaming (_⊎_ to _+_) hiding ([_,_])

--------------------------------------------------
{- Definir el siguiente funtor sobre Sets
 *usando suma y producto de functores*
 La idea es reusar lo que ya está definido.
 *No* definir functores usando el constructor de funtores.
  -}

-- Nat X = 1 + X
Nat : Fun Sets Sets
Nat = ?

module Nat where

  open Fun Nat
  open import clase09.FAlgebraCat Nat
  open F-algebra
  open F-homomorphism
  open import Data.Nat using (ℕ ; suc ; zero)

  -- definir constructores
  0N : μF
  0N = ?

  sucN : μF → μF
  sucN x = ?

--------------------------------------------------
{- Probar que los naturales, junto con foldℕ son el álgebra inicial de Nat -}

  foldℕ : ∀{A : Set} → (A → A) → A → ℕ → A
  foldℕ s z zero = z
  foldℕ s z (suc n) = s (foldℕ s z n)

  μNat : F-algebra
  μNat = ?

  init-homo-base : (k : F-algebra) → ℕ → carrier k 
  init-homo-base k = foldℕ ? ?

  lema-init-homo-prop : {X : F-algebra} → (n : OMap ℕ) → (init-homo-base X ∘ algebra μNat) n ≅
                                       (algebra X ∘ HMap (init-homo-base X)) n
  lema-init-homo-prop (inj₁ x) = refl
  lema-init-homo-prop (inj₂ y) = refl                              

  init-homo-prop : (X : F-algebra) →
       init-homo-base X ∘ algebra μNat ≅  algebra X ∘ HMap (init-homo-base X)
  init-homo-prop X = ext (λ n → lema-init-homo-prop {X} n)
  
  init-homoℕ : {X : F-algebra} → F-homomorphism μNat X
  init-homoℕ {X} = homo (init-homo-base X) (init-homo-prop X) 

  univℕ : ∀{X : F-algebra} → {f : F-homomorphism μNat X}
       → (n : ℕ) →  init-homo-base X n ≅ homo-base f n
  univℕ {f = homo mor prop} zero = ?
  univℕ {X}{f = homo mor prop} (suc n) = ?


  initial-ℕ : Initial (F-AlgebraCat) μNat
  initial-ℕ = ?

--------------------------------------------------
{- Definir un functor cuya algebra inicial sea las listas.
-}

L : (A : Set) → Fun (Sets {lzero}) (Sets {lzero})
L A = ?

module Listas (A : Set) where

  open Fun (L A)
  open import Functors.Algebra (L A)
  open F-homomorphism
  open F-algebra
  open import Data.Nat

  data List (A : Set) : Set where
     Nil : List A
     Cons : A → List A → List A

{-
   Definir constructores, y probar que
   efectivamente son listas (como hicimos con los naturales)
-}
  nil : μF
  nil = ?

  cons : A → μF → μF
  cons x xs = ?

{-
  Definir la función length para listas
-}

  length : μF → ℕ
  length = ?

--------------------------------------------------
{- Probar que los las Listas junto con foldr son el
   álgebra inicial de L -}

  foldr : ∀{A X : Set} → (n : X) → (c : A → X → X) → List A → X
  foldr n c Nil = n
  foldr n c (Cons x xs) = c x (foldr n c xs)

  μList : F-algebra
  μList = ?

  init-homo-base : (k : F-algebra) → List A → carrier k 
  init-homo-base k = ?

  init-homo-prop : (X : F-algebra) →
       init-homo-base X ∘ algebra μList ≅  algebra X ∘ HMap (init-homo-base X)
  init-homo-prop X = ?

  init-homoList : {X : F-algebra} → F-homomorphism μList X
  init-homoList {X} = ?

  univList : ∀{X : F-algebra} → {f : F-homomorphism μList X}
           → (xs : List A) → init-homo-base X xs ≅ homo-base f xs
  univList = ?

  initial-List : Initial (F-AlgebraCat) μList
  initial-List = ?
  