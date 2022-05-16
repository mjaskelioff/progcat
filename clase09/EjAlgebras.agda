
module clase09.EjAlgebras where

open import Library
open import Functors

open import Categories.Sets renaming (Sets to SetsL)
Sets = SetsL {lzero}

open import Functors.Coproduct (SetsHasCoproducts {lzero})
open import Functors.Product (SetsHasProducts {lzero})
open import Functors.Constant
open import Data.Sum


module Monoids where
  {- Como ejemplo de como una F-algebra puede capturar la estructura de un conjunto veamos las siguientes equivalencias -}

  record RawMonoid : Set₁ where
    field
      M : Set
      ε :  M
      _⊗_ :  M → M → M

  -- Un RawMonoid es como un monoide, pero solo verificamos que el portador tenga las operaciones correspondientes, sin verificar
  -- que se cumplan las ecuaciones.

  -- si descurrificamos el operador binario obtenemos:

  record RawMonoid2 : Set₁ where
    field
      M : Set
      ε :  ⊤ → M
      _⊗_ :  M × M → M

  equiv1 : RawMonoid → RawMonoid2
  equiv1 record { M = M ; ε = ε ; _⊗_ = _⊗_ } 
     = record { M = M ; ε = λ _ → ε ; _⊗_ = uncurry _⊗_ }

  -- Podemos juntar las dos operaciones en único par de operaciones:

  record RawMonoid3 : Set₁ where
    field
      M : Set
      opers :  (⊤ → M) × (M × M → M)

  equiv2 : RawMonoid2 → RawMonoid3
  equiv2 = {!   !}


  -- en lugar de tener un par de operaciones, podemos una operación cuyo dominio es una suma

  record RawMonoid4 : Set₁ where
    field
      M : Set
      opers :  (⊤ ⊎ M × M) → M

  equiv3 : RawMonoid3 → RawMonoid4
  equiv3 = {!   !}




  -- Definimos un funtor que capture esta estructura.

  MonF : Fun Sets Sets
  MonF = K ⊤ +F (IdF ×F IdF)

  open import clase09.F-Algebra MonF
  open F-algebra

  {- Dar una MonF-Algebra es lo mismo que dar un RawMonoid_i -}

  equiv4 : RawMonoid4 → F-algebra 
  equiv4 = {!   !}

  equiv5 : F-algebra → RawMonoid
  equiv5 = {!   !}


  -- Algunas algebra para MonF

  open import Data.Nat

  -- Ejercicio: Dar dos F-algebras con carrier ℕ
  Nat-alg1 : F-algebra
  Nat-alg1 = falgebra ℕ [ (λ _ → 0) , uncurry _+_ ]

  Nat-alg2 : F-algebra
  Nat-alg2 = {!   !}
  
  open import Data.List hiding ([_])

  List-alg : (X : Set) → F-algebra
  List-alg X = {!   !}

------------------------------

module Maybe where

  MaybeF : Fun Sets Sets
  MaybeF = K ⊤ +F IdF
  
  open import clase09.F-Algebra MaybeF
  open F-algebra

  --Ejercicio: completar las siguientes algebras

  open import Data.Nat

  Nat-alg3 : F-algebra
  Nat-alg3 = falgebra ℕ {!   !}

  open import Data.List hiding ([_])

  List-alg : F-algebra
  List-alg = {!   !}