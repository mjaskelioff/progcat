{-# OPTIONS --cumulativity #-}

open import Library

module clase06.ConstruccionesSet where
 
 open import Categories.Sets
 open import clase06.Construcciones Sets

 {- Ejercicios
   -- Probar que Sets tiene objeto terminal, productos, inicial, y coproductos
  -}
 SetsHasProducts : Products
 SetsHasProducts = {!!}

 OneSet : Terminal ⊤
 OneSet = {!!}

 -------------------------------------------------
 data _⊎_{a b : Level}(A : Set a)(B : Set b) : Set (a ⊔ b) where
     Inl : A → A ⊎ B
     Inr : B → A ⊎ B

 SetsHasCoproducts : Coproducts
 SetsHasCoproducts = {!   !}

--------------------------------------------------
 ZeroSet : Initial ⊥
 ZeroSet = {!   !}
--------------------------------------------------
 