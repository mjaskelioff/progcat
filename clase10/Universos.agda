
module clase10.Universos where 

open import Data.Unit    -- tipo con un elemento
open import Data.Sum     -- unión disjunta de tipos
open import Data.Product -- Producto de dos tipos
open import Data.Nat
open import Data.Vec hiding (toList ; fromList)
open import Data.Fin


-- Universo para los tipos de datos paramétricos finitos con más de un parámetro

data Sig {n : ℕ} : Set₁ where
  U   : Sig                         -- Tipo con un sólo elemento
  P   : Fin n → Sig                -- Parámetros de tipo
  _⊗_ : Sig {n} → Sig {n} → Sig   -- Producto de dos tipos
  _⊕_ : Sig {n} → Sig {n} → Sig   -- Union disjunta
  I   : Sig                         -- Para tipos recursivos (Posición recursiva)
 

-- Función de interpretación 
-- La función de interpretación está indexada por un vector de tipos

⟦_⟧ₚ : ∀ {n} → Sig {n} → Vec Set n → Set → Set
⟦ U ⟧ₚ v r = ⊤
⟦ P x ⟧ₚ v r = lookup v x   
⟦ F ⊗ G ⟧ₚ v r = ⟦ F ⟧ₚ v r × ⟦ G ⟧ₚ v r
⟦ F ⊕ G ⟧ₚ v r = ⟦ F ⟧ₚ v r ⊎ ⟦ G ⟧ₚ v r
⟦ I ⟧ₚ v r = r


data μ {n} (F : Sig {n}) (v : Vec Set n) : Set where
  ⟨_⟩ : ⟦ F ⟧ₚ v (μ F v) → μ F v



-- Otra extensión que agrega la composición de functores

data Signa : Set₁ where
  U   : Signa                        -- Tipo con un sólo elemento
  P   : Signa                        -- Parámetro del tipo
  I   : Signa                        -- Para tipos recursivos (Posición recursiva)
  _⊗_ : Signa → Signa → Signa      -- Producto de dos tipos
  _⊕_ : Signa  → Signa → Signa     -- Union disjunta
  _⊚_ : Signa → Signa → Signa      -- Composición de functores 


{- La función de interpretación está parametrizada por el functor, 
  el parámetro del tipo y la posición recursiva
-}

mutual 
  ⟦_⟧ : Signa → Set → Set → Set
  ⟦ U ⟧ v r = ⊤
  ⟦ P ⟧ v r = v
  ⟦ F ⊗ G ⟧ v r = ⟦ F ⟧ v r × ⟦ G ⟧ v r
  ⟦ F ⊕ G ⟧ v r = ⟦ F ⟧ v r ⊎ ⟦ G ⟧ v r
  ⟦ I ⟧ v r = r
  ⟦ F ⊚ G ⟧ v r = μ' F (⟦ G ⟧ v r)
 

  data μ' (F : Signa) (A : Set ) : Set where
    ⟨_⟩ : ⟦ F ⟧ A (μ' F A) → μ' F A

ListF : Signa
ListF = U ⊕ (P ⊗ I)

RoseF : Signa
RoseF = P ⊗ ( ListF ⊚ I )

ROSE : Set → Set
ROSE A = μ' RoseF A


{-# TERMINATING #-}
mapB : {A B C D : Set} (F : Signa) → (A → B) → (C → D) → ⟦ F ⟧ A C → ⟦ F ⟧ B D  
mapB U f g tt = tt
mapB P f g x = f x
mapB (F ⊗ F₁) f g (x , y) = mapB F f g x , mapB F₁ f g y
mapB (F ⊕ F₁) f g (inj₁ x) = inj₁ (mapB F f g x)
mapB (F ⊕ F₁) f g (inj₂ y) = inj₂ (mapB F₁ f g y)
mapB I f g x = g x
mapB (F ⊚ G) f g ⟨ x ⟩ = ⟨ mapB F (mapB G f g) (mapB (F ⊚ G) f g) x ⟩ 


-- Ejercicio Completar la definición de pmap

{-# TERMINATING #-}
pmap : {A B : Set } (F : Signa) → (A → B) → μ' F A → μ' F B
pmap F f ⟨ x ⟩ = ⟨ ? ⟩




