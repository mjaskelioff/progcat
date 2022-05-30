-- Introducción a Universos

-- Definición : Consiste en
-- * una descripción de los tipos mediante códigos
-- * una función de interpretación, donde los códigos son interpretados como tipos.  
-- (La intención es que la interpretación de un código paticular sea isomorfa al tipo que
-- representa)



open import Data.Empty   -- tipo vacío
open import Data.Unit    -- tipo con un elemento
open import Data.Sum     -- unión disjunta de tipos
open import Data.Product -- Producto de dos tipos
open import Data.Nat
open import Data.Bool

-- Universo Simple

-- Descripción de los tipos
data SU : Set where
  unit : SU
  nat : SU
  sum : SU → SU → SU
  prod : SU → SU → SU

-- Función de interpretación
⟦_⟧ₛ : SU → Set
⟦ unit ⟧ₛ =  ⊤
⟦ nat ⟧ₛ = ℕ
⟦ sum r s ⟧ₛ = ⟦ r ⟧ₛ ⊎ ⟦ s ⟧ₛ
⟦ prod r s ⟧ₛ = ⟦ r ⟧ₛ × ⟦ s ⟧ₛ


-- ¿Podemos definir _==_ : ∀ {A} → A -> A -> Bool? 

-- Función genérica _==_
-- Programación genérica : El objetivo es definir una función para una clase de tipos 

_==_ : {A : SU} → ⟦ A ⟧ₛ → ⟦ A ⟧ₛ → Bool
_==_ {A} x y = {!!} 











