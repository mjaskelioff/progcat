
module Functors.Constant where

open import Library
open import Functors
open import Categories

K : ∀{a b}{C D : Cat {a} {b}}(X : Cat.Obj D) → Fun C D
K {D = D} X = let open Cat D in
              functor (λ _ → X)
                      (λ _ → iden)
                      refl
                      (sym idr)
