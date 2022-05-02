
module Categories.CAT where

open import Library
open import Categories
open import Functors

{- Categoría (grande) de categorías chicas
-}

CAT : ∀{a}{b} → Cat
CAT {a}{b} = record
           { Obj = Cat {a} {b}
           ; Hom = Fun
           ; iden = IdF
           ; _∙_ = _○_
           ; idl = Functor-Eq refl refl
           ; idr = Functor-Eq refl refl
           ; ass = Functor-Eq refl refl
           }

--------------------------------------------------
-- The category CAT has products
--------------------------------------------------
open import Categories.Products
open import Categories.ProductCat
open import Functors

fstF : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}} → Fun (C ×C D) C
fstF = functor fst fst refl refl

sndF : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}} → Fun (C ×C D) D
sndF = functor snd snd refl refl

open Fun

pair : ∀{a1 a2 a3 b1 b2 b3}{A : Cat {a1}{b1}}{B : Cat {a2}{b2}}{C : Cat {a3}{b3}}
    → Fun C A → Fun C B → Fun C (A ×C B)
pair F G = functor (λ X → (OMap F X) , (OMap G X))
                   (λ f → HMap F f , HMap G f)
                   (cong₂ _,_ (fid F) (fid G))
                   (cong₂ _,_ (fcomp F) (fcomp G))

pair-ump : ∀{a1 a2 a3 b1 b2 b3}{A : Cat {a1}{b1}}{B : Cat {a2}{b2}}{C : Cat {a3}{b3}}
            {f : Fun C A} {g : Fun C B}
            {h : Fun C (A ×C B)}
          → fstF {C = A}{B} ○ h ≅ f
          → sndF {C = A}{B} ○ h ≅ g
          → h ≅ pair f g
pair-ump refl refl = Functor-Eq refl refl

CATHasProducts : ∀{a b} →  Products (CAT {a} {b})
CATHasProducts = prod (λ A B → A ×C B)
                      (λ {A} {B} → fstF {C = A}{B})
                      (λ {A} {B} → sndF {C = A}{B})
                      pair
                      (Functor-Eq refl refl)
                      (Functor-Eq refl refl)
                      pair-ump

--------------------------------------------------
