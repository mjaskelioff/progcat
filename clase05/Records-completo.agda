
module Records-completo where


open import Relation.Binary.PropositionalEquality  

postulate ext : ∀{a b}{A : Set a}{B : A → Set b}
                {f g : ∀ a → B a} → 
                (∀ a → f a ≡ g a) → f ≡ g


{- Veremos, el uso de records para definir estructuras algebraicas -}

{- Notar el uso de de Set₁ en lugar de Set ya que tenemos que
 situarnos en el nivel siguiente a Set₀ = Set, para hablar de cosas en
 Set (como carrier).

Los subindices son ₀ = \_0 y ₁ = \_1

 -}


record Monoid : Set₁  where
  infixr 7 _∙_
  field  Carrier : Set
         _∙_     : Carrier → Carrier → Carrier  {- ∙ = \. -}
         ε       : Carrier
         lid     : {x : Carrier} → ε ∙ x ≡ x
         rid     : {x : Carrier} → x ∙ ε ≡ x
         assoc   : {x y z : Carrier} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z) 

{- ¿Qué sucede si queremos usar un Carrier en Set₁? ¿o en Set₂? -}


open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
{- propiedades simples de la suma, como por ejemplo
 +-identityʳ, y +-assoc
-}

-- Monoide de Naturales y suma

module NatMonoid where

  NatMonoid : Monoid
  NatMonoid = record
                { Carrier = ℕ
                ; _∙_ = _+_
                ; ε = 0
                ; lid = refl
                ; rid = λ {n} → +-identityʳ n
                ; assoc = λ{x} {y} {z} → +-assoc x y z } 

open NatMonoid

--------------------------------------------------
{- Ejercicio: Probar que las listas son un monoide -}

open ≡-Reasoning renaming (begin_ to proof_)

data List (A : Set) : Set where
   [] : List A
   _∷_ : (x : A) → (xs : List A) → List A

infixl 5 _∷_

_++_ : ∀{A} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

ridList : ∀{A} {xs : List A} → (xs ++ []) ≡ xs
ridList {xs = []} = refl
ridList {xs = x ∷ xs} = cong (_∷_ x) ridList

assocList : ∀{A}{x y z : List A} → ((x ++ y) ++ z) ≡ (x ++ (y ++ z))
assocList {x = []} = refl
assocList {x = x ∷ xs} = cong (_∷_ x) (assocList {x = xs})

ListMonoid : (A : Set) → Monoid
ListMonoid A = record
                 { Carrier = List A
                 ; _∙_ = _++_
                 ; ε = []
                 ; lid = refl
                 ; rid = ridList
                 ; assoc = λ {xs} → assocList {_}{xs} }

--------------------------------------------------

{- Ejercicio: Probar que para todo monoide M, N, el producto
   cartesiano de los respectivos soportes (Carrier M × Carrier N)
   es  el soporte de un monoide

 Ayuda : puede ser útil cong₂
-}

open import Data.Product renaming (proj₁ to fst; proj₂ to snd)

Product : (M N : Monoid) → Monoid
Product M N = let  open Monoid M hiding (Carrier; lid; rid; assoc) renaming (ε to ε₁ ;  _∙_ to _∙₁_)
                   open Monoid N hiding (Carrier; lid; rid; assoc) renaming (ε to ε₂ ;  _∙_ to _∙₂_)
                   open Monoid
              in
              record
                { Carrier = Carrier M × Carrier N
                ; _∙_ = λ {(m , n) (m' , n') → (m ∙₁ m') , (n ∙₂ n') }
                ; ε = ε₁ , ε₂
                ; lid = cong₂ _,_ (lid M) (lid N) 
                ; rid = cong₂ _,_ (rid M) (rid N) 
                ; assoc = cong₂ _,_ (assoc M) (assoc N) }

--------------------------------------------------
open import Function

-- Monoide de endofunciones
EndoMonoid : Set → Monoid
EndoMonoid X = record
                 { Carrier = X → X
                 ; _∙_ = _∘′_
                 ; ε = id
                 ; lid = refl
                 ; rid = refl
                 ; assoc = refl }


module Cayley where

  open Monoid using (Carrier)

  Cayley : Monoid → Monoid
  Cayley M = EndoMonoid (Carrier M) 

  rep : (M : Monoid) → Carrier M → Carrier (Cayley M)
  rep M x = λ y → x ∙ y
           where open Monoid M

  abs : (M : Monoid) → Carrier (Cayley M) → Carrier M
  abs M f = f ε
           where open Monoid M

  lemma : (M : Monoid) → {x : Carrier M} →
          abs M (rep M x) ≡ x
  lemma M = rid
           where open Monoid M

module Monoid-Homomorphism where
 open Monoid

-- Homomorfismos de monoides
 record Is-Monoid-Homo (M N : Monoid)(morph : Carrier M → Carrier N) : Set where
   constructor is-monoid-homo
   open Monoid M renaming (ε to ε₁ ;  _∙_ to _∙₁_)
   open Monoid N renaming (ε to ε₂ ;  _∙_ to _∙₂_)
   field
    preserves-unit : morph ε₁ ≡ ε₂
    preserves-mult : ∀{x y} → morph (x ∙₁ y) ≡ morph x ∙₂ morph y 

open Monoid-Homomorphism
open Cayley

rep-is-monoid-homo : {M : Monoid} → Is-Monoid-Homo M (Cayley M) (rep M)
rep-is-monoid-homo {M} = record {
                         preserves-unit = ext (λ a → lid {a})
                       ; preserves-mult = ext (λ a → assoc) }
                  where open Monoid M


open Monoid-Homomorphism public

--------------------------------------------------
{- Ejercicio: Probar que length es un homorfismo de monoides -}

length : {A : Set} → List A → ℕ
length [] = 0
length (x ∷ xs) = 1 + length xs

length-mult : ∀{A}{xs ys : List A} → length (xs ++ ys) ≡ length xs + length ys
length-mult {xs = []} = refl
length-mult {xs = x ∷ xs} = cong ℕ.suc (length-mult {xs = xs})

length-homo : ∀{A} → Is-Monoid-Homo (ListMonoid A) NatMonoid length
length-homo = record {
               preserves-unit = refl ;
               preserves-mult =  λ{xs} → length-mult {xs = xs}  }
              
--------------------------------------------------
module Foldr (M : Monoid) where

 open Monoid M

 {- Ejercicio : Definir foldr y probar que (foldr _∙_ ε) es un homorfismo de monoides -}

 foldr : {A B : Set} → (A → B → B) → B → List A → B
 foldr _⊗_ e [] = e
 foldr _⊗_ e (x ∷ xs) = x ⊗ (foldr _⊗_ e xs)

 foldr-assoc : {xs ys : List Carrier} → foldr _∙_ ε (xs ++ ys)
                                      ≡ (foldr _∙_ ε xs) ∙ (foldr _∙_ ε ys)
 foldr-assoc {xs = []} = sym lid
 foldr-assoc {xs = x ∷ xs}{ys} =
                  proof
                  x ∙ foldr _∙_ ε (xs ++ ys)
                 ≡⟨ cong (_∙_ x) (foldr-assoc {xs}) ⟩
                  x ∙ (foldr _∙_ ε xs ∙ foldr _∙_ ε ys)
                 ≡⟨ sym assoc ⟩
                  (x ∙ foldr _∙_ ε xs) ∙ foldr _∙_ ε ys
                 ∎

 foldr-is-monoid-homo : Is-Monoid-Homo (ListMonoid Carrier) M (foldr _∙_ ε)
 foldr-is-monoid-homo = 
                     record {
                        preserves-unit = refl
                      ; preserves-mult =  λ{xs} → foldr-assoc {xs} 
                      }


--------------------------------------------------

{- Isomorfismos entre conjuntos -}

record Iso (A : Set)(B : Set)(fun : A → B) : Set where
 constructor iso
 field inv : B → A
       law1 : ∀ b → fun (inv b) ≡ b
       law2 : ∀ a → inv (fun a) ≡ a

--open Iso

-----------------------------

{- Ejercicio : introducir un tipo de datos ⊤ con un único habitante y
probar que  ℕ es isomorfo a List ⊤ -}

record ⊤ : Set where
   constructor tt

fun-ej1 : ℕ → List ⊤
fun-ej1 zero = []
fun-ej1 (suc n) = tt ∷ fun-ej1 n
law1-ej1 : (xs : List ⊤) → fun-ej1 (length xs) ≡ xs
law1-ej1 [] = refl
law1-ej1 (x ∷ xs) = cong (_∷_ x) (law1-ej1 xs)

law2-ej1 : (n : ℕ) → length (fun-ej1 n) ≡ n
law2-ej1 zero = refl
law2-ej1 (suc n) = cong suc (law2-ej1 n)

iso1 : Iso ℕ (List ⊤) fun-ej1
iso1 = record { inv = length
              ; law1 = law1-ej1
              ; law2 = law2-ej1 } 


{- Ejercicio: introducir un constructor de tipos Maybe y probar que
Maybe ℕ es isomorfo a ℕ -}

data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A

fun-ej2 : ℕ → Maybe ℕ
fun-ej2 zero = nothing
fun-ej2 (suc n) = just n

inv-ej2 : Maybe ℕ → ℕ
inv-ej2 nothing = 0
inv-ej2 (just x) = suc x

law1-ej2 : (m : Maybe ℕ) → fun-ej2 (inv-ej2 m) ≡ m
law1-ej2 nothing = refl
law1-ej2 (just x) = refl

law2-ej2 : (n : ℕ) → inv-ej2 (fun-ej2 n) ≡ n
law2-ej2 zero = refl
law2-ej2 (suc n) = refl

iso2 : Iso ℕ (Maybe ℕ) fun-ej2
iso2 = record { inv = inv-ej2 ; law1 = law1-ej2 ; law2 = law2-ej2 }

{- Ejercicio: introducir un constructor de tipos _×_ para productos
cartesianos (o usar el de Data.Product) y probar que (A → B × C) es
isomorfo a (A → B) × (A → C) para todos A, B, y C, habitantes de Set -}


--law1-ej3 : {A B C}(b : (A → B) × (A → C))

fun-ej3 : ∀{A B C : Set} → (A → B × C) → (A → B) × (A → C)
fun-ej3 f = (fst ∘ f) , (snd ∘ f)

inv-ej3 : ∀{A B C : Set} → (A → B) × (A → C) → (A → B × C) 
inv-ej3 (f , g) x = (f x) , (g x)

law1-ej3 : ∀{A B C}(b : (A → B) × (A → C)) → fun-ej3 (inv-ej3 b) ≡ b 
law1-ej3 (f , g) = cong₂ _,_ refl refl

iso3 : ∀{A B C} → Iso (A → B × C) ((A → B) × (A → C)) fun-ej3
iso3 = record { inv = inv-ej3
              ; law1 = law1-ej3
              ; law2 = λ a → refl }


{- Ejercicio: construir isomorfismos entre Vec A n × Vec B n y
Vec (A × B) n para todos A, B habitantes de Set y n natural -}

open import Data.Vec

law1-ej4 : ∀{n}{A B : Set}(b : Vec (A × B) n) → uncurry Data.Vec.zip (unzip b) ≡ b
law1-ej4 [] = refl
law1-ej4 (ab ∷ abs) = cong (_∷_ ab) (law1-ej4 abs)

law2-ej4 : ∀{n}{A B : Set}(a : Vec A n × Vec B n) → unzip (uncurry Data.Vec.zip a) ≡ a
law2-ej4 ([] , []) = refl
law2-ej4 (a ∷ as , b ∷ bs) = cong₂ _,_ (cong (_∷_ a) (cong fst (law2-ej4 (as , bs))))
                                       (cong (_∷_ b) (cong snd (law2-ej4 (as , bs))))

iso4 : ∀{A B n} → Iso (Vec A n × Vec B n) (Vec (A × B) n) (uncurry Data.Vec.zip)
iso4 = record { inv = unzip
              ; law1 = law1-ej4
              ; law2 = law2-ej4 }


--------------------------------------------------

{- Ejercicio
 Mostrar que en el caso de la categoría Sets, isomorfismo corresponde a biyección de funciones

Ayuda : puede ser útil usar cong-app
-}

Biyectiva : {X Y : Set}(f : X → Y) → Set
Biyectiva {X} {Y} f = (y : Y) → Σ X (λ x → (f x ≡ y) × (∀ x' → f x' ≡ y → x ≡ x')) 

{- Solucion
-}

iso-biyeccion : {A B : Set} → (f : A → B) → Iso A B f → Biyectiva f 
iso-biyeccion f (iso inv law1 law2) y =  inv y , law1 y , (λ a p → 
                                             proof
                                               inv y
                                               ≡⟨ cong inv (sym p) ⟩
                                               inv (f a)
                                               ≡⟨ law2 a ⟩
                                               a
                                               ∎  )

biyeccion-iso : {A B : Set} → (f : A → B) → Biyectiva f → Iso A B f
biyeccion-iso f biy = iso ((λ y → fst (biy y)))
                                  (λ b → let (x , p , _) = biy b in
                                       proof
                                        f x
                                        ≡⟨ p ⟩
                                        b
                                       ∎)
                                  (λ a → let (x , p , u) = biy (f a) in
                                       proof
                                        x
                                        ≡⟨ u a refl ⟩
                                        a
                                        ∎)
