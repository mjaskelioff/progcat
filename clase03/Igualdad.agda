{- 

  Introducción a la Programación con Tipos Dependientes
    
          Mauro Jaskelioff

-}


module Igualdad where


{-Igualdad -}
----------------------------------------------------------------------

{-
La noción de igualdad es una noción delicada en teoría de tipos.
Veremos tres nociones de igualdad
- igualdad definicional
- igualdad proposicional
- igualdad heterogénea

La igualdad definicional es la igualdad que chequea automáticamente
Agda. Se obtiene de normalizar (dentro de lo posible) dos expresiones y
ver si se llega a lo mismo. Esta igualdad surge de las ecuaciones en
las definiciones, de la beta-reducción, y en algunos casos de la
eta-reducción.  Por ejemplo, a diferencia de Coq, Agda incluye
eta-equivalencias para funciones, pares y unit

λ x . f x = f 

( fst p , snd p ) = p

⊤ = u

OJO, estas valen para la definición de pares y unit de la
biblioteca que no están definidas como data, sino como records (que ya
veremos). Los records de Agda tienen eta-equivalencias.

-}

--------------------------------------------------
{- Igualdad Proposicional -}

module Propositional where

{- Podríamos definir el tipo de igualdad proposicional en 
este archivo como

data _≡_ {A : Set} : A → A → Set where
   refl : x ≡ x

Pero vamos a importar la definición de la librería standar de Agda.
Para instalarla, seguir la instrucciones de 
  https://github.com/agda/agda-stdlib

En las máquinas del DCC, la librería está instalada en 
  /usr/share/agda-stdlib

Para accederla desde el VS Code modificar 
  agdaMode.connection.commandLineOptions
con
  -i/usr/share/agda-stdlib

Si la librería está bien instalada debería andar el siguiente import
-}

open import Relation.Binary.PropositionalEquality hiding (sym ; trans ; cong ; subst ; Extensionality )

{-
El import importa las deficiones con el fully qualified name.
 Por ej. Relation.Binary.PropositionalEquality._≡_

El open abre el módulo poniendo todos los nombres en top level.

El símbolo de la igualdad proposicional se escribe:
  ≡ = \==

Usando pattern matching podemos probar que ≡ es simétrica y
  transitiva, y dado que refl prueba reflexividad, es una relación de
  equivalencia. -}

sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl 

trans : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl q = q

{- Las funciones respetan la igualdad: -}

cong : {A B : Set} → (f : A → B) → {a b : A} → a ≡ b → f a ≡ f b
cong f {a} {b = .a} refl = refl

subst : {A : Set}(P : A → Set) → {a b : A} → a ≡ b → P a → P b
subst P {a} {.a} refl x = x

--------------------------------------------------
{- Ejercicio -}
{- Probar sym y trans usando subst -}

sym' : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym' {a = a} p = subst {!!} {!!} {!!}

trans' : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans' {a = a} ab bc = subst {!!} {!!} {!!}

--------------------------------------------------

{- unicidad de pruebas de identidad (UIP) -}

uip : {A : Set}{a b : A}(p q : a ≡ b) → p ≡ q
uip refl refl = refl

-------------------------------
{- Inducción y recursión -}

open import Data.Nat hiding (_⊔_) 

0+ : (n : ℕ) → zero + n ≡ n
0+ n = refl

+0 : (n : ℕ) → n + zero ≡ n
+0 zero = refl
+0 (suc otron) = cong suc (+0 otron)

{- Notar que la primera igualdad se deriva de una igualdad
  definicional, mientras que en la segunda hay querealizar cierto
  trabajo para llegar a la prueba -}


{- Miremos la interacción entre + y suc -}

+suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
+suc zero n = refl
+suc (suc m) n = cong suc (+suc m n)

{- Probemos que esta suma es equivalente a la otra -}
_+'_ : ℕ → ℕ → ℕ
x +' zero = x
x +' suc y = suc (x +' y)

suma-equiv : (x y : ℕ) → x + y ≡ x +' y 
suma-equiv x zero = +0 x
suma-equiv x (suc y) = trans (+suc x y) (cong suc (suma-equiv x y))



{- Podemos escribir las pruebas de una forma más elegante: -}

open ≡-Reasoning
open import Data.Product

suma-equiv' : (x y : ℕ) → x + y ≡ x +' y
suma-equiv' x zero = +0 x
suma-equiv' x (suc y) = 
      begin 
       x + suc y
      ≡⟨ +suc x y ⟩
       suc (x + y)
      ≡⟨ cong suc (suma-equiv' x y) ⟩
        suc (x +' y)
      ≡⟨ refl ⟩  
      (x +' suc y)
      ∎
       
{- ⟨ = \<
  ⟩ = \>
  ∎ = \qed
-}

-------------------------------------------------------
{- Ejercicios
intentar que la prueba sea legible usando ≡-Reasoning
-}
+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm m n = {!!}

+-assoc : (m n l : ℕ) → m + (n + l) ≡ (m + n) + l
+-assoc m n l = {!!}

*0 : ∀ m → 0 ≡ m * 0
*0 m = {!   !}

*suc : (m n : ℕ) → m + m * n ≡ m * suc n
*suc m n = {!   !} 

*-comm : (m n : ℕ) → m * n ≡ n * m
*-comm m n = {!   !}

{- 
Decidibilidad 

La igualdad sobre los números naturales es decidible. Es decir,
podemos implementar un función booleana que devuelve true si dos
números son iguales y false si no lo son.

-}

open import Data.Bool 

_≡b_ : ℕ → ℕ → Bool
zero ≡b zero = true
zero ≡b suc m = false
suc n ≡b zero = false
suc n ≡b suc m = n ≡b m


open import Relation.Nullary renaming (¬_ to neg)

{- Probamos que ≡ es "decidible", o sea que para todo m,n : ℕ podemos
  decidir m ≡ n.
-}

lem : (n : ℕ) → neg (0 ≡ suc n)
lem n ()

_≡?_ : (m n : ℕ) → Dec (m ≡ n)
zero ≡? zero = yes refl
zero ≡? suc n = no (lem n)
suc m ≡? zero = no (λ ())
suc m ≡? suc n with m ≡? n 
... | yes p = yes (cong suc p)
... | no nop = no (λ x → nop (cong pred x))

-- 3 ≡? 3
-- 3 ≡? 4

{- El parecido con ≡b debería ser obvio. La diferencia es que ≡?
  no sólo dice "yes" o "no" (que en ≡b es "true" y "false") sino que
  además provee evidencia de por qué esa es la respuesta.
  
  notar que  ≡? es a la vez un programa y una prueba. 
-}

{- La igualdad proposicional presenta algunos problemas:

- No es extensional.

Para solucionar esto último usualmente se agrega un postulado: -}
postulate extensionality : ∀{A : Set}{P : A → Set}
                {f g : (a : A) → P a} →
                (∀ a → f a ≡ g a) → f ≡ g



{- Probamos que _+_ y _+'_ son iguales *como funciones*: -}
suma-equiv-ext : _+_ ≡ _+'_ 
suma-equiv-ext = extensionality (λ a → extensionality (λ b → suma-equiv a b))

-------------------------------------------------------------------------------
{- Ejercicio 
La siguiente función no tipa, a pesar de ser obviamente verdadera. ¿por qué?.

Modificar la última línea de la declaración de tipo para que sea aceptada por Agda.
Ayuda: debe usar subst.
-}

-- Descomentar para realizar el ejercicio
respProp : {A : Set}{P : A → Set}{f : (a : A) → P a}{x y : A} →
        (q : x ≡ y) →
        subst P q (f x) ≡ f y
respProp refl = refl
















---------------------------------------------------------------------------------
{- Igualdad Heterogénea -}

{-

El uso de subst es confuso y hace los tipos difíciles de leer.
Para solucionar la molestia de los subst utilizamos la llamada "igualdad heterogénea":
-}

open import Relation.Binary.HeterogeneousEquality using (_≅_ ; refl)
import Relation.Binary.HeterogeneousEquality as H 

{-   ≅ = \cong
data _≅_ {A : Set} : A → {B : Set} → B → Set where
   refl : {x : A} → x ≅ x
-}

{- A diferencia de la igualdad proposicional, en esta la relación de
igualdad es entre tipos potencialmente diferentes. Por supuesto, sólo
podemos construir elementos sobre el mismo tipo.

Por este motivo fue denominada por su creador, Conor McBride como la
"igualdad de John Major" (Jonh Major fue un primer ministro conservador
del Reino Unido en los 80), porque
"it widens aspirations of equality without really changing the outcome".

Por ejemplo, la función de abajo tipa sin modificaciones
(comparar con respProp).

-}
respHet : {A : Set}{P : A → Set}{f : (a : A) → P a}{x y : A} →
          (x ≅ y) → f x ≅ f y
respHet refl = refl 

{- Toda igualdad heterogénea puede ser llevada a la igualdad
proposicional y viceversa -}

≅→≡ : ∀ {a} {A : Set a} {x y : A} → x ≅ y → x ≡ y
≅→≡ refl = refl

≡→≅ : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≅ y
≡→≅ refl = refl


{- La igualdad heterogénea tiene irrelevancia de prueba:
dadas dos pruebas de la misma igualdad, estas son iguales:
-}

ir : ∀{A B : Set}{a : A}{b : B} → (p q : a ≅ b) → p ≅ q
ir refl refl = refl

{-
Al igual que para la proposicional, tenemos que la igualdad
heterogénea es una relación de equivalencia (refl, sym, trans), posee
funciones como cong, y necesitamos de postulados de extensionalidad.

-}

Extensionality : Set₁
Extensionality =
  {A : Set} {B₁ B₂ : A → Set}
  {f₁ : (x : A) → B₁ x} {f₂ : (x : A) → B₂ x} →
  (∀ x → B₁ x ≡ B₂ x) → (∀ x → f₁ x ≅ f₂ x) → f₁ ≅ f₂

sym≅ : {A : Set} → {a b : A} → a ≅ b → b ≅ a
sym≅ refl = refl

postulate ext : Extensionality

{-
 Si queremos probar extensionalidad sobre una función con argumento implícito
-}

ExtensionalityImplicit : Set₁
ExtensionalityImplicit =
  {A : Set} {B : A → Set} {f g : {x : A} → B x} →
  (∀ {x} → f {x} ≅ g {x}) → (λ {x} → f {x}) ≅ (λ {x} → g {x})

{-
Ejercicio. Probar que no hace falta *postular* ExtensionalityImplicit ya que Extensionalidad la implica.
Puede ser últil el siguiente operador posfijo
-}
_$- : {A : Set} {B : A → Set} → ((x : A) → B x) → ({x : A} → B x)
f $- = f _

implicit-extensionality : Extensionality → ExtensionalityImplicit
implicit-extensionality ext f≅g = {!   !}

iext : ExtensionalityImplicit
iext = {!   !}


--------------------------------------------------
{- Ejercicios extras-}

{- ⊎ = \uplus -}
{- disjoint union (⊎) -}

open import Data.Sum

{- Definir funciones,
  mod₂ : resto de dividir por 2
  div₂ : división por 2
-}
mod₂ : ℕ → ℕ 
mod₂ n = {!   !}

div₂ : ℕ → ℕ
div₂ n = {!   !}

{- Probar las sigfuientes propiedades: -}

mod₂Lem : (n : ℕ) → (mod₂ n ≡ 0) ⊎ (mod₂ n ≡ 1)
mod₂Lem n = {!   !}

div₂Lem : ∀ {n} → 2 * (div₂ n) + mod₂ n ≡ n
div₂Lem {n} = {!   !}

{- Mostrar que la igualdad modulo 2 es decidible -}

_≡₂_ : ℕ → ℕ → Set
m ≡₂ n = mod₂ m ≡ mod₂ n

_≡₂?_ : (m n : ℕ) → Dec (m ≡₂ n)
m ≡₂? n = {!   !}
