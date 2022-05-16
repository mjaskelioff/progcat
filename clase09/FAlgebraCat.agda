
open import Categories
open import Functors

module clase09.FAlgebraCat {a}{b}{C : Cat {a}{b}}(F : Fun C C) where

open import Library
open import clase09.F-Algebra F public
open F-algebra
open Fun F

--------------------------------------------------
-- Suponemos que trabajamos con una categoría C dada y
-- un endofunctor F sobre ella
--------------------------------------------------
{-

    HOMOMORFISMOS DE ALGEBRAS DE UN FUNTOR

-}
--------------------------------------------------

--------------------------------------------------
{- Un homomorfismo de álgebras <A,α> → <B,β> consiste en:
    un morfismo h entre los portadores de las algebras A → B
    una prueba de que se preserva la estructura:

        FA ----HMap F h ----> FB
        |                      |
        α                      β
        |                      |
        V                      V
        a-----------h--------> B
-}

open Cat C

record F-homomorphism (f g : F-algebra): Set (a ⊔ b) where
   constructor homo
   open F-algebra
   field
      homo-base : Hom (carrier f) (carrier g)
      homo-prop :  homo-base  ∙ algebra f ≅ algebra g ∙ HMap (homo-base) 

open F-homomorphism

--------------------------------------------------
{- Como es usual definimos cuando dos morfismos en la categoría
son iguales: en este caso serán iguales si sus respectivos morfismos
de C (homo-base) son iguales.
-}

homomorphismEq : {X Y : F-algebra}
         → {h k : (F-homomorphism) X Y}
         → homo-base h ≅ homo-base k
         → h ≅ k 
homomorphismEq {h = homo homo-base₁ homo-prop₁} {homo .homo-base₁ homo-prop₂} refl = 
               cong (homo homo-base₁) (ir homo-prop₁ homo-prop₂)

--------------------------------------------------
{- La identidad es un homomorfismo -}

iden-homo : {h :  F-algebra} → (F-homomorphism) h h
iden-homo {h} = record {
               homo-base = iden;
               homo-prop = proof
                  iden ∙ algebra h
                  ≅⟨ idl ⟩
                  algebra h
                  ≅⟨ sym idr ⟩
                  algebra h ∙ iden
                  ≅⟨ congr (sym fid) ⟩
                  algebra h ∙ HMap iden
                  ∎
            }

--------------------------------------------------
{- La composición de homomorfismo es un homomorfismo -}
--composition of homomorphisms
comp-homo : {x y z : F-algebra} 
         → (F-homomorphism) y z
         → (F-homomorphism) x y
         → (F-homomorphism) x z
comp-homo {x}{y}{z} h k = record {
               homo-base = homo-base h ∙ homo-base k ;
               homo-prop = proof
               (homo-base h ∙ homo-base k) ∙ algebra x
               ≅⟨ ass ⟩
               homo-base h ∙ homo-base k ∙ algebra x
               ≅⟨ congr (homo-prop k) ⟩
               homo-base h ∙ algebra y ∙ HMap (homo-base k)
               ≅⟨ sym ass ⟩
               (homo-base h ∙ algebra y) ∙ HMap (homo-base k)
               ≅⟨ congl (homo-prop h) ⟩
               (algebra z ∙ HMap (homo-base h)) ∙ HMap (homo-base k)
               ≅⟨ ass ⟩
               algebra z ∙ HMap (homo-base h) ∙ HMap (homo-base k)
               ≅⟨ congr (sym fcomp) ⟩                    
               algebra z ∙ HMap (homo-base h ∙ homo-base k)
            ∎ } 

--------------------------------------------------
{- Con todo lo anterior podemos definir la 


   CATEGORÍA DE F-ALGEBRAS

   
-}


F-AlgebraCat  : Cat
F-AlgebraCat = record
                  { Obj  = F-algebra
                  ; Hom  = F-homomorphism
                  ; iden = iden-homo
                  ; _∙_  = comp-homo
                  ; idl  = homomorphismEq idl
                  ; idr  = homomorphismEq idr
                  ; ass  = homomorphismEq ass
                  }
                  
--------------------------------------------------
{- Ejercicio: Dada un algebra <X,h>, entonces  <FX, Fh> es un algebra-}

mapF : F-algebra → F-algebra
mapF falg = falgebra (OMap (carrier falg)) (HMap (algebra falg))

--------------------------------------------------
{- Tenemos un funtor que se olvida de la estructura y
   nos devuelve sólo el portador de las algebras y el morfismo base
-}
   
ForgetfulAlgebra : Fun (F-AlgebraCat) C
ForgetfulAlgebra = record{ OMap = carrier
                     ; HMap = homo-base
                     ; fid = refl
                     ; fcomp = refl}


--------------------------------------------------

open import Categories.Initial

{- Suponemos que la categoría tiene un álgebra inicial
(en general esto depende de F, pero siempre existe para
los funtores polinomiales)
-}
postulate inF : F-algebra
postulate F-initiality : Initial F-AlgebraCat inF

-- Por comodidad nombramos los componentes del álgebra inicial
open Initial F-initiality renaming (i to init-homo ; law to univ) public
open F-algebra inF renaming (carrier to μF ; algebra to α) public

fold : ∀{X : Obj} → (f : Hom (OMap X) X) → Hom μF X 
fold {X} f = homo-base (init-homo {falgebra X f})


{- El algebra inicial es un homomorfismo -}
α-homo : (F-homomorphism) (mapF inF) inF
α-homo = homo α refl

--------------------------------------------------
{- Lema de Lambek -}
{- El álgebra inicial es un isomorfismo -}

open import Categories.Iso

lemma : comp-homo α-homo init-homo ≅ iden-homo
lemma = homomorphismEq (proof
         α ∙ homo-base init-homo 
         ≅⟨ sym (cong homo-base (univ {f = comp-homo α-homo init-homo})) ⟩
         homo-base init-homo
         ≅⟨ cong homo-base univ ⟩
         iden
         ∎)

L : Iso F-AlgebraCat α-homo
L = iso init-homo
      lemma
      (homomorphismEq (proof  
        homo-base init-homo ∙ α
        ≅⟨ homo-prop init-homo ⟩
        HMap α ∙ HMap (homo-base init-homo)
        ≅⟨ sym fcomp ⟩
        HMap (α ∙ homo-base init-homo)
        ≅⟨ cong HMap (cong homo-base lemma) ⟩
        HMap (homo-base iden-homo)
        ≅⟨ fid ⟩
        iden
        ∎
        ))

----------------------------------------------------
-- Fusion
open F-algebra

alg-fusion : (f g : F-algebra) → (h : F-homomorphism f g) 
       →  comp-homo h (init-homo {f}) ≅ init-homo {g}
alg-fusion (falgebra A f) (falgebra B g) (homo h homo-prop) 
     = sym univ

{- Ejercicio: Probar el lema "funcional" de fusion -}
fusion : ∀{A B} → (f : Hom (OMap A) A) 
                → (g : Hom (OMap B) B) 
                → (h : Hom A B) 
                → (h ∙ f ≅ g ∙ HMap h) 
                → h ∙ fold f ≅ fold g
fusion {A} {B} f g h p = {!   !}

