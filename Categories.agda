module Categories where

open import Library

private
  variable
    a b : Level

--------------------------------------------------
record Cat : Set (lsuc (a ⊔ b)) where
  infixr 7 _∙_
  field Obj  : Set a
        Hom  : Obj → Obj → Set b
        iden : ∀{X} → Hom X X
        _∙_  : ∀{X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        idl  : ∀{X Y}{f : Hom X Y} → iden ∙ f ≅ f
        idr  : ∀{X Y}{f : Hom X Y} → f ∙ iden ≅ f
        ass  : ∀{W X Y Z}{f : Hom Y Z}{g : Hom X Y}{h : Hom W X} → 
                (f ∙ g) ∙ h ≅  f ∙ (g ∙ h)

  congl : ∀{X Y Z}{f g : Hom X Y}{h : Hom Z X} 
        → (p : f ≅ g) → f ∙ h ≅ g ∙ h
  congl p = cong₂ _∙_ p refl
  
  congr : ∀{X Y Z}{ f g : Hom X Y}{h : Hom Y Z} 
        → (p : f ≅ g) → h ∙ f ≅ h ∙ g
  congr p = cong₂ _∙_ refl p

  conglr : ∀{X Y Z}{ f g : Hom X Y}{h k : Hom Y Z} → (p : h ≅ k) → (q : f ≅ g) → h ∙ f ≅ k ∙ g
  conglr p q = cong₂ _∙_ p q


open Cat

--------------------------------------------------
_Op : ∀{a b} → Cat {a} {b} → Cat
C Op = 
  record{
  Obj  = Obj C; 
  Hom  = λ X Y → Hom C Y X;
  iden = iden C;
  _∙_ = λ f g → _∙_ C g f; 
  idl  = idr C;
  idr  = idl C;
  ass  = sym (ass C)}
