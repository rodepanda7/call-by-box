module boxCalc where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

infix  4 _⊢b_
infix  4 _∈b_
infixl 5 _,b_

infixr 7 _⇒b_

infix  5 ƛb
infixl 7 _·b_
infix  9 ε
infix  9 box

data Typeb : Set
data BoxedTypeb : Set

-- SPECIFICATION BOX LAMBDA CALCULUS

data Typeb where
  _⇒b_ : BoxedTypeb → Typeb → Typeb
  X  : Typeb
  Box : BoxedTypeb → Typeb

data BoxedTypeb where
  □ : Typeb → BoxedTypeb

BOX : Typeb → Typeb
BOX A = Box (□ A)

data Contextb : Set where
  ∅b   : Contextb
  _,b_ : Contextb → BoxedTypeb → Contextb

data _∈b_ : BoxedTypeb → Contextb → Set where
  Zb : ∀ {Γ □A} → □A ∈b (Γ ,b □A)
  Sb : ∀ {Γ □A □B} → □A ∈b Γ → □A ∈b (Γ ,b □B)

data _⊢b_ : Contextb → Typeb → Set where
  ε : ∀ {Γ A}
    → □ A ∈b Γ
      ------- 
    → Γ ⊢b A

  box : ∀ {Γ A} 
    → Γ ⊢b A 
    -------------
    → Γ ⊢b BOX A

  ƛb : ∀ {Γ A B} 
    → Γ ,b □ A ⊢b B 
      --------------
    → Γ ⊢b □ A ⇒b B

  _·b_ : ∀ {Γ A B} 
    → Γ ⊢b □ A ⇒b B 
    → Γ ⊢b BOX A 
      --------------
    → Γ ⊢b B


-- DEFINE SUBSTITUTION

extb : ∀ {Γ Δ}
  → (∀ {A} → A ∈b Γ → A ∈b Δ)
    -----------------------
  → (∀ {A B} → A ∈b Γ ,b B → A ∈b Δ ,b B)
extb f Zb = Zb
extb f (Sb x) = Sb (f x)

renameb : ∀ {Γ Δ}
  → (∀ {A} → A ∈b Γ → A ∈b Δ)
    -----------------------
  → (∀ {A} → Γ ⊢b A → Δ ⊢b A)
renameb f (ε x) = ε (f x)
renameb f (box N) = box (renameb f N)
renameb f (ƛb M) = ƛb (renameb (extb f) M)
renameb f (M ·b N) = renameb f M ·b (renameb f N)

extsb : ∀ {Γ Δ}
  → (∀ {A} → □ A ∈b Γ → Δ ⊢b A)
    -----------------------
  → (∀ {A B} → □ A ∈b Γ ,b B → Δ ,b B ⊢b A)
extsb f Zb = ε Zb
extsb f (Sb x) = renameb Sb ( f x )

substb : ∀ {Γ Δ}
  → (∀ {A} → □ A ∈b Γ → Δ ⊢b A)
    -------------------------
  → (∀ {A} → Γ ⊢b A → Δ ⊢b A)
substb f (ε x) = f x
substb f (box N) = box (substb f N)
substb f (ƛb M) = ƛb (substb (extsb f) M)
substb f (M ·b N) = substb f M ·b (substb f N) 

fb : ∀ {Γ C} (M : Γ ⊢b C) → ∀ {A} → □ A ∈b Γ ,b □ C → Γ ⊢b A
fb M Zb = M
fb M (Sb x) = ε x

_[_]b : ∀ {Γ A C}
  → Γ ,b □ C ⊢b A
  → Γ ⊢b C
    -------------
  → Γ ⊢b A
_[_]b N M = substb (fb M) N


-- REDUCTION

data Valueb : ∀ {Γ A} → Γ ⊢b A → Set where

  V-ƛb : ∀ {Γ A B} {N : Γ ,b □ A ⊢b B}
      ---------------------------
    → Valueb (ƛb N)

  V-ε : ∀ {Γ A} {x : □ A ∈b Γ}
      -----------------
    → Valueb (ε x)
