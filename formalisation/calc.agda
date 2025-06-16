module calc where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

infix  4 _⊢_
infix  4 _∈_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ
infixl 7 _·_

-- -- SPECIFICATION LAMBDA CALCULUS

data Type : Set where
  _⇒_ : Type → Type → Type
  X  : Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∈_ : Type → Context → Set where
  Z : ∀ {Γ A} → A ∈ (Γ , A)
  S : ∀ {Γ A B} → A ∈ Γ → A ∈ (Γ , B)

data _⊢_ : Context → Type → Set where
  ` : ∀ {Γ A}
    → A ∈ Γ
      ------- 
    → Γ ⊢ A

  ƛ : ∀ {Γ A B} 
    → Γ , A ⊢ B 
      --------------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B} 
    → Γ ⊢ A ⇒ B 
    → Γ ⊢ A 
      --------------
    → Γ ⊢ B


-- -- DEFINE SUBSTITUTION

ext : ∀ {Γ Δ}
  → (∀ {A} → A ∈ Γ → A ∈ Δ)
    -----------------------
  → (∀ {A B} → A ∈ Γ , B → A ∈ Δ , B)
ext f Z = Z
ext f (S x) = S (f x)

rename : ∀ {Γ Δ}
  → (∀ {A} → A ∈ Γ → A ∈ Δ)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename f (` x) = ` (f x)
rename f (ƛ M) = ƛ (rename (ext f) M)
rename f (M · N) = rename f M · (rename f N)

exts : ∀ {Γ Δ}
  → (∀ {A} → A ∈ Γ → Δ ⊢ A)
    -----------------------
  → (∀ {A B} → A ∈ Γ , B → Δ , B ⊢ A)
exts f Z = ` Z
exts f (S x) = rename S ( f x )

subst : ∀ {Γ Δ}
  → (∀ {A} → A ∈ Γ → Δ ⊢ A)
    -------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst f (` x) = f x
subst f (ƛ M) = ƛ (subst (exts f) M)
subst f (M · N) = subst f M · (subst f N) 

f : ∀ {Γ C} (M : Γ ⊢ C) → ∀ {A} → A ∈ Γ , C → Γ ⊢ A
f M Z = M
f M (S x) = ` x

_[_] : ∀ {Γ A C}
  → Γ , C ⊢ A
  → Γ ⊢ C
    -------------
  → Γ ⊢ A
_[_] {Γ} {A} {C} N M = subst (f M) N


data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-` : ∀ {Γ A} {x : A ∈ Γ}
      ---------------------------
    → Value (` x) 

infix 2 _↝_

data _↝_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  β : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
      --------------------
    → (ƛ N) · W ↝ N [ W ]

  μ : ∀ {Γ A B} {M M' : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}  
    → M ↝ M'
      -------------
    → M · N ↝ M' · N

  ν< : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N N' : Γ ⊢ A}  
    → Value M
    → N ↝ N'
      -------------
    → M · N ↝ M · N'
  
  ν : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N N' : Γ ⊢ A}  
    → N ↝ N'
      -------------
    → M · N ↝ M · N'

  ξ : ∀ {Γ A B} {M M' : Γ , A ⊢ B}
    → M ↝ M'
      --------------------
    → ƛ M ↝ ƛ M'

infix  1 begin_
infixr 2 _↝⟨_⟩_
infix  3 _∎

data _↝*_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A)
      ------
    → M ↝* M

  step↝ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → M ↝* N
    → L ↝ M
      ------
    → L ↝* N

pattern _↝⟨_⟩_ L L↝M M↝*N = step↝ L M↝*N L↝M

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ↝* N
    ------
  → M ↝* N
begin_ M↝*N = M↝*N