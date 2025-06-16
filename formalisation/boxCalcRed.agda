module boxCalcRed where

open import boxCalc
open import embedCBVIntoCBB

-- Standard reduction for boxed Lambda calculus
infix 2 _↝βb_

data _↝βb_ : ∀ {Γ A} → (Γ ⊢b A) → (Γ ⊢b A) → Set where

  βb : ∀ {Γ A B} {M : Γ ,b □ A ⊢b B} {W : Γ ⊢b A}
      --------------------
    → (ƛb M) ·b box W ↝βb M [ W ]b

  μ : ∀ {Γ A B} {M M' : Γ ⊢b □ A ⇒b B} {N : Γ ⊢b BOX A}  
    → M ↝βb M'
      -------------
    → M ·b N ↝βb M' ·b N

  ν : ∀ {Γ A B} {M : Γ ⊢b □ A ⇒b B} {N N' : Γ ⊢b BOX A} -- hier BOX weggehaald 
    → N ↝βb N'
      -------------
    → M ·b N ↝βb M ·b N' -- heb box voor N en N' gezet

  ξ : ∀ {Γ A B} {M M' : Γ ,b □ A ⊢b B}
    → M ↝βb M'
      -----------------
    → (ƛb M) ↝βb (ƛb M')

  ζ : ∀ {Γ A} {M M' : Γ ⊢b A}
    → M ↝βb M'
      ------------------
    → box M ↝βb box M'

infix  1 beginβb_
infixr 2 _↝βb⟨_⟩_
infix  3 _∎βb

data _↝βb*_ {Γ A} : (Γ ⊢b A) → (Γ ⊢b A) → Set where

  _∎βb : (M : Γ ⊢b A)
      ------
    → M ↝βb* M

  stepβb↝ : (L : Γ ⊢b A) {M N : Γ ⊢b A}
    → M ↝βb* N
    → L ↝βb M
      ------
    → L ↝βb* N

pattern _↝βb⟨_⟩_ L L↝βbM M↝βb*N = stepβb↝ L M↝βb*N L↝βbM

beginβb_ : ∀ {Γ A} {M N : Γ ⊢b A}
  → M ↝βb* N
    ------
  → M ↝βb* N
beginβb M↝βb*N = M↝βb*N


-- Call-by-name reduction on the boxed Lambda calculus
infix 2 _↝bₙ_

data _↝bₙ_ : ∀ {Γ A} → (Γ ⊢b A) → (Γ ⊢b A) → Set where

  βb : ∀ {Γ A B} {M : Γ ,b □ A ⊢b B} {W : Γ ⊢b A}
      --------------------
    → (ƛb M) ·b box W ↝bₙ M [ W ]b

  μ : ∀ {Γ A B} {M M' : Γ ⊢b □ A ⇒b B} {N : Γ ⊢b BOX A}  
    → M ↝bₙ M'
      -------------
    → M ·b N ↝bₙ M' ·b N

infix  1 beginbₙ_
infixr 2 _↝bₙ⟨_⟩_
infix  3 _∎bₙ

data _↝bₙ*_ {Γ A} : (Γ ⊢b A) → (Γ ⊢b A) → Set where

  _∎bₙ : (M : Γ ⊢b A)
      ------
    → M ↝bₙ* M

  stepbₙ↝ : (L : Γ ⊢b A) {M N : Γ ⊢b A}
    → M ↝bₙ* N
    → L ↝bₙ M
      ------
    → L ↝bₙ* N

pattern _↝bₙ⟨_⟩_ L L↝bₙM M↝bₙ*N = stepbₙ↝ L M↝bₙ*N L↝bₙM

beginbₙ_ : ∀ {Γ A} {M N : Γ ⊢b A}
  → M ↝bₙ* N
    ------
  → M ↝bₙ* N
beginbₙ M↝bₙ*N = M↝bₙ*N


-- Standard reduction for boxed Lambda calculus with 2 steps
infix 2 _↝βb²_

data _↝βb²_ : ∀ {Γ A} → (Γ ⊢b A) → (Γ ⊢b A) → Set where

  βb² : ∀ {Γ A}
    → (t₁ t₂ t₃ : Γ ⊢b A)
    → (t₁ ↝βb t₂) 
    → (t₂ ↝βb t₃)
    -----------------
    → t₁ ↝βb² t₃

  μ : ∀ {Γ A B} {M M' : Γ ⊢b □ A ⇒b B} {N : Γ ⊢b BOX A}  
    → M ↝βb² M'
      -------------
    → M ·b N ↝βb² M' ·b N

  ν : ∀ {Γ A B} {M : Γ ⊢b □ A ⇒b B} {N N' : Γ ⊢b BOX A}
    → N ↝βb² N'
      -------------
    → M ·b N ↝βb² M ·b N' 

  ξ : ∀ {Γ A B} {M M' : Γ ,b □ A ⊢b B}
    → M ↝βb² M'
      -----------------
    → (ƛb M) ↝βb² (ƛb M')

  ζ : ∀ {Γ A} {M M' : Γ ⊢b A}
    → M ↝βb² M'
      ------------------
    → box M ↝βb² box M'

infix  1 beginβb²_
infixr 2 _↝βb²⟨_⟩_
infix  3 _∎βb²

data _↝βb²*_ {Γ A} : (Γ ⊢b A) → (Γ ⊢b A) → Set where

  _∎βb² : (M : Γ ⊢b A)
      ------
    → M ↝βb²* M

  stepβb²↝ : (L : Γ ⊢b A) {M N : Γ ⊢b A}
    → M ↝βb²* N
    → L ↝βb² M
      ------
    → L ↝βb²* N

pattern _↝βb²⟨_⟩_ L L↝βb²M M↝βb²*N = stepβb²↝ L M↝βb²*N L↝βb²M

beginβb²_ : ∀ {Γ A} {M N : Γ ⊢b A}
  → M ↝βb²* N
    ------
  → M ↝βb²* N
beginβb² M↝βb²*N = M↝βb²*N


-- New β rule to make two seperate reduction steps one
infix 2 _↝βb₂_

data _↝βb₂_ : ∀ {Γ A} → (Γ ⊢b A) → (Γ ⊢b A) → Set where

  βb₂ : ∀ {Γ A B} {M : Γ ,b □ A ⊢b BOX B} {W : Γ ⊢b A}
      --------------------
    → raise (box W) ·b (box (ƛb M)) ↝βb₂ M [ W ]b

  μ : ∀ {Γ A B} {M M' : Γ ⊢b □ A ⇒b B} {N : Γ ⊢b BOX A}  
    → M ↝βb₂ M'
      -------------
    → M ·b N ↝βb₂ M' ·b N

  ν : ∀ {Γ A B} {M : Γ ⊢b □ A ⇒b B} {N N' : Γ ⊢b BOX A}
    → N ↝βb₂ N'
      -------------
    → M ·b N ↝βb₂ M ·b N' 

  ξ : ∀ {Γ A B} {M M' : Γ ,b □ A ⊢b B}
    → M ↝βb₂ M'
      -----------------
    → (ƛb M) ↝βb₂ (ƛb M')

  ζ : ∀ {Γ A} {M M' : Γ ⊢b A}
    → M ↝βb₂ M'
      ------------------
    → box M ↝βb₂ box M'

infix  1 beginβb₂_
infixr 2 _↝βb₂⟨_⟩_
infix  3 _∎βb₂

data _↝βb₂*_ {Γ A} : (Γ ⊢b A) → (Γ ⊢b A) → Set where

  _∎βb₂ : (M : Γ ⊢b A)
      ------
    → M ↝βb₂* M

  stepβb₂↝ : (L : Γ ⊢b A) {M N : Γ ⊢b A}
    → M ↝βb₂* N
    → L ↝βb₂ M
      ------
    → L ↝βb₂* N

pattern _↝βb₂⟨_⟩_ L L↝βb₂M M↝βb₂*N = stepβb₂↝ L M↝βb₂*N L↝βb₂M

beginβb₂_ : ∀ {Γ A} {M N : Γ ⊢b A}
  → M ↝βb₂* N
    ------
  → M ↝βb₂* N
beginβb₂ M↝βb₂*N = M↝βb₂*N


-- Call-by-value reduction on the boxed Lambda calculus
infix 2 _↝bᵥ_

data _↝bᵥ_ : ∀ {Γ A} → (Γ ⊢b A) → (Γ ⊢b A) → Set where

  βb : ∀ {Γ A B} {M : Γ ,b □ A ⊢b B} {W : Γ ⊢b A}
      --------------------
    → (ƛb M) ·b box W ↝bᵥ M [ W ]b

  ν : ∀ {Γ A B} {M : Γ ⊢b □ A ⇒b B} {N N' : Γ ⊢b BOX A}
    → N ↝bᵥ N'
      -------------
    → M ·b N ↝bᵥ M ·b N' 

infix  1 beginbᵥ_
infixr 2 _↝bᵥ⟨_⟩_
infix  3 _∎bᵥ

data _↝bᵥ*_ {Γ A} : (Γ ⊢b A) → (Γ ⊢b A) → Set where

  _∎bᵥ : (M : Γ ⊢b A)
      ------
    → M ↝bᵥ* M

  stepbᵥ↝ : (L : Γ ⊢b A) {M N : Γ ⊢b A}
    → M ↝bᵥ* N
    → L ↝bᵥ M
      ------
    → L ↝bᵥ* N

pattern _↝bᵥ⟨_⟩_ L L↝bᵥM M↝bᵥ*N = stepbᵥ↝ L M↝bᵥ*N L↝bᵥM

beginbᵥ_ : ∀ {Γ A} {M N : Γ ⊢b A}
  → M ↝bᵥ* N
    ------
  → M ↝bᵥ* N
beginbᵥ M↝bᵥ*N = M↝bᵥ*N

infix  1 beginbᵥ⁺_
infixr 2 _↝bᵥ⁺⟨_⟩_
infix  3 ∎bᵥ⁺

data _↝bᵥ⁺_ {Γ A} : (Γ ⊢b A) → (Γ ⊢b A) → Set where

  ∎bᵥ⁺ : {M N : Γ ⊢b A}  
    → (M ↝bᵥ N)
      ----------
    → M ↝bᵥ⁺ N

  stepbᵥ⁺↝ : (L : Γ ⊢b A) {M N : Γ ⊢b A}
    → M ↝bᵥ⁺ N
    → L ↝bᵥ M
      ------
    → L ↝bᵥ⁺ N

pattern _↝bᵥ⁺⟨_⟩_ L L↝bᵥ⁺M M↝bᵥ⁺N = stepbᵥ⁺↝ L M↝bᵥ⁺N L↝bᵥ⁺M

beginbᵥ⁺_ : ∀ {Γ A} {M N : Γ ⊢b A}
  → M ↝bᵥ⁺ N
    ------
  → M ↝bᵥ⁺ N
beginbᵥ⁺ M↝bᵥ⁺N = M↝bᵥ⁺N