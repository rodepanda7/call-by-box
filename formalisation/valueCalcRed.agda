module valueCalcRed where
open import calc


-- corresponds to ->_{β_v} in Santo paper
infix 2 _↝βᵥ_

data _↝βᵥ_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  βᵥ : ∀ {Γ A B} {M : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      --------------------
    → (ƛ M) · W ↝βᵥ M [ W ]

  μ : ∀ {Γ A B} {M M' : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}  
    → M ↝βᵥ M'
      -------------
    → M · N ↝βᵥ M' · N

  ν< : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N N' : Γ ⊢ A}  
    → Value M
    → N ↝βᵥ N'
      -------------
    → M · N ↝βᵥ M · N'
  
  ν : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N N' : Γ ⊢ A}  
    → N ↝βᵥ N'
      -------------
    → M · N ↝βᵥ M · N'

  ξ : ∀ {Γ A B} {M M' : Γ , A ⊢ B}
    → M ↝βᵥ M'
      --------------------
    → ƛ M ↝βᵥ ƛ M'

infix  2 _↝βᵥ*_
infix  1 beginβᵥ_
infixr 2 _↝βᵥ⟨_⟩_
infix  3 _∎βᵥ

data _↝βᵥ*_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎βᵥ : (M : Γ ⊢ A)
      ------
    → M ↝βᵥ* M

  stepβᵥ↝ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → M ↝βᵥ* N
    → L ↝βᵥ M
      ------
    → L ↝βᵥ* N

pattern _↝βᵥ⟨_⟩_ L L↝βᵥM M↝βᵥ*N = stepβᵥ↝ L M↝βᵥ*N L↝βᵥM

beginβᵥ_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ↝βᵥ* N
    ------
  → M ↝βᵥ* N
beginβᵥ_ M↝βᵥ*N = M↝βᵥ*N


-- corresponds to →ᵥ in Santo paper
infix 2 _↝ᵥ_

data _↝ᵥ_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  βᵥ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      --------------------
    → (ƛ N) · W ↝ᵥ N [ W ]

  μ : ∀ {Γ A B} {M M' : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}  
    → M ↝ᵥ M'
      -------------
    → M · N ↝ᵥ M' · N

  ν< : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N N' : Γ ⊢ A}  
    → Value M
    → N ↝ᵥ N'
      -------------
    → M · N ↝ᵥ M · N'


infix  2 _↝ᵥ*_
infix  1 begincbv_
infixr 2 _↝ᵥ⟨_⟩_
infix  3 _∎cbv


data _↝ᵥ*_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎cbv : (M : Γ ⊢ A)
      ------
    → M ↝ᵥ* M

  step↝ᵥ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → M ↝ᵥ* N
    → L ↝ᵥ M
      ------
    → L ↝ᵥ* N

pattern _↝ᵥ⟨_⟩_ L L↝ᵥM M↝ᵥ*N = step↝ᵥ L M↝ᵥ*N L↝ᵥM

begincbv_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ↝ᵥ* N
    ------
  → M ↝ᵥ* N
begincbv_ M↝ᵥ*N = M↝ᵥ*N
