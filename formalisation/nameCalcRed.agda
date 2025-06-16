module nameCalcRed where
open import calc

-- corresponds to ->_{β_n} in Santo paper
infix 2 _↝βₙ_

data _↝βₙ_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  βₙ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
      --------------------
    → (ƛ N) · W ↝βₙ N [ W ]

  μ : ∀ {Γ A B} {M M' : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}  
    → M ↝βₙ M'
      -------------
    → M · N ↝βₙ M' · N

  ν< : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N N' : Γ ⊢ A}  
    → Value M
    → N ↝βₙ N'
      -------------
    → M · N ↝βₙ M · N'
  
  ν : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N N' : Γ ⊢ A}  
    → N ↝βₙ N'
      -------------
    → M · N ↝βₙ M · N'

  ξ : ∀ {Γ A B} {M M' : Γ , A ⊢ B}
    → M ↝βₙ M'
      --------------------
    → ƛ M ↝βₙ ƛ M'

infix  2 _↝βₙ*_
infix  1 beginβₙ_
infixr 2 _↝βₙ⟨_⟩_
infix  3 _∎βₙ

data _↝βₙ*_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎βₙ : (M : Γ ⊢ A)
      ------
    → M ↝βₙ* M

  stepβₙ↝ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → M ↝βₙ* N
    → L ↝βₙ M
      ------
    → L ↝βₙ* N

pattern _↝βₙ⟨_⟩_ L L↝βₙM M↝βₙ*N = stepβₙ↝ L M↝βₙ*N L↝βₙM

beginβₙ_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ↝βₙ* N
    ------
  → M ↝βₙ* N
beginβₙ_ M↝βₙ*N = M↝βₙ*N


-- corresponds to →ₙ in Santo paper
infix 2 _↝ₙ_

data _↝ₙ_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  βₙ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
      --------------------
    → (ƛ N) · W ↝ₙ N [ W ]

  μ : ∀ {Γ A B} {M M' : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}  
    → M ↝ₙ M'
      -------------
    → M · N ↝ₙ M' · N


infix  2 _↝ₙ*_
infix  1 begincbn_
infixr 2 _↝ₙ⟨_⟩_
infix  3 _∎cbn


data _↝ₙ*_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎cbn : (M : Γ ⊢ A)
      ------
    → M ↝ₙ* M

  step↝ₙ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → M ↝ₙ* N
    → L ↝ₙ M
      ------
    → L ↝ₙ* N

pattern _↝ₙ⟨_⟩_ L L↝ₙM M↝ₙ*N = step↝ₙ L M↝ₙ*N L↝ₙM

begincbn_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ↝ₙ* N
    ------
  → M ↝ₙ* N
begincbn_ M↝ₙ*N = M↝ₙ*N
