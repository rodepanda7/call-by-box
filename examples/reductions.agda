module reductions where

open import boxCalc
open import calc
open import nameCalcRed
open import valueCalcRed

I : ∀ {Γ A} → Γ ⊢ A ⇒ A
I = ƛ (` Z)

t1 : ∀ {A} → ∅ ⊢ A ⇒ A
t1 = (I · I) · (I · I)

t2 : ∀ {A} → ∅ ⊢ A ⇒ A
t2 = I · (I · I)

_ : t1 {X} ↝* t2
_ = 
  begin
    (I · I) · (I · I)
  ↝⟨ μ β ⟩
    I · (I · I)
  ∎


t3 : ∀ {A} → ∅ ⊢ A ⇒ A
t3 = (I · I) · I

_ : t1 {X} ↝* t3
_ = 
  begin
    (I · I) · (I · I)
  ↝⟨ ν β ⟩
    (I · I) · I
  ∎


t4 : ∀ {A} → ∅ ⊢ A ⇒ A
t4 = ƛ (I · ` Z)

_ : t4 {X} ↝* I
_ = 
  begin
    ƛ (I · ` Z)
  ↝⟨ ξ β ⟩
    I
  ∎


t5 : ∀ {A} → ∅ ⊢ A ⇒ A
t5 = (I · (ƛ (I · ` Z))) · (I · I) 

_ : t5 {X} ↝* I
_ = 
  begin
    (I · (ƛ (I · ` Z))) · (I · I) 
  ↝⟨ μ (ν (ξ β)) ⟩
    (I · I) · (I · I)
  ↝⟨ ν β ⟩
    I · I · I
  ↝⟨ μ β ⟩
    I · I
  ↝⟨ β ⟩
    I
  ∎


-- Example cbn evaluation

_ : t5 {X} ↝ₙ* I
_ =
  begincbn
    (I · (ƛ (I · ` Z))) · (I · I)
  ↝ₙ⟨ μ βₙ ⟩
    (ƛ (I · ` Z)) · (I · I)
  ↝ₙ⟨ βₙ ⟩
    I · (I · I)
  ↝ₙ⟨ βₙ ⟩
    I · I
  ↝ₙ⟨ βₙ ⟩
    I
  ∎cbn


-- Example cbv evaluation

_ : t5 {X} ↝ᵥ* I
_ =   
  begincbv
    (I · (ƛ (I · ` Z))) · (I · I)
  ↝ᵥ⟨ μ (βᵥ V-ƛ) ⟩
    (ƛ (I · ` Z)) · (I · I)
  ↝ᵥ⟨ ν< V-ƛ (βᵥ V-ƛ) ⟩
    (ƛ (I · ` Z)) · I
  ↝ᵥ⟨ βᵥ V-ƛ ⟩
    I · I
  ↝ᵥ⟨ βᵥ V-ƛ ⟩
    I
  ∎cbv


-- Example simple lambda box reduction

t6 : ∅b ,b □ X ⊢b _
t6 = ƛb (ε Zb) ·b box (ε Zb)

t7 : ∅b ,b □ X ⊢b _
t7 = ε Zb

_ : t6 ↝b* t7
_ = 
  beginb
    ƛb (ε Zb) ·b box (ε Zb)
  ↝b⟨ β-ƛb ⟩
    ε Zb
  ∎b