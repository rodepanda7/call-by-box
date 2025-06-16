module calcExamples where

open import calc
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)


-- -- EXAMPLE TERMS

_ : ∅ , X ⊢ X
_ = ` Z
-- same as x

_ : ∅ ⊢ X ⇒ X
_ = ƛ (` Z) 
-- same as λx.x

_ : ∅ , X ⊢ X
_ = ƛ (` Z) · ` Z
-- same as (λx.x) y

M0 : ∅ , X ⇒ X ⊢ X ⇒ X
M0 = ƛ (` (S Z) · (` (S Z) · ` Z))
-- same as λx.y(yx)

M1 : ∅ , X ⇒ X , X ⊢ X ⇒ X
M1 = ƛ (` (S (S Z)) · (` (S (S Z)) · ` Z))
-- same as λx.y(yx), but with a different context

_ : rename S M0 ≡ M1
_ = refl --schrijf ook alles uit

-- _ : rename (S {□B = □ X}) M0 ≡ M1
-- _ = refl

M2 : ∅ , X ⇒ X ⊢ X ⇒ X
M2 = ƛ (` (S Z) · (` (S Z) · ` Z))

M3 : ∅ ⊢ X ⇒ X
M3 = ƛ (` Z)

M4 : ∅ ⊢ X ⇒ X
M4 = ƛ (ƛ (` Z) · (ƛ (` Z) · ` Z))

_ : M2 [ M3 ] ≡ M4 
_ = refl


term1 : ∅ , X ⊢ _
term1 = ƛ (` Z) · ` Z

term2 : ∅ , X ⊢ _
term2 = ` Z

-- _ : term1 ↝* term2
-- _ = 
--   begin
--     ƛ (` Z) · (` Z)
--   ↝⟨ β-ƛ ⟩
--     ` Z
--   ∎

x : ∅ , X , X ⊢ X
x = ` (S Z)

x' : ∅ , X ⊢ X
x' = ` Z

_ : ∀ {N} → x [ N ] ≡ x'
_ = refl

fun : ∅ , X ⇒ X ⊢ X ⇒ X
fun = ƛ (` Z)

