module boxExamples where

open import boxCalc
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

-- EXAMPLE TERMS

_ : ∅b ,b □ X ⊢b X
_ = ε Zb

_ : ∅b ⊢b □ X ⇒b X
_ = ƛb (ε Zb) 
-- λx. ε(x)

_ : ∅b ,b □ X ⊢b X
_ = ƛb (ε Zb) ·b box (ε Zb)
-- (λx . ε(x)) box(ε y)

M0 : ∅b ,b □ (□ X ⇒b X) ⊢b □ X ⇒b X
M0 = ƛb (ε (Sb Zb) ·b box (ε (Sb Zb) ·b box (ε Zb)))

M1 : ∅b ,b □ (□ X ⇒b X) ,b □ X ⊢b □ X ⇒b X
M1 = ƛb (ε (Sb (Sb Zb)) ·b box (ε (Sb (Sb Zb)) ·b box (ε Zb)))


_ : rename Sb M0 ≡ M1
_ = refl


M2 : ∅b ,b □ (□ X ⇒b X) ⊢b □ X ⇒b X
M2 = ƛb (ε (Sb Zb) ·b box (ε (Sb Zb) ·b box (ε Zb)))

M3 : ∅b ⊢b □ X ⇒b X
M3 = ƛb (ε Zb)

M4 : ∅b ⊢b □ X ⇒b X
M4 = ƛb (ƛb (ε Zb) ·b box (ƛb (ε Zb) ·b box (ε Zb)))

_ : M2 [ M3 ]b ≡ M4
_ = refl

