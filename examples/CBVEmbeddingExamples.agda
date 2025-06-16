module CBVEmbeddingExamples where

open import boxCalc
open import calc
open import embedCBVIntoCBB

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

t1 : ∅ , X ⊢ X
t1 = ƛ (` Z) · ` Z

t2 : ∅b ,b □ X ⊢b BOX X
t2 = (raise ·b box (ε Zb) ) ·b box (ƛb (box (ε Zb)))

t3 : ∅b ,b □ X ⊢b BOX X
t3 = box (ε Zb)

_ : embedTerm t1 ≡ t2
_ = refl

_ : t2 ↝b* t3
_ =
  beginb
    (ƛb (ƛb (ε Zb ·b box (ε (Sb Zb)))) ·b box (ε Zb) ) ·b box (ƛb (box (ε Zb)))
  ↝b⟨ μ βb ⟩
    ƛb (ε Zb ·b box (ε (Sb Zb))) ·b box (ƛb (box (ε Zb)))
  ↝b⟨ βb ⟩
    ƛb (box (ε Zb)) ·b box (ε Zb)
  ↝b⟨ βb ⟩
    box (ε Zb)
  ∎b