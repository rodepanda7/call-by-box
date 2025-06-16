module CBNEmbeddingExamples where

open import boxCalc
open import calc
open import embedCBNIntoCBB

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

t1 : ∅ , X ⊢ X
t1 = ƛ (` Z) · ` Z

t2 : ∅b ,b □ X ⊢b X
t2 = ƛb (ε Zb) ·b box (ε Zb)

t3 : ∅b ,b □ X ⊢b X
t3 = ε Zb

_ : embedTerm t1 ≡ t2
_ = refl

_ : t2 ↝b* t3
_ = 
  beginb
    ƛb (ε Zb) ·b box (ε Zb)
  ↝b⟨ βb ⟩
    ε Zb
  ∎b