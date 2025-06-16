module test where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open Eq.≡-Reasoning renaming (begin_ to beginEq_; _∎ to _∎eq)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import boxCalc
open import calc

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  beginEq
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎eq
+-assoc (suc m) n p =
  beginEq
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎eq

e1 : ∅ , X ⇒ X ⊢ X ⇒ X
e1 = ƛ (` (S Z) · ` Z)

e2 : ∅ ⊢ X ⇒ X
e2 = ƛ (` Z)

_ : e1 [ e2 ] ≡ ƛ (ƛ (` Z) · ` Z)
_ = refl

