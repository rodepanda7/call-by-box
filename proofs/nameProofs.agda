module nameProofs where

open import boxCalc
open import calc
open import embedCBNIntoCBB
open import nameCalcRed
open import boxCalcRed

open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym)

open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open Eq.≡-Reasoning renaming (begin_ to beginEq_; _∎ to _∎eq)
open import Function.Bundles using (_⇔_; mk⇔)

-- GIRARD'S embedding

-- Preservation of typing by Girard's translation
pres-typing : ∀ {Γ A} → Γ ⊢ A → embedContext Γ ⊢b embedType A
pres-typing x = embedTerm x

-- Preservation and Reflection of 
-- ext of Girard's translation
pres-ext : ∀ {Γ Δ A' A} 
  → (f' : ∀ {A} → A ∈ Γ → A ∈ Δ)
  → (fb' : ∀ {Ab} → Ab ∈b embedContext Γ → Ab ∈b embedContext Δ)
  → ({A' : Type} (x : A' ∈ Γ) → fb' (embedLookup x) ≡ embedLookup (f' x))
  → (x : A' ∈ Γ , A)
  → extb fb' (embedLookup x) ≡ embedLookup (ext f' x)
pres-ext f' fb' h Z = refl
pres-ext f' fb' h (S x) = cong Sb (h x)

-- Preservation and Reflection of 
-- rename of Girard's translation
pres-rename : ∀ {Γ A Δ} 
  → (f' : ∀ {A} → A ∈ Γ → A ∈ Δ)
  → (fb' : ∀ {Ab} → Ab ∈b embedContext Γ → Ab ∈b embedContext Δ)
  → ({A' : Type} (x : A' ∈ Γ) → fb' (embedLookup x) ≡ embedLookup (f' x))
  → (t : Γ ⊢ A) 
  → renameb fb' (embedTerm t) ≡ embedTerm (rename f' t)
pres-rename f' fb' h (` x) = 
  cong ε (h x)
pres-rename f' fb' h (ƛ t) = 
  cong ƛb (pres-rename (calc.ext f') (extb fb') (pres-ext f' fb' h) t)
pres-rename f' fb' h (t · t₁) = 
  cong₂ _·b_ (pres-rename f' fb' h t) (cong box (pres-rename f' fb' h t₁))

-- Preservation and Reflection of 
-- exts of Girard's translation
pres-exts : ∀ {Γ Δ} 
  → (fb' : ∀ {Ab} → □ Ab ∈b embedContext Γ → embedContext Δ ⊢b Ab)
  → (f' : ∀ {A} → A ∈ Γ → Δ ⊢ A)
  → ({A' : Type} (x : A' ∈ Γ) → fb' (embedLookup x) ≡ embedTerm (f' x))
  → {A' A : Type} (x : A' ∈ Γ , A) → extsb fb' (embedLookup x) ≡ embedTerm (exts f' x)
pres-exts fb' f' h Z = refl
pres-exts fb' f' h (S x) =
  beginEq
    renameb Sb (fb' (embedLookup x))
  ≡⟨ cong (renameb Sb) (h x) ⟩
    renameb Sb (embedTerm (f' x))
  ≡⟨ pres-rename S Sb (λ x₁ → refl) (f' x) ⟩
    embedTerm (rename S (f' x))
  ∎eq

-- Preservation and Reflection of 
-- simultaneous substitution of Girard's translation
pres-simultaneous-subst : ∀ {Γ Δ A}
  → (fb' : ∀ {Ab} → □ Ab ∈b embedContext Γ → embedContext Δ ⊢b Ab)
  → (f' : ∀ {A} → A ∈ Γ → Δ ⊢ A)
  → (h : ∀ {A'} → (x : A' ∈ Γ) → fb' (embedLookup x) ≡ embedTerm (f' x) )
  → (M : Γ ⊢ A) 
  → substb fb' (embedTerm M) ≡ embedTerm (subst f' M)
pres-simultaneous-subst fb' f' h (` x) = 
  h x
pres-simultaneous-subst fb' f' h (ƛ M) = 
  cong ƛb ( pres-simultaneous-subst (extsb fb') (exts f') (pres-exts fb' f' h) M )
pres-simultaneous-subst fb' f' h (M · M₁) = 
  cong₂ _·b_ (pres-simultaneous-subst fb' f' h M) (cong box (pres-simultaneous-subst fb' f' h M₁))


-- Lemma for assumption h in lemma
-- pres-simultaneous-subst
pres-subst-func : ∀ {A C Γ}
  → (N : Γ ⊢ C)
  → (x : A ∈ Γ , C)
  → fb (embedTerm N) (embedLookup x) ≡ embedTerm ((f N) x)
pres-subst-func N Z = refl
pres-subst-func N (S x) = refl

-- Preservation and Reflection of 
-- single substitution of Girard's translation
pres-subst : ∀ {Γ A B} (M : Γ , B ⊢ A) → (N : Γ ⊢ B) → (embedTerm M) [ embedTerm N ]b ≡ embedTerm (M [ N ])
pres-subst M N = pres-simultaneous-subst (fb (embedTerm N)) (f N) (pres-subst-func N) M

-- Preservation of reduction of Girard's translation
pres-red : ∀ {Γ A} 
  → (M : Γ ⊢ A) 
  → (N : Γ ⊢ A) 
  → (M ↝βₙ N) 
  → (embedTerm M ↝βb embedTerm N)
pres-red (ƛ M₁ · M₂) N βₙ = 
  Eq.subst (λ t → ƛb (embedTerm M₁) ·b box (embedTerm M₂) ↝βb t) 
  (pres-subst M₁ M₂) 
  βb
pres-red M N (μ {M = M₁} {M' = M'} red) = 
  μ (pres-red M₁ M' red)
pres-red M N (ν< {M = M₁} {N = N₁} {N' = N'} x red) = 
  ν (ζ (pres-red N₁ N' red))
pres-red M N (ν {M = M₁} {N = N₁} {N' = N'} red) = 
  ν (ζ (pres-red N₁ N' red))
pres-red M N (ξ {M = M₁} {M' = M'} red) = 
  ξ (pres-red M₁ M' red)

-- Preservation of evaluation of Girard's translation
pres-eval : ∀ {Γ A} 
  → (M : Γ ⊢ A) 
  → (N : Γ ⊢ A) 
  → (M ↝ₙ N) 
  → (embedTerm M ↝bₙ embedTerm N)
pres-eval (ƛ M₁ · M₂) N βₙ = 
  Eq.subst 
    (λ t → ƛb (embedTerm M₁) ·b box (embedTerm M₂) ↝bₙ t) 
    (pres-subst M₁ M₂) 
    βb
pres-eval M N (μ {M = M₁} {M' = M'} red) = 
  μ (pres-eval M₁ M' red)
