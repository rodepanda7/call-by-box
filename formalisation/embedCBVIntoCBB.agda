module embedCBVIntoCBB where

open import boxCalc
open import calc

open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym)

embedTypeValue : Type → Typeb
embedTypeValue (A ⇒ B) = □ (embedTypeValue A) ⇒b BOX (embedTypeValue B)
embedTypeValue X = X

embedType : Type → Typeb
embedType x = BOX (embedTypeValue x)

embedContext : Context → Contextb
embedContext ∅ = ∅b
embedContext (Γ , A) = (embedContext Γ) ,b □ (embedTypeValue A)

embedLookup : ∀ {Γ A} → A ∈ Γ → □ (embedTypeValue A) ∈b embedContext Γ
embedLookup Z = Zb
embedLookup (S x) = Sb (embedLookup x)

raise : ∀ {Γ A B} 
  → (t : Γ ⊢b BOX B) 
  → Γ ⊢b □ (□ B ⇒b BOX A) ⇒b BOX A
raise t = ƛb (ε Zb ·b renameb Sb t)

embedValue : ∀ {Γ A} (V : Γ ⊢ A) → (x : Value V) → embedContext Γ ⊢b embedTypeValue A
embedTerm : ∀ {Γ A} → Γ ⊢ A → embedContext Γ ⊢b embedType A
  
--embedValue : ∀ {Γ A} (V : Γ ⊢ A) → Value V → embedContext Γ ⊢b embedTypeValue A
embedValue (` x₁) x = ε (embedLookup x₁)
embedValue (ƛ V) x = ƛb (embedTerm V)

--embedTerm : ∀ {Γ A} → Γ ⊢ A → embedContext Γ ⊢b embedType A
embedTerm (` x) = box (embedValue (` x) V-`)
embedTerm (ƛ M) = box (embedValue (ƛ M) V-ƛ)
embedTerm (M · N) = raise (embedTerm N) ·b embedTerm M
