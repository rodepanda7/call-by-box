module embedCBNIntoCBB where

open import boxCalc
open import calc

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

embedType : Type → Typeb
embedType (C ⇒ D) = □ (embedType C) ⇒b embedType D
embedType X = X

embedContext : Context → Contextb
embedContext ∅ = ∅b
embedContext (M , N) = embedContext M ,b □ (embedType N)

embedLookup : ∀ {Γ A} → A ∈ Γ → □ (embedType A) ∈b embedContext Γ
embedLookup Z = Zb
embedLookup (S x) = Sb (embedLookup x)

embedTerm : ∀ {Γ A} → Γ ⊢ A → embedContext Γ ⊢b embedType A
embedTerm (` x) = ε (embedLookup x)
embedTerm (ƛ x) = ƛb (embedTerm x)
embedTerm (M · N) = embedTerm M ·b box (embedTerm N) 
