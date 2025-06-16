module valueProofs where
  
open import calc
open import boxCalc
open import embedCBVIntoCBB
open import valueCalcRed
open import boxCalcRed

open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym)

open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open Eq.≡-Reasoning renaming (begin_ to beginEq_; _∎ to _∎eq)

-- Preservation of typing by Gödel's translation
pres-typing : ∀ {Γ A} → Γ ⊢ A → embedContext Γ ⊢b embedType A
pres-typing x = embedTerm x

-- Preservation of typing of Values by Gödel's translation
pres-typing-val : ∀ {Γ A} → (V : Γ ⊢ A) → (Value V) → embedContext Γ ⊢b embedTypeValue A
pres-typing-val V x = embedValue V x

-- Helper lemma: applying embedTerm to a Value is equivalent to wrapping the result of embedValue in a box
box-embedValue : ∀ {Γ A} → {V : Γ ⊢ A} → (x : Value V) → box (embedValue V x) ≡ embedTerm V
box-embedValue V-ƛ = refl
box-embedValue V-` = refl

-- HELPER LEMMA'S SIMULTANIOUS SUBSTITUTION

-- Preservation and Reflection of 
-- ext of Gödel's translation
pres-ext : ∀ {Γ Δ A' A} 
  → (f' : ∀ {A} → A ∈ Γ → A ∈ Δ)
  → (fb' : ∀ {Ab} → Ab ∈b embedContext Γ → Ab ∈b embedContext Δ)
  → ({A' : Type} (x : A' ∈ Γ) → fb' (embedLookup x) ≡ embedLookup (f' x))
  → (x : A' ∈ Γ , A)
  → extb fb' (embedLookup x) ≡ embedLookup (ext f' x)
pres-ext f' fb' h Z = refl
pres-ext f' fb' h (S x) = cong Sb (h x)

-- Extb preserves pointwise equality 
-- of renaming functions
extb-cong : ∀ {Γ₁ Γ₂ A A'}
  → {fb' : ∀ {Ab} → Ab ∈b Γ₁ → Ab ∈b Γ₂}
  → {fb'' : ∀ {Ab} → Ab ∈b Γ₁ → Ab ∈b Γ₂}
  → (h : ∀ {Ab} → (x : Ab ∈b Γ₁) → fb' x ≡ fb'' x)
  → (x : A ∈b Γ₁ ,b □ A') 
  → extb fb' x ≡ extb fb'' x
extb-cong h Zb = refl
extb-cong h (Sb x) = cong Sb (h x)

-- Renameb preserves pointwise equality
-- of renaming functions
renameb-cong : ∀ {Γ₁ Γ₂ A}
  → {fb' : ∀ {Ab} → Ab ∈b Γ₁ → Ab ∈b Γ₂}
  → {fb'' : ∀ {Ab} → Ab ∈b Γ₁ → Ab ∈b Γ₂}
  → (h : ∀ {Ab} → (x : Ab ∈b Γ₁) → fb' x ≡ fb'' x)
  → (t : Γ₁ ⊢b A)
  → renameb fb' t ≡ renameb fb'' t
renameb-cong h (ε x) = cong ε (h x)
renameb-cong h (box t) = cong box (renameb-cong h t)
renameb-cong h (ƛb t) = cong ƛb (renameb-cong (extb-cong h) t)
renameb-cong h (t ·b t₁) = cong₂ _·b_ (renameb-cong h t) (renameb-cong h t₁)

-- extb distributes over composition:
-- Extending first with fb', then with fb'', 
-- is the same as extending once with fb'' ∘ fb'.
extb-comp : ∀ {Γ₁ Γ₂ Γ₃ A B}
  → (fb' : ∀ {Ab} → Ab ∈b Γ₁ → Ab ∈b Γ₂)
  → (fb'' : ∀ {Ab} → Ab ∈b Γ₂ → Ab ∈b Γ₃)
  → (x : A ∈b Γ₁ ,b B)
  → extb fb'' (extb fb' x) ≡ extb (λ x₁ → fb'' (fb' x₁)) x
extb-comp fb' fb'' Zb = refl
extb-comp fb' fb'' (Sb x) = refl

-- renameb distributes over composition:
-- Renaming first with fb', then with fb''
-- is the same as renaming once with fb'' ∘ fb'.
renameb-comp : ∀ {Γ₁ Γ₂ Γ₃ A}
  → (fb' : ∀ {Ab} → Ab ∈b Γ₁ → Ab ∈b Γ₂)
  → (fb'' : ∀ {Ab} → Ab ∈b Γ₂ → Ab ∈b Γ₃)
  → (t : Γ₁ ⊢b A)
  → renameb fb'' (renameb fb' t) ≡ renameb (λ x → fb'' (fb' x)) t
renameb-comp fb' fb'' (ε x) = refl
renameb-comp fb' fb'' (box t) = cong box (renameb-comp fb' fb'' t)
renameb-comp fb' fb'' (ƛb t) = 
  beginEq
    ƛb (renameb (extb fb'') (renameb (extb fb') t))
  ≡⟨ cong ƛb (renameb-comp (extb fb') (extb fb'') t) ⟩
    ƛb (renameb (λ x → extb fb'' (extb fb' x)) t)
  ≡⟨ cong ƛb (renameb-cong (extb-comp fb' fb'') t) ⟩
    ƛb (renameb (extb (λ x → fb'' (fb' x))) t)
  ∎eq
renameb-comp fb' fb'' (t ·b t₁) = cong₂ _·b_ (renameb-comp fb' fb'' t) (renameb-comp fb' fb'' t₁)

-- extb and Sb commute under renameb.
rename-extb-Sb-commute : ∀ {Γ A B Δ}
  → (fb' : ∀ {Ab} → Ab ∈b Γ → Ab ∈b Δ)
  → (t : Γ ⊢b A)
  → renameb (extb fb' {B = B}) (renameb Sb t) 
    ≡ renameb Sb (renameb fb' t)
rename-extb-Sb-commute fb' t =
  beginEq
    renameb (extb fb') (renameb Sb t) 
  ≡⟨ renameb-comp Sb (extb fb') t ⟩
    renameb (λ x → extb fb' (Sb x)) t
  ≡⟨ renameb-cong (λ x → refl) t ⟩
    renameb (λ x → Sb (fb' x)) t
  ≡⟨ sym (renameb-comp fb' Sb t) ⟩
    renameb Sb (renameb fb' t)
  ∎eq

-- Preservation and Reflection of 
-- rename of Gödel's translation
pres-rename : ∀ {Γ A Δ} 
  → (f' : ∀ {A} → A ∈ Γ → A ∈ Δ)
  → (fb' : ∀ {Ab} → Ab ∈b embedContext Γ → Ab ∈b embedContext Δ)
  → ({A' : Type} (x : A' ∈ Γ) → fb' (embedLookup x) ≡ embedLookup (f' x))
  → (t : Γ ⊢ A) 
  → renameb fb' (embedTerm t) ≡ embedTerm (rename f' t)
pres-rename f' fb' h (` x) = cong box (cong ε (h x))
pres-rename f' fb' h (ƛ t) = cong box (cong ƛb (pres-rename (calc.ext f') (boxCalc.extb fb') (pres-ext f' fb' h) t))
pres-rename f' fb' h (t · t₁) =
  beginEq
    ƛb (ε Zb ·b renameb (extb fb') (renameb Sb (embedTerm t₁))) ·b renameb fb' (embedTerm t)
  ≡⟨ cong₂ _·b_ refl (pres-rename f' fb' h t) ⟩ 
    ƛb (ε Zb ·b renameb (extb fb') (renameb Sb (embedTerm t₁))) ·b embedTerm (rename f' t)
  ≡⟨ cong₂ _·b_ (cong ƛb (cong₂ _·b_ refl (rename-extb-Sb-commute fb' (embedTerm t₁)))) refl ⟩
    ƛb (ε Zb ·b renameb Sb (renameb fb' (embedTerm t₁))) ·b embedTerm (rename f' t)
  ≡⟨ cong₂ _·b_ (cong ƛb (cong₂ _·b_ refl (cong (renameb Sb) (pres-rename f' fb' h t₁)))) refl ⟩
    ƛb (ε Zb ·b renameb Sb (embedTerm (rename f' t₁))) ·b embedTerm (rename f' t)
  ∎eq

-- Preservation and Reflection of 
-- exts of Gödel's translation
pres-exts : ∀ {Γ Δ} 
  → (fb' : ∀ {Ab} → □ Ab ∈b embedContext Γ → embedContext Δ ⊢b Ab)
  → (f' : ∀ {A} → A ∈ Γ → Δ ⊢ A)
  → ({A' : Type} (x : A' ∈ Γ) → box (fb' (embedLookup x)) ≡ embedTerm (f' x))
  → {A' A : Type} (x : A' ∈ Γ , A) → box (extsb fb' (embedLookup x)) ≡ embedTerm (exts f' x)
pres-exts fb' f' h Z = refl
pres-exts fb' f' h (S x) =
  beginEq
    box (renameb Sb (fb' (embedLookup x)))
  ≡⟨ refl ⟩
    renameb Sb (box (fb' (embedLookup x)))
  ≡⟨ cong (renameb Sb) (h x) ⟩
    renameb Sb (embedTerm (f' x))
  ≡⟨ pres-rename S Sb (λ x₁ → refl) (f' x) ⟩
    embedTerm (rename S (f' x))
  ∎eq

-- Extsb preserves pointwise equality
-- of renaming functions
extsb-cong : ∀ {Γ₁ Γ₂ A A'}
  → {fb' : ∀ {Ab} → □ Ab ∈b Γ₁ → Γ₂ ⊢b Ab}
  → {fb'' : ∀ {Ab} → □ Ab ∈b Γ₁ → Γ₂ ⊢b Ab}
  → (h : ∀ {Ab} → (x : □ Ab ∈b Γ₁) → fb' x ≡ fb'' x)
  → (x : □ A ∈b Γ₁ ,b □ A')
  → extsb fb' x ≡ extsb fb'' x
extsb-cong h Zb = refl
extsb-cong h (Sb x) = cong (renameb Sb) (h x)

-- substb preserves pointwise equality
-- of renaming functions
substb-cong : ∀ {Γ₁ Γ₂ A}
  → {fb' : ∀ {Ab} → □ Ab ∈b Γ₁ → Γ₂ ⊢b Ab}
  → {fb'' : ∀ {Ab} → □ Ab ∈b Γ₁ → Γ₂ ⊢b Ab}
  → (h : ∀ {Ab} → (x : □ Ab ∈b Γ₁) → fb' x ≡ fb'' x)
  → (t : Γ₁ ⊢b A)
  → substb fb' t ≡ substb fb'' t
substb-cong h (ε x) = h x
substb-cong h (box t) = cong box (substb-cong h t)
substb-cong h (ƛb t) = cong ƛb (substb-cong (extsb-cong h) t)
substb-cong h (t ·b t₁) = cong₂ _·b_ (substb-cong h t) (substb-cong h t₁)

-- Commutativity of renameb and extsb:
extsb-rename-commute : ∀ {Γ₁ Γ₂ Γ₃ A B}
  → (fb' : ∀ {Ab} → Ab ∈b Γ₂ → Ab ∈b Γ₃)
  → (fb'' : ∀ {Ab} → □ Ab ∈b Γ₁ → Γ₂ ⊢b Ab)
  → (x : □ A ∈b Γ₁ ,b B)
  → extsb (λ x₁ → renameb fb' (fb'' x₁)) x ≡ 
    renameb (extb fb') (extsb fb'' x)
extsb-rename-commute fb' fb'' Zb = refl
extsb-rename-commute fb' fb'' (Sb x) = sym (rename-extb-Sb-commute fb' (fb'' x))

-- Commutativity of substb and renameb
substb-rename-commute : ∀ {Γ₁ Γ₂ Γ₃ A} 
  → (fb' : ∀ {Ab} → Ab ∈b Γ₂ → Ab ∈b Γ₃)
  → (fb'' : ∀ {Ab} → □ Ab ∈b Γ₁ → Γ₂ ⊢b Ab)
  → (t : Γ₁ ⊢b A)
  → substb (λ x → renameb fb' (fb'' x)) t ≡ renameb fb' (substb fb'' t)
substb-rename-commute fb' fb'' (ε x) = refl
substb-rename-commute fb' fb'' (box t) = cong box (substb-rename-commute fb' fb'' t)
substb-rename-commute fb' fb'' (ƛb t) =
  beginEq
    ƛb (substb (extsb (λ x → renameb fb' (fb'' x))) t)
  ≡⟨ cong ƛb (substb-cong (λ x → extsb-rename-commute fb' fb'' x) t) ⟩
    ƛb (substb (λ x → renameb (extb fb') ((extsb fb'') x)) t)
  ≡⟨ cong ƛb (substb-rename-commute (extb fb') (extsb fb'') t) ⟩
    ƛb (renameb (extb fb') (substb (extsb fb'') t))
  ∎eq
substb-rename-commute fb' fb'' (t ·b t₁) = 
  cong₂ 
    _·b_ 
    (substb-rename-commute fb' fb'' t) 
    (substb-rename-commute fb' fb'' t₁)

-- extsb distributes over composition:
-- Executing extsb first with fb', then with fb''
-- is the same as doing extsb once with fb'' ∘ fb'.
extsb-comp : ∀ {Γ₁ Γ₂ Γ₃ A B}
  → (fb' : ∀ {Ab} → Ab ∈b Γ₁ → Ab ∈b Γ₂)
  → (fb'' : ∀ {Ab} → □ Ab ∈b Γ₂ → Γ₃ ⊢b Ab)
  → (x : □ A ∈b Γ₁ ,b B)
  → extsb fb'' (extb fb' x) ≡ extsb (λ x₁ → fb'' (fb' x₁)) x
extsb-comp fb' fb'' Zb = refl
extsb-comp fb' fb'' (Sb x) = refl 

-- substb and rename distribute over composition:
-- Renaming first with fb' and substituting with fb''
-- is the same as substituting with fb'' ∘ fb'
subst-renameb-comp : ∀ {Γ₁ Γ₂ Γ₃ A}
  → (fb' : ∀ {Ab} → Ab ∈b Γ₁ → Ab ∈b Γ₂)
  → (fb'' : ∀ {Ab} → □ Ab ∈b Γ₂ → Γ₃ ⊢b Ab)
  → (t : Γ₁ ⊢b A)
  → substb fb'' (renameb fb' t) ≡ substb (λ x → fb'' (fb' x)) t
subst-renameb-comp fb' fb'' (ε x) = refl
subst-renameb-comp fb' fb'' (box t) = cong box (subst-renameb-comp fb' fb'' t)
subst-renameb-comp fb' fb'' (ƛb t) =
  beginEq
    ƛb (substb (extsb fb'') (renameb (extb fb') t))
  ≡⟨ cong ƛb (subst-renameb-comp (extb fb') (extsb fb'') t) ⟩
    ƛb (substb (λ x → (extsb fb'') ((extb fb') x)) t)
  ≡⟨ cong ƛb (substb-cong (λ x → extsb-comp fb' fb'' x) t) ⟩
    ƛb (substb (extsb (λ x → fb'' (fb' x))) t)
  ∎eq
subst-renameb-comp fb' fb'' (t ·b t₁) = cong₂ _·b_ (subst-renameb-comp fb' fb'' t) (subst-renameb-comp fb' fb'' t₁)

-- Renaming followed by substitution with an extended context (extsb)
-- commutes with substitution followed by renaming.
renameb-substb-exts-Sb-commute : ∀ {Γ A B Δ}
  → (fb' : ∀ {Ab} → □ Ab ∈b Γ → Δ ⊢b Ab)
  → (t : Γ ⊢b A)
  → substb (extsb fb' {B = B}) (renameb Sb t)
    ≡ renameb Sb (substb fb' t)
renameb-substb-exts-Sb-commute fb' t =
  beginEq
    substb (extsb fb') (renameb Sb t)
  ≡⟨ subst-renameb-comp Sb (extsb fb') t ⟩
    substb (λ x → renameb Sb (fb' x)) t
  ≡⟨ substb-rename-commute Sb fb' t ⟩
    renameb Sb (substb fb' t)
  ∎eq

-- Preservation and Reflection of 
-- simultaneous substitution of Gödel's translation
pres-simultaneous-subst : ∀ {Γ Δ A}
  → (fb' : ∀ {Ab} → □ Ab ∈b embedContext Γ → embedContext Δ ⊢b Ab)
  → (f' : ∀ {A} → A ∈ Γ → Δ ⊢ A)
  → (h : ∀ {A'} → (x : A' ∈ Γ) → box (fb' (embedLookup x)) ≡ embedTerm (f' x) )
  → (M : Γ ⊢ A) 
  → substb fb' (embedTerm M) ≡ embedTerm (subst f' M)
pres-simultaneous-subst fb' f' h (` x) = 
  h x
pres-simultaneous-subst fb' f' h (ƛ M) = 
  cong box (cong ƛb (pres-simultaneous-subst (extsb fb') (exts f') (pres-exts fb' f' h) M))
pres-simultaneous-subst fb' f' h (M · M₁) =
  beginEq
    ƛb (ε Zb ·b substb (extsb fb') (renameb Sb (embedTerm M₁))) ·b substb fb' (embedTerm M)
  ≡⟨ cong₂ _·b_ refl (pres-simultaneous-subst fb' f' h M) ⟩ 
    ƛb (ε Zb ·b substb (extsb fb') (renameb Sb (embedTerm M₁))) ·b embedTerm (subst f' M)
  ≡⟨ cong₂ _·b_ (cong ƛb (cong₂ _·b_ refl (renameb-substb-exts-Sb-commute fb' (embedTerm M₁)))) refl ⟩
    ƛb (ε Zb ·b renameb Sb (substb fb' (embedTerm M₁))) ·b embedTerm (subst f' M)
  ≡⟨ cong₂ _·b_ (cong ƛb (cong₂ _·b_ refl (cong (renameb Sb) (pres-simultaneous-subst fb' f' h M₁)))) refl ⟩
    ƛb (ε Zb ·b renameb Sb (embedTerm (subst f' M₁))) ·b embedTerm (subst f' M)
  ∎eq

-- HELPER LEMMA'S TO PROVE h

-- Lemma for assumption h in lemma
-- pres-simultaneous-subst
pres-subst-func : ∀ {A C Γ}
  → (V : Γ ⊢ C)
  → (y : Value V)
  → (x : A ∈ Γ , C)
  → box (fb (embedValue V y) (embedLookup x)) ≡ embedTerm ((f V) x)
pres-subst-func V y Z = box-embedValue y
pres-subst-func V y (S x) = refl

-- exts lemma for assumption h in lemma
exts-pres-subst-func : ∀ {A C Γ B}
  → (V : Γ ⊢ C)
  → (y : Value V)
  → (x : A ∈ Γ , C , B)
  → box (extsb (fb (embedValue V y)) (embedLookup x)) ≡ embedTerm (exts (f V) x)
exts-pres-subst-func V y Z = refl
exts-pres-subst-func V y (S x) =
  beginEq
    box (renameb Sb (fb (embedValue V y) (embedLookup x)))
  ≡⟨ refl ⟩
    renameb Sb (box (fb (embedValue V y) (embedLookup x)))
  ≡⟨ cong (renameb Sb) (pres-subst-func V y x) ⟩
    renameb Sb (embedTerm ( (f V) x ))
  ≡⟨ pres-rename S Sb (λ x₁ → refl) (f V x) ⟩
    embedTerm (rename S (f V x))
  ∎eq

-- Preservation and Reflection of 
-- single substitution of Gödel's translation
pres-subst : ∀ {Γ A B} → (M : Γ , B ⊢ A) → (V : Γ ⊢ B) → (x : Value V) → embedTerm M [ embedValue V x ]b ≡ embedTerm (M [ V ])
pres-subst M V x = pres-simultaneous-subst (fb (embedValue V x)) (f V) (pres-subst-func V x) M

-- Helper lemma: if a value is substituted in a value, the resulting lambda term will also be a value
val-after-subst : ∀ {Γ A B} → (M : Γ , B ⊢ A) → (N : Γ ⊢ B) → (x : Value M) → (y : Value N) → Value (M [ N ])
val-after-subst (` Z) N x y = y
val-after-subst (` (S x₁)) N x y = V-`
val-after-subst (ƛ M) N x y = V-ƛ

-- Preservation and Reflection of 
-- single substitution in values of Gödel's translation 
pres-subst-val : ∀ {Γ A B} 
  → (M : Γ , B ⊢ A) 
  → (V : Γ ⊢ B) 
  → (x : Value M) 
  → (y : Value V) 
  → embedValue M x [ embedValue V y ]b ≡ embedValue (M [ V ]) (val-after-subst M V x y)
pres-subst-val (` Z) V x y = refl
pres-subst-val (` (S x₁)) V x y = refl
pres-subst-val (ƛ M) V x y =
  beginEq
    embedValue (ƛ M) x [ embedValue V y ]b
  ≡⟨ refl ⟩
    ƛb (substb (extsb (fb (embedValue V y))) (embedTerm M))
  ≡⟨ cong ƛb (pres-simultaneous-subst (extsb (fb (embedValue V y))) (exts (f V)) (exts-pres-subst-func V y) M) ⟩
    ƛb (embedTerm (subst (exts (f V)) M))
  ≡⟨ refl ⟩
    embedValue ((ƛ M) [ V ]) (val-after-subst (ƛ M) V x y)
  ∎eq

-- fb and renameb commute under extended context.
fb-renameb-extb-commute : ∀ {Γ A B Δ}
  → (fb' : ∀ {Ab} → Ab ∈b Γ → Ab ∈b Δ)
  → (W : Γ ⊢b B)
  → (x : □ A ∈b Γ ,b □ B)
  → fb (renameb fb' W) (extb fb' x) ≡ renameb fb' (fb W x)
fb-renameb-extb-commute fb' W Zb = refl
fb-renameb-extb-commute fb' W (Sb x) = refl

-- Preservation and reflection of 
-- single substitution under renaming
pres-subst-func-rename : ∀ {Γ B A Δ}
  → (fb' : ∀ {Ab} → Ab ∈b Γ → Ab ∈b Δ)
  → (M : Γ ,b □ B ⊢b A)
  → (W : Γ ⊢b B)
  → renameb (extb fb') M [ renameb fb' W ]b
    ≡ renameb fb' (M [ W ]b)
pres-subst-func-rename fb' M W =
  beginEq
    substb (fb (renameb fb' W)) (renameb (extb fb') M) 
  ≡⟨ subst-renameb-comp (extb fb') (fb (renameb fb' W)) M ⟩
    substb (λ x → fb (renameb fb' W) (extb fb' x)) M
  ≡⟨ substb-cong (fb-renameb-extb-commute fb' W) M ⟩
    substb (λ x → renameb fb' (fb W x)) M
  ≡⟨ substb-rename-commute fb' (fb W) M ⟩
    renameb fb' (substb (fb W) M)
  ∎eq

-- Preservation of reduction under renaming   
pres-rename-red : ∀ {Γ A Δ}
  → (fb' : ∀ {Ab} → Ab ∈b Γ → Ab ∈b Δ)
  → (M : Γ ⊢b A)
  → (N : Γ ⊢b A)
  → (M ↝βb N)
  → renameb fb' M ↝βb renameb fb' N
pres-rename-red fb' (ƛb M₁ ·b box M₂) N βb = Eq.subst (λ x → ƛb (renameb (extb fb') M₁) ·b box (renameb fb' M₂) ↝βb x) (pres-subst-func-rename fb' M₁ M₂) βb
pres-rename-red fb' M N (μ {M = M₁} {M' = M'} red) = μ (pres-rename-red fb' M₁ M' red)
pres-rename-red fb' M N (ν {M = M₁} {N = N₁} {N' = N'} red) = ν (pres-rename-red fb' N₁ N' red)
pres-rename-red fb' M N (ξ {M = M₁} {M' = M'} red) = ξ (pres-rename-red (extb fb') M₁ M' red)
pres-rename-red fb' M N (ζ {M = M₁} {M' = M'} red) = ζ (pres-rename-red fb' M₁ M' red)

-- Preservation of 2 step reduction
-- under renaming
pres-rename-red-2 : ∀ {Γ A Δ}
  → (fb' : ∀ {Ab} → Ab ∈b Γ → Ab ∈b Δ)
  → (M : Γ ⊢b A)
  → (N : Γ ⊢b A)
  → (M ↝βb² N)
  → renameb fb' M ↝βb² renameb fb' N
pres-rename-red-2 fb' M N (βb² .M t₂ .N x x₁) = βb² (renameb fb' M) (renameb fb' t₂) (renameb fb' N) (pres-rename-red fb' M t₂ x) (pres-rename-red fb' t₂ N x₁)
pres-rename-red-2 fb' M N (μ {M = M₁} {M' = M'} red) = μ (pres-rename-red-2 fb' M₁ M' red)
pres-rename-red-2 fb' M N (ν {M = M₁} {N = N₁} {N' = N'} red) = ν (pres-rename-red-2 fb' N₁ N' red)
pres-rename-red-2 fb' M N (ξ {M = M₁} {M' = M'} red) = ξ (pres-rename-red-2 (extb fb') M₁ M' red)
pres-rename-red-2 fb' M N (ζ {M = M₁} {M' = M'} red) = ζ (pres-rename-red-2 fb' M₁ M' red)

-- extsb of ε is ε
ε-exts : ∀ {Γ A B}
  → (x : □ A ∈b Γ ,b B)
  → extsb ε x ≡ ε x
ε-exts Zb = refl
ε-exts (Sb x) = refl

-- Simultaneous substitution with ε 
-- leaves the term unchanged  
subst-with-id : ∀ {Γ A}
  → (M : Γ ⊢b A)
  → substb (λ x₁ → ε x₁) M ≡ M
subst-with-id (ε x) = refl
subst-with-id (box M) = cong box (subst-with-id M)
subst-with-id (ƛb M) =
  beginEq
    ƛb (substb (extsb ε) M) 
  ≡⟨ cong ƛb (substb-cong (λ x → ε-exts x) M) ⟩
    ƛb (substb ε M)
  ≡⟨ cong ƛb (subst-with-id M) ⟩
    ƛb M
  ∎eq
subst-with-id (M ·b M₁) = cong₂ _·b_ (subst-with-id M) (subst-with-id M₁)

-- Substitution composed with renaming with Sb 
-- is the same as embedding that term.
subst-rename-fb-comp : ∀ {Γ A B}
  → (M₁ : Γ , B ⊢ A)
  → (M₂ : Γ ⊢ B)
  → (x : Value M₂ )
  → substb (fb (ƛb (embedTerm M₁))) (renameb Sb (embedTerm M₂))
    ≡ box (embedValue M₂ x)
subst-rename-fb-comp M₁ M₂ x =
  beginEq
    substb (fb (ƛb (embedTerm M₁))) (renameb Sb (embedTerm M₂))
  ≡⟨ subst-renameb-comp Sb (fb (ƛb (embedTerm M₁))) (embedTerm M₂) ⟩
    substb (λ x₁ → ε x₁) (embedTerm M₂)
  ≡⟨ subst-with-id (embedTerm M₂) ⟩
    embedTerm M₂
  ≡⟨ sym (box-embedValue x) ⟩
    box (embedValue M₂ x)
  ∎eq

-- Preservation of 2 step reduction of Gödel's translation
pres-red : ∀ {Γ A} 
  → (M : Γ ⊢ A) 
  → (N : Γ ⊢ A) 
  → (M ↝βᵥ N) 
  → (embedTerm M ↝βb² embedTerm N)
pres-red (ƛ M₁ · M₂) N (βᵥ x) = 
  βb² 
  (raise (embedTerm M₂) ·b box (ƛb (embedTerm M₁))) 
  (ƛb (embedTerm M₁) ·b box (embedValue M₂ x)) 
  (embedTerm (M₁ [ M₂ ])) 
  (Eq.subst 
    (λ x → ƛb (ε Zb ·b renameb Sb (embedTerm M₂)) ·b box (ƛb (embedTerm M₁)) ↝βb x) 
    (cong₂ _·b_ refl (subst-rename-fb-comp M₁ M₂ x)) 
    βb) 
  (Eq.subst (λ t → ƛb (embedTerm M₁) ·b box (embedValue M₂ x) ↝βb t) (pres-subst M₁ M₂ x) βb)
pres-red M N (μ {M = M₁} {M' = M'} red) = ν (pres-red M₁ M' red)
pres-red M N (ν< {M = M₁} {N = N₁} {N' = N'} x red) = μ (ξ (ν (pres-rename-red-2 Sb (embedTerm N₁) (embedTerm N') (pres-red N₁ N' red))))
pres-red M N (ν {M = M₁} {N = N₁} {N' = N'} red) = μ (ξ (ν (pres-rename-red-2 Sb (embedTerm N₁) (embedTerm N') (pres-red N₁ N' red))))
pres-red M N (ξ {M = M₁} {M' = M'} red) = ζ (ξ (pres-red M₁ M' red))

-- Preservation of the 2 step reduction rule under rename
pres-rename-red-↝βb₂ : ∀ {Γ A Δ}
  → (fb' : ∀ {Ab} → Ab ∈b Γ → Ab ∈b Δ)
  → (M : Γ ⊢b A)
  → (N : Γ ⊢b A)
  → (M ↝βb₂ N)
  → renameb fb' M ↝βb₂ renameb fb' N
pres-rename-red-↝βb₂ fb' M N (βb₂ {M = M'} {W = W'}) = 
  Eq.subst 
    (λ x → x ↝βb₂ renameb fb' 
    (M' [ W' ]b)) 
    (cong₂ _·b_ (cong ƛb (cong₂ _·b_ refl (cong box (sym (rename-extb-Sb-commute fb' W'))))) refl) 
    (Eq.subst 
      (λ x → (raise  (box (renameb fb' W'))) ·b box (ƛb (renameb (extb fb') M')) ↝βb₂ x) 
      (pres-subst-func-rename fb' M' W') 
      βb₂
    )
pres-rename-red-↝βb₂ fb' M N (μ {M = M₁} {M' = M'} red) = μ (pres-rename-red-↝βb₂ fb' M₁ M' red)
pres-rename-red-↝βb₂ fb' M N (ν {N = N₁} {N' = N'} red) = ν (pres-rename-red-↝βb₂ fb' N₁ N' red)
pres-rename-red-↝βb₂ fb' M N (ξ {M = M₁} {M' = M'} red) = ξ (pres-rename-red-↝βb₂ (extb fb') M₁ M' red)
pres-rename-red-↝βb₂ fb' M N (ζ {M = M₁} {M' = M'} red) = ζ (pres-rename-red-↝βb₂ fb' M₁ M' red)

-- Preservation of reduction by Gödel's translation
-- with the two step reduction rule
pres-red↝βb₂ : ∀ {Γ A} 
  → (M : Γ ⊢ A) 
  → (N : Γ ⊢ A) 
  → (M ↝βᵥ N) 
  → (embedTerm M ↝βb₂ embedTerm N)
pres-red↝βb₂ (ƛ M₁ · M₂) N (βᵥ x) = 
  Eq.subst 
    (λ t → t ↝βb₂ embedTerm (M₁ [ M₂ ])) 
    (cong₂ _·b_ (cong ƛb (cong₂ _·b_ refl (cong (renameb Sb) (box-embedValue x)))) refl) 
    (Eq.subst 
      (λ t → raise ( box (embedValue M₂ x) ) ·b box (ƛb (embedTerm M₁)) ↝βb₂ t) 
      (pres-subst M₁ M₂ x) 
      βb₂
    )
pres-red↝βb₂ M N (μ {M = M₁} {M' = M'} red) = ν (pres-red↝βb₂ M₁ M' red)
pres-red↝βb₂ M N (ν< {N = N₁} {N' = N'} x red) = μ (ξ (ν (pres-rename-red-↝βb₂ Sb (embedTerm N₁) (embedTerm N') (pres-red↝βb₂ N₁ N' red))))
pres-red↝βb₂ M N (ν {N = N₁} {N' = N'} red) = μ (ξ (ν (pres-rename-red-↝βb₂ Sb (embedTerm N₁) (embedTerm N') (pres-red↝βb₂ N₁ N' red))))
pres-red↝βb₂ M N (ξ {M = M₁} {M' = M'} red) = ζ (ξ (pres-red↝βb₂ M₁ M' red))
  