module SelfInterpreter where

open import Relation.Binary.PropositionalEquality as P using (_≡_; module ≡-Reasoning)
open import Function
open import SystemF

`Id : ∀ {Δ} → Type Δ
`Id = `∀ (` Z ⇒ ` Z)

□_ : ∀ {Δ} → Type Δ → Type Δ
□ A = `Id ⇒ A

swapCtx : ∀ {Δ Γ B C} → Rename Δ (Γ , B , C) (Γ , C , B)
swapCtx Z = S Z
swapCtx (S Z) = Z
swapCtx (S S x) = (S S x)

`prequote
  : ∀ {Δ Γ A}
  → Δ ؛ Γ ⊢ A
    ------------------------------
  → Δ ؛ Γ , `∀ ((` Z) ⇒ (` Z)) ⊢ A
`prequote {A} (` x) = ` (S x)
`prequote (ƛ M) = ƛ rename swapCtx (`prequote M)
`prequote (_·_ {A = A} {B = B} M N) = ((` Z) ∙ (A ⇒ B)) · `prequote M · `prequote N
`prequote (Λ M) = Λ `prequote M
`prequote (_∙_ {A = A} M B) = (((` Z) ∙ (`∀ A)) · (`prequote M)) ∙ B

`quote
  : ∀ {Δ Γ A}
  → Δ ؛ Γ ⊢ A
    -----------
  → Δ ؛ Γ ⊢ □ A
`quote M = ƛ `prequote M

`id : ∀ {Δ Γ} → Δ ؛ Γ ⊢ `Id
`id = Λ (ƛ ` Z)

`unquote : ∀ {Δ Γ A} → Δ ؛ Γ ⊢ □ A ⇒ A
`unquote = ƛ ` Z · `id

-- M : A
--   prequote ((x A) (prequote M))
-- = y (A ⇒ A) (prequote (x A)) (prequote (prequote M))
-- = y (A ⇒ A) (y (∀ X. X ⇒ X) x A) (prequote (prequote M))
--   prequote_y (prequote_x (M N))
-- = prequote_y (((x A) (prequote_x M)) (prequote_x N))
-- = y A (prequote_y ((x A) (prequote_x M))) (prequote_y (prequote_x N))
-- = y A (y (A ⇒ A) (y (∀ X. X ⇒ X) x A) (prequote_y (prequote_x M))) (prequote_y (prequote_x N))
-- = (x A (prequote_x M) (prequote_x N)) [x := Λ A. ƛ e. y A (y (A ⇒ A) (y (∀ X. X ⇒ X) x A) e)]
-- = prequote_x (M N) [x := Λ A. ƛ e. y A (y (A ⇒ A) (y (∀ X. X ⇒ X) x A) e)]

`id₂ : ∀ {Δ Γ} → Δ ؛ Γ , `Id , `Id ⊢ `Id
`id₂ = Λ (ƛ (` S S Z) ∙ ` Z · ((` S S Z) ∙ (` Z ⇒ ` Z) · (((` S S Z) ∙ (`∀ (` Z ⇒ ` Z)) · (` S Z)) ∙ ` Z) · ` Z))

`4 : ∀ {Δ Γ A} → Δ ؛ Γ ⊢ □ A ⇒ □ (□ A)
`4 = ƛ ƛ ƛ (` S S Z) · `id₂

-- Properties {{{

rename-preserves-normal
  : ∀ {Δ Γ Γ' A} {M : Δ ؛ Γ ⊢ A}
  → (ρ : ∀ {A} → Δ ؛ Γ ∋ A → Δ ؛ Γ' ∋ A)
  → Normal M
  → Normal (rename ρ M)

rename-preserves-neutral-·
  : ∀ {Δ Γ Γ' A} {M : Δ ؛ Γ ⊢ A}
  → (ρ : ∀ {A} → Δ ؛ Γ ∋ A → Δ ؛ Γ' ∋ A)
  → Neutral-· M
  → Neutral-· (rename ρ M)

rename-preserves-neutral-∙
  : ∀ {Δ Γ Γ' A} {M : Δ ؛ Γ ⊢ A}
  → (ρ : ∀ {A} → Δ ؛ Γ ∋ A → Δ ؛ Γ' ∋ A)
  → Neutral-∙ M
  → Neutral-∙ (rename ρ M)

rename-preserves-neutral-·∙
  : ∀ {Δ Γ Γ' A} {M : Δ ؛ Γ ⊢ A}
  → (ρ : ∀ {A} → Δ ؛ Γ ∋ A → Δ ؛ Γ' ∋ A)
  → Neutral-·∙ M
  → Neutral-·∙ (rename ρ M)

rename-preserves-normal ρ (′ M) = ′ rename-preserves-neutral-· ρ M
rename-preserves-normal ρ (″ M) = ″ rename-preserves-neutral-∙ ρ M
rename-preserves-neutral-· ρ (″ M) = ″ rename-preserves-neutral-·∙ ρ M
rename-preserves-neutral-· ρ (Λ M) = Λ rename-preserves-normal (ext' ρ) M
rename-preserves-neutral-∙ ρ (′ M) = ′ rename-preserves-neutral-·∙ ρ M
rename-preserves-neutral-∙ ρ (ƛ M) = ƛ rename-preserves-normal (ext ρ) M
rename-preserves-neutral-·∙ ρ (` x) = ` ρ x
rename-preserves-neutral-·∙ ρ (M · N) = rename-preserves-neutral-· ρ M · rename-preserves-normal ρ N
rename-preserves-neutral-·∙ ρ (M ∙ B) = rename-preserves-neutral-∙ ρ M ∙ B

normal-`prequote : ∀ {Δ Γ A} → (M : Δ ؛ Γ ⊢ A) → Normal (`prequote M)
normal-`prequote (` x) = ‴ ` S x
normal-`prequote (ƛ M) = ″ ƛ rename-preserves-normal swapCtx (normal-`prequote M)
normal-`prequote (M · N) = ‴ (″ (″ (′ ` Z) ∙ _) · normal-`prequote M) · normal-`prequote N
normal-`prequote (Λ M) = ′ Λ (normal-`prequote M)
normal-`prequote (M ∙ B) = ‴ (′ (″ (′ ` Z) ∙ _) · normal-`prequote M) ∙ B

normal-`quote :  ∀ {Δ Γ A} → (M : Δ ؛ Γ ⊢ A) → Normal (`quote M)
normal-`quote M = ″ (ƛ normal-`prequote M)

`id-∙-· : ∀ {Δ Γ} → (A : Type Δ) → (M : Δ ؛ Γ ⊢ A) → (`id ∙ A) · M —↠ M
`id-∙-· {Γ = Γ} A M =
  begin
    (`id ∙ A) · M
  —→⟨ ξ-·ₗ β-Λ ⟩
    (ƛ ` Z) · M
  —→⟨ β-ƛ ⟩
    M
  ∎

`prequote-[`id] : ∀ {Δ Γ A} → (M : Δ ؛ Γ ⊢ A) → `prequote M [ `id ] —↠ M

`prequote-[`id] (` x) = ` x ∎

`prequote-[`id] {Δ} {Γ} (ƛ_ {A = A} {B = B} M) =
  begin
    (`prequote (ƛ M)) [ `id ]
  ≡⟨ P.refl ⟩
    ƛ subst (exts (Z↦ `id)) (rename swapCtx (`prequote M))
  ≡⟨ P.sym (P.cong ƛ_ (subst-∘ (exts (Z↦ `id)) swapCtx (`prequote M))) ⟩
    ƛ subst (λ {A} x → (exts (Z↦ `id) {A} (swapCtx {A = A} x))) (`prequote M)
  ≡⟨ P.cong ƛ_ (subst-cong lemma (`prequote M)) ⟩
    ƛ subst (Z↦ `id) (`prequote M)
  —↠⟨ ƛ-cong (`prequote-[`id] M) ⟩
    ƛ M
  ∎
  where
    lemma : ∀ {Γ B} → ∀ {A} → exts {Γ' = Γ} (Z↦ `id) {A} ∘ swapCtx {B = B} {A = A} ≗ Z↦ `id {A}
    lemma Z = P.refl
    lemma (S Z) = P.refl
    lemma (S (S x)) = P.refl

`prequote-[`id] (_·_ {A = A} {B = B} M N) =
  begin
    (`prequote (M · N)) [ `id ]
  —↠⟨ _ ∎ ⟩
    (`id ∙ (A ⇒ B)) · (`prequote M [ Λ ƛ ` Z ]) · (`prequote N [ Λ ƛ ` Z ])
  —↠⟨ ·-congᵣ (`prequote-[`id] N) ⟩
    (`id ∙ (A ⇒ B)) · (`prequote M [ Λ ƛ ` Z ]) · N
  —↠⟨ ·-congₗ (·-congᵣ (`prequote-[`id] M)) ⟩
    (`id ∙ (A ⇒ B)) · M · N
  —↠⟨ ·-congₗ (`id-∙-· (A ⇒ B) M) ⟩
    M · N
  ∎

`prequote-[`id] (Λ M) =
  begin
    (`prequote (Λ M)) [ `id ]
  ≡⟨ P.cong Λ_ (subst-cong lemma (`prequote M)) ⟩
    Λ (`prequote M [ `id ])
  —↠⟨ Λ-cong (`prequote-[`id] M) ⟩
    Λ M
  ∎
  where
    lemma : ∀ {Δ Γ} → ∀ {A} → exts' (Z↦ (`id {Δ = Δ} {Γ = Γ})) {A} ≗ Z↦ `id {A}
    lemma {Γ = Γ} Z = P.refl
    lemma {Γ = Γ} (S x) = exts'-` x

`prequote-[`id] (M ∙ B) =
  begin
    (`prequote (M  ∙ B)) [ `id ]
  —↠⟨ _ ∎ ⟩
    ((`id ∙ (`∀ _)) · (`prequote M) [ `id ]) ∙ B
  —↠⟨ ∙-congₗ (`id-∙-· (`∀ _) (`prequote M [ `id ])) ⟩
    ((`prequote M) [ `id ]) ∙ B
  —↠⟨ ∙-congₗ (`prequote-[`id] M) ⟩
    M ∙ B
  ∎

`unquote-`quote :  ∀ {Δ Γ A} → (M : Δ ؛ Γ ⊢ A) → `unquote · (`quote M) —↠ M
`unquote-`quote M =
  begin
    `unquote · (`quote M)
  —→⟨ β-ƛ ⟩
    `quote M · `id
  —→⟨ β-ƛ ⟩
    `prequote M [ `id ]
  —↠⟨ `prequote-[`id] M ⟩
    M
  ∎

`prequote-rename : ∀ {Δ Γ Γ' A} → (ρ : Rename Δ Γ Γ') → (M : Δ ؛ Γ ⊢ A) → `prequote (rename ρ M) ≡ rename (ext ρ) (`prequote M)
`prequote-rename ρ (` x) = P.refl
`prequote-rename ρ (ƛ M) = {! !}
`prequote-rename ρ (M · N) = {! !}
`prequote-rename ρ (Λ M) = {! !}
`prequote-rename ρ (M ∙ B) = {! P.cong !}

`id₂-∙-· : ∀ {Δ Γ} → (A : Type Δ) → (M : Δ ؛ Γ , `Id , `Id ⊢ A) → (`id₂ ∙ A) · M —↠ (` S Z) ∙ A · ((` S Z) ∙ (A ⇒ A) · (((` S Z) ∙ (`∀ (` Z ⇒ ` Z)) · (` Z)) ∙ A) · M)
`id₂-∙-· A M =
  begin
    (`id₂ ∙ A) · M
  —→⟨ ξ-·ₗ β-Λ ⟩
    _ · M
  —→⟨ β-ƛ ⟩
    _
  ∎

Z↦`id₂ : ∀ {Δ Γ A} → Δ ؛ Γ , `∀ (` Z ⇒ ` Z) ∋ A → Δ ؛ Γ , `∀ (` Z ⇒ ` Z) , `∀ (` Z ⇒ ` Z) ⊢ A
Z↦`id₂ Z     = `id₂
Z↦`id₂ (S x) = ` S S x

ext'-swapCtx : ∀ {Δ Γ B C A} → ext' (swapCtx {Δ = Δ} {Γ = Γ} {B = B} {C = C}) {A} ≗ swapCtx
ext'-swapCtx Z = P.refl
ext'-swapCtx (S Z) = P.refl
ext'-swapCtx (S S x) =
  ≡-Reasoning.begin
    (ext' (λ x → S S x) x)
  ≡-Reasoning.≡⟨ ext'-S-∘ S_ x ⟩
    S (ext' (λ x → S x) x)
  ≡-Reasoning.≡⟨ P.cong S_ (ext'-S-∘ id x) ⟩
    S S (ext' id x)
  ≡-Reasoning.≡⟨ P.cong (λ x → S S x) (ext'-id x) ⟩
    (S S x)
  ≡-Reasoning.∎

exts'-Z↦`id₂ : ∀ {Δ Γ A} → exts' (Z↦`id₂ {Δ = Δ} {Γ = Γ}) {A} ≗ Z↦`id₂
exts'-Z↦`id₂ Z = P.refl
exts'-Z↦`id₂ (S x) =
  ≡-Reasoning.begin
    exts' (λ x → ` S S x) x
  ≡-Reasoning.≡⟨ exts'-`-∘ (λ x → S S x) x ⟩
    ` ext' (λ x → S S x) x
  ≡-Reasoning.≡⟨ P.cong `_ (ext'-S-∘ S_ x) ⟩
    ` S (ext' (λ x → S x) x)
  ≡-Reasoning.≡⟨ P.cong `_ (P.cong S_ (ext'-S-∘ id x)) ⟩
    ` S S (ext' id x)
  ≡-Reasoning.≡⟨ P.cong `_ (P.cong (λ x → S S x) (ext'-id x)) ⟩
    ` S S x
  ≡-Reasoning.∎

`prequote-[`id₂] : ∀ {Δ Γ A} → (M : Δ ؛ Γ ⊢ A) → subst Z↦`id₂ (`prequote M) —↠ rename swapCtx (`prequote (`prequote M))
`prequote-[`id₂] (` x) = _ ∎

`prequote-[`id₂] (ƛ M) =
  begin
    subst Z↦`id₂ (`prequote (ƛ M))
  ≡⟨ P.refl ⟩
    ƛ subst (exts Z↦`id₂) (rename swapCtx (`prequote M))
  ≡⟨ P.sym (P.cong ƛ_ (subst-∘ (exts Z↦`id₂) swapCtx (`prequote M))) ⟩
    ƛ subst (exts Z↦`id₂ ∘ swapCtx) (`prequote M)
  ≡⟨ {!!} ⟩
    ƛ subst (rename (swapCtx ∘ ext swapCtx) ∘ Z↦`id₂) (`prequote M)
  ≡⟨ P.cong ƛ_ {! subst-rename-∘ !} ⟩
    ƛ rename (swapCtx ∘ ext swapCtx) (subst (Z↦`id₂) (`prequote M))
  —↠⟨ ƛ-cong {! rename-cong-—↠ ... !} ⟩
    ƛ rename (swapCtx ∘ ext swapCtx) (rename swapCtx (`prequote (`prequote M)))
  ≡⟨ P.cong ƛ_ {! rename-∘ ... !} ⟩
    ƛ rename (swapCtx ∘ ext swapCtx ∘ swapCtx) (`prequote (`prequote M))
  ≡⟨ P.cong ƛ_ (rename-cong (λ {Z → P.refl ; (S Z) → P.refl ; (S S Z) → P.refl; (S S S _) → P.refl}) (`prequote (`prequote M))) ⟩
    ƛ rename (ext swapCtx ∘ swapCtx ∘ ext swapCtx) (`prequote (`prequote M))
  ≡⟨ P.cong ƛ_ {! rename-∘ ... !} ⟩
    ƛ rename (ext swapCtx) (rename swapCtx (rename (ext swapCtx) (`prequote (`prequote M))))
  ≡⟨ P.sym (P.cong (λ M' → ƛ rename (ext swapCtx) (rename swapCtx M')) (`prequote-rename swapCtx (`prequote M))) ⟩
    ƛ rename (ext swapCtx) (rename swapCtx (`prequote (rename swapCtx (`prequote M))))
  ≡⟨ P.refl ⟩
    rename swapCtx (`prequote (`prequote (ƛ M)))
  ∎

`prequote-[`id₂] (_·_ {A = A} {B = B} M N) =
  begin
    subst Z↦`id₂ (`prequote (M · N))
  ≡⟨ P.refl ⟩
    (`id₂ ∙ (A ⇒ B) · subst Z↦`id₂ (`prequote M)) · (subst Z↦`id₂ (`prequote N))
  —↠⟨ ·-congₗ (·-congᵣ (`prequote-[`id₂] M)) ⟩
    (`id₂ ∙ (A ⇒ B) · rename swapCtx (`prequote (`prequote M))) · (subst Z↦`id₂ (`prequote N))
  —↠⟨ ·-congᵣ (`prequote-[`id₂] N) ⟩
    (`id₂ ∙ (A ⇒ B) · rename swapCtx (`prequote (`prequote M))) · rename swapCtx (`prequote (`prequote N))
  —↠⟨ ·-congₗ (`id₂-∙-· (A ⇒ B) (rename swapCtx (`prequote (`prequote M)))) ⟩
    rename swapCtx (`prequote (`prequote (M · N)))
  ∎

`prequote-[`id₂] (Λ M) =
  begin
    Λ subst (exts' Z↦`id₂) (`prequote M)
  ≡⟨ P.cong Λ_ (subst-cong exts'-Z↦`id₂ (`prequote M)) ⟩
    Λ subst Z↦`id₂ (`prequote M)
  —↠⟨ Λ-cong (`prequote-[`id₂] M) ⟩
    Λ rename swapCtx (`prequote (`prequote M))
  ≡⟨ P.sym (P.cong Λ_ (rename-cong ext'-swapCtx (`prequote (`prequote M)))) ⟩
    Λ rename (ext' swapCtx) (`prequote (`prequote M))
  ∎

`prequote-[`id₂] (_∙_ {A = A} M B) =
  begin
    subst Z↦`id₂ (`prequote (M ∙ B))
  ≡⟨ P.refl ⟩
    (`id₂ ∙ (`∀ A) · subst Z↦`id₂ (`prequote M)) ∙ B
  —↠⟨ ∙-congₗ (·-congᵣ (`prequote-[`id₂] M)) ⟩
    (`id₂ ∙ (`∀ A) · rename swapCtx (`prequote (`prequote M))) ∙ B
  —↠⟨ ∙-congₗ (`id₂-∙-· (`∀ A) (rename swapCtx (`prequote (`prequote M)))) ⟩
    rename swapCtx (`prequote (`prequote (M ∙ B)))
  ∎

`4-`quote : ∀ {Δ Γ A} → (M : Δ ؛ Γ ⊢ A) → `4 · `quote M —↠ `quote (`quote M)
`4-`quote M =
  begin
    `4 · `quote M
  —→⟨ β-ƛ ⟩
    ƛ ƛ rename S_ (rename S_ (`quote M)) · `id₂
  —→⟨ ξ-ƛ (ξ-ƛ β-ƛ) ⟩
    ƛ ƛ rename (ext S_) (rename (ext S_) (`prequote M)) [ `id₂ ]
  ≡⟨ P.cong ƛ_ (P.cong ƛ_ {! !}) ⟩
    ƛ ƛ subst Z↦`id₂ (`prequote M)
  —↠⟨ ƛ-cong (ƛ-cong (`prequote-[`id₂] M)) ⟩
    ƛ ƛ rename swapCtx (`prequote (`prequote M))
  ≡⟨ P.refl ⟩
    `quote (`quote M)
  ∎
-- }}}
