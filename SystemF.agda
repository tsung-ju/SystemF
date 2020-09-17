module SystemF where

open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)
open import Function
open import Data.Empty
open import Data.Product using (∃-syntax) renaming (_,_ to ⟨_,_⟩)

-- Operators {{{

infix 4 _≗_

infix 2 _—→_
infix 2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infixr 2 _—↠⟨_⟩_
infixr 2 _≡⟨_⟩_
infix  3 _∎

infix  4 _؛_⊢_
infix  4 _؛_∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ′_
infix  5 ″_
infix  5 ‴_
infix  5 ƛ_
infix  5 Λ_
infixl 7 _·_
infixl 7 _∙_
infix  9 `_
infix  9 S_

-- }}}

_≗_ : {A : Set} {B : (x : A) → Set} → (f g : (x : A) → B x) → Set
f ≗ g  = ∀ x → f x ≡ g x

-- Types {{{
data TypeContext : Set where
  ∅ : TypeContext
  _,· : TypeContext → TypeContext

data _∋· : TypeContext → Set where
  Z : ∀ {Γ} → Γ ,· ∋·
  S_ : ∀ {Γ} → Γ ∋· → Γ ,· ∋·

data Type : TypeContext → Set where
 `_ : ∀ {Δ} → Δ ∋· → Type Δ
 _⇒_ : ∀ {Δ} → Type Δ → Type Δ → Type Δ
 `⊥ : ∀ {Δ} → Type Δ
 `∀_ : ∀ {Δ} → Type (Δ ,·) → Type Δ

-- Type Renaming

TypeRename : TypeContext → TypeContext → Set
TypeRename Δ Δ' = Δ ∋· → Δ' ∋·

TypeSubst : TypeContext → TypeContext → Set
TypeSubst Δ Δ' = Δ ∋· → Type Δ'

typeExt : ∀ {Δ Δ'} → TypeRename Δ Δ' → TypeRename (Δ ,·) (Δ' ,·)
typeExt ρ Z = Z
typeExt ρ (S x) = S (ρ x)

typeRename : ∀ {Δ Δ'} →  TypeRename Δ Δ' → Type Δ → Type Δ'
typeRename ρ (` x) = ` ρ x
typeRename ρ (A ⇒ B) = typeRename ρ A ⇒ typeRename ρ B
typeRename ρ `⊥ = `⊥
typeRename ρ (`∀ A) = `∀ typeRename (typeExt ρ) A

typeWeaken : ∀ {Δ} → Type Δ → Type (Δ ,·)
typeWeaken = typeRename S_

-- Type Substitution

typeExts : ∀ {Δ Δ'} → TypeSubst Δ Δ' → TypeSubst (Δ ,·) (Δ' ,·)
typeExts σ Z = ` Z
typeExts σ (S x) = typeWeaken (σ x)

typeSubst : ∀ {Δ Δ'} → TypeSubst Δ Δ' → Type Δ → Type Δ'
typeSubst σ (` x) = σ x
typeSubst σ (A ⇒ B) = typeSubst σ A ⇒ typeSubst σ B
typeSubst σ `⊥ = `⊥
typeSubst σ (`∀ A) = `∀ typeSubst (typeExts σ) A

Z↦ₜ_ : ∀ {Δ} → Type Δ → TypeSubst (Δ ,·) Δ
Z↦ₜ_ B Z = B
Z↦ₜ_ B (S x) = ` x

_[_]ₜ : ∀ {Δ} → Type (Δ ,·) → Type Δ → Type Δ
_[_]ₜ A B = typeSubst (Z↦ₜ B) A

-- Properties {{{

-- Congruence {{{

typeExt-cong
  : ∀ {Δ Δ'} {ρ ρ' : TypeRename Δ Δ'}
  → ρ ≗ ρ'
  → typeExt ρ ≗ typeExt ρ'
typeExt-cong ρ≗ρ' Z = refl
typeExt-cong ρ≗ρ' (S x) = cong S_ (ρ≗ρ' x)

typeRename-cong
  : ∀ {Δ Δ'} {ρ ρ' : TypeRename Δ Δ'}
  → ρ ≗ ρ'
  → typeRename ρ ≗ typeRename ρ'
typeRename-cong ρ≗ρ' (` x) = cong `_ (ρ≗ρ' x)
typeRename-cong ρ≗ρ' (A ⇒ B) = cong₂ _⇒_ (typeRename-cong ρ≗ρ' A) (typeRename-cong ρ≗ρ' B)
typeRename-cong ρ≗ρ' `⊥ = refl
typeRename-cong ρ≗ρ' (`∀ A) = cong `∀_ (typeRename-cong (typeExt-cong ρ≗ρ') A)

typeExts-cong
  : ∀ {Δ Δ'} {σ σ' : TypeSubst Δ Δ'}
  → σ ≗ σ'
  → typeExts σ ≗ typeExts σ'
typeExts-cong σ≗σ' Z = refl
typeExts-cong σ≗σ' (S x) = cong (typeRename S_) (σ≗σ' x)

typeSubst-cong
  : ∀ {Δ Δ'} {σ σ' : TypeSubst Δ Δ'}
  → σ ≗ σ'
  → typeSubst σ ≗ typeSubst σ'
typeSubst-cong σ≗σ' (` x) = σ≗σ' x
typeSubst-cong σ≗σ' (A ⇒ B) = cong₂ _⇒_ (typeSubst-cong σ≗σ' A) (typeSubst-cong σ≗σ' B)
typeSubst-cong σ≗σ' `⊥ = refl
typeSubst-cong σ≗σ' (`∀ A) = cong `∀_ (typeSubst-cong (typeExts-cong σ≗σ') A)

-- }}}

typeExt-id : ∀ {Δ} → typeExt (id {A = Δ ∋·}) ≗ id
typeExt-id Z = refl
typeExt-id (S _) = refl

typeExt-∘
  : ∀ {Δ Δ' Δ''}
  → (ρ' : TypeRename Δ' Δ'')
  → (ρ : TypeRename Δ Δ')
  → typeExt (ρ' ∘ ρ) ≗ typeExt ρ' ∘ typeExt ρ
typeExt-∘ ρ' ρ Z = refl
typeExt-∘ ρ' ρ (S _) = refl

typeRename-id : ∀ {Δ} → typeRename (id {A = Δ ∋·}) ≗ id
typeRename-id (` x) = refl
typeRename-id (A ⇒ B) = cong₂ _⇒_ (typeRename-id A) (typeRename-id B)
typeRename-id `⊥ = refl
typeRename-id (`∀ A) =
  begin
    `∀ typeRename (typeExt id) A
  ≡⟨ cong `∀_ (typeRename-cong typeExt-id A) ⟩
    `∀ typeRename id A
  ≡⟨ cong `∀_ (typeRename-id A) ⟩
    `∀ A
  ∎
  where open ≡-Reasoning

typeRename-∘
  : ∀ {Δ Δ' Δ''}
  → (ρ' : TypeRename Δ' Δ'')
  → (ρ : TypeRename Δ Δ')
  → typeRename (ρ' ∘ ρ) ≗ typeRename ρ' ∘ typeRename ρ
typeRename-∘ ρ' ρ (` x) = refl
typeRename-∘ ρ' ρ (A ⇒ B) = cong₂ _⇒_ (typeRename-∘ ρ' ρ A) (typeRename-∘ ρ' ρ B)
typeRename-∘ ρ' ρ `⊥ = refl
typeRename-∘ ρ' ρ (`∀ A) =
  begin
    `∀ typeRename (typeExt (ρ' ∘ ρ)) A
  ≡⟨ cong `∀_ (typeRename-cong (typeExt-∘ ρ' ρ) A) ⟩
    `∀ typeRename (typeExt ρ' ∘ typeExt ρ) A
  ≡⟨ cong `∀_ (typeRename-∘ (typeExt ρ') (typeExt ρ) A) ⟩
    `∀ (typeRename (typeExt ρ') ∘ typeRename (typeExt ρ)) A
  ∎
  where open ≡-Reasoning

typeExt-S
  : ∀ {Δ Δ'}
  → (ρ : TypeRename Δ Δ')
  → typeExt ρ ∘ S_ ≗ S_ ∘ ρ
typeExt-S ρ _ = refl

typeWeaken-typeRename
  : ∀ {Δ Δ'}
  → (ρ : TypeRename Δ Δ')
  → typeWeaken ∘ typeRename ρ ≗ typeRename (typeExt ρ) ∘ typeWeaken
typeWeaken-typeRename ρ A =
  begin
    (typeWeaken ∘ typeRename ρ) A
  ≡⟨ sym (typeRename-∘ S_ ρ A) ⟩
    typeRename (S_ ∘ ρ) A
  ≡⟨ sym (typeRename-cong (typeExt-S ρ) A) ⟩
    typeRename (typeExt ρ ∘ S_) A
  ≡⟨ typeRename-∘ (typeExt ρ) S_ A ⟩
    (typeRename (typeExt ρ) ∘ typeWeaken) A
  ∎
  where open ≡-Reasoning

typeExts-` : ∀ {Δ} → typeExts {Δ = Δ} `_ ≗ `_
typeExts-` Z = refl
typeExts-` (S _) = refl

typeExts-∘
  : ∀ {Δ Δ' Δ''}
  → (σ : TypeSubst Δ' Δ'')
  → (ρ : TypeRename Δ Δ')
  → typeExts (σ ∘ ρ) ≗ typeExts σ ∘ typeExt ρ
typeExts-∘ σ ρ Z = refl
typeExts-∘ σ ρ (S _) = refl

typeExts-typeRename-∘
  : ∀ {Δ Δ' Δ''}
  → (ρ : TypeRename Δ' Δ'')
  → (σ : TypeSubst Δ Δ')
  → typeExts (typeRename ρ ∘ σ) ≗ typeRename (typeExt ρ) ∘ typeExts σ
typeExts-typeRename-∘ ρ σ Z = refl
typeExts-typeRename-∘ ρ σ (S x) =
  begin
    typeRename S_ (typeRename ρ (σ x))
  ≡⟨ sym (typeRename-∘ S_ ρ (σ x)) ⟩
    typeRename (S_ ∘ ρ) (σ x)
  ≡⟨ typeRename-cong (λ _ → refl) (σ x) ⟩
    typeRename ((typeExt ρ) ∘ S_) (σ x)
  ≡⟨ typeRename-∘ (typeExt ρ) S_ (σ x) ⟩
    typeRename (typeExt ρ) (typeRename S_ (σ x))
  ∎
  where open ≡-Reasoning

typeSubst-` : ∀ {Δ} → (A : Type Δ) → typeSubst `_ A ≡ A
typeSubst-` (` x) = refl
typeSubst-` (A ⇒ B) = cong₂ _⇒_ (typeSubst-` A) (typeSubst-` B)
typeSubst-` `⊥ = refl
typeSubst-` {Δ = Δ} (`∀ A) rewrite typeSubst-cong (typeExts-`) A = cong `∀_ (typeSubst-` A)

typeSubst-∘
  : ∀ {Δ Δ' Δ''}
  → (σ : TypeSubst Δ' Δ'')
  → (ρ : TypeRename Δ Δ')
  → typeSubst (σ ∘ ρ) ≗ typeSubst σ ∘ typeRename ρ 
typeSubst-∘ σ ρ (` x) = refl
typeSubst-∘ σ ρ (A ⇒ B) = cong₂ _⇒_ (typeSubst-∘ σ ρ A) (typeSubst-∘ σ ρ B)
typeSubst-∘ σ ρ `⊥ = refl
typeSubst-∘ σ ρ (`∀ A) rewrite typeSubst-cong (typeExts-∘ σ ρ) A = cong `∀_ (typeSubst-∘ (typeExts σ) (typeExt ρ) A)

typeSubst-typeRename-∘
  : ∀ {Δ Δ' Δ''}
  → (ρ : TypeRename Δ' Δ'')
  → (σ : TypeSubst Δ Δ')
  → typeSubst (typeRename ρ ∘ σ) ≗ typeRename ρ ∘ typeSubst σ
typeSubst-typeRename-∘ ρ σ (` x) = refl
typeSubst-typeRename-∘ ρ σ (A ⇒ B) = cong₂ _⇒_ (typeSubst-typeRename-∘ ρ σ A) (typeSubst-typeRename-∘ ρ σ B)
typeSubst-typeRename-∘ ρ σ `⊥ = refl
typeSubst-typeRename-∘ ρ σ (`∀ A) rewrite typeSubst-cong (typeExts-typeRename-∘ ρ σ) A = cong `∀_ (typeSubst-typeRename-∘ (typeExt ρ) (typeExts σ) A)

typeExts-S
  : ∀ {Δ Δ'}
  → (σ : TypeSubst Δ Δ')
  → typeExts σ ∘ S_ ≗ typeWeaken ∘ σ
typeExts-S σ _ = refl

typeWeaken-typeSubst
  : ∀ {Δ Δ'}
  → (σ : TypeSubst Δ Δ')
  → typeWeaken ∘ typeSubst σ ≗ typeSubst (typeExts σ) ∘ typeWeaken
typeWeaken-typeSubst σ A =
  begin
    (typeWeaken ∘ typeSubst σ) A
  ≡⟨ sym (typeSubst-typeRename-∘ S_ σ A) ⟩
    typeSubst (typeWeaken ∘ σ) A
  ≡⟨ sym (typeSubst-cong (typeExts-S σ) A) ⟩
    typeSubst (typeExts σ ∘ S_) A
  ≡⟨ typeSubst-∘ (typeExts σ) S_ A ⟩
    (typeSubst (typeExts σ) ∘ typeWeaken) A
  ∎
  where open ≡-Reasoning

typeExts-typeSubst-∘
  : ∀ {Δ Δ' Δ''}
  → (σ' : TypeSubst Δ' Δ'')
  → (σ : TypeSubst Δ Δ')
  → typeExts (typeSubst σ' ∘ σ) ≗ typeSubst (typeExts σ') ∘ typeExts σ
typeExts-typeSubst-∘ σ' σ Z = refl
typeExts-typeSubst-∘ σ' σ (S x) = typeWeaken-typeSubst σ' (σ x)

typeSubst-typeSubst-∘
  : ∀ {Δ Δ' Δ''}
  → (σ' : TypeSubst Δ' Δ'')
  → (σ : TypeSubst Δ Δ')
  → typeSubst (typeSubst σ' ∘ σ) ≗ typeSubst σ' ∘ typeSubst σ
typeSubst-typeSubst-∘ σ' σ (` x) = refl
typeSubst-typeSubst-∘ σ' σ (A ⇒ B) = cong₂ _⇒_ (typeSubst-typeSubst-∘ σ' σ A) (typeSubst-typeSubst-∘ σ' σ B)
typeSubst-typeSubst-∘ σ' σ `⊥ = refl
typeSubst-typeSubst-∘ σ' σ (`∀ A) = cong `∀_
  (begin
    typeSubst (typeExts (typeSubst σ' ∘ σ)) A
  ≡⟨ typeSubst-cong (typeExts-typeSubst-∘ σ' σ) A ⟩
    typeSubst (typeSubst (typeExts σ') ∘ typeExts σ) A
  ≡⟨ typeSubst-typeSubst-∘ (typeExts σ') (typeExts σ) A ⟩
    typeSubst (typeExts σ') (typeSubst (typeExts σ) A)
  ∎)
  where open ≡-Reasoning

Z↦ₜ-S : ∀ {Δ} → (B : Type Δ) → (Z↦ₜ B) ∘ S_ ≗ `_
Z↦ₜ-S B A = refl

typeSubst-Z↦ₜ-typeWeaken
  : ∀ {Δ}
  → (B : Type Δ)
  → typeSubst (Z↦ₜ B) ∘ typeWeaken ≗ id
typeSubst-Z↦ₜ-typeWeaken B A =
  begin
    (typeSubst (Z↦ₜ B) ∘ typeWeaken) A
  ≡⟨ sym (typeSubst-∘ (Z↦ₜ B) S_ A) ⟩
    typeSubst ((Z↦ₜ B) ∘ S_) A
  ≡⟨ typeSubst-cong (Z↦ₜ-S B) A ⟩
    typeSubst `_ A
  ≡⟨ typeSubst-` A ⟩
    A
  ∎
  where open ≡-Reasoning

typeRename∘Z↦ₜ
  : ∀ {Δ Δ'}
  → (ρ : TypeRename Δ Δ')
  → (B : Type Δ)
  → typeRename ρ ∘ (Z↦ₜ B) ≗ (Z↦ₜ typeRename ρ B) ∘ (typeExt ρ)
typeRename∘Z↦ₜ ρ B Z = refl
typeRename∘Z↦ₜ ρ B (S _) = refl

typeSubst∘Z↦ₜ
  : ∀ {Δ Δ'}
  → (σ : TypeSubst Δ Δ')
  → (B : Type Δ)
  → typeSubst σ ∘ (Z↦ₜ B) ≗ typeSubst (Z↦ₜ typeSubst σ B) ∘ (typeExts σ)
typeSubst∘Z↦ₜ σ B Z = refl
typeSubst∘Z↦ₜ σ B (S x) =
  begin
    σ x
  ≡⟨ sym (typeSubst-` (σ x)) ⟩
    typeSubst `_ (σ x)
  ≡⟨ typeSubst-∘ (Z↦ₜ typeSubst σ B) S_ (σ x) ⟩
    typeSubst (Z↦ₜ typeSubst σ B) (typeRename S_ (σ x))
  ∎
  where open ≡-Reasoning

typeRename-[]ₜ
  : ∀ {Δ Δ'}
  → (ρ : TypeRename Δ Δ')
  → (A : Type (Δ ,·))
  → (B : Type Δ)
  → typeRename ρ (A [ B ]ₜ) ≡ (typeRename (typeExt ρ) A) [ typeRename ρ B ]ₜ
typeRename-[]ₜ ρ A B = 
  begin
    typeRename ρ (A [ B ]ₜ)
  ≡⟨⟩
    typeRename ρ (typeSubst (Z↦ₜ B) A)
  ≡⟨ sym (typeSubst-typeRename-∘ ρ (Z↦ₜ B) A) ⟩
    typeSubst (typeRename ρ ∘ (Z↦ₜ B)) A
  ≡⟨ typeSubst-cong (typeRename∘Z↦ₜ ρ B) A ⟩
    typeSubst ((Z↦ₜ typeRename ρ B) ∘ (typeExt ρ)) A
  ≡⟨ typeSubst-∘ (Z↦ₜ typeRename ρ B) (typeExt ρ) A ⟩
    typeSubst (Z↦ₜ typeRename ρ B) (typeRename (typeExt ρ) A)
  ≡⟨⟩
    typeRename (typeExt ρ) A [ typeRename ρ B ]ₜ
  ∎
  where open ≡-Reasoning

typeSubst-[]ₜ
  : ∀ {Δ Δ'}
  → (σ : TypeSubst Δ Δ')
  → (A : Type (Δ ,·))
  → (B : Type Δ)
  → typeSubst σ (A [ B ]ₜ) ≡ (typeSubst (typeExts σ) A) [ typeSubst σ B ]ₜ
typeSubst-[]ₜ σ A B = 
  begin
    typeSubst σ (A [ B ]ₜ)
  ≡⟨⟩
    typeSubst σ (typeSubst (Z↦ₜ B) A)
  ≡⟨ sym (typeSubst-typeSubst-∘ σ (Z↦ₜ B) A) ⟩
    typeSubst (typeSubst σ ∘ (Z↦ₜ B)) A
  ≡⟨ typeSubst-cong (typeSubst∘Z↦ₜ σ B) A ⟩
    typeSubst (typeSubst (Z↦ₜ typeSubst σ B) ∘ typeExts σ) A
  ≡⟨ typeSubst-typeSubst-∘ (Z↦ₜ typeSubst σ B) (typeExts σ) A ⟩
    typeSubst (Z↦ₜ typeSubst σ B) (typeSubst (typeExts σ) A)
  ≡⟨⟩
    typeSubst (typeExts σ) A [ typeSubst σ B ]ₜ
  ∎
  where open ≡-Reasoning
-- }}}

-- }}}

-- Context {{{

data Context : TypeContext → Set where
  ∅ : ∀ {Δ} → Context Δ
  _,_ : ∀ {Δ} → Context Δ → Type Δ → Context Δ

ctxMap : ∀ {Δ Δ'} → (Type Δ → Type Δ') → Context Δ → Context Δ'
ctxMap f ∅ = ∅
ctxMap f (Γ , A) = ctxMap f Γ , f A

ctxRename : ∀ {Δ Δ'} → TypeRename Δ Δ' → Context Δ → Context Δ'
ctxRename ρ = ctxMap (typeRename ρ)

ctxWeaken : ∀ {Δ} → Context Δ → Context (Δ ,·)
ctxWeaken = ctxMap typeWeaken

ctxSubst : ∀ {Δ Δ'} → TypeSubst Δ Δ' → Context Δ → Context Δ'
ctxSubst σ = ctxMap (typeSubst σ)

-- Properties {{{
ctxWeaken-ctxRename
  : ∀ {Δ Δ'}
  → (ρ : TypeRename Δ Δ')
  → ctxWeaken ∘ ctxRename ρ ≗ ctxRename (typeExt ρ) ∘ ctxWeaken
ctxWeaken-ctxRename ρ ∅ = refl
ctxWeaken-ctxRename ρ (Γ , A) = cong₂ _,_ (ctxWeaken-ctxRename ρ Γ) (typeWeaken-typeRename ρ A)

ctxRename-∘ : ∀ {Δ Δ' Δ''}
  → (g : TypeRename Δ' Δ'')
  → (f : TypeRename Δ Δ')
  → ctxRename (g ∘ f) ≗ ctxRename g ∘ ctxRename f
ctxRename-∘ g f ∅ = refl
ctxRename-∘ g f (Γ , A) = cong₂ _,_ (ctxRename-∘ g f Γ) (typeRename-∘ g f A)

ctxWeaken-ctxSubst
  : ∀ {Δ Δ'}
  → (σ : TypeSubst Δ Δ')
  → ctxWeaken ∘ ctxSubst σ ≗ ctxSubst (typeExts σ) ∘ ctxWeaken
ctxWeaken-ctxSubst ρ ∅ = refl
ctxWeaken-ctxSubst ρ (Γ , A) = cong₂ _,_ (ctxWeaken-ctxSubst ρ Γ) (typeWeaken-typeSubst ρ A)

ctxSubst-Z↦ₜ-ctxWeaken
  : ∀ {Δ}
  → (B : Type Δ)
  → ctxSubst (Z↦ₜ B) ∘ ctxWeaken ≗ id
ctxSubst-Z↦ₜ-ctxWeaken B ∅ = refl
ctxSubst-Z↦ₜ-ctxWeaken B (Γ , A) = cong₂ _,_ (ctxSubst-Z↦ₜ-ctxWeaken B Γ) (typeSubst-Z↦ₜ-typeWeaken B A)
-- }}}
-- }}}

-- Variables {{{

data _؛_∋_ : (Δ : TypeContext) → Context Δ → Type Δ → Set where
  Z : ∀ {Δ Γ A} → Δ ؛ Γ , A ∋ A
  S_ : ∀ {Δ Γ A B} → Δ ؛ Γ ∋ A → Δ ؛ Γ , B ∋ A

∋-map
  : ∀ {Δ Δ' Γ A}
  → (f : Type Δ → Type Δ')
  → Δ ؛ Γ ∋ A
  → Δ' ؛ ctxMap f Γ ∋ f A
∋-map f Z = Z
∋-map f (S x) = S (∋-map f x)

-- }}}

-- Terms {{{

data _؛_⊢_ : (Δ : TypeContext) → Context Δ → Type Δ → Set where
  `_
    : ∀ {Δ Γ A}
    → Δ ؛ Γ ∋ A
      ---------
    → Δ ؛ Γ ⊢ A

  ƛ_
    : ∀ {Δ Γ A B}
    → Δ ؛ Γ , A ⊢ B
      -------------
    → Δ ؛ Γ ⊢ A ⇒ B

  _·_
    : ∀ {Δ Γ A B}
    → Δ ؛ Γ ⊢ A ⇒ B
    → Δ ؛ Γ ⊢ A
      -------------
    → Δ ؛ Γ ⊢ B

  Λ_
    : ∀ {Δ Γ A}
    → Δ ,· ؛ ctxWeaken Γ ⊢ A
      ----------------------
    → Δ ؛ Γ ⊢ `∀ A

  _∙_
    : ∀ {Δ Γ A}
    → Δ ؛ Γ ⊢ `∀ A
    → (B : Type Δ)
      ---------------
    → Δ ؛ Γ ⊢ A [ B ]ₜ
-- }}}

-- Term Substitution {{{

Rename : (Δ : TypeContext) → Context Δ → Context Δ → Set
Rename Δ Γ Γ' = ∀ {A} → Δ ؛ Γ ∋ A → Δ ؛ Γ' ∋ A

Subst : (Δ : TypeContext) → Context Δ → Context Δ → Set
Subst Δ Γ Γ' = ∀ {A} → Δ ؛ Γ ∋ A → Δ ؛ Γ' ⊢ A

ext : ∀ {Δ Γ Γ' B} → Rename Δ Γ Γ' → Rename Δ (Γ , B) (Γ' , B)
ext ρ Z = Z
ext ρ (S x) = S ρ x

ext' : ∀ {Δ Γ Γ'} → Rename Δ Γ Γ' →  Rename (Δ ,·) (ctxWeaken Γ) (ctxWeaken Γ')
ext' {Γ = Γ , _} ρ Z = ∋-map typeWeaken (ρ Z)
ext' {Γ = Γ , _} ρ (S x) = ext' (ρ ∘ S_) x

rename : ∀ {Δ Γ Γ'} → Rename Δ Γ Γ' → (∀ {A} → Δ ؛ Γ ⊢ A → Δ ؛ Γ' ⊢ A)
rename ρ (` x) = ` ρ x
rename ρ (ƛ M) = ƛ rename (ext ρ) M
rename ρ (M · N) = rename ρ M · rename ρ N
rename ρ (Λ M) = Λ rename (ext' ρ) M
rename ρ (M ∙ B) = rename ρ M ∙ B

exts : ∀ {Δ Γ Γ' B} → Subst Δ Γ Γ' → Subst Δ (Γ , B) (Γ' , B)
exts σ Z = ` Z
exts σ (S x) = rename S_ (σ x)

lemmaS : ∀ {Δ} {Γ Γ' : Context Δ} {A A'} → Γ , A ≡ Γ' , A' → Γ ≡ Γ'
lemmaS refl = refl

∋-substCtx : ∀ {Δ Γ Γ'} → Γ ≡ Γ' → Rename Δ Γ Γ'
∋-substCtx refl x = x

⊢-substCtx : ∀ {Δ Γ Γ'} → Γ ≡ Γ' → (∀ {A} → Δ ؛ Γ ⊢ A → Δ ؛ Γ' ⊢ A)
⊢-substCtx eq = rename (∋-substCtx eq)

⊢-typeRename
  : ∀ {Δ Δ' Γ}
  → (ρ : TypeRename Δ Δ')
  → ∀ {A} → Δ ؛ Γ ⊢ A → Δ' ؛ ctxRename ρ Γ ⊢ typeRename ρ A
⊢-typeRename ρ (` x) = ` ∋-map (typeRename ρ) x
⊢-typeRename ρ (ƛ M) = ƛ ⊢-typeRename ρ M
⊢-typeRename ρ (M · N) = ⊢-typeRename ρ M · ⊢-typeRename ρ N
⊢-typeRename {Γ = Γ} ρ (Λ M) = Λ ⊢-substCtx (sym (ctxWeaken-ctxRename ρ Γ)) (⊢-typeRename (typeExt ρ) M)
⊢-typeRename ρ (_∙_ {A = A} M B) rewrite typeRename-[]ₜ ρ A B = ⊢-typeRename ρ M ∙ typeRename ρ B

⊢-typeSubst
  : ∀ {Δ Δ' Γ}
  → (σ : TypeSubst Δ Δ')
  → ∀ {A} → Δ ؛ Γ ⊢ A → Δ' ؛ ctxSubst σ Γ ⊢ typeSubst σ A
⊢-typeSubst σ (` x) = ` ∋-map (typeSubst σ) x
⊢-typeSubst σ (ƛ M) = ƛ ⊢-typeSubst σ M
⊢-typeSubst σ (M · N) = ⊢-typeSubst σ M · ⊢-typeSubst σ N
⊢-typeSubst {Γ = Γ} σ (Λ M) = Λ ⊢-substCtx (sym (ctxWeaken-ctxSubst σ Γ)) (⊢-typeSubst (typeExts σ) M)
⊢-typeSubst σ (_∙_ {A = A} M B) rewrite typeSubst-[]ₜ σ A B = (⊢-typeSubst σ M) ∙ (typeSubst σ B)

exts' : ∀ {Δ Γ Γ'} → Subst Δ Γ Γ' → Subst (Δ ,·) (ctxWeaken Γ) (ctxWeaken Γ')
exts' {Γ = Γ , _} σ Z = ⊢-typeRename S_ (σ Z)
exts' {Γ = Γ , _} σ (S x) = exts' (σ ∘ S_) x

subst : ∀ {Δ Γ Γ'} → Subst Δ Γ Γ' → (∀ {A} → Δ ؛ Γ ⊢ A → Δ ؛ Γ' ⊢ A)
subst σ (` x) = σ x
subst σ (ƛ M) = ƛ subst (exts σ) M
subst σ (M · N) = subst σ M · subst σ N
subst σ (Λ M) = Λ subst (exts' σ) M
subst σ (M ∙ B) = subst σ M ∙ B

Z↦ : ∀ {Δ Γ B} → Δ ؛ Γ ⊢ B → Subst Δ (Γ , B) Γ
Z↦ N Z = N 
Z↦ N (S x) = ` x

_[_] : ∀ {Δ Γ A B}
     → Δ ؛ Γ , A ⊢ B
     → Δ ؛ Γ ⊢ A
     → Δ ؛ Γ ⊢ B
M [ N ]  = subst (Z↦ N) M

_[[_]] : ∀ {Δ Γ A}
     → Δ ,· ؛ ctxWeaken Γ ⊢ A
     → (B : Type Δ)
     → Δ ؛ Γ ⊢ A [ B ]ₜ
_[[_]] {Γ = Γ} {A = A} M B = ⊢-substCtx (ctxSubst-Z↦ₜ-ctxWeaken B Γ) (⊢-typeSubst (Z↦ₜ B) M)

-- Properties {{{

-- Congruence {{{

ext-cong
  : ∀ {Δ Γ Γ'} {ρ ρ' : Rename Δ Γ Γ'}
  → (∀ {A} → ρ {A} ≗ ρ' {A})
  → ∀ {B}
  → (∀ {A} → ext {B = B} ρ {A} ≗ ext {B = B} ρ' {A})
ext-cong ρ≗ρ' Z = refl
ext-cong ρ≗ρ' (S x) = cong S_ (ρ≗ρ' x)

ext'-cong
  : ∀ {Δ Γ Γ'} {ρ ρ' : Rename Δ Γ Γ'}
  → (∀ {A} → ρ {A} ≗ ρ' {A})
  → (∀ {A} → ext' ρ {A} ≗ ext' ρ' {A})
ext'-cong {Γ = Γ , _} ρ≗ρ' Z = cong (∋-map (typeRename S_)) (ρ≗ρ' Z)
ext'-cong {Γ = Γ , _} ρ≗ρ' (S x) = ext'-cong (ρ≗ρ' ∘ S_) x

rename-cong
  : ∀ {Δ Γ Γ'} {ρ ρ' : Rename Δ Γ Γ'}
  → (∀ {A} → ρ {A} ≗ ρ' {A})
  → (∀ {A} → rename ρ {A} ≗ rename ρ' {A})
rename-cong ρ≗ρ' (` x) = cong `_ (ρ≗ρ' x)
rename-cong ρ≗ρ' (ƛ M) = cong ƛ_ (rename-cong (ext-cong ρ≗ρ') M)
rename-cong ρ≗ρ' (M · N) = cong₂ _·_ (rename-cong ρ≗ρ' M) (rename-cong ρ≗ρ' N)
rename-cong ρ≗ρ' (Λ M) = cong Λ_ (rename-cong (ext'-cong ρ≗ρ') M)
rename-cong ρ≗ρ' (M ∙ B) = cong (_∙ B) (rename-cong ρ≗ρ' M)

exts-cong
  : ∀ {Δ Γ Γ'} {σ σ' : Subst Δ Γ Γ'}
  → (∀ {A} → σ {A} ≗ σ' {A})
  → ∀ {B}
  → (∀ {A} → exts {B = B} σ {A} ≗ exts {B = B} σ' {A})
exts-cong σ≗σ' Z = refl
exts-cong σ≗σ' (S x) = cong (rename S_) (σ≗σ' x)

exts'-cong
  : ∀ {Δ Γ Γ'} {σ σ' : Subst Δ Γ Γ'}
  → (∀ {A} → σ {A} ≗ σ' {A})
  → (∀ {A} → exts' σ {A} ≗ exts' σ' {A})
exts'-cong {Γ = Γ , _} σ≗σ' Z = cong (⊢-typeRename S_) (σ≗σ' Z)
exts'-cong {Γ = Γ , _} σ≗σ' (S x) = exts'-cong (σ≗σ' ∘ S_) x

subst-cong
  : ∀ {Δ Γ Γ'} {σ σ' : Subst Δ Γ Γ'}
  → (∀ {A} → σ {A} ≗ σ' {A})
  → (∀ {A} → subst σ {A} ≗ subst σ' {A})
subst-cong σ≗σ' (` x) = σ≗σ' x
subst-cong σ≗σ' (ƛ M) = cong ƛ_ (subst-cong (exts-cong σ≗σ') M)
subst-cong σ≗σ' (M · N) = cong₂ _·_ (subst-cong σ≗σ' M) (subst-cong σ≗σ' N)
subst-cong σ≗σ' (Λ M) = cong Λ_ (subst-cong (exts'-cong σ≗σ') M)
subst-cong σ≗σ' (M ∙ B) = cong (_∙ B) (subst-cong σ≗σ' M)

-- }}}

exts-∘
  : ∀ {Δ Γ Γ' Γ'' B}
  → (σ : Subst Δ Γ' Γ'')
  → (ρ : Rename Δ Γ Γ')
  → ∀ {A} → exts {B = B} (σ ∘ ρ) {A} ≗ exts σ ∘ ext ρ
exts-∘ σ ρ Z = refl
exts-∘ σ ρ (S x) = refl

ext'-S-∘ : ∀ {Δ Γ Γ' B} → (ρ : Rename Δ Γ Γ') → ∀ {A} → ext' {Γ' = Γ' , B} (S_ ∘ ρ) {A} ≗ S_ ∘ ext' ρ
ext'-S-∘ {Γ = Γ , _} ρ Z = refl
ext'-S-∘ {Γ = Γ , _} ρ (S x) = ext'-S-∘ (ρ ∘ S_) x

ext'-id : ∀ {Δ Γ} → ∀ {A} → ext' {Δ = Δ} {Γ = Γ} id {A} ≗ id
ext'-id {Γ = Γ , _} Z = refl
ext'-id {Γ = Γ , _} (S x) =
  begin
    ext' S_ x
  ≡⟨ ext'-S-∘ id x ⟩
    S (ext' id x)
  ≡⟨ cong S_ (ext'-id x) ⟩
    S x
  ∎
  where open ≡-Reasoning

ext'-typeWeaken : ∀ {Δ Γ Γ'} → (ρ : Rename Δ Γ Γ') → ∀ {A} → ext' ρ ∘ ∋-map typeWeaken ≗  ∋-map typeWeaken ∘ ρ {A}
ext'-typeWeaken ρ Z = refl
ext'-typeWeaken ρ (S x) = ext'-typeWeaken (ρ ∘ S_) x

ext'-∘
  : ∀ {Δ Γ Γ' Γ''}
  → (ρ' : Rename Δ Γ' Γ'')
  → (ρ : Rename Δ Γ Γ')
  → ∀ {A} → ext' (ρ' ∘ ρ) {A} ≗ ext' ρ' ∘ ext' ρ
ext'-∘ {Γ = Γ , _} ρ' ρ Z = sym (ext'-typeWeaken ρ' (ρ Z))
ext'-∘ {Γ = Γ , _} ρ' ρ (S x) = ext'-∘ ρ' (ρ ∘ S_) x

exts'-`-∘ : ∀ {Δ Γ Γ'} → (ρ : Rename Δ Γ Γ') →  ∀ {A} → exts' (`_ ∘ ρ) {A} ≗ `_ ∘ ext' ρ 
exts'-`-∘ {Γ = Γ , _} ρ Z = refl
exts'-`-∘ {Γ = Γ , _} ρ (S x) = exts'-`-∘ (ρ ∘ S_) x

exts'-` : ∀ {Δ Γ} → ∀ {A} → exts' {Δ = Δ} {Γ = Γ} `_ {A} ≗ `_
exts'-` x =
  begin
    exts' `_ x
  ≡⟨ exts'-`-∘ id x ⟩
    ` ext' id x
  ≡⟨ cong `_ (ext'-id x) ⟩
    ` x
  ∎
  where open ≡-Reasoning

exts'-typeWeaken : ∀ {Δ Γ Γ'} → (σ : Subst Δ Γ Γ') → ∀ {A} → exts' σ ∘ ∋-map typeWeaken ≗  ⊢-typeRename S_ ∘ σ {A}
exts'-typeWeaken σ Z = refl
exts'-typeWeaken σ (S x) = exts'-typeWeaken (σ ∘ S_) x

exts'-∘
  : ∀ {Δ Γ Γ' Γ''}
  → (σ : Subst Δ Γ' Γ'')
  → (ρ : Rename Δ Γ Γ')
  → ∀ {A} → exts' (σ ∘ ρ) {A} ≗ exts' σ ∘ ext' ρ
exts'-∘ {Γ = Γ , _} σ ρ Z = sym (exts'-typeWeaken σ (ρ Z))
exts'-∘ {Γ = Γ , _} σ ρ (S x) = exts'-∘ σ (ρ ∘ S_) x

subst-∘
  : ∀ {Δ Γ Γ' Γ''}
  → (σ : ∀ {A} → Δ ؛ Γ' ∋ A → Δ ؛ Γ'' ⊢ A)
  → (ρ : ∀ {A} → Δ ؛ Γ ∋ A → Δ ؛ Γ' ∋ A)
  → ∀ {A} → subst (σ ∘ ρ) {A} ≗ subst σ ∘ rename ρ
subst-∘ σ ρ (` x) = refl
subst-∘ σ ρ (ƛ M) =
  begin
    ƛ subst (exts (σ ∘ ρ)) M
  ≡⟨ cong ƛ_ (subst-cong (exts-∘ σ ρ) M) ⟩
    ƛ subst (exts σ ∘ ext ρ) M
  ≡⟨ cong ƛ_ (subst-∘ (exts σ) (ext ρ) M) ⟩
    ƛ subst (exts σ) (rename (ext ρ) M)
  ∎
  where open ≡-Reasoning
subst-∘ σ ρ (M · N) = cong₂ _·_ (subst-∘ σ ρ M) (subst-∘ σ ρ N)
subst-∘ σ ρ (Λ M) =
  begin
    Λ subst (exts' (σ ∘ ρ)) M
  ≡⟨ cong Λ_ (subst-cong (exts'-∘ σ ρ) M) ⟩
    Λ subst (exts' σ ∘ ext' ρ) M
  ≡⟨ cong Λ_ (subst-∘ (exts' σ) (ext' ρ) M) ⟩
    Λ subst (exts' σ) (rename (ext' ρ) M)
  ∎
  where open ≡-Reasoning
subst-∘ σ ρ (M ∙ B) = cong (_∙ B) (subst-∘ σ ρ M)

-- }}}

-- }}}

-- Reduction {{{

data _—→_ : ∀ {Δ Γ A} → Δ ؛ Γ ⊢ A →  Δ ؛ Γ ⊢ A → Set where
  β-ƛ
    : ∀ {Δ Γ A B}
    → {M : Δ ؛ Γ , A ⊢ B}
    → {N : Δ ؛ Γ ⊢ A}
      ------------------------
    → (ƛ M) · N —→ M [ N ]

  β-Λ
    : ∀ {Δ Γ A}
    → {M : Δ ,· ؛ ctxWeaken Γ ⊢ A}
    → {B : Type Δ}
      ----------------------------
    → (Λ M) ∙ B —→ M [[ B ]]

  ξ-ƛ
    : ∀ {Δ Γ A B}
    → {M M' : Δ ؛ Γ , A ⊢ B}
    → M —→ M'
      ----------------------
    → ƛ M —→ ƛ M'

  ξ-·ₗ
    : ∀ {Δ Γ A B}
    → {M M' : Δ ؛ Γ ⊢ A ⇒ B}
    → {N : Δ ؛ Γ ⊢ A}
    → M —→ M'
      ----------------------
    → M · N —→ M' · N

  ξ-·ᵣ
    : ∀ {Δ Γ A B}
    → {M : Δ ؛ Γ ⊢ A ⇒ B}
    → {N N' : Δ ؛ Γ ⊢ A}
    → N —→ N'
      -------------------
    → M · N —→ M · N'

  ξ-Λ
    : ∀ {Δ Γ A}
    → {M M' : Δ ,· ؛ ctxWeaken Γ ⊢ A}
    → M —→ M'
      -------------------------------
    → Λ M —→ Λ M'

  ξ-∙ₗ
    : ∀ {Δ Γ A}
    → {M M' : Δ ؛ Γ ⊢ `∀ A}
    → {B : Type Δ}
    → M —→ M'
      ---------------------
    → M ∙ B —→ M' ∙ B


data _—↠_ : ∀ {Δ Γ A} → (Δ ؛ Γ ⊢ A) → (Δ ؛ Γ ⊢ A) → Set where

  _∎ : ∀ {Δ Γ A} (M : Δ ؛ Γ ⊢ A)
      ------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Δ Γ A} (L : Δ ؛ Γ ⊢ A) {M N : Δ ؛ Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {Δ Γ A} {M N : Δ ؛ Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

_—↠⟨_⟩_ : ∀ {Δ Γ A} (L : Δ ؛ Γ ⊢ A) {M N : Δ ؛ Γ ⊢ A}
  → L —↠ M
  → M —↠ N
    ------
  → L —↠ N
L —↠⟨ _ ∎ ⟩ M-↠N = M-↠N
L —↠⟨ _ —→⟨ L—→L' ⟩ L'—↠M ⟩ M-↠N = L —→⟨ L—→L' ⟩ _ —↠⟨ L'—↠M ⟩ M-↠N

_≡⟨_⟩_ : ∀ {Δ Γ A} (L : Δ ؛ Γ ⊢ A) {M N : Δ ؛ Γ ⊢ A}
  → L ≡ M
  → M —↠ N
    ------
  → L —↠ N
L ≡⟨ refl ⟩ M-↠N = M-↠N

·-congₗ
  : ∀ {Δ Γ A B}
  → {M M' : Δ ؛ Γ ⊢ A ⇒ B}
  → {N : Δ ؛ Γ ⊢ A}
  → M —↠ M'
    ----------------------
  → M · N —↠ M' · N
·-congₗ (_ ∎) = _ ∎
·-congₗ (_ —→⟨ M—↠M₁ ⟩ M₁—↠M') = _ —→⟨ ξ-·ₗ M—↠M₁ ⟩ ·-congₗ M₁—↠M'

·-congᵣ
  : ∀ {Δ Γ A B}
  → {M : Δ ؛ Γ ⊢ A ⇒ B}
  → {N N' : Δ ؛ Γ ⊢ A}
  → N —↠ N'
  -------------------
  → M · N —↠ M · N'
·-congᵣ (_ ∎) = _ ∎
·-congᵣ (_ —→⟨ N—↠N₁ ⟩ N₁—↠N') = _ —→⟨ ξ-·ᵣ N—↠N₁ ⟩ ·-congᵣ N₁—↠N'

∙-congₗ
  : ∀ {Δ Γ A}
  → {M M' : Δ ؛ Γ ⊢ `∀ A}
  → {B : Type Δ}
  → M —↠ M'
    ----------------------
  → M ∙ B —↠ M' ∙ B
∙-congₗ (_ ∎) = _ ∎
∙-congₗ (_ —→⟨ M—↠M₁ ⟩ M₁—↠M') = _ —→⟨ ξ-∙ₗ M—↠M₁ ⟩ ∙-congₗ M₁—↠M'

Λ-cong
  : ∀ {Δ Γ A}
  → {M M' : (Δ ,·) ؛ ctxWeaken Γ ⊢ A}
  → M —↠ M'
    ----------------------
  → Λ M —↠ Λ M'
Λ-cong  (_ ∎) = _ ∎
Λ-cong (_ —→⟨ M—↠M₁ ⟩ M₁—↠M') = _ —→⟨ ξ-Λ M—↠M₁ ⟩ Λ-cong M₁—↠M'

ƛ-cong
  : ∀ {Δ Γ A B}
  → {M M' : Δ ؛ Γ , A ⊢ B}
  → M —↠ M'
    ----------------------
  → ƛ M —↠ ƛ M'
ƛ-cong  (_ ∎) = _ ∎
ƛ-cong (_ —→⟨ M—↠M₁ ⟩ M₁—↠M') = _ —→⟨ ξ-ƛ M—↠M₁ ⟩ ƛ-cong M₁—↠M'

-- }}}

-- Normal Form {{{

data Normal : ∀ {Δ Γ A} → Δ ؛ Γ ⊢ A → Set
data Neutral-· : ∀ {Δ Γ A} → Δ ؛ Γ ⊢ A → Set
data Neutral-∙ : ∀ {Δ Γ A} → Δ ؛ Γ ⊢ A → Set
data Neutral-·∙ : ∀ {Δ Γ A} → Δ ؛ Γ ⊢ A → Set

data Normal where
  ′_ 
    : ∀ {Δ Γ A} {M : Δ ؛ Γ ⊢ A}
    → Neutral-· M
    → Normal M

  ″_
    : ∀ {Δ Γ A} {M : Δ ؛ Γ ⊢ A}
    → Neutral-∙ M
    → Normal M

data Neutral-· where
  ″_ 
    : ∀ {Δ Γ A} {M : Δ ؛ Γ ⊢ A}
    → Neutral-·∙ M
    → Neutral-· M

  Λ_ 
    : ∀ {Δ Γ A} {M : (Δ ,·) ؛ ctxWeaken Γ ⊢ A}
    → Normal M
    → Neutral-· (Λ M)


data Neutral-∙ where
  ′_ 
    : ∀ {Δ Γ A} {M : Δ ؛ Γ ⊢ A}
    → Neutral-·∙ M
    → Neutral-∙ M

  ƛ_
    : ∀ {Δ Γ A B} {M : Δ ؛ Γ , A ⊢ B}
    → Normal M
    → Neutral-∙ (ƛ M)

data Neutral-·∙ where
  `_
    : ∀ {Δ Γ A}
    → (x : Δ ؛ Γ ∋ A)
    → Neutral-·∙ (` x)

  _·_ 
    : ∀ {Δ Γ A B} {M : Δ ؛ Γ ⊢ A ⇒ B} {N : Δ ؛ Γ ⊢ A}
    → Neutral-· M
    → Normal N
    → Neutral-·∙ (M · N)

  _∙_ 
    : ∀ {Δ Γ A} {M : Δ ؛ Γ ⊢ `∀ A}
    → Neutral-∙ M
    → (B : Type Δ)
    → Neutral-·∙ (M ∙ B)

‴_ 
  : ∀ {Δ Γ A} {M : Δ ؛ Γ ⊢ A}
  → Neutral-·∙ M
  → Normal M
‴ x = ′ (″ x)

normal-soundness
  : ∀ {Δ Γ A} {M : Δ ؛ Γ ⊢ A}
  → Normal M
  → ∃[ M' ] (M —→ M')
  → ⊥

neutral-·-soundness
  : ∀ {Δ Γ A} {M : Δ ؛ Γ ⊢ A}
  → Neutral-· M
  → ∃[ M' ] (M —→ M')
  → ⊥

neutral-∙-soundness
  : ∀ {Δ Γ A} {M : Δ ؛ Γ ⊢ A}
  → Neutral-∙ M
  → ∃[ M' ] (M —→ M')
  → ⊥

neutral-·∙-soundness
  : ∀ {Δ Γ A} {M : Δ ؛ Γ ⊢ A}
  → Neutral-·∙ M
  → ∃[ M' ] (M —→ M')
  → ⊥

normal-soundness (′ M) p = neutral-·-soundness M p
normal-soundness (″ M) p = neutral-∙-soundness M p
neutral-·-soundness (″ M) p = neutral-·∙-soundness M p
neutral-·-soundness (Λ M) ⟨ _ , ξ-Λ M—→M' ⟩ = normal-soundness M ⟨ _ , M—→M' ⟩
neutral-∙-soundness (′ M) p = neutral-·∙-soundness M p
neutral-∙-soundness (ƛ M) ⟨ _ , ξ-ƛ M—→M' ⟩ = normal-soundness M ⟨ _ , M—→M' ⟩
neutral-·∙-soundness (M ∙ B) ⟨ _ , ξ-∙ₗ M—→M' ⟩ = neutral-∙-soundness M ⟨ _ , M—→M' ⟩
neutral-·∙-soundness ((′ ()) ∙ B) ⟨ _ , β-Λ ⟩
neutral-·∙-soundness (M · N) ⟨ _ , ξ-·ₗ M—→M' ⟩ = neutral-·-soundness M ⟨ _ , M—→M' ⟩
neutral-·∙-soundness (M · N) ⟨ _ , ξ-·ᵣ N—→N' ⟩ = normal-soundness N ⟨ _ , N—→N' ⟩
neutral-·∙-soundness ((″ ()) · N) ⟨ _ , β-ƛ ⟩

normal-completeness
  : ∀ {Δ Γ A} {M : Δ ؛ Γ ⊢ A}
  → (∃[ M' ] (M —→ M') → ⊥)
  → Normal M
normal-completeness {M = ` x} p = ‴ (` x)
normal-completeness {M = ƛ M} p = ″ (ƛ normal-completeness (p ∘ (λ (⟨ _ , M—→M' ⟩) → ⟨ _ , ξ-ƛ M—→M' ⟩)))
normal-completeness {M = M · N} p with normal-completeness (p ∘ (λ (⟨ _ , M—→M' ⟩) → ⟨ _ , ξ-·ₗ M—→M' ⟩))
... | ′ neutral-·-M = ‴ (neutral-·-M · normal-completeness (p ∘ (λ  (⟨ _ , N—→N' ⟩) → ⟨ _ , ξ-·ᵣ N—→N' ⟩)))
... | ″ (′ neutral-·∙-M) = ‴ ((″ neutral-·∙-M) · normal-completeness (p ∘ (λ  (⟨ _ , N—→N' ⟩) → ⟨ _ , ξ-·ᵣ N—→N' ⟩)))
... | ″ (ƛ_ {M = M₁} _) = ⊥-elim (p ⟨ M₁ [ N ] , β-ƛ ⟩)
normal-completeness {M = Λ M} p = ′ (Λ normal-completeness (p ∘ (λ (⟨ _ , M—→M' ⟩) → ⟨ _ , ξ-Λ M—→M' ⟩)))
normal-completeness {M = M ∙ B} p with normal-completeness (p ∘ (λ (⟨ _ , M—→M' ⟩) → ⟨ _ , ξ-∙ₗ M—→M' ⟩))
... | ″ neutral-∙-M = ‴ (neutral-∙-M ∙ B)
... | ′ (″ neutral-·∙-M) = ‴ ((′ neutral-·∙-M) ∙ B)
... | ′ (Λ_ {M = M₁} _) = ⊥-elim (p ⟨ (M₁ [[ B ]]) , β-Λ ⟩)

-- }}}
