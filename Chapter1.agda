{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
import Cubical.Data.Nat
import Cubical.Data.Prod
import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude

module Chapter1 where

module ex-1-1 where

    variable ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    variable A : Set ℓ₁
    variable B : Set ℓ₂
    variable C : Set ℓ₃
    variable D : Set ℓ₄
    variable h : C → D
    variable g : B → C
    variable f : A → B

    _∘_ : (B → C) → (A → B) → A → C
    _∘_ g f a = g (f a)

    ex1-1 : h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    ex1-1 = refl

module ex-1-2-1 where

    open Cubical.Data.Prod

    variable ℓ₁ ℓ₂ ℓ₃ : Level
    variable A : Set ℓ₁
    variable B : Set ℓ₂
    variable C : Set ℓ₃

    ex1-2-1 : (A → B → C) → A × B → C
    ex1-2-1 A→B→C A×B = A→B→C (proj₁ A×B) (proj₂ A×B)

module ex-1-2-2 where

    open Cubical.Data.Sigma

    variable ℓ₁ ℓ₂ ℓ₃ : Level
    variable A : Set ℓ₁
    variable B : Set ℓ₂
    variable C : Set ℓ₃
    variable f : A → B

    ex1-2-2 : ((a : A) → f a → C) → Σ A f → C
    ex1-2-2 A→f-a→C ΣA-f = A→f-a→C (fst ΣA-f) (snd ΣA-f)

module ex-1-3-1 where

    open Cubical.Data.Prod

    variable ℓ₁ ℓ₂ ℓ₃ : Level
    variable A : Set ℓ₁
    variable B : Set ℓ₂

    uniq-A×B : (A×B : A × B) → (proj₁ A×B , proj₂ A×B) ≡ A×B
    uniq-A×B (_ , _) = refl

    ex1-3-1 : (C : A × B → Set ℓ₃) → ((a : A) (b : B) → C ( a , b )) → (A×B : A × B) → C A×B
    ex1-3-1 C A→B→C-[a,b] A×B = transport (cong C (uniq-A×B A×B)) (A→B→C-[a,b] (proj₁ A×B) (proj₂ A×B))

module ex-1-3-2 where

    open Cubical.Data.Sigma

    variable ℓ₁ ℓ₂ ℓ₃ : Level
    variable A : Set ℓ₁
    variable B : Set ℓ₂
    variable f : A → B

    uniq-ΣA-f : (ΣA-f : Σ A f) → (fst ΣA-f , snd ΣA-f) ≡ ΣA-f
    uniq-ΣA-f (_ , _) = refl

    ex-1-3-2 : (C : Σ A f → Set ℓ₃) → ((a : A) (f-a : f a) → C ( a , f-a )) → (ΣA-f : Σ A f) → C ΣA-f
    ex-1-3-2 C A→f-a→C-[a,f-a] ΣA-f = transport (cong C (uniq-ΣA-f ΣA-f)) (A→f-a→C-[a,f-a] (fst ΣA-f) (snd ΣA-f))

module ex-1-4 where

    open Cubical.Data.Nat using (ℕ; suc; zero)
    open Cubical.Data.Prod

    iter : ∀ {ℓ} (C : Set ℓ) → C → (C → C) → ℕ → C
    iter C c₀ cₛ 0 = c₀
    iter C c₀ cₛ (suc n) = cₛ (iter C c₀ cₛ n)

    rec-ℕ : ∀ {ℓ} (C : Set ℓ) → C → (ℕ → C → C) → ℕ → C
    rec-ℕ C c₀ cₛ n = proj₂ (iter (ℕ × C) (0 , c₀) (λ ℕ×C → suc (proj₁ ℕ×C) , cₛ (proj₁ ℕ×C) (proj₂ ℕ×C)) n)
    
    ex-1-4-1 : ∀ {ℓ} (C : Set ℓ) c₀ cₛ → rec-ℕ C c₀ cₛ 0 ≡ c₀
    ex-1-4-1 _ _ _ = refl

    ex-1-4-2 : ∀ {ℓ} (C : Set ℓ) c₀ cₛ n → rec-ℕ C c₀ cₛ (suc n) ≡ cₛ n (rec-ℕ C c₀ cₛ n)
    ex-1-4-2 C c₀ cₛ n = cong (λ z → cₛ z (rec-ℕ C c₀ cₛ n)) (lemma n) where
        lemma : ∀ n → proj₁ (iter (ℕ × C) (0 , c₀) (λ ℕ×C → suc (proj₁ ℕ×C) , cₛ (proj₁ ℕ×C) (proj₂ ℕ×C)) n) ≡ n
        lemma zero = refl
        lemma (suc n) = cong suc (lemma n)

module ex-1-5 where

    open Cubical.Data.Sigma

    data 𝟚 : Set where
        0₂ : 𝟚
        1₂ : 𝟚

    rec-𝟚 : ∀ {ℓ} {C : Set ℓ} → C → C → 𝟚 → C
    rec-𝟚 c₀ _ 0₂ = c₀
    rec-𝟚 _ c₁ 1₂ = c₁

    _+_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
    A + B = Σ 𝟚 (λ x → rec-𝟚 A B x)

    inl : ∀ {ℓ} {A B : Set ℓ} → A → A + B
    inl a = 0₂ , a

    inr : ∀ {ℓ} {A B : Set ℓ} → B → A + B
    inr b = 1₂ , b

    ind-A+B : ∀ {ℓ₁ ℓ₂} {A B : Set ℓ₁} (C : A + B → Set ℓ₂) → ((a : A) → C (inl a)) → ((b : B) → C (inr b)) → (A+B : A + B) → C A+B
    ind-A+B C A→C-[inl-a] B→C-[inr-b] (0₂ , A) = A→C-[inl-a] A
    ind-A+B C A→C-[inl-a] B→C-[inr-b] (1₂ , B) = B→C-[inr-b] B

    ex-1-5-1 : ∀ {ℓ₁ ℓ₂} {A B : Set ℓ₁} (C : A + B → Set ℓ₂) (g₀ : (a : A) → C (inl a)) (g₁ : (b : B) → C (inr b)) → (a : A) → ind-A+B C g₀ g₁ (inl a) ≡ g₀ a
    ex-1-5-1 _ _ _ _ = refl

    ex-1-5-2 : ∀ {ℓ₁ ℓ₂} {A B : Set ℓ₁} (C : A + B → Set ℓ₂) (g₀ : (a : A) → C (inl a)) (g₁ : (b : B) → C (inr b)) → (b : B) → ind-A+B C g₀ g₁ (inr b) ≡ g₁ b
    ex-1-5-2 _ _ _ _ = refl

module ex-1-6 where

    variable ℓ₁ ℓ₂ : Level
    variable A B : Set ℓ₁

    data 𝟚 : Set where
        0₂ : 𝟚
        1₂ : 𝟚

    rec-𝟚 : A → A → 𝟚 → A
    rec-𝟚 a₀ _ 0₂ = a₀
    rec-𝟚 _ a₁ 1₂ = a₁

    _×_ : Set ℓ₁ → Set ℓ₁ → Set ℓ₁
    A × B = (x : 𝟚) → rec-𝟚 A B x

    pair : A → B → A × B
    pair a _ 0₂ = a
    pair _ b 1₂ = b

    proj₁ : A × B → A
    proj₁ A×B = A×B 0₂

    proj₂ : A × B → B
    proj₂ A×B = A×B 1₂

    uniq-A×B-app : ∀ (A×B : A × B) x → pair (proj₁ A×B) (proj₂ A×B) x ≡ A×B x
    uniq-A×B-app _ 0₂ = refl
    uniq-A×B-app _ 1₂ = refl

    uniq-A×B : (A×B : A × B) → pair (proj₁ A×B) (proj₂ A×B) ≡ A×B
    uniq-A×B A×B = funExt (uniq-A×B-app A×B)

    ind-A×B : (C : A × B → Set ℓ₂) → (∀ a b → C (pair a b)) → ∀ A×B → C A×B
    ind-A×B C D A×B = transport (cong C (uniq-A×B A×B)) (D (proj₁ A×B) (proj₂ A×B))

    ex-1-6 : (C : A × B → Set ℓ₂) → ∀ D a b → ind-A×B C D (pair a b) ≡ D a b
    ex-1-6 C D a b =
            ind-A×B C D (pair a b)
        ≡⟨⟩
            transport (cong C (uniq-A×B (pair a b))) (D (proj₁ (pair a b)) (proj₂ (pair a b)))
        ≡⟨⟩
            transport (cong C (uniq-A×B (pair a b))) (D a b)
        ≡⟨⟩
            transport (cong C (funExt (uniq-A×B-app (pair a b)))) (D a b)
        ≡⟨ cong (λ x → transport x (D a b)) lemma ⟩
            transport refl (D a b)
        ≡⟨ transportRefl (D a b) ⟩
            D a b
        ∎
        where
            lemma : cong C (funExt (uniq-A×B-app (pair a b))) ≡ refl 
            lemma = transport (cong (λ x → cong C (funExt x) ≡ refl) λ{ _ 0₂ → refl ; _ 1₂ → refl}) refl
 