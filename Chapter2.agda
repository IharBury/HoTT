{-# OPTIONS --cubical #-}

import Cubical.Algebra.CommMonoid.Base
import Cubical.Algebra.Monoid.Base
import Cubical.Algebra.Semigroup.Base
open import Cubical.Core.Everything
open import Cubical.Data.Empty
import Cubical.Data.Nat
import Cubical.Data.Nat.Order
import Cubical.Data.Prod
import Cubical.Data.Sigma
import Cubical.Data.Sum
import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary

module Chapter2 where

module ex-2-1 where

    H : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} →
        (C : (x y : A) → x ≡ y → Type ℓ₂) →
        ((x : A) → C x x refl) →
        (x y : A) (x≡y : x ≡ y) →
        C x y x≡y
    H C c x y x≡y = J (C x) (c x) x≡y

    proof0 : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    proof0 {ℓ} {A} {x} {y} {z} p = lemma x y p z where
        D : (x y : A) → x ≡ y → Type ℓ
        D x y p = (z : A) (q : y ≡ z) → x ≡ z
        E : (x z : A) → x ≡ z → Type ℓ
        E x z q = x ≡ z
        e : (x : A) → E x x refl
        e _ = refl
        d : (x z : A) (q : x ≡ z) → E x z q
        d = H E e
        lemma : (x y : A) → x ≡ y → (z : A) → y ≡ z → x ≡ z
        lemma = H D d

    proof1 : ∀ {ℓ} (A : Type ℓ) (x y z : A) → x ≡ y → y ≡ z → x ≡ z
    proof1 _ x y z = H (λ x₁ y₁ _ → y₁ ≡ z → x₁ ≡ z)
        (λ x₁ → H (λ x₁ z₁ _ → x₁ ≡ z₁) (λ _ → refl) x₁ z) x y

    proof2 : ∀ {ℓ} (A : Type ℓ) (x y z : A) → x ≡ y → y ≡ z → x ≡ z
    proof2 _ x y z = H (λ x₁ y₁ _ → y₁ ≡ z → x₁ ≡ z)
        (λ _ q → q) x y

    proof3 : ∀ {ℓ} (A : Type ℓ) (x y z : A) → x ≡ y → y ≡ z → x ≡ z
    proof3 _ x y z p q = H (λ y₁ z₁ _ → x ≡ y₁ → x ≡ z₁)
        (λ _ p₁ → p₁) y z q p

    H-refl : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : (x y : A) → x ≡ y → Type ℓ₂)
        (P-refl : ∀ x → P x x refl) {x : A} →
        H P P-refl x x refl ≡ P-refl x
    H-refl P P-refl {x} = transportRefl (P-refl x)

    proof1≡2 : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) →
        proof1 A x y z p q ≡ proof2 A x y z p q
    proof1≡2 {ℓ} {A} {x} {y} {z} = H
        (λ x₁ y₁ p₁ → ∀ (q₁ : y₁ ≡ z) →
            proof1 A x₁ y₁ z p₁ q₁ ≡ proof2 A x₁ y₁ z p₁ q₁)
        (λ x₁ → H
            (λ x₂ z₁ q₁ →
                proof1 A x₂ x₂ z₁ refl q₁ ≡ proof2 A x₂ x₂ z₁ refl q₁)
                lemma x₁ z) x y where
        lemma : ∀ x₁ →
            proof1 A x₁ x₁ x₁ refl refl ≡ proof2 A x₁ x₁ x₁ refl refl
        lemma x₁ = 
                proof1 A x₁ x₁ x₁ refl refl
            ≡⟨ cong (λ v → v refl)
                (H-refl (λ x₂ y₁ _ → y₁ ≡ x₁ → x₂ ≡ x₁)
                    (λ x₂ → H (λ x₁ z₁ _ → x₁ ≡ z₁) (λ _ → refl) x₂ x₁)) ⟩
                (J (λ z₁ _ → x₁ ≡ z₁) refl) refl
            ≡⟨ (J-refl (λ z₁ _ → x₁ ≡ z₁) refl) ⟩
                refl
            ≡⟨ sym (cong (λ v → v refl)
                (H-refl (λ x₂ y₁ _ → y₁ ≡ x₁ → x₂ ≡ x₁) (λ x₂ q → q))) ⟩
                proof2 A x₁ x₁ x₁ refl refl
            ∎

    proof1≡3 : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) →
        proof1 A x y z p q ≡ proof3 A x y z p q
    proof1≡3 {ℓ} {A} {x} {y} {z} = H
        (λ x₁ y₁ p₁ → ∀ (q₁ : y₁ ≡ z) →
            proof1 A x₁ y₁ z p₁ q₁ ≡ proof3 A x₁ y₁ z p₁ q₁)
        (λ x₁ → H
            (λ x₂ z₁ q₁ →
                proof1 A x₂ x₂ z₁ refl q₁ ≡ proof3 A x₂ x₂ z₁ refl q₁)
            lemma x₁ z) x y where
        lemma : ∀ x₁ →
            proof1 A x₁ x₁ x₁ refl refl ≡ proof3 A x₁ x₁ x₁ refl refl
        lemma x₁ =
                proof1 A x₁ x₁ x₁ refl refl
            ≡⟨ cong (λ v → v refl)
                (H-refl (λ x₂ y₁ _ → y₁ ≡ x₁ → x₂ ≡ x₁)
                    (λ x₂ → H (λ x₁ z₁ _ → x₁ ≡ z₁) (λ _ → refl) x₂ x₁)) ⟩
                (J (λ z₁ _ → x₁ ≡ z₁) refl) refl
            ≡⟨ (J-refl (λ z₁ _ → x₁ ≡ z₁) refl) ⟩
                refl
            ≡⟨ sym (cong (λ v → v refl)
                (H-refl (λ y₁ z₁ _ → x₁ ≡ y₁ → x₁ ≡ z₁) λ x₂ p → p)) ⟩
                proof3 A x₁ x₁ x₁ refl refl
            ∎

module ex-2-1-J where

    proof1 : ∀ {ℓ} (A : Type ℓ) (x y z : A) → x ≡ y → y ≡ z → x ≡ z
    proof1 _ x _ z = J (λ y₁ _ → y₁ ≡ z → x ≡ z) (J (λ z₁ _ → x ≡ z₁) refl)

    proof2 : ∀ {ℓ} (A : Type ℓ) (x y z : A) → x ≡ y → y ≡ z → x ≡ z
    proof2 _ x _ z = J (λ y₁ _ → y₁ ≡ z → x ≡ z) (λ q → q)

    proof3 : ∀ {ℓ} (A : Type ℓ) (x y z : A) → x ≡ y → y ≡ z → x ≡ z
    proof3 _ x _ _ p = J (λ z₁ _ → x ≡ z₁) p

    J-refl : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {x : A}
        (P : (y : A) → x ≡ y → Type ℓ₂)
        (P-refl : P x refl) → J P P-refl refl ≡ P-refl
    J-refl P = transportRefl

    proof1≡2 : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) →
        proof1 A x y z p q ≡ proof2 A x y z p q
    proof1≡2 {ℓ} {A} {x} {y} {z} = J
        (λ y₁ p₁ → ∀ (q₁ : y₁ ≡ z) →
            proof1 A x y₁ z p₁ q₁ ≡ proof2 A x y₁ z p₁ q₁)
        (J (λ z₁ q₁ → proof1 A x x z₁ refl q₁ ≡ proof2 A x x z₁ refl q₁)
            lemma) where
        lemma : proof1 A x x x refl refl ≡ proof2 A x x x refl refl
        lemma =
                proof1 A x x x refl refl
            ≡⟨ cong (λ v → v refl)
                (J-refl (λ y₁ _ → y₁ ≡ x → x ≡ x)
                    (J (λ z₁ _ → x ≡ z₁) refl)) ⟩
                (J (λ z₁ _ → x ≡ z₁) refl) refl
            ≡⟨ (J-refl (λ z₁ _ → x ≡ z₁) refl) ⟩
                refl
            ≡⟨ sym (cong (λ v → v refl)
                (J-refl (λ y₁ _ → y₁ ≡ x → x ≡ x) (λ q → q))) ⟩
                proof2 A x x x refl refl
            ∎

    proof1≡3 : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) →
        proof1 A x y z p q ≡ proof3 A x y z p q
    proof1≡3 {ℓ} {A} {x} {y} {z} = J
        (λ y₁ p₁ → ∀ (q₁ : y₁ ≡ z) →
            proof1 A x y₁ z p₁ q₁ ≡ proof3 A x y₁ z p₁ q₁)
        (J (λ z₁ q₁ → proof1 A x x z₁ refl q₁ ≡ proof3 A x x z₁ refl q₁)
            lemma) where
        lemma : proof1 A x x x refl refl ≡ proof3 A x x x refl refl
        lemma =
                proof1 A x x x refl refl
            ≡⟨ cong (λ v → v refl)
                (J-refl (λ y₁ _ → y₁ ≡ x → x ≡ x)
                    (J (λ z₁ _ → x ≡ z₁) refl)) ⟩
                (J (λ z₁ _ → x ≡ z₁) refl) refl
            ≡⟨ (J-refl (λ z₁ _ → x ≡ z₁) refl) ⟩
                refl
            ≡⟨ sym (J-refl (λ z₁ _ → x ≡ z₁) refl) ⟩
                proof3 A x x x refl refl
            ∎
