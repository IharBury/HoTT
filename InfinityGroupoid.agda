{-# OPTIONS --safe --without-K --guardedness #-}

module InfinityGroupoid where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Primitive

record ZeroGroupoid {ℓ} (T0 : Set ℓ) : Set (lsuc ℓ) where

zeroGroupoidFromTypes : ∀ {ℓ} (A : Set ℓ) → ZeroGroupoid A
zeroGroupoidFromTypes A = record{}

record SucGroupoidParts {ℓ} (T0 : Set ℓ) (T1 : T0 → T0 → Set ℓ) (T2 : (x y : T0) → T1 x y → T1 x y → Set ℓ) : Set ℓ where
    field
        id : ∀ x → T1 x x
        _∘_ : ∀ {x y z} → T1 y z → T1 x y → T1 x z
        _⁻¹ : ∀ {x y} → T1 x y → T1 y x
        id∘ : ∀ {x y} (f : T1 x y) → T2 x y (id y ∘ f) f
        ∘id : ∀ {x y} (f : T1 x y) → T2 x y (f ∘ id x) f
        assoc : ∀ {x y z t} (f : T1 x y) (g : T1 y z) (h : T1 z t) → T2 x t ((h ∘ g) ∘ f) (h ∘ (g ∘ f))
        ⁻¹∘ : ∀ {x y} (f : T1 x y) → T2 x x ((f ⁻¹) ∘ f) (id x)
        ∘⁻¹ : ∀ {x y} (f : T1 x y) → T2 y y (f ∘ (f ⁻¹)) (id y)

record OneGroupoid {ℓ} (T0 : Set ℓ) (T1 : T0 → T0 → Set ℓ) : Set (lsuc ℓ) where
    field
        next : (x y : T0) → ZeroGroupoid (T1 x y)
        parts : SucGroupoidParts T0 T1 (λ _ _ p q → p ≡ q)

sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

oneGroupoidFromTypes : ∀ {ℓ} (A : Set ℓ) → OneGroupoid A (λ x y → x ≡ y)
oneGroupoidFromTypes A = record
    { next = λ x y → zeroGroupoidFromTypes (x ≡ y)
    ; parts = record
        { id = λ _ → refl
        ; _∘_ = λ q p → trans p q
        ; _⁻¹ = sym
        ; id∘ = λ where refl → refl
        ; ∘id = λ where refl → refl
        ; assoc = λ where refl refl refl → refl
        ; ⁻¹∘ = λ where refl → refl
        ; ∘⁻¹ = λ where refl → refl
        }
    }

record TwoGroupoid ℓ (T0 : Set ℓ) (T1 : T0 → T0 → Set ℓ) : Set (lsuc ℓ) where
    field
        T2 : (x y : T0) → T1 x y → T1 x y → Set ℓ
        next : (x y : T0) → OneGroupoid (T1 x y) (T2 x y)
        parts : SucGroupoidParts T0 T1 T2

twoGroupoidFromTypes : ∀ {ℓ} (A : Set ℓ) → TwoGroupoid ℓ A (λ x y → x ≡ y)
twoGroupoidFromTypes A = record
    { next = λ x y → oneGroupoidFromTypes (x ≡ y)
    ; parts = record
        { id = λ _ → refl
        ; _∘_ = λ q p → trans p q
        ; _⁻¹ = sym
        ; id∘ = λ where refl → refl
        ; ∘id = λ where refl → refl
        ; assoc = λ where refl refl refl → refl
        ; ⁻¹∘ = λ where refl → refl
        ; ∘⁻¹ = λ where refl → refl
        }
    }

data FinGroupoid ℓ : (T0 : Set ℓ) → (T0 → T0 → Set ℓ) → Nat → Set (lsuc ℓ) where
    zeroGroupoid : (T0 : Set ℓ) → FinGroupoid ℓ T0 (λ x y → x ≡ y) 0
    sucGroupoid :
        (n : Nat)
        (T0 : Set ℓ)
        (T1 : T0 → T0 → Set ℓ)
        (T2 : (x y : T0) → T1 x y → T1 x y → Set ℓ)
        (next : (x y : T0) → FinGroupoid ℓ (T1 x y) (T2 x y) n)
        (parts : SucGroupoidParts T0 T1 T2)
        → FinGroupoid ℓ T0 T1 (suc n)

finGroupoidFromTypes : ∀ {ℓ} (A : Set ℓ) (n : Nat) → FinGroupoid ℓ A (λ x y → x ≡ y) n
finGroupoidFromTypes A zero = zeroGroupoid A
finGroupoidFromTypes A (suc n) = sucGroupoid
    n
    A
    (λ x y → x ≡ y)
    (λ _ _ p q → p ≡ q)
    (λ x y → finGroupoidFromTypes (x ≡ y) n)
    (record
        { id = λ _ → refl
        ; _∘_ = λ q p → trans p q
        ; _⁻¹ = sym
        ; id∘ = λ where refl → refl
        ; ∘id = λ where refl → refl
        ; assoc = λ where refl refl refl → refl
        ; ⁻¹∘ = λ where refl → refl
        ; ∘⁻¹ = λ where refl → refl
        })

record InfinityGroupoid ℓ (T0 : Set ℓ) (T1 : T0 → T0 → Set ℓ) : Set (lsuc ℓ) where
    coinductive
    field
        T2 : (x y : T0) → T1 x y → T1 x y → Set ℓ
        next : (x y : T0) → InfinityGroupoid ℓ (T1 x y) (T2 x y)
        parts : SucGroupoidParts T0 T1 T2

infinityGroupoidFromTypes : ∀ {ℓ} (A : Set ℓ) → InfinityGroupoid ℓ A (λ x y → x ≡ y)
InfinityGroupoid.T2 (infinityGroupoidFromTypes A) _ _ p q = p ≡ q
InfinityGroupoid.next (infinityGroupoidFromTypes A) x y = infinityGroupoidFromTypes (x ≡ y)
InfinityGroupoid.parts (infinityGroupoidFromTypes A) = record
    { id = λ _ → refl
    ; _∘_ = λ q p → trans p q
    ; _⁻¹ = sym
    ; id∘ = λ where refl → refl
    ; ∘id = λ where refl → refl
    ; assoc = λ where refl refl refl → refl
    ; ⁻¹∘ = λ where refl → refl
    ; ∘⁻¹ = λ where refl → refl
    }

-- This inductive type is valid but cannot be constructed due to termination issue:
--
-- record InfinityGroupoid ℓ (T0 : Set ℓ) (T1 : T0 → T0 → Set ℓ) : Set (lsuc ℓ) where
--     inductive
--     field
--         T2 : (x y : T0) → T1 x y → T1 x y → Set ℓ
--         next : (x y : T0) → InfinityGroupoid ℓ (T1 x y) (T2 x y)
--         parts : SucGroupoidParts T0 T1 T2
--
-- infinityGroupoidFromTypes A = record
--     { T2 = λ _ _ p q → p ≡ q
--     ; next = λ x y → infinityGroupoidFromTypes (x ≡ y)
--     ; parts = record
--         { id = λ _ → refl
--         ; _∘_ = λ q p → trans p q
--         ; _⁻¹ = sym
--         ; id∘ = λ where refl → refl
--         ; ∘id = λ where refl → refl
--         ; assoc = λ where refl refl refl → refl
--         ; ⁻¹∘ = λ where refl → refl
--         ; ∘⁻¹ = λ where refl → refl
--         }
--     }
