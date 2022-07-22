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
 
module ex-1-7 where

    open Cubical.Data.Sigma
    open Cubical.Foundations.Function

    ind-≡ : {A : Set} → (C : (x y : A) → x ≡ y → Set) → ((x : A) → C x x refl) → (x y : A) (x≡y : x ≡ y) → C x y x≡y
    ind-≡ C c x y x≡y = J (C x) (c x) x≡y

    ind′-≡ : {A : Set} → (a : A) (C : (x : A) → a ≡ x → Set) → C a refl → (x : A) (a≡x : a ≡ x) → C x a≡x
    ind′-≡ {A} a C C-a-refl x a≡x = transport (cong (uncurry C) lemma) C-a-refl where
        lemma : (a , refl) ≡ (x , a≡x)
        lemma = snd (isContrSingl a) (x , a≡x)
  
module ex-1-8 where

    open Cubical.Algebra.CommMonoid.Base
    open Cubical.Algebra.Monoid.Base
    open Cubical.Algebra.Semigroup.Base
    open Cubical.Data.Nat using (ℕ; zero; suc; _+_; isSetℕ)
    open Cubical.Data.Sigma

    rec-ℕ : ∀ {ℓ} {C : Set ℓ} → C → (ℕ → C → C) → ℕ → C
    rec-ℕ c₀ cₛ zero = c₀
    rec-ℕ c₀ cₛ (suc n) = cₛ n (rec-ℕ c₀ cₛ n)

    ind-ℕ : ∀ {ℓ} (C : ℕ → Set ℓ) → C 0 → (∀ n → C n → C (suc n)) → ∀ n → C n
    ind-ℕ C c₀ cₛ zero = c₀
    ind-ℕ C c₀ cₛ (suc n) = cₛ n (ind-ℕ C c₀ cₛ n)

    _·_ : ℕ → ℕ → ℕ
    n · m = rec-ℕ 0 (λ n₁ n₁·m → m + n₁·m) n

    _^_ : ℕ → ℕ → ℕ
    n ^ m = rec-ℕ 1 (λ m₁ n^m₁ → n · n^m₁) m

    +-assoc : ∀ x y z → x + (y + z) ≡ x + y + z
    +-assoc x y z = ind-ℕ (λ x₁ → x₁ + (y + z) ≡ x₁ + y + z) refl (λ _ x₁+[y+z]≡x₁+y+z → cong suc x₁+[y+z]≡x₁+y+z) x

    +-zero : ∀ x → x + 0 ≡ x
    +-zero x = ind-ℕ (λ x₁ → x₁ + 0 ≡ x₁) refl (λ _ x₁+0≡x₁ → cong suc x₁+0≡x₁) x

    +-suc : ∀ x y → x + suc y ≡ suc (x + y)
    +-suc x y = ind-ℕ (λ x₁ → x₁ + suc y ≡ suc (x₁ + y)) refl (λ _ x₁+suc-y≡suc-[x+y] → cong suc x₁+suc-y≡suc-[x+y]) x

    +-comm : ∀ x y → x + y ≡ y + x
    +-comm x y = ind-ℕ (λ x₁ → x₁ + y ≡ y + x₁) (sym (+-zero y)) lemma₂ x where
        lemma₁ : (x₁ : ℕ) → (suc (x₁ + y) ≡ suc (y + x₁)) ≡ (suc (x₁ + y) ≡ y + suc x₁)
        lemma₁ x₁ = cong (λ v → suc (x₁ + y) ≡ v) (sym (+-suc y x₁))
        lemma₂ : (x₁ : ℕ) → x₁ + y ≡ y + x₁ → suc (x₁ + y) ≡ (y + suc x₁)
        lemma₂ x₁ x₁+y≡y+x₁ = transport (lemma₁ x₁) (cong suc x₁+y≡y+x₁)

    0≡m·0 : ∀ x → 0 ≡ x · 0
    0≡m·0 x = ind-ℕ (λ x₁ → 0 ≡ x₁ · 0) refl (λ x₁ 0≡x₁·0 → 0≡x₁·0) x

    ·-suc : ∀ x y → x · suc y ≡ x + x · y
    ·-suc x y = ind-ℕ (λ x₁ → x₁ · suc y ≡ x₁ + x₁ · y) refl lemma x where
        lemma : (x₁ : ℕ) → x₁ · suc y ≡ x₁ + x₁ · y → suc x₁ · suc y ≡ suc x₁ + suc x₁ · y
        lemma x₁ x₁·suc-y≡x₁+x₁·y =
                suc x₁ · suc y
            ≡⟨⟩
                suc y + x₁ · suc y
            ≡⟨ cong (λ v → suc y + v) x₁·suc-y≡x₁+x₁·y ⟩
                suc y + (x₁ + x₁ · y)
            ≡⟨ +-assoc (suc y) x₁ (x₁ · y) ⟩
                suc y + x₁ + x₁ · y
            ≡⟨⟩
                suc (y + x₁) + x₁ · y
            ≡⟨ cong (λ v → suc v + x₁ · y) (+-comm y x₁) ⟩
                suc (x₁ + y) + x₁ · y
            ≡⟨⟩
                suc x₁ + y + x₁ · y
            ≡⟨ sym (+-assoc (suc x₁) y (x₁ · y)) ⟩
                suc x₁ + (y + x₁ · y)
            ≡⟨⟩
                suc x₁ + suc x₁ · y
            ∎

    ·-comm : ∀ x y → x · y ≡ y · x
    ·-comm x y = ind-ℕ (λ x₁ → x₁ · y ≡ y · x₁) (0≡m·0 y) lemma x where
        lemma : (x₁ : ℕ) → x₁ · y ≡ y · x₁ → suc x₁ · y ≡ y · suc x₁
        lemma x₁ x₁·y≡y·x₁ =
                suc x₁ · y
            ≡⟨⟩
                y + x₁ · y
            ≡⟨ cong (λ v → y + v) x₁·y≡y·x₁ ⟩
                y + y · x₁
            ≡⟨ sym (·-suc y x₁) ⟩
                y · suc x₁
            ∎

    ·-distribˡ : ∀ x y z → x · y + x · z ≡ x · (y + z)
    ·-distribˡ x y z = ind-ℕ (λ x₁ → x₁ · y + x₁ · z ≡ x₁ · (y + z)) refl lemma x where
        lemma : (x₁ : ℕ) → x₁ · y + x₁ · z ≡ x₁ · (y + z) → suc x₁ · y + suc x₁ · z ≡ suc x₁ · (y + z)
        lemma x₁ x₁·y+x₁·z≡x₁·[y+z] =
                suc x₁ · y + suc x₁ · z
            ≡⟨⟩
                y + x₁ · y + (z + x₁ · z)
            ≡⟨ +-assoc (y + x₁ · y) z (x₁ · z) ⟩
                y + x₁ · y + z + x₁ · z
            ≡⟨ cong (_+ (x₁ · z)) (sym (+-assoc y (x₁ · y) z)) ⟩
                y + (x₁ · y + z) + x₁ · z
            ≡⟨ cong (λ v → y + v + x₁ · z) (+-comm (x₁ · y) z) ⟩
                y + (z + x₁ · y) + x₁ · z
            ≡⟨ cong (_+ (x₁ · z)) (+-assoc y z (x₁ · y)) ⟩
                y + z + x₁ · y + x₁ · z
            ≡⟨ sym (+-assoc (y + z) (x₁ · y) (x₁ · z)) ⟩
                y + z + (x₁ · y + x₁ · z)
            ≡⟨ cong (λ v → y + z + v) x₁·y+x₁·z≡x₁·[y+z] ⟩
                y + z + x₁ · (y + z)
            ≡⟨⟩
                suc x₁ · (y + z)
            ∎

    ·-distribʳ : ∀ x y z → x · z + y · z ≡ (x + y) · z
    ·-distribʳ x y z =
            x · z + y · z
        ≡⟨ cong ((x · z) +_) (·-comm y z) ⟩
            x · z + z · y
        ≡⟨ cong (_+ (z · y)) (·-comm x z) ⟩
            z · x + z · y
        ≡⟨ ·-distribˡ z x y ⟩
            z · (x + y)
        ≡⟨ ·-comm z (x + y) ⟩
            (x + y) · z
        ∎

    ·-assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
    ·-assoc x y z = ind-ℕ (λ x₁ → x₁ · (y · z) ≡ (x₁ · y) · z) refl lemma x where
        lemma : (x₁ : ℕ) → x₁ · (y · z) ≡ (x₁ · y) · z → suc x₁ · (y · z) ≡ (suc x₁ · y) · z
        lemma x₁ x₁·[y·z]≡[x₁·y]·z =
                suc x₁ · (y · z)
            ≡⟨⟩
                y · z + x₁ · (y · z)
            ≡⟨ cong (y · z +_) x₁·[y·z]≡[x₁·y]·z ⟩
                y · z + (x₁ · y) · z
            ≡⟨ ·-distribʳ y (x₁ · y) z ⟩
                (y + (x₁ · y)) · z
            ≡⟨⟩
                (suc x₁ · y) · z
            ∎
    x·1≡x : ∀ x → x · 1 ≡ x
    x·1≡x x =
            x · 1
        ≡⟨ ·-suc x 0 ⟩
            x + x · 0
        ≡⟨ cong (x +_) (sym (0≡m·0 x)) ⟩
            x + 0
        ≡⟨ +-zero x ⟩
            x
        ∎

    IsSemigroup-ℕ-+ : IsSemigroup _+_
    IsSemigroup-ℕ-+ = issemigroup isSetℕ +-assoc

    IsMonoid-ℕ-+ : IsMonoid 0 _+_
    IsMonoid-ℕ-+ = ismonoid IsSemigroup-ℕ-+ +-zero λ _ → refl

    IsCommMonoid-ℕ-+ : IsCommMonoid 0 _+_
    IsCommMonoid-ℕ-+ = iscommmonoid IsMonoid-ℕ-+ +-comm

    IsSemigroup-ℕ-· : IsSemigroup _·_
    IsSemigroup-ℕ-· = issemigroup isSetℕ ·-assoc

    IsMonoid-ℕ-· : IsMonoid 1 _·_
    IsMonoid-ℕ-· = ismonoid IsSemigroup-ℕ-· x·1≡x +-zero

    record IsSemiring {ℓ} {A : Set ℓ} (_+_ _·_ : A → A → A) (a₀ a₁ : A) : Type ℓ where
        constructor issemiring
        field
            +IsCommMonoid : IsCommMonoid a₀ _+_
            ·IsMonoid : IsMonoid a₁ _·_
            ·DistR+ : ∀ x y z → x · (y + z) ≡ (x · y) + (x · z)
            ·DistL+ : ∀ x y z → (x + y) · z ≡ (x · z) + (y · z)
            ·ZeroL : ∀ x → a₀ · x ≡ a₀
            ·ZeroR : ∀ x → x · a₀ ≡ a₀

    IsSemiring-ℕ : IsSemiring _+_ _·_ 0 1
    IsSemiring-ℕ = issemiring
        IsCommMonoid-ℕ-+
        IsMonoid-ℕ-·
        (λ x y z → sym (·-distribˡ x y z))
        (λ x y z → sym (·-distribʳ x y z))
        (λ x → refl)
        λ x → sym (0≡m·0 x)

module ex-1-9 where

    open Cubical.Data.Nat
    open Cubical.Data.Nat.Order
    open import Cubical.Data.Unit
    open Cubical.Data.Sum

    Fin : ℕ → Set
    Fin zero = ⊥
    Fin (suc n) = Unit ⊎ Fin n

    fmax : (n : ℕ) → Fin (suc n)
    fmax zero = inl tt
    fmax (suc n) = inr (fmax n)

    fsuc : (n : ℕ) → Fin n → Fin (suc n)
    fsuc n = inr

    Fin' : ℕ → Set
    Fin' zero = ⊥
    Fin' (suc n) = Unit ⊎ Fin' n

    fmax' : (n : ℕ) → Fin' (suc n)
    fmax' zero = inl tt
    fmax' (suc n) = inr (fmax' n)

    fsuc' : (n : ℕ) → Fin' n → Fin' (suc n)
    fsuc' n = inr

module ex-1-10 where

    open Cubical.Data.Nat

    rec-ℕ : ∀ {ℓ} {C : Set ℓ} → C → (ℕ → C → C) → ℕ → C
    rec-ℕ c₀ cₛ zero = c₀
    rec-ℕ c₀ cₛ (suc n) = cₛ n (rec-ℕ c₀ cₛ n)

    ind-ℕ : ∀ {ℓ} (C : ℕ → Set ℓ) → C 0 → (∀ n → C n → C (suc n)) → ∀ n → C n
    ind-ℕ C c₀ cₛ zero = c₀
    ind-ℕ C c₀ cₛ (suc n) = cₛ n (ind-ℕ C c₀ cₛ n)

    ack : ℕ → ℕ → ℕ
    ack x = rec-ℕ (λ y → suc y)
        (λ x₁ ack-x₁ y → rec-ℕ (ack-x₁ 1)
            (λ y₁ ack-[x₁+1]-y₁ → ack-x₁ ack-[x₁+1]-y₁) y) x

    ex-1-10-1 : ∀ x → ack 0 x ≡ suc x
    ex-1-10-1 x = refl

    ex-1-10-2 : ∀ x → ack (suc x) 0 ≡ ack x 1
    ex-1-10-2 x = refl

    ex-1-10-3 : ∀ x y → ack (suc x) (suc y) ≡ ack x (ack (suc x) y)
    ex-1-10-3 x y = refl

module ex-1-11 where

    ex-1-11 : ∀ {ℓ} (A : Set ℓ) → ¬ ¬ ¬ A → ¬ A
    ex-1-11 A ¬¬¬A a = ¬¬¬A λ ¬A → ¬A a

module ex-1-12 where

    open Cubical.Data.Prod
    open Cubical.Data.Sum

    variable
        ℓ₁ ℓ₂ : Level
        A : Set ℓ₁
        B : Set ℓ₂

    ex-1-12-1 : A → B → A
    ex-1-12-1 a b = a

    ex-1-12-2 : A → ¬ ¬ A
    ex-1-12-2 a ¬A = ¬A a

    ex-1-12-3 : (¬ A) ⊎ (¬ B) → ¬ (A × B)
    ex-1-12-3 (inl ¬A) (a , _) = ¬A a
    ex-1-12-3 (inr ¬B) (_ , b) = ¬B b

module ex-1-13 where

    open Cubical.Data.Sum

    ex-1-13 : ∀ {ℓ} (P : Set ℓ) → ¬ ¬ (P ⊎ (¬ P))
    ex-1-13 P ¬[P⊎¬P] = ¬[P⊎¬P] (inr (λ p → ¬[P⊎¬P] (inl p)))

module ex-1-14 where

    open import Cubical.Data.Unit

    data 𝟚 : Set where
        0₂ : 𝟚
        1₂ : 𝟚

    inverse : 𝟚 → 𝟚
    inverse 0₂ = 1₂
    inverse 1₂ = 0₂

    inverse² : ∀ x → inverse (inverse x) ≡ x
    inverse² 0₂ = refl
    inverse² 1₂ = refl

    ex-1-14 : (∀ ℓ (A : Set ℓ) (x : A) (p : x ≡ x) → p ≡ refl) → ⊥
    ex-1-14 P = {! J  !} where -- P (ℓ-suc ℓ-zero) Set 𝟚
        q : 𝟚 ≡ 𝟚
        q = ua (inverse , (record { 
                equiv-proof =
                    λ x → ((inverse x) , inverse² x)
                    , λ{ (y , inverse-y≡x) → {!   !} }
            }))
        q≡refl : q ≡ refl
        q≡refl = P (ℓ-suc ℓ-zero) Set 𝟚 q

    data S¹' : Set where
        base : S¹'
        loop : base ≡ base
        noloop : loop ≡ refl

    -- t : S¹' → Set
    -- t base = {!   !}
    -- t (loop i) = {!   !}
    -- t (noloop i i₁) = {!   !}

    -- data 𝟚 : Set where
    --     0₂ 1₂ : 𝟚

    dist-𝟚 : 𝟚 → Set
    dist-𝟚 0₂ = Unit
    dist-𝟚 1₂ = ⊥

    uniq-𝟚 : ¬ (0₂ ≡ 1₂)
    uniq-𝟚 eq = transport (cong dist-𝟚 eq) tt

module Circle where

    open import Cubical.Data.Unit

    data S¹ : Set where
        base : S¹
        loop : base ≡ base

    data 𝟚 : Set where
        0₂ 1₂ : 𝟚

    postulate nonRefl𝟚≡𝟚 : 𝟚 ≡ 𝟚
    postulate nonRefl𝟚≡𝟚IsNotRefl : ¬ (nonRefl𝟚≡𝟚 ≡ refl)

    dist-S¹-eq : S¹ → Set
    dist-S¹-eq base = 𝟚
    dist-S¹-eq (loop i) = nonRefl𝟚≡𝟚 i

    uniq-loop : ¬ (loop ≡ refl)
    uniq-loop refl≡loop = nonRefl𝟚≡𝟚IsNotRefl λ i j → dist-S¹-eq (refl≡loop i j)

    
module ex-1-15 where

    open Cubical.Data.Sigma

    ex-1-15 : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (C : A → Set ℓ₂) → (x y : A)
        → (p : x ≡ y) → C x → C y
    ex-1-15 C x y p C-x = J (λ a _ → C a) C-x p

module ex-1-16 where

    open Cubical.Data.Nat using (ℕ; zero; suc; _+_; +-suc; +-zero)

    +-comm : ∀ x y → x + y ≡ y + x
    +-comm zero y = sym (+-zero y)
    +-comm (suc x) y =
            suc (x + y)
        ≡⟨ cong suc (+-comm x y) ⟩
            suc (y + x)
        ≡⟨ sym (+-suc y x) ⟩
            y + suc x
        ∎
