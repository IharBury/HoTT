{-# OPTIONS --safe --without-K #-}

module InfinityGroupoid where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Primitive

data Parameters {ℓ} : Nat → Set ℓ where
    base : Parameters 0

-- data FixET {ℓ} : Nat → Set ℓ → Set (lsuc ℓ) where
--     base : (ET0 : Set ℓ) → FixET 0 ET0
--     next : {n : Nat} {et etNext : Set ℓ} → FixET n et → ETNext et etNext → FixET (suc n) etNext

-- record ETNext {ℓ} (et : Set ℓ) (etNext : Set ℓ) : Set (lsuc ℓ) where
--     field
--         source target : et

-- data FixET {ℓ} : Nat → Set ℓ → Set (lsuc ℓ) where
--     base : (ET0 : Set ℓ) → FixET 0 ET0
--     next : {n : Nat} {et etNext : Set ℓ} → FixET n et → ETNext et etNext → FixET (suc n) etNext

record ZeroGroupoid
        {T0L : Level}
        (T0 : Set T0L)
        : Set T0L where

zeroGroupoidFromTypes : ∀ {ℓ} (A : Set ℓ) → ZeroGroupoid A
zeroGroupoidFromTypes _ = record{}

record OneGroupoid
        {T0L : Level}
        {T1L : Level}
        (T0 : Set T0L)
        (T1 : T0 → T0 → Set T1L)
        (id : ∀ x → T1 x x)
        (_∘_ : ∀ {x y z} → T1 y z → T1 x y → T1 x z)
        (_⁻¹ : ∀ {x y} → T1 x y → T1 y x)
        : Set (T0L ⊔ T1L) where
    field
        id∘ : ∀ {x y} (f : T1 x y) → id y ∘ f ≡ f
        ∘id : ∀ {x y} (f : T1 x y) → f ∘ id x ≡ f
        assoc : ∀ {x y z t} (f : T1 x y) (g : T1 y z) (h : T1 z t) → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
        ⁻¹∘ : ∀ {x y} (f : T1 x y) → (f ⁻¹) ∘ f ≡ id x
        ∘⁻¹ : ∀ {x y} (f : T1 x y) → f ∘ (f ⁻¹) ≡ id y

sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

oneGroupoidFromTypes : ∀ {ℓ} (A : Set ℓ) →
        OneGroupoid A (λ x y → x ≡ y) (λ _ → refl) (λ q p → trans p q) sym
oneGroupoidFromTypes A = record
    { id∘ = λ where refl → refl
    ; ∘id = λ where refl → refl
    ; assoc = λ where refl refl refl → refl
    ; ⁻¹∘ = λ where refl → refl
    ; ∘⁻¹ = λ where refl → refl
    }

2GT1A : ∀ {T0L T1L} (T0 : Set T0L) (T1 : T0 → T0 → Set T1L) → Set (T0L ⊔ T1L)
2GT1A T0 T1 = Σ T0 λ x → Σ T0 λ y → T1 x y

record TwoGroupoid
        {T0L : Level}
        {T1L : Level}
        {T2L : Level}
        (T0 : Set T0L)
        (T1 : T0 → T0 → Set T1L)
        (T2 : 2GT1A T0 T1 → 2GT1A T0 T1 → Set T2L)
        : Set (T0L ⊔ T1L ⊔ T2L) where
    field
        id₁ : ∀ x → T1 x x
        _∘₁_ : ∀ {x y z} → T1 y z → T1 x y → T1 x z
        _⁻¹₁ : ∀ {x y} → T1 x y → T1 y x
        
        id∘₁ : ∀ {x y} (f : T1 x y) → T2 (x , y , id₁ y ∘₁ f) (x , y , f)
        ∘id₁ : ∀ {x y} (f : T1 x y) → T2 (x , y , f ∘₁ id₁ x) (x , y , f)
        assoc₁ : ∀ {x y z t} (f : T1 x y) (g : T1 y z) (h : T1 z t) → T2 (x , t , (h ∘₁ g) ∘₁ f) (x , t , h ∘₁ (g ∘₁ f))
        ⁻¹∘₁ : ∀ {x y} (f : T1 x y) → T2 (x , x , (f ⁻¹₁) ∘₁ f) (x , x , id₁ x)
        ∘⁻¹₁ : ∀ {x y} (f : T1 x y) → T2 (y , y , f ∘₁ (f ⁻¹₁)) (y , y , id₁ y)

        id₂ : ∀ x → T2 x x
        _∘₂_ : ∀ {x y z} → T2 y z → T2 x y → T2 x z
        _⁻¹₂ : ∀ {x y} → T2 x y → T2 y x

        id∘₂ : ∀ {x y} (f : T2 x y) → id₂ y ∘₂ f ≡ f
        ∘id₂ : ∀ {x y} (f : T2 x y) → f ∘₂ id₂ x ≡ f
        assoc₂ : ∀ {x y z t} (f : T2 x y) (g : T2 y z) (h : T2 z t) → (h ∘₂ g) ∘₂ f ≡ h ∘₂ (g ∘₂ f)
        ⁻¹∘₂ : ∀ {x y} (f : T2 x y) → (f ⁻¹₂) ∘₂ f ≡ id₂ x
        ∘⁻¹₂ : ∀ {x y} (f : T2 x y) → f ∘₂ (f ⁻¹₂) ≡ id₂ y

-- data IGTS (TL : Nat → Level) : (n : Nat) → Set (TL n) → Setω where
--     base : (T0 : Set (TL 0)) → IGTS TL 0 T0
--     next : {n : Nat} {Tn : Set (TL n)} (Tsn : Set (TL (suc n))) → IGTS TL n Tn → IGTS TL (suc n) Tsn

-- record InfinityGroupoid
--         (TL : Nat → Level)
--         : Setω where
--     field
--         T0 : Set (TL 0)

-- ET0 : ∀ {ℓ} (A : Set ℓ) → Set ℓ
-- ET0 A = A

-- ET1 : ∀ {ℓ} {A : Set ℓ} → ET0 A → ET0 A → Set ℓ
-- ET1 x y = x ≡ y

-- ET2 : ∀ {ℓ} {A : Set ℓ} {x y : A} → ET1 x y → ET1 x y → Set ℓ
-- ET2 p q = p ≡ q

-- data ETS {ℓ} (A : Set ℓ) : Nat → Set ℓ → Set (lsuc ℓ) where
--     base : ETS A 0 A
--     next : ∀ {n ETn} → ETS A n ETn → (x y : ETn) → ETS A (suc n) (x ≡ {!   !})

-- infinityGroupoidFromTypes : ∀ {ℓ} (A : Set ℓ) → Set
-- infinityGroupoidFromTypes {ℓ} A = {!   !} where
--     TL : Nat → Level
--     TL zero = ℓ
--     TL (suc n) = lsuc (TL n)
--     -- IGT : ∀ n → Σ (Set (TL n)) (λ T → IGTS TL n T)
--     -- IGT = ?

-- -- record liftω : Setω where

-- -- TT : ∀ {L} → Set L → Nat → Setω
-- -- T : ∀ {L} (TT0 : Set L) n → TT TT0 n
-- -- TT TT0 zero = TT0
-- -- TT _ (suc n) = ?
-- -- T = ?

-- -- data MorphismTree {EL} (ET : Set EL) : Nat → Set EL where
-- --     base : ET → ET → MorphismTree ET 0
-- --     next : {n : Nat} → MorphismTree ET n → MorphismTree ET n → MorphismTree ET (suc n)

-- -- record InfinityGroupoid : Setω where
-- --     field
-- --         EL : Level
-- --         ET : Set EL
-- --         ML : Nat → Level
-- --         MT : ∀ n → MorphismTree ET n → Set (ML n)
--         -- inverse : 
    

-- -- data MorphismTree {ℓ} (A : Set ℓ) : Nat → Set ℓ where
-- --     base : A → A → MorphismTree A 0
-- --     next : {n : Nat} → MorphismTree A n → MorphismTree A n → MorphismTree A (suc n)

-- -- record Morphism (EL ML : Level) (ET : Set EL) : Set (EL ⊔ lsuc ML) where
-- --     field 
-- --         M : ET → ET → Set ML

-- -- record InfinityGroupoid : Setω where
-- --     field
-- --         EL : Nat → Level
-- --         ET0 : Set (EL 0)
-- --         M0 : Morphism (EL 0) (EL 1) ET0
-- --         MN : ()

-- -- private
-- --     IGT : (TL : Nat → Level) → Set (TL 0) → (n : Nat) → Set (TL n)
-- --     IGT TL T0 zero = T0
-- --     IGT TL T0 (suc n) = {!   !}

-- -- record InfinityGroupoid : Setω where
-- --     field
-- --         TL : Nat → Level
-- --         T0 : Set (TL 0)
-- --         M : (n : Nat) → IGT TL T0 n → IGT TL T0 n → Set (TL n)

-- --     T = IGT TL T0
    
