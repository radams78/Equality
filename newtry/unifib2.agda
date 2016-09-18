{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --type-in-type #-}

module unifib2 where

open import Data.Product

{- This is playground.

Common pattern in universes:

1. syntax of types
2. notion of dependency
3. target structure for decoding types
-}

postulate Structure : Set
postulate Domain : Structure → Set
postulate Fibration : ∀ {X : Structure} → (Domain X → Structure) → Set

data U where
    𝟘 𝟙 : U
    Ω : U    -- "smaller" universe, or another basic type
    π : ∀ A → Σ[ f ∈ Domain X → Structure ] (Fibration f) → U
    σ : ∀ A → (T A → U) → U
    _≃_ : U → U → U

T 𝟘 = ⊥
T 𝟙 = ⊤
T Ω = Set
T (π A B) = ∀ a → T (B a)
T (σ A B) = Σ[ a ∈ T A ] T (B a)
T (A ≃ B) = Eq A B     -- A ⇔ B

data Eq where
    𝟘* : Eq 𝟘 𝟘
    𝟙* : Eq 𝟙 𝟙
    Ω* : Eq Ω Ω
    π* : ∀ {A} {A'} (A* : Eq A A')
           {B} {B'} (B* : ∀ {a} {a'} (a* : a ∼⟨ A* ⟩ a') → Eq (B a) (B' a')) →
           Eq (π A B) (π A' B')
    σ* : ∀ {A} {A'} (A* : Eq A A')
           {B} {B'} (B* : ∀ {a} {a'} (a* : a ∼⟨ A* ⟩ a') → Eq (B a) (B' a')) →
           Eq (σ A B) (σ A' B')
    _≃*_ : ∀ {A} {A'} (A* : Eq A A') {B} {B'} (B* : Eq B B') → 
           Eq (A ≃ B) (A' ≃ B')

x ∼⟨ 𝟘* ⟩ y = ⊤
x ∼⟨ 𝟙* ⟩ y = ⊤
A ∼⟨ Ω* ⟩ B = A ⇔ B
f ∼⟨ π* {A} {A'} A* {B} {B'} B* ⟩ g = ∀ {x : T A} {x' : T A'} {x* : x ∼⟨ A* ⟩ x'} →
                                         f x ∼⟨ B* x* ⟩ g x'
p ∼⟨ σ* {A} {A'} A* {B} {B'} B* ⟩ q = Σ[ a* ∈ proj₁ p ∼⟨ A* ⟩ proj₁ q ]
                                           proj₂ p ∼⟨ B* a* ⟩ proj₂ q
e ∼⟨ _≃*_ {A} {A'} A* {B} {B'} B* ⟩ e' = ∀ {x : T A} {x' : T A'} {x* : x ∼⟨ A* ⟩ x'} →
                                         ∀ {y : T B} {y' : T B'} {y* : y ∼⟨ B* ⟩ y'} →
                                           (x ∼⟨ e ⟩ y) ⇔ (x' ∼⟨ e' ⟩ y')
syntax π A (λ a → B) = π[ a ∶ A ] B
syntax σ A (λ a → B) = σ[ a ∶ A ] B
