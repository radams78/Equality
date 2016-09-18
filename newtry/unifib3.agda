{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --type-in-type #-}

open import Function using (_∘_)
open import prop
open import Data.Empty
open import Data.Unit
open import Data.Product
open import freeSetoid
open import Setoid

module unifib3 where

π1 : ∀ {A : Set} {B : A → Set} → Σ[ x ∈ A ] (B x) → A
π1 {A} {B} (x , y) = x

data U : Set 
T : U → Set
P : ∀ {A : U} → T A → Set
Elt : ∀ (A : U) → Set
Eqt : ∀ (A : U) → T A → T A → Set
S : (A : U) → isSetoid (Elt A)


data Eq : U → U → Set
_∼⟨_⟩_ : ∀ {A} {B} → T A → Eq A B → T B → Set
Fibru : ∀ (A : U) → Set


-- The following symbol is entered as \~\< \> :
infix 60 _∼⟨_⟩_

Elt A = Σ[ x ∈ T A ] P x
Eqt A = λ x y → ⊤

data U where
    𝟘 𝟙 : U
    Ω : U    -- smaller universe, or some basic type
    π : ∀ A → Fibru A → U
    σ : ∀ A → Fibru A → U
    _≃_ : U → U → U

Fibru A = Σ[ B ∈ (T A → U) ] (∀ {x y} → (Eqt A x y) → Eq (B x) (B y))

T 𝟘 = ⊥
T 𝟙 = ⊤
T Ω = Set
T (π A (B , B*)) = ∀ a → T (B a)
T (σ A (B , B*)) = Σ[ a ∈ T A ] T (B a)
T (A ≃ B) = T A ⇔ T B
-- Σ[ R ∈ (T A → T B → Set) ] areCohIso (setT A) (setT B) fg R

P {𝟘} x = ⊤
P {𝟙} x = ⊤
P {Ω} x = ⊤
P {π A (B , B*)} f = (x : T A) → P {B x} (f x)
P {σ A (B , B*)} (a , b) = P {A} a × P {B a} b
P {A ≃ B} e = ⊤

S A = makeChaos

data Eq where
    𝟘* : Eq 𝟘 𝟘
    𝟙* : Eq 𝟙 𝟙
    Ω* : Eq Ω Ω
    π* : ∀ {A} {A'} (A* : Eq A A')
           {B} {B'} (B* : ∀ {a} {a'} (a* : a ∼⟨ A* ⟩ a') → Eq (π1 B a) (π1 B' a')) →
           Eq (π A B) (π A' B')
    σ* : ∀ {A} {A'} (A* : Eq A A')
           {B} {B'} (B* : ∀ {a} {a'} (a* : a ∼⟨ A* ⟩ a') → Eq (π1 B a) (π1 B' a')) →
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
                                         ∀ {y : T B} {y' : T B'} {y* : y ∼⟨ B* ⟩ y'} → ⊤
--                                           (x ∼⟨ e ⟩ y) ⇔ (x' ∼⟨ e' ⟩ y')
syntax π A (λ a → B) = π[ a ∶ A ] B
syntax σ A (λ a → B) = σ[ a ∶ A ] B


