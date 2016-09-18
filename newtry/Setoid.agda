{-# OPTIONS --type-in-type #-}

module Setoid where

open import Data.Unit
open import Data.Empty
open import Data.Product
open import prop

record isSetoid (X : Set) : Set where
  constructor
    makeSetoid
  field
    E : X → X → Set
    r : ∀ (x : X) → E x x
    E* : ∀ {x x' : X} → E x x' → ∀ {y y' : X} → E y y' → (E x y ⇔ E x' y')

  sym : ∀ {x y : X} → E x y → E y x
  sym {x} {y} p = proj₁ (E* p (r x)) (r x)

  trans : ∀ {x y z : X} → E x y → E y z → E x z
  trans xy yz = proj₁ (E* (r _) yz) xy

--TODO Make proj₁, proj₂ into lemmas in Prop?

open isSetoid public

Setoid = Σ[ X ∈ Set ] isSetoid X

El : Setoid → Set
El (proj₁ , proj₂) = proj₁

makeChaos : ∀ {X : Set} → isSetoid X
makeChaos = makeSetoid (λ x y → ⊤) (λ x → tt)
        (λ {x} {x'} _ {y} {y'} _ → (λ x₁ → tt) , (λ x₁ → tt))

𝟙:Set : isSetoid ⊤
𝟙:Set = makeChaos

𝟘:Set : isSetoid ⊥
𝟘:Set = makeChaos

Prop:Set : isSetoid Set
Prop:Set = record {
  E = _⇔_;
  r = λ S → refl-p;
  E* = ⇔* }
    
record ContrS {X : Set} (S : isSetoid X) : Set where
  field
    c : X
    p : ∀ (x : X) → E S x c

