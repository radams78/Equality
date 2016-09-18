{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --type-in-type #-}

{- To make sure the universe subscripts are displayed correctly,
   Agda needs to have the dejavu fonts installed; these can be found at
        http://dejavu-fonts.org/wiki/Download
   To install on OS X, just move the unzipped folder into ~/Library/Fonts 8-}

module univ where
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Nat
open import prop
open import Setoid

{- Originally, was gonna define two universes: Uₚ and Uₛ -- for props and sets, respectively.
Then realized it's better to use Agda's Set for the former, and just plain universe for the latter.
In the groupoid model, we'll need two universes, and afterwards parametrized by dimension. -}

{- 9.8.16.  Thinking about how the different universes should be presented...
One could imagine the following scenario:
The syntax of types (Pi, Sigma, Simeq) is fixed, doesn't change w/ dimension.
But the decoding map goes to the corresponding homotopy universe (setoids, groupouds,..)
Still we will need the "underlying naked type" map as well, to construct terms of type U.
With this approach, the syntax of U will never change..-}

data U : Set
T : U → Set
-- T : U → Setoid
-- Elt : U → Set
-- Elt = El o T

data Eq : U → U → Set
-- The following symbol is entered as \~\< \> :
infix 60 _∼⟨_⟩_
_∼⟨_⟩_ : ∀ {A} {B} → T A → Eq A B → T B → Set
-- Rel : ∀ {A} {B} → Eq A B → T A → T B → Set
-- Rel e a b = a ∼⟨ e ⟩ b

data U where
    𝟘 𝟙 : U
    Ω : U    -- the setoid of propositions
    π : ∀ A → (T A → U) → U
    σ : ∀ A → (T A → U) → U
    _≃_ : U → U → U

T 𝟘 = ⊥
T 𝟙 = ⊤
T Ω = Set
T (π A B) = ∀ a → T (B a)
T (σ A B) = Σ[ a ∈ T A ] T (B a)
T (A ≃ B) = Eq A B     -- A ⇔ B

{-
T 𝟘 = (⊥ , 𝟘:Set)
T 𝟙 = (⊤ , 𝟙:Set)
T Ω = (Set , Prop:Set)
T (π A B) = Σ[ f ∈ ∀ a → T (B a) ] ...
T (σ A B) = Σ[ a ∈ T A ] T (B a)
T (A ≃ B) = Σ[ fg ∈ A ⇔ B ] Σ[R ∈ A → B → Set ] areCohIso (T A) (T B) fg R -- Eq A B 
-}

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

{-
T' : ∀ (A : U) → isSetoid (T A)
T' 𝟘 = 𝟘:Set
T' 𝟙 = 𝟙:Set
T' Ω = Prop:Set
T' (π A B) = {!!}
T' (σ A B) = {!!}
T' (A ≃ B) = {!!}

To define the setoid structure on elements of U, will need contexts; see main.agda.
-}

-- EqT : ∀ {n} Telescope
