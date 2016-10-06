{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --type-in-type #-}

-- open import Function using (_∘_)
open import prop
open import Data.Empty
open import Data.Unit
open import Data.Product
open import freeSetoid
open import Setoid

module unifib where

π1 : ∀ {A : Set} {B : A → Set} → Σ[ x ∈ A ] (B x) → A
π1 {A} {B} (x , y) = x

nice : ∀ {A : Set} {B : A → Set} → Σ[ x ∈ A ] (B x) → A
nice {A} {B} = λ { (x , y) → x }

data U : Set 
T : U → Setoid
Elt : U → Set
Eqt : ∀ (A : U) → Elt A → Elt A → Set

Elt A = El (T A)
Eqt A = E (proj₂ (T A))

data Eq : U → U → Set
_∼⟨_⟩_ : ∀ {A} {B} → Elt A → Eq A B → Elt B → Set
Fibru : ∀ (A : U) → Set

-- The following symbol is entered as \~\< \> :
infix 60 _∼⟨_⟩_ 

data U where
    𝟘 𝟙 : U
    Ω : U    -- the universe of propositions
    π : ∀ A → Fibru A → U
    σ : ∀ A → Fibru A → U
    _≃_ : U → U → U

Fibru A = Σ[ B ∈ (Elt A → U) ] (∀ {x y} → (Eqt A x y) → Eq (B x) (B y))

T 𝟘 = (⊥ , 𝟘:Set)
T 𝟙 = (⊤ , 𝟙:Set)
T Ω = (Set , Prop:Set)
T (π A (B , B*)) = (Σ[ f ∈ (∀ a → Elt (B a)) ] (∀ {x} {y} (a* : Eqt A x y) → f x ∼⟨ B* a* ⟩ f y)) ,
        makeSetoid (λ {(f , f*) (g , g*) → (x : Elt A) → Eqt (B x) (f x) (g x)})
                   (λ {(f , f*) → λ x → r (proj₂ (T (B x))) (f x)})
                   (λ { {(f1 , f1*)} {(f2 , f2*)} f12 {(g1 , g1*)} {(g2 , g2*)} g12 →
                      (λ f1g1 x → proj₁ (E* (proj₂ (T (B x))) (f12 x) (g12 x)) (f1g1 x)) ,
                      (λ f2g2 x → proj₂ (E* (proj₂ (T (B x))) (f12 x) (g12 x)) (f2g2 x)) })
T (σ A (B , B*)) = (Σ[ a ∈ π1 (T A) ] π1 (T (B a))) ,
        makeSetoid (λ {(a , b) (a' , b') → Σ[ a* ∈ (Eqt A a a') ] b ∼⟨ B* a* ⟩ b'})
                   (λ {(a , b) → r (proj₂ (T A)) a , {!!} })
                   (λ { {(a1 , b1)} {(a1' , b1')} (a1* , b1*) {(a2 , b2)} {(a2' , b2')} (a2* , b2*)
                       → (λ {(a* , b*) → (proj₁ (E* (proj₂ (T A)) a1* a2*) a*) ,
                                         {!!}}) ,
                         {!!}} )
T (A ≃ B) = (Σ[ fg ∈ (Elt A ⇔ Elt B) ] Σ[ R ∈ (Elt A → Elt B → Set) ]
                  areCohIso (proj₂ (T A)) (proj₂ (T B)) fg R) , makeChaos

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
f ∼⟨ π* {A} {A'} A* {B} {B'} B* ⟩ g = ∀ {x : Elt A} {x' : Elt A'} {x* : x ∼⟨ A* ⟩ x'} →
                                         π1 f x ∼⟨ B* x* ⟩ π1 g x'
p ∼⟨ σ* {A} {A'} A* {B} {B'} B* ⟩ q = Σ[ a* ∈ proj₁ p ∼⟨ A* ⟩ proj₁ q ]
                                           proj₂ p ∼⟨ B* a* ⟩ proj₂ q
e ∼⟨ _≃*_ {A} {A'} A* {B} {B'} B* ⟩ e' = ∀ {x : Elt A} {x' : Elt A'} {x* : x ∼⟨ A* ⟩ x'} →
                                         ∀ {y : Elt B} {y' : Elt B'} {y* : y ∼⟨ B* ⟩ y'} →
                                           (proj₁ (proj₂ e) x y) ⇔ (proj₁ (proj₂ e') x' y')
syntax π A (λ a → B) = π[ a ∶ A ] B
syntax σ A (λ a → B) = σ[ a ∶ A ] B


