module Kipling where

open import Combinators
open import Data.Unit
--open import Universes.EqRel
open import Universes.EqSim

mutual
  infixl 70 _,,_
  data Context : Set where
    〈〉 : Context
    _,,_ : ∀ Γ → (⟦ Γ ⟧C → U) → Context

  ⟦_⟧C : Context → Set
  ⟦ 〈〉 ⟧C = Unit
  ⟦ Γ ,, A ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] T (A γ)

Type : Context → Set
Type Γ = ⟦ Γ ⟧C → U

⟦_⟧T : ∀ {Γ} → Type Γ → Set
⟦ A ⟧T = ∀ γ → T (A γ)

data Var : ∀ (Γ : Context) (A : Type Γ) → Set where
  ⊥ : ∀ {Γ} {A} → Var (Γ ,, A) (A ∘ proj₁)
  ↑ : ∀ {Γ} {A} {B} → Var Γ B → Var (Γ ,, A) (B ∘ proj₁)

⟦_⟧V : ∀ {Γ} {A} → Var Γ A → ⟦ A ⟧T
⟦ ⊥ ⟧V (_ , a) = a
⟦ ↑ x ⟧V (γ , _) = ⟦ x ⟧V γ

mutual
  data _⊢_ (Γ : Context) : Type Γ → Set where
    star  : Γ ⊢ K *
    var   : ∀ {A} → Var Γ A → Γ ⊢ A
    pi    : ∀ (A : Γ ⊢ K *) → Γ ,, ⟦ A ⟧ ⊢ K * → Γ ⊢ K *
    sigma : ∀ (A : Γ ⊢ K *) → Γ ,, ⟦ A ⟧ ⊢ K * → Γ ⊢ K *
    eq    : Γ ⊢ K * → Γ ⊢ K * → Γ ⊢ K *
    ∼     : ∀ {A B : Γ ⊢ K *} → Γ ⊢ (λ γ → ⟦ A ⟧ γ ≃ ⟦ B ⟧ γ) → Γ ⊢ ⟦ A ⟧ → Γ ⊢ ⟦ B ⟧ → Γ ⊢ K *
    Λ     : ∀ {A : Γ ⊢ K *} {B : Γ ,, ⟦ A ⟧ ⊢ K *} → Γ ,, ⟦ A ⟧ ⊢ ⟦ B ⟧ → Γ ⊢ K π S ⟦ A ⟧ S ∧ ⟦ B ⟧
    app   : ∀ {A : Γ ⊢ K *} {B : Γ ,, ⟦ A ⟧ ⊢ K *} → Γ ⊢ K π S ⟦ A ⟧ S ∧ ⟦ B ⟧ → ∀ (a : Γ ⊢ ⟦ A ⟧) → Γ ⊢ ∧ ⟦ B ⟧ S ⟦ a ⟧
    pair  : ∀ {A : Γ ⊢ K *} {B : Γ ,, ⟦ A ⟧ ⊢ K *} (a : Γ ⊢ ⟦ A ⟧) → Γ ⊢ ∧ ⟦ B ⟧ S ⟦ a ⟧ → Γ ⊢ K σ S ⟦ A ⟧ S ∧ ⟦ B ⟧
    π₁    : ∀ {A : Γ ⊢ K *} {B : Γ ,, ⟦ A ⟧ ⊢ K *} → Γ ⊢ K σ S ⟦ A ⟧ S ∧ ⟦ B ⟧ → Γ ⊢ ⟦ A ⟧
    π₂    : ∀ {A : Γ ⊢ K *} {B : Γ ,, ⟦ A ⟧ ⊢ K *} (p : Γ ⊢ K σ S ⟦ A ⟧ S ∧ ⟦ B ⟧) → Γ ⊢ ∧ ⟦ B ⟧ S ((λ _ → proj₁) S ⟦ p ⟧)
    **    : Γ ⊢ K (* ≃ *)
    pistar : ∀ {A A' : Γ ⊢ K *} (A* : Γ ⊢ (λ γ → ⟦ A ⟧ γ ≃ ⟦ A' ⟧ γ))
               {B : Γ ,, ⟦ A ⟧ ⊢ K *} {B' : Γ ,, ⟦ A' ⟧ ⊢ K *} 
               (B* : Γ ,, ⟦ A ⟧ ,, ⟦ A' ⟧ ∘ proj₁ ,, (λ x → ⟦ A ⟧ (proj₁ (proj₁ x)) ≃ ⟦ A' ⟧ ((proj₁ (proj₁ x)))) ⊢ λ γ → ⟦ B ⟧ ((proj₁ (proj₁ (proj₁ γ))) , proj₂ (proj₁ (proj₁ γ))) ≃ ⟦ B' ⟧ ((proj₁ (proj₁ (proj₁ γ))) , (proj₂ (proj₁ γ)))) →
               Γ ⊢ λ γ → π (⟦ A ⟧ γ) (λ a → ⟦ B ⟧ (γ , a)) ≃ π (⟦ A' ⟧ γ) (λ a → ⟦ B' ⟧ (γ , a))
    sigmastar : ∀ {A A' : Γ ⊢ K *} (A* : Γ ⊢ (λ γ → ⟦ A ⟧ γ ≃ ⟦ A' ⟧ γ))
               {B : Γ ,, ⟦ A ⟧ ⊢ K *} {B' : Γ ,, ⟦ A' ⟧ ⊢ K *} 
               (B* : Γ ,, ⟦ A ⟧ ,, ⟦ A' ⟧ ∘ proj₁ ,, (λ x → ⟦ A ⟧ (proj₁ (proj₁ x)) ≃ ⟦ A' ⟧ ((proj₁ (proj₁ x)))) ⊢ λ γ → ⟦ B ⟧ ((proj₁ (proj₁ (proj₁ γ))) , proj₂ (proj₁ (proj₁ γ))) ≃ ⟦ B' ⟧ ((proj₁ (proj₁ (proj₁ γ))) , (proj₂ (proj₁ γ)))) →
               Γ ⊢ λ γ → σ (⟦ A ⟧ γ) (λ a → ⟦ B ⟧ (γ , a)) ≃ σ (⟦ A' ⟧ γ) (λ a → ⟦ B' ⟧ (γ , a))
    eqstar : ∀ {A A' B B' : Γ ⊢ K *} → Γ ⊢ (λ γ → ⟦ A ⟧ γ ≃ ⟦ A' ⟧ γ) → Γ ⊢ (λ γ → ⟦ B ⟧ γ ≃ ⟦ B' ⟧ γ) →
             Γ ⊢ λ γ → (⟦ A ⟧ γ ≃ ⟦ B ⟧ γ) ≃ (⟦ A' ⟧ γ ≃ ⟦ B' ⟧ γ)

  ⟦_⟧ : ∀ {Γ} {A} → Γ ⊢ A → ⟦ A ⟧T
  ⟦ var x ⟧ γ  = ⟦ x ⟧V γ
  ⟦ star ⟧ _ = *
  ⟦ pi A B ⟧ γ = π (⟦ A ⟧ γ) (‌∧ ⟦ B ⟧ γ)
  ⟦ sigma A B ⟧ γ = σ (⟦ A ⟧ γ) (‌∧ ⟦ B ⟧ γ)
  ⟦ eq A B ⟧ γ = ⟦ A ⟧ γ ≃ ⟦ B ⟧ γ
  ⟦ ∼ e a b ⟧ γ = ⟦ a ⟧ γ ∼〈 ⟦ e ⟧ γ 〉 ⟦ b ⟧ γ
  ⟦ Λ M ⟧ γ = λ a → ⟦ M ⟧ (γ , a)
  ⟦ app M N ⟧ γ = ⟦ M ⟧ γ (⟦ N ⟧ γ)
  ⟦ pair a b ⟧ γ = (⟦ a ⟧ γ) , (⟦ b ⟧ γ)
  ⟦ π₁ p ⟧ γ = proj₁ (⟦ p ⟧ γ)
  ⟦ π₂ p ⟧ γ = proj₂ (⟦ p ⟧ γ)
  ⟦ ** ⟧ γ = r*
  ⟦ pistar A* B* ⟧ γ = π* (⟦ A* ⟧ γ) (λ a a' _ → ⟦ B* ⟧ (((γ , a) , a') , (⟦ A* ⟧ γ)))
  ⟦ sigmastar A* B* ⟧ γ = σ* (⟦ A* ⟧ γ) (λ a a' _ → ⟦ B* ⟧ (((γ , a) , a') , ⟦ A* ⟧ γ))
  ⟦ eqstar A* B* ⟧ γ = ⟦ A* ⟧ γ ≃* ⟦ B* ⟧ γ
