{-# OPTIONS --type-in-type #-}

module setoid-model where

open import Data.Unit
open import Data.Product
open import Data.Sum
open import prop
open import Setoid
open import Setoid.Isomorphism
open import Setoid.Fibra-SP
open import genSetoid

infixl 70 _,,_
data Context : Set
Type : Context → Set
⟦_⟧C : Context → Set
⟦_⟧C' : ∀ (Γ : Context) → graphOver (⟦ Γ ⟧C)

-- postulate Fib : (G : Setoid) → Fibra-SS G → Ob G → Setoid
-- The collection of contexts Γ

data Context where
  〈〉 : Context
  _,,_ : ∀ Γ → (Type Γ) → Context

-- The collection of Γ-types
Type  Γ = genSP (⟦ Γ ⟧C')
Type' Γ = genFib (⟦ Γ ⟧C')

-- The collection of Γ-instances
⟦ 〈〉 ⟧C = ⊤
⟦ Γ ,, A ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] El (genFib.Fam A γ)

⟦ 〈〉 ⟧C' = UnitGen
⟦ Γ ,, A ⟧C' = Σ-C-S (⟦ Γ ⟧C') A

-- The elements of a Γ-type on the meta-level
⟦_⟧T : ∀ {Γ} → Type Γ → Set
⟦_⟧T {Γ} A = ∀ γ → Ob (Fib ⟦ Γ ⟧C A γ)

{-
-- Some types are interpreted by Setoids; others by naked Sets.
data Var : ∀ (Γ : Context) (A : Type Γ) → Set where
  ⊥ : ∀ {Γ} {A} → Var (Γ ,, A) (A ∘ proj₁)
  ↑ : ∀ {Γ} {A} {B} → Var Γ B → Var (Γ ,, A) (B ∘ proj₁)

⟦_⟧V : ∀ {Γ} {A} → Var Γ A → ⟦ A ⟧T
⟦ ⊥ ⟧V (_ , a) = a
⟦ ↑ x ⟧V (γ , _) = ⟦ x ⟧V γ

Telescope : ℕ → Set
Telescope zero = U
Telescope (suc n) = Σ[ A ∈ U ] (T A → Telescope n)

cons : ∀ {n} (A : U) → (T A → Telescope n) → Telescope (suc n)
cons A B = A , B

syntax cons A (λ a → B) = a ∶ A ⇒ B

tjt : ∀ {n} Γ → (⟦ Γ ⟧C → Telescope n) → Set -- "Typing judgement with telescope"
data tj (Γ : Context) : Type Γ → Set
infix 75 ⟦_⟧
⟦_⟧ : ∀ {Γ} {A} → tj Γ A → ⟦ A ⟧T

tjt {zero} Γ A = tj Γ A
tjt {suc n} Γ P = tjt {n} (Γ ,, (λ γ → proj₁ (P γ))) (λ γ → proj₂ (P (proj₁ γ)) (proj₂ γ))

syntax tjt Γ (λ γ → A) = γ ∶ Γ ⊢ A

data tj Γ where -- "Typing judgement"
  star  : 

    -------------
      γ ∶ Γ ⊢ *

  var   : ∀ {A} → 

      Var Γ A → 
    ---------------
      γ ∶ Γ ⊢ A γ

  pi    : ∀ 

      (A : (γ ∶ Γ ⊢ *)) → (γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)) →
    -----------------------------------------------------
                   γ ∶ Γ ⊢ *

  sigma : ∀ 

      (A : γ ∶ Γ ⊢ *) → (γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)) →
    --------------------------------------------------
                   γ ∶ Γ ⊢ *

  eq    : 

      γ ∶ Γ ⊢ * → γ ∶ Γ ⊢ * → 
    ------------------------
            γ ∶ Γ ⊢ *

  ∼     : ∀ 

      {A : γ ∶ Γ ⊢ *}   {B : γ ∶ Γ ⊢ *} → (γ ∶ Γ ⊢ ⟦ A ⟧ γ ≃ ⟦ B ⟧ γ) →
    -------------------------------------------------------------------
                    γ ∶ Γ ⊢ ⟦ A ⟧ γ → γ ∶ Γ ⊢ ⟦ B ⟧ γ → γ ∶ Γ ⊢ *

  Λ     : ∀ 

      {A : γ ∶ Γ ⊢ *}    {B : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)} →  γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ ⟦ B ⟧ (γ , a)) → 
    ------------------------------------------------------------------------------------------------
                     γ ∶ Γ ⊢ π[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a)

  app   : ∀ 

      {A : γ ∶ Γ ⊢ *}   {B : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)} →   γ ∶ Γ ⊢ π[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a) →      ∀ (a : γ ∶ Γ ⊢ ⟦ A ⟧ γ) →
    ---------------------------------------------------------------------------------------------------------------------------------
                                     γ ∶ Γ ⊢ ⟦ B ⟧ (γ , (⟦ a ⟧ γ))

  pair  : ∀ 

      {A : γ ∶ Γ ⊢ *}   {B : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)}     (a : γ ∶ Γ ⊢ ⟦ A ⟧ γ) →    γ ∶ Γ ⊢ ⟦ B ⟧ (γ , ⟦ a ⟧ γ) →
    -------------------------------------------------------------------------------------------------------------------
                                   γ ∶ Γ ⊢ σ[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a)

  π₁    : ∀ 

      {A : γ ∶ Γ ⊢ *}     {B : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)} →      γ ∶ Γ ⊢ σ[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a) →
    ----------------------------------------------------------------------------------------------------------
                                        γ ∶ Γ ⊢ ⟦ A ⟧ γ

  π₂    : ∀ 

      {A : γ ∶ Γ ⊢ *}        {B : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)}     (p : γ ∶ Γ ⊢ σ[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a)) → 
    ---------------------------------------------------------------------------------------------------------------
                      γ ∶ Γ ⊢ ⟦ B ⟧ (γ , (proj₁ (⟦ p ⟧ γ)))

  **    : 

    -----------------
      γ ∶ Γ ⊢ * ≃ *

  pistar : ∀ 

      {A  : γ ∶ Γ ⊢ *}                                         {B : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)}
      {A' : γ ∶ Γ ⊢ *}                                         {B' : γ ∶ Γ ⊢ (a ∶ ⟦ A' ⟧ γ ⇒ *)}
      (A* : γ ∶ Γ ⊢ ⟦ A ⟧ γ ≃ ⟦ A' ⟧ γ) →    (γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ (a' ∶ ⟦ A' ⟧ γ ⇒ (a* ∶ a ∼〈 ⟦ A* ⟧ γ 〉 a' ⇒ ⟦ B ⟧ (γ , a) ≃ ⟦ B' ⟧ (γ , a'))))) →
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------
                                  γ ∶ Γ ⊢ (π[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a)) ≃ (π[ a' ∶ ⟦ A' ⟧ γ ] ⟦ B' ⟧ (γ , a'))

  sigmastar : ∀ 

      {A  : γ ∶ Γ ⊢ *}                                         {B : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)}
      {A' : γ ∶ Γ ⊢ *}                                         {B' : γ ∶ Γ ⊢ (a ∶ ⟦ A' ⟧ γ ⇒ *)}
      (A* : γ ∶ Γ ⊢ ⟦ A ⟧ γ ≃ ⟦ A' ⟧ γ) →    (γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ (a' ∶ ⟦ A' ⟧ γ ⇒ (a* ∶ a ∼〈 ⟦ A* ⟧ γ 〉 a' ⇒ ⟦ B ⟧ (γ , a) ≃ ⟦ B' ⟧ (γ , a'))))) →
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------
                                  γ ∶ Γ ⊢ (σ[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a)) ≃ (σ[ a' ∶ ⟦ A' ⟧ γ ] ⟦ B' ⟧ (γ , a'))

  eqstar : ∀ 

      {A : γ ∶ Γ ⊢ *}                   {B : γ ∶ Γ ⊢ *}
      {A' : γ ∶ Γ ⊢ *}                  {B' : γ ∶ Γ ⊢ *} →
      (γ ∶ Γ ⊢ ⟦ A ⟧ γ ≃ ⟦ A' ⟧ γ) →    (γ ∶ Γ ⊢ ⟦ B ⟧ γ ≃ ⟦ B' ⟧ γ) →
    ----------------------------------------------------------------------
              γ ∶ Γ ⊢ (⟦ A ⟧ γ ≃ ⟦ B ⟧ γ) ≃ (⟦ A' ⟧ γ ≃ ⟦ B' ⟧ γ)

⟦ var x ⟧ γ           = ⟦ x ⟧V γ
⟦ star ⟧ _            = *
⟦ pi A B ⟧ γ          = π[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a)
⟦ sigma A B ⟧ γ       = σ[ a ∶ ⟦ A ⟧ γ ] ⟦ B ⟧ (γ , a)
⟦ eq A B ⟧ γ          = ⟦ A ⟧ γ ≃ ⟦ B ⟧ γ
⟦ ∼ e a b ⟧ γ         = ⟦ a ⟧ γ ∼〈 ⟦ e ⟧ γ 〉 ⟦ b ⟧ γ
⟦ Λ M ⟧ γ             = λ a → ⟦ M ⟧ (γ , a)
⟦ app M N ⟧ γ         = ⟦ M ⟧ γ (⟦ N ⟧ γ)
⟦ pair a b ⟧ γ        = (⟦ a ⟧ γ) , (⟦ b ⟧ γ)
⟦ π₁ p ⟧ γ            = proj₁ (⟦ p ⟧ γ)
⟦ π₂ p ⟧ γ            = proj₂ (⟦ p ⟧ γ)
⟦ ** ⟧ γ              = r*
⟦ pistar A* B* ⟧ γ    = π* (⟦ A* ⟧ γ) (λ a a' a* → ⟦ B* ⟧ (((γ , a) , a') , a*))
⟦ sigmastar A* B* ⟧ γ = σ* (⟦ A* ⟧ γ) (λ a a' a* → ⟦ B* ⟧ (((γ , a) , a') , a*))
⟦ eqstar A* B* ⟧ γ    = ⟦ A* ⟧ γ ≃* ⟦ B* ⟧ γ

-}
