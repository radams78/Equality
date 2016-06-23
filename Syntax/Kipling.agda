{-# OPTIONS --type-in-type #-}

module Syntax.Kipling where

open import Data.Product
open import Setoid
open import Setoid.Unit
open import Setoid.Isomorphism
open import Setoid.Fibra-SS
open import genSetoid2

infixl 70 _,,_
data Context : Set
Type : Context → Set
⟦_⟧C : Context → Graph

-- postulate Fib : (G : Setoid) → Fibra-SS G → Ob G → Setoid
-- The collection of contexts Γ

data Context where
  〈〉 : Context
  _,,_ : ∀ Γ → (Type Γ) → Context

-- The collection of Γ-types
Type Γ = Fibra-GS (⟦ Γ ⟧C)

-- The collection of Γ-instances
⟦ 〈〉 ⟧C = UnitG
⟦ Γ ,, A ⟧C = Sigma-GS ⟦ Γ ⟧C A

lift : ∀ Γ A → Type Γ → Type (Γ ,, A)
lift Γ A B = record { 
  FibGS = λ {(γ , _) → FibGS B γ} ; 
  SubGS = λ {(e , _) → SUBGS B e} }

-- The elements of a Γ-type on the meta-level
⟦_⊢_⟧T : ∀ Γ → Type Γ → Set
⟦ _ ⊢ A ⟧T = ∀ γ → El (FibGS A γ)

data Var : ∀ (Γ : Context) (A : Type Γ) → Set where
  ⊥ : ∀ {Γ} {A} → Var (Γ ,, A) (lift Γ A A)
  ↑ : ∀ {Γ} {A} {B} → Var Γ B → Var (Γ ,, A) (lift Γ A B)

⟦_⟧V : ∀ {Γ} {A} → Var Γ A → Section A
⟦ ⊥ ⟧V = record { app = λ {(_ , a) → a} ; wd = λ {_ _ (_ , a*) → a*} }
⟦ ↑ x ⟧V = record { app = λ {(γ , _) → Section.app ⟦ x ⟧V γ} ; wd = λ {(γ , _) (γ' , _) (γ* , _) → Section.WD ⟦ x ⟧V γ γ' γ*} }

U : ∀ {Γ} → Type Γ
U {Γ} = record { 
  FibGS = λ _ → Prop:Set ; 
  SubGS = λ _ → id-iso Prop:Set }

Pi : ∀ {Γ} A → Type (Γ ,, A) → Type Γ
Pi {Γ} A B = record { 
  FibGS = λ γ → Pi-SS (FibGS A γ) (record { 
    FibSS = λ a → FibGS B (γ , a) ; 
    SubSS = λ a* → SubGS B (empty γ , a*) ; 
    SubSSr = {!!} ; 
    SubSS* = {!!} });
  SubGS = λ x* → record { 
    R = record { 
      Fib = λ {((f , fwd) , (g , gwd)) → ∀ a a' (a* : a ~< SubGS A x* > a') → f a ~< SubGS B (plus x* (empty _) , a*) > g a'} ; 
      Sub = {!!} } ; R+ = {!!} ; R- = {!!} }
  }

data _⊢_ : ∀ Γ → Type Γ → Set
⟦_⟧ : ∀ {Γ} {A} → Γ ⊢ A → Section A

data _⊢_ where
  var : ∀ {Γ} {A} → Var Γ A → Γ ⊢ A
  lam : ∀ {Γ} {A} {B} → Γ ,, A ⊢ B → Γ ⊢ Pi {Γ} A B
  app : ∀ {Γ} {A} {B} → (Γ ⊢ Pi {Γ} A B) → ∀ (M : Γ ⊢ A) → Γ ⊢ record { FibGS = λ γ → FibGS B (γ , Section.app ⟦ M ⟧ γ) ; 
                                                                        SubGS = λ γ* → SubGS B ((plus γ* (empty _)) , (Section.wd ⟦ M ⟧ _ _ γ*)) }

⟦ var x ⟧ = ⟦ x ⟧V
⟦ lam M ⟧ = record { app = λ γ → (λ a → Section.app ⟦ M ⟧ (γ , a)) , 
                                 (λ a a' a* → Section.wd ⟦ M ⟧ (γ , a) (γ , a') ((empty γ) , a*)) ; 
                     wd = λ γ γ' γ* a a' a* → Section.wd ⟦ M ⟧ (γ , a) (γ' , a') ((plus γ* (empty _)) , a*) }
⟦ app M N ⟧ = record { app = λ γ → let (f , _) = Section.app ⟦ M ⟧ γ in f (Section.app ⟦ N ⟧ γ) ; 
                       wd = λ γ γ' γ* → Section.wd ⟦ M ⟧ γ γ' γ* (Section.app ⟦ N ⟧ γ) (Section.app ⟦ N ⟧ γ') (Section.wd ⟦ N ⟧ γ γ' γ*) }

subst : ∀ {Γ} {A} {B} (M : Γ ⊢ A) → Γ ,, A ⊢ B → Γ ⊢ record { FibGS = λ γ → FibGS B (γ , Section.app ⟦ M ⟧ γ) ; 
                                                                        SubGS = λ γ* → SubGS B ((plus γ* (empty _)) , (Section.wd ⟦ M ⟧ _ _ γ*)) }
subst {B = record { FibGS = _ ; SubGS = _ }} M (var ⊥) = {!!}
subst {B = record { FibGS = _ ; SubGS = _ }} M (var (↑ x)) = {!var x!}
subst {B = record { FibGS = _ ; SubGS = _ }} M (lam N) = {!!}
subst {B = record { FibGS = _ ; SubGS = _ }} M (app N₁ N) = app (subst M N₁) {!!}

{- Telescope : ℕ → Set
Telescope zero = Setoid
Telescope (suc n) = Σ[ A ∈ Setoid ] (El A → Telescope n)

cons : ∀ {n} (A : Setoid) → (El A → Telescope n) → Telescope (suc n)
cons A B = A , B

syntax cons A (λ a → B) = a ∶ A ⇒ B

tjt : ∀ {n} Γ → (Vertex ⟦ Γ ⟧C → Telescope n) → Set -- "Typing judgement with telescope"
data tj (Γ : Context) : Type Γ → Set
infix 75 ⟦_⟧
⟦_⟧ : ∀ {Γ} {A} → tj Γ A → ⟦ Γ ⊢ A ⟧T

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
