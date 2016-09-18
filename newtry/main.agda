{-# OPTIONS --type-in-type #-}

module main where

open import Function
open import Data.Unit
open import Data.Product
open import Data.Nat
-- open import Data.Sum
open import prop
open import freeSetoid
open import univ

open graphOver

-- Contexts, types, instances
data Context : Set
Type : Context → Set
⟦_⟧C : Context → Set
=C : ∀ (Γ : Context) → Set
sC : ∀ {Γ : Context} → =C Γ → ⟦ Γ ⟧C
tC : ∀ {Γ : Context} → =C Γ → ⟦ Γ ⟧C

-- A context is either empty, or the extension of Γ by a Γ-type
data Context where
  ⟨⟩ : Context  -- this is now \<\>
  _,,_ : ∀ Γ → (Type Γ) → Context

-- A Γ-type is a family of elts of U indexed by Γ-instances
Type Γ = Σ[ A ∈ (⟦ Γ ⟧C → U) ] (∀ (e : =C Γ) → Eq (A (sC e)) (A (tC e)))

-- An instance of Γ is a tuple of elts of corresponding types
⟦ ⟨⟩ ⟧C = ⊤
⟦ Γ ,, A ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] T (proj₁ A γ)
infixl 70 _,,_

-- The elements of a Γ-type on the metalevel
⟦_⟧T : ∀ {Γ} → Type Γ → Set
⟦_⟧T {Γ} A = ∀ (γ : ⟦ Γ ⟧C) → T (proj₁ A γ)
EltT : ∀ {Γ} → Type Γ → ⟦ Γ ⟧C → Set
EltT A = T ∘ (proj₁ A)

-- The free setoid structure on contexts
=C ⟨⟩ = ⊤
=C (Γ ,, A) = Σ[ γ* ∈ (=C Γ) ] (
                 Σ[ a₁a₂ ∈ (EltT A (sC γ*) × EltT A (tC γ*)) ]
                   (proj₁ a₁a₂ ∼⟨ proj₂ A γ* ⟩ proj₂ a₁a₂))
sC {⟨⟩} _ = tt
sC {Γ ,, A} (γ* , ((a1 , a2) , a*)) = sC γ* , a1
tC {⟨⟩} _ = tt
tC {Γ ,, A} (γ* , ((a1 , a2) , a*)) = tC γ* , a2

⟦_⟧C' : ∀ (Γ : Context) → graphOver ⟦ Γ ⟧C
⟦ Γ ⟧C' = makeGraph (=C Γ) sC tC


-- The setoid structure on (interpretation of) types
-- Type' : ∀ (Γ : Context) (A : Type Γ) → isFibS ⟦ Γ ⟧C' (EltT A)
-- Type' Γ A = makeFibS {!!} {!!} {!!}

{-
-- ⟦_⟧T' : ∀ {Γ} (A : Type Γ) (γ : ⟦ Γ ⟧C) → isSetoid (⟦ A ⟧T γ)
T' 𝟘 = 𝟘:Set
T' 𝟙 = 𝟙:Set
T' Ω = Prop:Set
T' (π A B) = {!!}
T' (σ A B) = {!!}
T' (A ≃ B) = {!!} -}

data Var : ∀ (Γ : Context) (A : Type Γ) → Set where
  ⊥ : ∀ {Γ} {A} → Var (Γ ,, A) (proj₁ A ∘ proj₁ , proj₂ A ∘ proj₁)
  ↑ : ∀ {Γ} {A} {B} → Var Γ B → Var (Γ ,, A) (proj₁ B ∘ proj₁ , proj₂ B ∘ proj₁)

-- Projection functions: ⟦Γ⟧ → ⟦Aᵢ⟧, given index (xᵢ : Aᵢ) ∈ Γ
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
  𝔱 : 
    -------------
      γ ∶ Γ ⊢ 𝟙

  TT : 
    -------------
      γ ∶ Γ ⊢ Ω

  FF : 
    -------------
      γ ∶ Γ ⊢ Ω

  var : ∀ {A} → 
      Var Γ A → 
    ---------------
      γ ∶ Γ ⊢ A γ

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

⟦ 𝔱 ⟧                 = unit
⟦ TT ⟧                = ⊤
⟦ FF ⟧                = ⊥
⟦ var x ⟧ γ           = ⟦ x ⟧V γ
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

postulate Γ : Context
postulate A : γ ∶ Γ ⊢ *
postulate B : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ *)
postulate M : γ ∶ Γ ⊢ (a ∶ ⟦ A ⟧ γ ⇒ ⟦ B ⟧ ( γ , a ))
postulate N : γ ∶ Γ ⊢ ⟦ A ⟧ γ
postulate g : ⟦ Γ ⟧C
postulate P : T (⟦ B ⟧ (g , ⟦ N ⟧ g)) → Set
postulate x : P (⟦ app {A = A} {B} (Λ {A = A} {B} M) N ⟧ g)
y : P (⟦ M ⟧ (g , ⟦ N ⟧ g))
y = x
  
