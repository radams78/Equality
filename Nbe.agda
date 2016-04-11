{-# OPTIONS --no-positivity-check #-}

module Nbe where

open import Function using (_∘_)
open import Data.Unit
open import Data.Product
open import Data.Nat using (ℕ;zero;suc)
--open import Universes.EqRel
--open import Universes.EqSim

infix 75 _⇒_
data U : Set where
  One : U
  _⇒_  : U → U → U

T : U → Set
T One = Unit
T (A ⇒ B) = T A → T B

infix 70 _,,_
data Context : Set where
  〈〉 : Context
  _,,_ : Context → U → Context

⟦_⟧C : Context → Set
⟦ 〈〉 ⟧C = Unit
⟦ Γ ,, A ⟧C = ⟦ Γ ⟧C × T A

data Var : ∀ (Γ : Context) (A : U) → Set where
  ⊥ : ∀ {Γ} {A} → Var (Γ ,, A) A
  ↑ : ∀ {Γ} {A} {B} → Var Γ B → Var (Γ ,, A) B

⟦_⟧V : ∀ {Γ} {A} → Var Γ A → ⟦ Γ ⟧C → T A
⟦ ⊥ ⟧V (_ , a) = a
⟦ ↑ x ⟧V (γ , _) = ⟦ x ⟧V γ

infix 25 _⊢_
data _⊢_ (Γ : Context) : U → Set
infix 75 ⟦_⟧
⟦_⟧ : ∀ {Γ} {A} → Γ ⊢ A → ⟦ Γ ⟧C → T A

data _⊢_ Γ where
  var   : ∀ {A} → 

      Var Γ A → 
    ---------------
      Γ ⊢ A

  〈〉 : Γ ⊢ One

  Λ     : ∀ {A} {B} →

     Γ ,, A ⊢ B → 
    ------------------------
     Γ ⊢ A ⇒ B

  app   : ∀ {A} {B} →

    Γ ⊢ A ⇒ B →   Γ ⊢ A →
    ---------------------------
            Γ ⊢ B

⟦ var x ⟧ γ = ⟦ x ⟧V γ
⟦ 〈〉 ⟧ _ = unit
⟦ Λ M ⟧ γ = λ a → ⟦ M ⟧ (γ , a)
⟦ app M N ⟧ γ = ⟦ M ⟧ γ (⟦ N ⟧ γ)

data Value : U → Set where
  fun : ∀ {A} {B} → (Value A → Value B) → Value (A ⇒ B)
  〈〉 : Value One

value : ∀ {A} → Value A → T A
eval : ∀ A → T A → Value A

value (fun f) = λ x → value (f (eval _ x))
value 〈〉 = unit

eval One unit = 〈〉
eval (A ⇒ B) f = fun (λ x → eval B (f (value x)))

reify : ∀ {Γ} {A} → Value A → Γ ⊢ A
reflect : ∀ {Γ} {A} → Γ ⊢ A → Value A

reify {Γ} {A ⇒ B} (fun f) = Λ (reify (f (reflect (var {Γ ,, A} ⊥))))
reify 〈〉 = 〈〉

reflect {Γ} {One} M = 〈〉
reflect {Γ} {A ⇒ B} M = fun (λ a → reflect (app M (reify a)))

Reify : ∀ {Γ} {A} → T A → Γ ⊢ A
Reflect : ∀ {Γ} {A} → Γ ⊢ A → T A

Reify {Γ} {One} unit = 〈〉
Reify {Γ} {A ⇒ B} f = Λ (Reify (f (Reflect (var {Γ ,, A} ⊥))))

Reflect {Γ} {One} _ = unit
Reflect {Γ} {A ⇒ B} M = λ x → Reflect {Γ} (app M (Reify x))

nbe : ∀ {Γ} {A} → Γ ⊢ A → Γ ⊢ A
nbe x = Reify (Reflect x)

term : 〈〉 ,, One ⊢ One
term = app (Λ (var ⊥)) (var ⊥)

