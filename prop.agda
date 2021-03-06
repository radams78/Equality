module prop where

open import Data.Product

infix 5 _⇔_
_⇔_ : Set → Set → Set
p ⇔ q = (p → q) × (q → p)

refl-p : ∀ {p : Set} → p ⇔ p
refl-p = (λ x → x) , (λ x → x)

⇔* : ∀ {p1 p2} → (p1 ⇔ p2) → ∀ {q1 q2} → (q1 ⇔ q2) → (p1 ⇔ q1) ⇔ (p2 ⇔ q2)
⇔* {p1} {p2} p12 {q1} {q2} q12 = (
  (λ x → (λ z → proj₁ q12 (proj₁ x (proj₂ p12 z))) , (λ z → proj₁ p12 (proj₂ x (proj₂ q12 z)))) ,
  (λ x → (λ z → proj₂ q12 (proj₁ x (proj₁ p12 z))) , (λ z → proj₂ p12 (proj₂ x (proj₁ q12 z)))) )

∀* : ∀ {A} {P Q : A → Set} → (∀ x → P x ⇔ Q x) → (∀ x → P x) ⇔ (∀ x → Q x)
∀* {A} {P} {Q} hyp = (λ p x → proj₁ (hyp x) (p x)) , (λ q x → proj₂ (hyp x) (q x))

∀** : ∀ {A} {P Q : A → Set} → (∀ x → P x ⇔ Q x) → (∀ {x} → P x) ⇔ (∀ {x} → Q x)
∀** {A} {P} {Q} hyp = (λ p → proj₁ (hyp _) p) , (λ q → proj₂ (hyp _) q)

imp* : ∀ {P Q R S : Set} → P ⇔ Q → R ⇔ S → (P → R) ⇔ (Q → S)
imp* (PQ , QP) (RS , SR) = (λ PR q → RS (PR (QP q))) , (λ QS p → SR (QS (PQ p)))

flip : ∀ {A B : Set} {P Q R S : A → B → Set} → (∀ x y → (P x y ⇔ Q x y)) → (∀ x y → (R x y ⇔ S x y)) → ((∀ x y → (P x y ⇔ R x y)) ⇔ (∀ x y → (Q x y ⇔ S x y)))
flip {A} {B} {P} {Q} {R} {S} P⇔Q R⇔S = 
  ∀* (λ x → ∀* (λ y → ⇔* (P⇔Q x y) (R⇔S x y)))
--TODO Inline this?
