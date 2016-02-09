{-# OPTIONS --no-positivity-check #-}

module Equality4 where

data Σ {A : Set} (B : A → Set) : Set where
  _,_ : ∀ a → B a → Σ B

π₁ : ∀ {A} {B} → Σ B → A
π₁ (a , _) = a

π₂ : ∀ {A} {B} (p : Σ {A} B) → B (π₁ p)
π₂ (_ , b) = b

mutual
  data U : Set where
    * : U
    π : ∀ A → (T A → U) → U
    σ : ∀ A → (T A → U) → U
    _≃_ : U → U → U

  T : U → Set
  T * = U
  T (π A B) = ∀ a → T (B a)
  T (σ A B) = Σ (λ a → T (B a))
  T (A ≃ B) = Eq A B

  data Eq : U → U → Set where
    r* : Eq * *
    π* : ∀ {A} {A'} (A* : Eq A A')
           {B} {B'} (B* : ∀ a a' (a* : Rel A* a a') → Eq (B a) (B' a')) →
           Eq (π A B) (π A' B')
    σ* : ∀ {A} {A'} (A* : Eq A A')
           {B} {B'} (B* : ∀ a a' (a* : Rel A* a a') → Eq (B a) (B' a')) →
           Eq (σ A B) (σ A' B')
    _≃*_ : ∀ {A} {A'} (A* : Eq A A') {B} {B'} (B* : Eq B B') → 
           Eq (A ≃ B) (A' ≃ B')

  Rel : ∀ {A} {B} → Eq A B → T A → T B → Set
  Rel e a b = T (a ∼〈 e 〉 b)

  _∼〈_〉_ : ∀ {A} {B} → T A → Eq A B → T B → U
  A ∼〈 r* 〉 B = A ≃ B
  f ∼〈 π* {A} {A'} A* {B} {B'} B* 〉 g = π A (λ x → π A' (λ x' → 
    π (x ∼〈 A* 〉 x') (λ x* → f x ∼〈 B* x x' x* 〉 g x')))
  p ∼〈 σ* {A} {A'} A* {B} {B'} B* 〉 q = σ (π₁ p ∼〈 A* 〉 π₁ q) 
    (λ a* → π₂ p ∼〈 B* (π₁ p) (π₁ q) a* 〉 π₂ q)
  e ∼〈 _≃*_ {A} {A'} A* {B} {B'} B* 〉 e' = 
    π A (λ a → π A' (λ a' → π (a ∼〈 A* 〉 a') (λ a* → 
    π B (λ b → π B' (λ b' → π (b ∼〈 B* 〉 b') (λ b* → 
    (a ∼〈 e 〉 b) ≃ (a' ∼〈 e' 〉 b')))))))

ref : ∀ A → Eq A A
ref * = r*
ref (π A B) = π* (ref A) {!!} -- FAIL: Need a ∼〈 ref A 〉 b => Eq (B a) (B b)
ref (σ A B) = σ* (ref A) {!!} -- FAIL: Need a ∼〈 ref A 〉 b => Eq (B a) (B b)
ref (A ≃ B) = (ref A) ≃* (ref B)

mutual
  Sym : ∀ {A} {B} → Eq A B → Eq B A
  Sym r* = r*
  Sym (π* A* B*) = π* (Sym A*) (λ a a' a* → Sym (B* a' a (sym a*)))
  Sym (σ* A* B*) = σ* (Sym A*) (λ a a' a* → Sym (B* a' a (sym a*)))
  Sym (e ≃* e') = (Sym e) ≃* (Sym e')

  sym : ∀ {A} {B} {e : Eq A B} {a} {b} → Rel (Sym e) a b → Rel e b a
  sym {.*} {.*} {r*} δ = Sym δ
  sym {(π A B)} {(π A' B')} {π* A* B*} δ = λ a' a a* → sym {B a'} {B' a} {_} (δ a a' (sym₂ a*)) -- FAIL?
  sym {(σ A B)} {(σ A' B')} {σ* e B*} δ = {!!}
  sym {(A ≃ B)} {(A' ≃ B')} {e ≃* e₁} δ = {!!}

  sym₂ : ∀ {A} {B} {e : Eq A B} {a} {b} → Rel e a b → Rel (Sym e) b a
  sym₂ {A} {B} {e} {a} {b} δ = {!!}

record is-contr (A : U) : Set where
  field
    point : T A
    path  : ∀ y → Rel (ref A) point y

record Iso (A B : U) : Set₁ where
  field
    iso : T A → T B
    inv : T B → T A
    isoinv : ∀ b → Rel (ref B) (iso (inv b)) b
    inviso : ∀ a → Rel (ref A) (inv (iso a)) a

mutual
  decode : ∀ {A} {B} → Eq A B → Iso A B
  decode r* = record { 
    iso = λ X → X; 
    inv = λ X → X; 
    isoinv = ref; 
    inviso = ref }
  decode (π* A* B*) = record { 
    iso = λ f a' → Iso.iso (decode (B* (Iso.inv (decode A*) a') a' (inv-decode A* a'))) (f (Iso.inv (decode A*) a')); 
    inv = λ g a → Iso.inv (decode (B* a (Iso.iso (decode A*) a) (iso-decode A* a))) (g (Iso.iso (decode A*) a)); 
    isoinv = {!!}; -- Needs a solution to goal 0
    inviso = {!!} }
  decode (σ* e B*) = {!!}
  decode (e ≃* e') = record { 
    iso = λ e´´ → {!!}; inv = {!!}; isoinv = {!!}; inviso = {!!} }

  inv-decode : ∀ {A} {B} (e : Eq A B) (b : T B) → Rel e (Iso.inv (decode e) b) b
  inv-decode r* A = ref A
  inv-decode (π* A* B*) f = λ b b' b-is-b' → {!!}
  inv-decode (σ* e B*) b = {!!}
  inv-decode (e ≃* e₁) b = {!!}

  iso-decode : ∀ {A} {B} (e : Eq A B) (a : T A) → Rel e a (Iso.iso (decode e) a)
  iso-decode r* A = ref A
  iso-decode (π* A* B*) f = λ a a' a-is-a' → {!!}
  iso-decode (σ* e B*) a = {!!}
  iso-decode (e ≃* e₁) a = {!!}
