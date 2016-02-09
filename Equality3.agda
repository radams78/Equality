{-# OPTIONS --no-positivity-check #-}

module Equality3 where

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

record is-contr (A : U) : Set where
  field
    point : T A
    path  : ∀ y → T (point ∼〈 ref A 〉 y)

record Iso (A B : U) : Set₁ where
  field
    R : T A → T B → U
    R+ : ∀ x → is-contr (σ B (λ y → R x y))
    R- : ∀ y → is-contr (σ A (λ x → R x y))

iso' : ∀ {A} {B} → Iso A B → T A → T B
iso' i a = π₁ (is-contr.point (Iso.R+ i a))

inv' : ∀ {A} {B} → Iso A B → T B → T A
inv' i b = π₁ (is-contr.point (Iso.R- i b))

mutual
  decode : ∀ {A} {B} → Eq A B → Iso A B
  decode r* = record { 
    R = _≃_; 
    R+ = λ A → record { 
      point = A , (ref A); 
      path = λ B → (π₂ B) , {!!} }; -- FAIL: Need to finish definition of ref
    R- = λ A → record { 
      point = A , (ref A); 
      path = λ B → {!Sym (π₂ B)!} , {!!} } }
  decode (π* A* B*) = record { 
    R = λ f g → f ∼〈 π* A* B* 〉 g; 
    R+ = λ f → record { 
      point = (λ a' → iso' (decode (B* (inv' (decode A*) a') a' (decode-inv A* a'))) (f (inv' (decode A*) a'))) ,
     (λ a a' a* → {!!}); 
     path = {!!} }; R- = {!!} }
  decode (σ* A* B*) = {!!}
  decode (A* ≃* B*) = {!!}

  decode-iso : ∀ {A} {B} (e : Eq A B) (a : T A) → Rel e a (iso' (decode e) a)
  decode-iso e a = {!!}

  decode-inv : ∀ {A} {B} (e : Eq A B) (b : T B) → Rel e (inv' (decode e) b) b
  decode-inv e b = {!!}

  Trans : ∀ {A} {B} {C} → Eq B C → Eq A B → Eq A C
  Trans r* r* = r*
  Trans (π* C* D*) (π* A* B*) = π* (Trans C* A*) (λ a a' a* → Trans (D* (inv' (decode C*) a') a' (decode-inv C* a')) (B* a (inv' (decode C*) a') {!!})) 
    -- FAIL: a ∼〈 Trans C* A* 〉 a' → a ∼〈 A* 〉 inv (decode C*) a'
  Trans (σ* e B*) f = {!!}
  Trans (e ≃* e₁) f = {!!}

  lm1 : ∀ {A} {B} {C} (q : Eq B C) (p : Eq A B) (a : T A) (c : T C) →
    Rel (Trans q p) a c → Rel p a (inv' (decode q) c)
  lm1 r* r* A C = λ x → x
  lm1 (π* C* D*) (π* A* B*) f g = λ x a a' a* → lm1 (D* a' (iso' (decode C*) a') (decode-iso C* a')) (B* a a' a*) (f a) (g (iso' (decode C*) a')) {!!}
    --FAIL: Need f a ∼〈 Trans (D* a' (iso C* a') (decode-iso C* a')) (B* a a' a*) 〉 g (iso C* a')
    -- whene we have f a ∼〈 Trans (D* (inv C* (iso C* a')) (iso C* a') (decode-inv C* (iso C* a'))) (B* a (inv C* (iso C* a')) ?12 〉 g (iso C* a')
  lm1 (σ* q B*) p a c = {!!}
  lm1 (q ≃* q₁) p a c = {!!}
