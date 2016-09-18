{-# OPTIONS --type-in-type #-}

module freeSetoid where

open import Function

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import prop
open import Setoid
-- open import Setoid.Isomorphism
-- open import Setoid.Fibra-SP

record graphOver (X : Set) : Set where
  constructor makeGraph
  field
    Edg  : Set
    s : Edg → X
    t : Edg → X
open graphOver

data pathsIn {X : Set} (G : graphOver X) : X → X → Set where
  empty : ∀ (x : X) → pathsIn G x x
  plus  : ∀ {z : X} → (e : Edg G) → pathsIn G (t G e) z → pathsIn G (s G e) z
  minus : ∀ {z : X} → (e : Edg G) → pathsIn G (s G e) z → pathsIn G (t G e) z

{- append : ∀ {X} {G : graphOver X} {x y z : X} → pathsIn G x y → pathsIn G y z → pathsIn G x z
append (empty x) q = q
append (plus e p) q = plus e (append p q)
append (minus e p) q = minus e (append p q) -}

append-reverse : ∀ {X} {G : graphOver X} {x y z : X}
                → pathsIn G y x → pathsIn G y z → pathsIn G z x
append-reverse p (empty _) = p
append-reverse p (plus e q) = append-reverse (minus e p) q
append-reverse p (minus e q) = append-reverse (plus e p) q 

conjugate : ∀ {X} {G : graphOver X} {x x' y y' : X}
            → pathsIn G x x' → pathsIn G y y' → pathsIn G x y → pathsIn G x' y'
conjugate {X} {G} x* y* p = append-reverse y* (append-reverse x* p)

reverse  : ∀ {X} {G : graphOver X} {x y : X} → pathsIn G x y → pathsIn G y x
reverse' : ∀ {X} {G : graphOver X} {x y : X} → pathsIn G x y → pathsIn G y x
reverse  {X} {G} {x} {y} p = append-reverse  (empty x) p
reverse' p = conjugate p (empty _) (empty _)

append  : ∀ {X} {G : graphOver X} {x y z : X} → pathsIn G x y → pathsIn G y z → pathsIn G x z
append' : ∀ {X} {G : graphOver X} {x y z : X} → pathsIn G x y → pathsIn G y z → pathsIn G x z
append  p q = append-reverse q (reverse p)
append' p q = conjugate (empty _) q p

freeS : ∀ {X : Set} → graphOver X → isSetoid X
freeS {X} G = record {  E = pathsIn G; r = empty;
  E* = λ x* y* → (λ xy   → conjugate x* y* xy) ,
                 (λ x'y' → conjugate (reverse x*) (reverse y*) x'y') }

-- (f,g) are iso if x=g(y) <=> f(x)=y
isFunIso : ∀ {X Y : Set} (XS : isSetoid X) (YS : isSetoid Y) (fg : X ⇔ Y) → Set
isFunIso XS YS fg = ∀ x y → E XS x (proj₂ fg y) ⇔ E YS (proj₁ fg x) y

-- R ⊆ X×Y is iso if ∃ R⁺, R⁻, R⁼.. so it's bijective
record isRelIso {X Y : Set} (XS : isSetoid X) (YS : isSetoid Y) (R : X → Y → Set) : Set where
  constructor
    makeIso
  field
    R+ : ∀ (x : X) → Σ[ x+ ∈ Y ] (∀ (y : Y) → R x y ⇔ E YS x+ y)
    R- : ∀ (y : Y) → Σ[ y- ∈ X ] (∀ (x : X) → E XS x y- ⇔ R x y)
  R⁺ : X → Y
  R⁻ : Y → X
  R⁼ : ∀ x y → E XS x (R⁻ y) ⇔ E YS (R⁺ x) y
  R⁺ x = proj₁ (R+ x)
  R⁻ y = proj₁ (R- y)
  R⁼ x y = proj₁ (proj₂ (R+ x) y) ∘ proj₁ (proj₂ (R- y) x) ,
           proj₂ (proj₂ (R- y) x) ∘ proj₂ (proj₂ (R+ x) y)
open isRelIso

RelIsoIsFunIso : ∀ {X Y : Set} (XS : isSetoid X) (YS : isSetoid Y) (R : X → Y → Set)
                 → (RR : isRelIso XS YS R) → isFunIso XS YS (R⁺ RR , R⁻ RR)
RelIsoIsFunIso XS YS R RR = R⁼ RR

-- sometimes, a pair of maps (f,g) and a relation R "fit together" into one iso...
areCohIso : ∀ {X Y : Set} (XS : isSetoid X) (YS : isSetoid Y) (fg : X ⇔ Y) (R : X → Y → Set) → Set
areCohIso {X} {Y} XS YS fg R = (∀ x y → E XS x (proj₂ fg y) ⇔ R x y) × (∀ x y → R x y ⇔ E YS (proj₁ fg x) y)

FreeUnit : graphOver ⊤
FreeUnit = record { Edg = ⊥; s = λ _ → tt; t = λ _ → tt }

FreeEmpty : graphOver ⊥
FreeEmpty = record { Edg = ⊥; s = λ z → z; t = λ z → z }

isFibP : ∀ {X : Set} (G : graphOver X) (F : X → Set) → Set
isFibP {X} G F = ∀ (e : Edg G) → F (s G e) ⇔ F (t G e)

record isFibS {X : Set} (G : graphOver X) (F : X → Set) : Set where
  constructor
    makeFibS
  field
    Fp : isFibP G F
    Fs : ∀ (x : X) → isSetoid (F x)
    Fi : ∀ (e : Edg G) → Σ[ R ∈ (F (s G e) → F (t G e) → Set) ] (areCohIso (Fs (s G e)) (Fs (t G e)) (Fp e) R)
open isFibS

FibS : ∀ {X : Set} (G : graphOver X) → Set
FibS {X} G = Σ[ F ∈ (X → Set) ] isFibS G F

ΣfS0 : ∀ {X : Set} (G : graphOver X) {F : X → Set} (FF : isFibS G F) → Set
ΣfS0 {X} G {F} FF = Σ[ x ∈ X ] (F x)

data ΣfS1 {X : Set} (G : graphOver X) {F : X → Set} (FF : isFibS G F) : Set where
  ΣfS-top : ∀ (x : X) (a b : F x) →
              E (Fs FF x) a b → ΣfS1 G FF
  ΣfS-gen : ∀ (e : Edg G) (a : F (s G e)) (b : F (t G e)) →
              proj₁ (Fi FF e) a b → ΣfS1 G FF

ΣfS : ∀ {X : Set} (G : graphOver X) {F : X → Set} (FF : isFibS G F)
      → graphOver (Σ[ x ∈ X ] (F x))
ΣfS {X} G {F} FF = record { Edg = ΣfS1 G FF; s = s'; t = t' } where
            s' : ΣfS1 G FF → (Σ[ x ∈ X ] (F x))
            s' (ΣfS-top x a b x₁) = x , a
            s' (ΣfS-gen e a b x) = s G e , a
            t' : ΣfS1 G FF → (Σ[ x ∈ X ] (F x))
            t' (ΣfS-top x a b x₁) = x , b
            t' (ΣfS-gen e a b x) = t G e , b

-- data ΠfS1 : {X : Set} (G : graphOver X) {F : X → Set} (FF : isFibS G F) : Set 
ΠfS0 : ∀ {X : Set} (G : graphOver X) {F : X → Set} (FF : isFibS G F) → Set
ΠfS0 {X} G {F} FF = Σ[ f ∈ (∀ (x : X) → F x) ] (∀ (g : Edg G) → proj₁ (Fi FF g) (f (s G g)) (f (t G g)))

ΠfS1 : ∀ {X : Set} (G : graphOver X) {F : X → Set} (FF : isFibS G F) →
         (f g : (∀ (x : X) → F x)) → Set
ΠfS1 {X} G FF f g = ∀ (x : X) → E (Fs FF x) (f x) (g x)

ΠfS : ∀ {X : Set} (G : graphOver X) {F : X → Set} (FF : isFibS G F)
      → isSetoid (ΠfS0 G FF)
ΠfS G {F} FF  = makeSetoid
              (λ f g → ΠfS1 G FF (proj₁ f) (proj₁ g))
              (λ f → λ x → r (Fs FF x) (proj₁ f x))
              (λ {f1} {f2} f12 {g1} {g2} g12 →
                 (λ f1=g1 → λ x → proj₁ (E* (Fs FF x) (f12 x) (g12 x)) (f1=g1 x)) ,
                 (λ f2=g2 → λ x → proj₂ (E* (Fs FF x) (f12 x) (g12 x)) (f2=g2 x)))

{-
record genFib {X : Set} (G : graphOver X) : Set where
  field
    Fam  : X → Setoid
    Fam* : ∀ (e : Edg G) → Iso (Fam (s G e)) (Fam (t G e))
open genFib

Σ-C-S-Base : ∀ {X : Set} (G : graphOver X) (F : genFib G) → Set
Σ-C-S-Base {X} G F = Σ[ x ∈ X ] (El (Fam F x))

data Σ-C-S-Data {X : Set} (G : graphOver X) (F : genFib G) : Set where
  ΣfS-top : ∀ (x : X) (a b : El (Fam F x)) →
              E (Fam F x) a b → Σ-C-S-Data G F
  ΣfS-gen : ∀ (e : Edg G) (a : El (Fam F (s G e))) (b : El (Fam F (t G e))) →
              FibSP.Fib (Iso.R (Fam* F e)) (a , b) → Σ-C-S-Data G F

Σ-C-S : ∀ {X : Set} (G : graphOver X) (F : genFib G) → graphOver (Σ-C-S-Base G F)
Σ-C-S {X} G F = record {Edg = Σ-C-S-Data G F; s = s'; t = t'} where
            s' : Σ-C-S-Data G F → Σ-C-S-Base G F
            s' (ΣfS-top x a b x₁) = x , a
            s' (ΣfS-gen e a b x) = s G e , a
            t' : Σ-C-S-Data G F → Σ-C-S-Base G F
            t' (ΣfS-top x a b x₁) = x , b
            t' (ΣfS-gen e a b x) = t G e , b
-}

{- genFun : ∀ {X Y : Set} (f : X → Y) (G : graphOver X) (H : graphOver Y) → Set
genFun f G H = (e : Edg G) → pathsIn H (f (s G e)) (f (t G e))

-- genFuns : ∀ {X Y} (G : graphOver X) (H : graphOver Y) : graphOver (genFun ? ?)

record genIso {X Y : Set} (fg : X ⇔ Y) (G : graphOver X) (H : graphOver Y) : Set where
  field
    I+ : genFun (proj₁ fg) G H
    I- : genFun (proj₂ fg) H G
    I= : ∀ (x : X) (y : Y) → pathsIn G x ((proj₂ fg) y) ⇔ pathsIn H ((proj₁ fg) x) y
open genIso

record genFibS {X : Set} (G : graphOver X) : Set where
  constructor fibra
  field
    sFam  : X → Set
    sFamS : ∀ (x : X) → graphOver (sFam x)
    sFib  : ∀ (e : Edg G) → sFam (s G e) ⇔ sFam (t G e)
    sFibI : ∀ (e : Edg G) → genIso (sFib e) (sFamS (s G e)) (sFamS (t G e))
open genFibS

Π-S-Base : ∀ {X : Set} (G : graphOver X) (F : genFibS G) → Set
Π-S-Base {X} G F = Σ[ f ∈ ((x : X) → sFam F x) ]
                    ((e : Edg G) →
                      pathsIn (sFamS F (t G e)) (proj₁ (sFib F e) (f (s G e))) (f (t G e)))

Π-S-S : ∀ {X : Set} (G : graphOver X) (F : genFibS G) → graphOver (Π-S-Base G F)
Π-S-S G (fibra Fam FamS Fib FibI) =
  record {
   Edg = {!(e : Edg G X) → ?!};
   s = {!!};
   t = {!!} }
-}
