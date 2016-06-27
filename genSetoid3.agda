{-# OPTIONS --type-in-type #-}

module genSetoid3 where

open import Setoid
open import prop
open import Data.Empty
open import Data.Unit
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Fin
open import Setoid.Fibra-SS
open import Setoid.Isomorphism

record Graph : Set₁ where
  field
    Vertex : Set
    Edge   : Vertex → Vertex → Set

  MaybeEdge : Vertex → Vertex → Set
  MaybeEdge a b = ∀ (X : Vertex → Vertex → Set) →
    (∀ x → X x x) →
    (∀ {x} {y} → Edge x y → X x y) →
    X a b

  empty : ∀ a → MaybeEdge a a
  empty a = λ X Xemp _ → Xemp a

  just : ∀ {a b} → Edge a b → MaybeEdge a b
  just e = λ X _ Xjust → Xjust e

  record Fibra-GP : Set where
    field
      FibGP : Vertex → Set
      SubGP : ∀ {x y} → Edge x y → FibGP x ⇔ FibGP y

    Sigma-GP : Graph
    Sigma-GP = record { 
      Vertex = Σ[ g ∈ Vertex ] FibGP g ; 
      Edge = λ { (g , _) (g' , _) → Edge g g' } }

  open Fibra-GP public

open Graph public

UnitG : Graph
UnitG = record { Vertex = ⊤ ; Edge = λ _ _ → ⊥ }

SETOID : Graph
SETOID = record { Vertex = Setoid ; Edge = Iso }

MaybeIso = MaybeEdge SETOID

flatten : ∀ {A} {B} → MaybeIso A B → Iso A B
flatten p = p Iso id-iso (λ φ → φ)

record mGraph (G H : Graph) : Set where
  field
    appV : Vertex G → Vertex H
    appE : ∀ {g} {g'} → Edge G g g' → MaybeEdge H (appV g) (appV g')

  map : ∀ {g g'} → MaybeEdge G g g' → MaybeEdge H (appV g) (appV g')
  map p X Xemp Xjust = p (λ x y → X (appV x) (appV y)) (λ x → Xemp (appV x)) (λ e → appE e X Xemp Xjust)

Fibra-GS : Graph → Set
Fibra-GS G = mGraph G SETOID

-- Constant morphism

K : ∀ G {H} → Vertex H → mGraph G H
K G {H} h = record { appV = λ _ → h ; appE = λ _ → empty H h }

-- Product of two graphs

module Product (G H : Graph) where
  data EdgeProd : Vertex G × Vertex H → Vertex G × Vertex H → Set where
    -horiz : ∀ {g} {g'} → Edge G g g' → ∀ h → EdgeProd (g , h) (g' , h)
    -vert  : ∀ g {h} {h'} → Edge H h h' → EdgeProd (g , h) (g , h')

  ProdG : Graph
  ProdG = record { Vertex = Vertex G × Vertex H ; Edge = EdgeProd }
open Product public

record build-mPGraph (G H K : Graph) : Set where
  field
    appV : Vertex G → Vertex H → Vertex K
    appE1 : ∀ {g g'} → Edge G g g' → ∀ h → MaybeEdge K (appV g h) (appV g' h)
    appE2 : ∀ g {h h'} → Edge H h h' → MaybeEdge K (appV g h) (appV g h')
  
  appV-out : Vertex G × Vertex H → Vertex K
  appV-out (g , h) = appV g h

  appE-out : ∀ {x} {y} → Edge (ProdG G H) x y → MaybeEdge K (appV-out x) (appV-out y)
  appE-out (-horiz x h) = appE1 x h
  appE-out (-vert g x) = appE2 g x

  out : mGraph (ProdG G H) K
  out = record { appV = appV-out ; appE = appE-out }

module Fibra-GS {G} (A : Fibra-GS G) where
  
  FibGS = mGraph.appV A
  SubGS = mGraph.appE A
  SUBGS = mGraph.map A

  record Section : Set where
    field
      app : ∀ x → El (FibGS x)
      wd  : ∀ x x' x* → app x ~< flatten (SubGS x*) > app x'

    postulate WD : ∀ x x' x* → app x ~< flatten (SUBGS x*) > app x'
--    WD x x' x* with MaybeEdgeiMaybeEdge G x*
--    WD a .a x* | empty .a = {!r (FibGS _) (app a)!}
--    WD x x' x* | plus x₁ p = {!!}
--    WD x x' x* | minus x₁ p = {!!}

  EdgeSig : Σ[ g ∈ Vertex G ] El (FibGS g) → Σ[ g ∈ Vertex G ] El (FibGS g) → Set
  EdgeSig x y = ∀ (X : Σ[ g ∈ Vertex G ] El (FibGS g) → Σ[ g ∈ Vertex G ] El (FibGS g) → Set) →
    (∀ {g g' a} (e : Edge G g g') → X (g , a) (g' , transport (flatten (SubGS e)) a)) →
    (∀ {g a a'} → E (FibGS g) a a' → X (g , a) (g , a')) →
    X x y

  vert : ∀ {g a b} → E (FibGS g) a b → EdgeSig (g , a) (g , b)
  vert e _ _ Xvert = Xvert e

  Sigma-GS : Graph
  Sigma-GS = record { 
    Vertex = Σ[ g ∈ Vertex G ] El (FibGS g) ; 
    Edge = EdgeSig }

  π₁ : ∀ x y (e : EdgeSig x y) → MaybeEdge G (proj₁ x) (proj₁ y)
  π₁ _ _ e X Xemp Xjust = e (λ x y → X (proj₁ x) (proj₁ y)) (λ e → Xjust e) (λ _ → Xemp _)

  pp : mGraph Sigma-GS G
  pp = record { appV = proj₁ ; appE = π₁ _ _ }

  postulate  π₂ : ∀ x y (e : EdgeSig x y) → proj₂ x ~< flatten (SUBGS (π₁ x y e)) > proj₂ y
--  π₂ _ _ e = {!!}

open Fibra-GS public

pullback : ∀ {G} {H} → mGraph G H → Fibra-GS H → Fibra-GS G
pullback f A = record { 
  appV = λ g → mGraph.appV A (mGraph.appV f g) ; 
  appE = λ e → mGraph.map A (mGraph.appE f e) }

pullbackS : ∀ {G} {H} (f : mGraph G H) (A : Fibra-GS H) → Section A → Section (pullback f A)
pullbackS f A s = record { app = λ g → Section.app s (mGraph.appV f g) ; 
  wd = λ x x' x* → Section.WD s _ _ (mGraph.appE f x*) }

{-append : ∀ {Q R S} → MaybeIso Q R → MaybeIso R S → MaybeIso Q S
append (empty _) l = l
append (plus φ l) m = plus φ (append l m)

flatten : ∀ {R S} → MaybeIso R S → Iso R S
flatten (empty S) = id-iso S
flatten (plus x p) = comp-iso (flatten p) x

reverse : ∀ {R S} → MaybeIso R S → MaybeIso S R
reverse (empty S) = empty S
reverse (plus x l) = append (reverse l) (plus (inv-iso x) (empty _))

record Graph : Set₁ where
  field
    Vertex : Set
    Edge   : Vertex → Vertex → Set

  data MaybeEdge : Vertex → Vertex → Set where
    empty : ∀ x → MaybeEdge x x
    single : ∀ {x} {y} → Edge x y → MaybeEdge x y
    plus  : ∀ {x y z} → Edge x y → MaybeEdge y z → MaybeEdge x z
    minus : ∀ {x y z} → Edge y x → MaybeEdge y z → MaybeEdge x z

  record Fibra-GP : Set where
    field
      FibGP : Vertex → Set
      SubGP : ∀ {x y} → Edge x y → FibGP x ⇔ FibGP y

  open Fibra-GP public

  record Fibra-GS : Set where
    field
      FibGS : Vertex → Setoid
      SubGS : ∀ {x y} → Edge x y → MaybeIso (FibGS x) (FibGS y)

    SUBGS : ∀ {x y} → MaybeEdge x y → MaybeIso (FibGS x) (FibGS y)
    SUBGS (empty x) = empty (FibGS x)
    SUBGS (single e) = SubGS e
    SUBGS (plus e p) = append (SubGS e) (SUBGS p)
    SUBGS (minus e p) = append (reverse (SubGS e)) (SUBGS p)

  open Fibra-GS public

open Graph public

Setoid2Graph : Setoid → Graph
Setoid2Graph S = record { 
  Vertex = El S ;
  edgeList = E S }
--TODO Define setoid generated by a graph.  Prove these are inverses.

Sigma-GP : ∀ G → Fibra-GP G → Graph
Sigma-GP G φ = record { 
  Vertex = Σ[ g ∈ Vertex G ] FibGP φ g ; 
  edgeList = λ { (g , _) (g' , _) → Edge G g g' } }

Sigma-GS : ∀ G → Fibra-GS G → Graph
Sigma-GS G A = record { 
  Vertex = Σ[ g ∈ Vertex G ] El (FibGS A g) ; 
  edgeList = EdgeSig G A }

UnitG : Graph
UnitG = record { Vertex = ⊤ ; edgeList = λ _ _ → ⊥ }

{- append : ∀ {X} {G : graphOver X} {x y z : X} → pathsIn G x y → pathsIn G y z → pathsIn G x z
append (empty x) q = q
append (plus e p) q = plus e (append p q)
append (minus e p) q = minus e (append p q)

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

generateS : ∀ {X : Set} → graphOver X → Setoid
generateS {X} G = record { El = X; E = pathsIn G; r = empty;
  E* = λ x* y* → (λ xy   → conjugate x* y* xy) ,
                 (λ x'y' → conjugate (reverse x*) (reverse y*) x'y') }

genFun : ∀ {X Y : Set} (f : X → Y) (G : graphOver X) (H : graphOver Y) → Set
genFun f G H = (e : Edg G) → pathsIn H (f (s G e)) (f (t G e))

{- genFuns : ∀ {X Y} (G : graphOver X) (H : graphOver Y) → graphOver (genFun {!!} {!!} {!!})
genFuns = {!!} -}

record genIso {X Y : Set} (fg : X ⇔ Y) (G : graphOver X) (H : graphOver Y) : Set where
  field
    I+ : genFun (proj₁ fg) G H
    I- : genFun (proj₂ fg) H G
    I= : ∀ (x : X) (y : Y) → pathsIn G x ((proj₂ fg) y) ⇔ pathsIn H ((proj₁ fg) x) y
open genIso

record genFibS {X : Set} (G : graphOver X) : Set where
  constructor fibra
  field
    Fam  : X → Set
    FamS : ∀ (x : X) → graphOver (Fam x)
    Fib  : ∀ (e : Edg G) → Fam (s G e) ⇔ Fam (t G e)
    FibI : ∀ (e : Edg G) → genIso (Fib e) (FamS (s G e)) (FamS (t G e))
open genFibS

Π-S-Base : ∀ {X : Set} (G : graphOver X) (F : genFibS G) → Set
Π-S-Base {X} G F = Σ[ f ∈ ((x : X) → Fam F x) ]
                    ((e : Edg G) →
                      pathsIn (FamS F (t G e)) (proj₁ (Fib F e) (f (s G e))) (f (t G e)))

{- Π-S-S : ∀ {X : Set} (G : graphOver X) (F : genFibS G) → graphOver (Π-S-Base G F)
Π-S-S G (fibra Fam FamS Fib FibI) =
  record {
   Edg = {!(e : Edg G X) → ?!};
   s = {!!};
   t = {!!} } -}

record Graph : Set₁ where
  field
    Vertex  : Set
    isGraph : graphOver Vertex
  open graphOver isGraph public

Fib-GS : Graph → Set
Fib-GS G = genFibS (Graph.isGraph G)

UnitG : Graph
UnitG = record { 
  Vertex = ⊤ ; 
  isGraph = record { 
    Edg = ⊤ ; 
    s = λ _ → tt ; 
    t = λ _ → tt } }

Sigma-GP : ∀ G → Fib-GS G → Graph
Sigma-GP G A = record { 
  Vertex = Σ[ g ∈ Graph.Vertex G ] genFibS.Fam A g ; 
  isGraph = record { 
    Edg = Σ[ e ∈ Graph.Edg G ] ({!!} ∋ {!!} ~[ {!!} ] {!!}) ; s = {!!} ; t = {!!} } }
-}
-}

