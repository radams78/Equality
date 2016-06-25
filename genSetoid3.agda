{-# OPTIONS --type-in-type #-}

module genSetoid3 where

open import Setoid
open import prop
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Setoid.Fibra-SS
open import Setoid.Isomorphism

data Shape : Set where
  empty : Shape
  single : Shape

record Graph : Set₁ where
  field
    Vertex : Set
    Edge   : Vertex → Vertex → Set

  data VertexList : Shape → Vertex → Vertex → Set where
    empty : ∀ a → VertexList empty a a
    single : ∀ a b → VertexList single a b

  data EdgePos : ∀ {s a b} → VertexList s a b → Vertex → Vertex → Set where
    edge : ∀ {a b} → EdgePos (single a b) a b

  EdgeList : ∀ {s a b} → VertexList s a b → Set
  EdgeList l = ∀ {a'} {b'} → EdgePos l a' b' → Edge a' b'

--  tail : ∀ {a} {b} {c} {l : VertexList b c} → EdgeList (cons a l) → EdgeList l
--  tail l e = l (next e)

--  appendE : ∀ {a b c} {l : VertexList a b} {m : VertexList b c} → EdgeList l → EdgeList m → EdgeList (append l m)
--  appendE {l = empty _} _ Em e = Em e
--  appendE {l = cons _ _} El _ first = El first
--  appendE {l = cons _ _} El Em (next e) = appendE (tail El) Em e

  record Path (shape : Shape) (a b : Vertex) : Set where
    field
      vertexList : VertexList shape a b
      edgeList   : EdgeList vertexList

  emptyP : ∀ a → Path empty a a
  emptyP a = record {
    vertexList = empty a;
    edgeList = λ () }

  singleE : ∀ {a} {b} → Edge a b → EdgeList (single a b)
  singleE e edge = e

  singleP : ∀ {a} {b} → Edge a b → Path single a b
  singleP {a} {b} e = record { vertexList = single a b ; edgeList = singleE e }

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

mapV : ∀ {s} {G H : Graph} (f : Vertex G → Vertex H) {a} {b} → VertexList G s a b → VertexList H s (f a) (f b)
mapV f (empty a) = empty (f a)
mapV f (single a b) = single (f a) (f b)

UnitG : Graph
UnitG = record { Vertex = ⊤ ; Edge = λ _ _ → ⊥ }

SETOID : Graph
SETOID = record { Vertex = Setoid ; Edge = Iso }

SetoidList = VertexList SETOID

pre-flatten : ∀ {s S T} {RR : SetoidList s S T} → (∀ {S' T'} → EdgePos SETOID RR S' T' → Iso S' T') → Iso S T
pre-flatten {RR = empty S} ee = id-iso S
pre-flatten {RR = single S T} ee = ee edge

IsoList = Path SETOID

flatten : ∀ {s} {S} {T} → IsoList s S T → Iso S T
flatten l = pre-flatten (Path.edgeList l)

mapIso* : ∀ {s A B C D} → IsoList s A B → IsoList s C D → IsoList s (ISO A C) (ISO B D)
mapIso* {empty} record { vertexList = (empty a₁) ; edgeList = edgeList } record { vertexList = (empty a) ; edgeList = edgeList₁ } = emptyP SETOID (ISO a₁ a)
mapIso* {single} record { vertexList = (single a₁ b) ; edgeList = edgeList } record { vertexList = (single a D) ; edgeList = edgeList₁ } = singleP SETOID (Iso* (edgeList edge) (edgeList₁ edge))

flatten-mapIso* : ∀ {s A B C D} (l : IsoList s A B) (m : IsoList s C D) →
  E (ISO (ISO A C) (ISO B D)) (flatten (mapIso* l m)) (Iso* (flatten l) (flatten m))
flatten-mapIso* {empty} record { vertexList = (empty a₁) ; edgeList = edgeList } record { vertexList = (empty a) ; edgeList = edgeList₁ } x y = sym-p (iso-eq {a₁} {a} {x} {y})
flatten-mapIso* {single} record { vertexList = (single a₁ b) ; edgeList = edgeList } record { vertexList = (single a D) ; edgeList = edgeList₁ } x y = refl-p

record Fibra-GS (G : Graph) : Set where
  field
    FibGS : Vertex G → Setoid
    shape : ∀ {x y} → Edge G x y → Shape
    SubGS : ∀ {x y} (e : Edge G x y) → IsoList (shape e) (FibGS x) (FibGS y)

  SHAPE : ∀ {s x y} → Path G s x y → Shape
  SHAPE {empty} p = empty
  SHAPE {single} record { vertexList = (single x b) ; edgeList = edgeList } = shape (edgeList edge)

  SUBGS : ∀ {s x y} (p : Path G s x y) → IsoList (SHAPE p) (FibGS x) (FibGS y)
  SUBGS {empty} record { vertexList = (empty a) ; edgeList = edgeList } = emptyP SETOID (FibGS a)
  SUBGS {single} record { vertexList = (single x b) ; edgeList = edgeList } = SubGS (edgeList edge)

  record Section : Set where
    field
      app : ∀ x → El (FibGS x)
      wd  : ∀ x x' x* → app x ~< flatten (SubGS x*) > app x'

    WD : ∀ {s} x x' x* → app x ~< flatten (SUBGS {s} x*) > app x'
    WD {empty} a .a record { vertexList = (empty .a) ; edgeList = edgeList } = r (FibGS a) (app a)
    WD {single} a b record { vertexList = (single .a .b) ; edgeList = edgeList } = wd a b (edgeList edge)

  data EdgeSig : Σ[ g ∈ Vertex G ] El (FibGS g) → Σ[ g ∈ Vertex G ] El (FibGS g) → Set where
    horiz : ∀ {g g' a} (e : Edge G g g') → EdgeSig (g , a) (g' , transport (flatten (SubGS e)) a)
    vert  : ∀ {g a a'} → E (FibGS g) a a' → EdgeSig (g , a) (g , a')

  horiz? : ∀ {x} {y} → EdgeSig x y → Shape
  horiz? (horiz _) = single
  horiz? (vert _) = empty

  π₁ : ∀ x y (e : EdgeSig x y) → Path G (horiz? e) (proj₁ x) (proj₁ y)
  π₁ _ _ (horiz e) = singleP G e
  π₁ _ _ (vert x) = emptyP G _

  π₂ : ∀ x y (e : EdgeSig x y) → proj₂ x ~< flatten (SUBGS (π₁ x y e)) > proj₂ y
  π₂ _ _ (horiz e) = iso-transport (flatten (SubGS e)) _
  π₂ _ _ (vert x) = x

  Sigma-GS : Graph
  Sigma-GS = record { 
    Vertex = Σ[ g ∈ Vertex G ] El (FibGS g) ; 
    Edge = EdgeSig }

open Fibra-GS public

{-append : ∀ {Q R S} → IsoList Q R → IsoList R S → IsoList Q S
append (empty _) l = l
append (plus φ l) m = plus φ (append l m)

flatten : ∀ {R S} → IsoList R S → Iso R S
flatten (empty S) = id-iso S
flatten (plus x p) = comp-iso (flatten p) x

reverse : ∀ {R S} → IsoList R S → IsoList S R
reverse (empty S) = empty S
reverse (plus x l) = append (reverse l) (plus (inv-iso x) (empty _))

record Graph : Set₁ where
  field
    Vertex : Set
    Edge   : Vertex → Vertex → Set

  data Path : Vertex → Vertex → Set where
    empty : ∀ x → Path x x
    single : ∀ {x} {y} → Edge x y → Path x y
    plus  : ∀ {x y z} → Edge x y → Path y z → Path x z
    minus : ∀ {x y z} → Edge y x → Path y z → Path x z

  record Fibra-GP : Set where
    field
      FibGP : Vertex → Set
      SubGP : ∀ {x y} → Edge x y → FibGP x ⇔ FibGP y

  open Fibra-GP public

  record Fibra-GS : Set where
    field
      FibGS : Vertex → Setoid
      SubGS : ∀ {x y} → Edge x y → IsoList (FibGS x) (FibGS y)

    SUBGS : ∀ {x y} → Path x y → IsoList (FibGS x) (FibGS y)
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
