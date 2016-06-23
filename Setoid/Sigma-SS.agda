module Setoid.Sigma-SS where

open import Data.Product
open import Setoid
open import Setoid.Fibra-SS

Sigma-SS : ∀ A → Fibra-SS A → Setoid
Sigma-SS A B = record { 
  El = Σ[ a ∈ El A ] ElF B a ; 
  E = λ {(a , b) (a' , b') → 
    Σ[ a* ∈ E A a a' ] (B ∋ b ~[ a* ] b')} ; 
  r = λ {(a , b) → (r A a) , {!Fibra-SS.SubSSr B b b!}} ; E* = {!!} }
