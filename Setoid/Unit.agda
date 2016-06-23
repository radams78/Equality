module Setoid.Unit where

open import Data.Unit
open import prop
open import Setoid

UnitS : Setoid
UnitS = record { 
  El = ⊤ ; 
  E = λ _ _ → ⊤ ; 
  r = λ _ → tt ; 
  E* = λ _ _ → refl-p }
