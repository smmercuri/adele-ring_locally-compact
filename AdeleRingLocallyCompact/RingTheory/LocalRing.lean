import Mathlib

variable (R : Type u) [CommRing R] [LocalRing R]

def ResidueRing_order (n : ℕ) := R ⧸ (LocalRing.maximalIdeal R)^n

noncomputable instance : CommRing (ResidueRing_order R n) :=
  show CommRing (R ⧸ (LocalRing.maximalIdeal R)^n) from inferInstance
