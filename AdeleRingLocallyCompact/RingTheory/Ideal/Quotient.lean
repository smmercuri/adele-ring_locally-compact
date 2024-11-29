/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.RingTheory.Ideal.Quotient

/-!
# Ideal quotients

Ideal quotient versions of some basic results.

-/

namespace Ideal

theorem Quotient.mk_out' {R : Type*} [CommRing R] {I : Ideal R} (x : R ⧸ I) :
    Ideal.Quotient.mk I (Quotient.out' x) = x := by
  rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk''_eq_mk, Quotient.out_eq']

theorem Quotient.out_sub {R : Type*} [CommRing R] (I : Ideal R) (x : R) :
    (Ideal.Quotient.mk I x).out' - x ∈ I := by
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out']

theorem Quotient.out_sub_dvd {R : Type*} [CommRing R] {I : Ideal R} {y : R} (x : R)
    (hI : I = Ideal.span {y}) :
    y ∣ (Ideal.Quotient.mk I x).out' - x := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, hI, Ideal.Quotient.mk_out']

end Ideal
