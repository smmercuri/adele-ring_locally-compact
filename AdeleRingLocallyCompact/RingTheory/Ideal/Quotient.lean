/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# Ideal quotients

Ideal quotient version of `Submodule.mk_out'`.

-/

namespace Ideal

theorem Quotient.mk_out' {R : Type*} [CommRing R] {I : Ideal R} {x : R ⧸ I} :
    Ideal.Quotient.mk I (Quotient.out' x) = x := by
  rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk''_eq_mk, Quotient.out_eq']

end Ideal
