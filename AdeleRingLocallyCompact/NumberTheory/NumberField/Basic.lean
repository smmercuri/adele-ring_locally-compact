/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib

/-!
# Number fields

In this file we define the linear equivalence between a number field `K` and `ℚⁿ`, where `n` is the
degree of the field extension of `K` over `ℚ`.
-/

noncomputable section

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

def ratBasis_equiv : (Fin (FiniteDimensional.finrank ℚ K) → ℚ) ≃ₗ[ℚ] K :=
  LinearEquiv.symm (Basis.equivFun (FiniteDimensional.finBasis ℚ K))

end NumberField
