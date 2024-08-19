/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# Factorization of ideals and fractional ideals of Dedekind domains

This file includes finset versions of ideal factors.
-/

noncomputable section

open scoped Classical

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable [IsDedekindDomain R] (v : HeightOneSpectrum R)

namespace Ideal

theorem finite_factors_of_nonZeroDivisor (r : nonZeroDivisors R) :
    { v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {r.val} }.Finite :=
  (Ideal.span {r.val}).finite_factors
    (nonZeroDivisors.ne_zero <| (Ideal.span_singleton_nonZeroDivisors.2 r.2))

abbrev factorsFinset {I : Ideal R} (h : I ≠ 0) :=
    (Ideal.finite_factors h).toFinset

abbrev factorsFinset_of_nonZeroDivisor (r : nonZeroDivisors R) :=
    (Ideal.finite_factors_of_nonZeroDivisor r).toFinset

end Ideal
