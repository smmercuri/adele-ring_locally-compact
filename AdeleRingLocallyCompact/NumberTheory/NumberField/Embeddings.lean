/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib
import AdeleRingLocallyCompact.Topology.UniformSpace.Basic
import AdeleRingLocallyCompact.Analysis.NormedSpace.Completion
import AdeleRingLocallyCompact.NumberTheory.NumberField.Completion

/-!
# Embeddings of number fields

This file contains decidability criteria for checking whether an infinite place of a
number field is real or complex.

## Main results
 - `NumberField.InfinitePlace.Completion.isReal_iff_basis`: Decidability criterion for whether
  an infinite place is real; given by checking whether the imaginary parts of the finitely-many
  basis elements of a number field over ℚ are all zero.

## Tags
number field, embeddings, places, infinite places
-/
noncomputable section

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K] (v : InfinitePlace K)

theorem isReal_iff_basis :
    IsReal v ↔ ∀ (i : Fin (FiniteDimensional.finrank ℚ K)),
      (v.embedding ((FiniteDimensional.finBasis ℚ K) i)).im = 0 := by
  simp only [isReal_iff, ComplexEmbedding.isReal_iff, RingHom.ext_iff,
      ComplexEmbedding.conjugate_coe_eq, Complex.conj_eq_iff_im]
  refine ⟨fun hv _ => hv _, fun hv x => ?_⟩
  · rw [← (FiniteDimensional.finBasis ℚ K).sum_repr x]
    simp only [map_sum, Complex.im_sum, map_rat_smul, Complex.smul_im, hv, smul_zero,
      Finset.sum_const_zero]

instance : DecidablePred (IsReal : InfinitePlace K → Prop) :=
  letI (v : InfinitePlace K) : Decidable (∀ (i : Fin (FiniteDimensional.finrank ℚ K)),
    (v.embedding ((FiniteDimensional.finBasis ℚ K) i)).im = 0) := Fintype.decidableForallFintype
  fun v => decidable_of_iff
    (∀ (i : Fin (FiniteDimensional.finrank ℚ K)), (v.embedding ((FiniteDimensional.finBasis ℚ K) i)).im = 0)
      v.isReal_iff_basis.symm

instance : DecidablePred (IsComplex : InfinitePlace K → Prop) :=
  fun v => decidable_of_iff (¬IsReal v) not_isReal_iff_isComplex

end NumberField.InfinitePlace
