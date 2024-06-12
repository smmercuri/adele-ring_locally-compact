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

This file defines the main approach to the completion of a number field with respect to an
infinite place.

## Main definitions
 - `NumberField.InfinitePlace.completion` is the Archimedean completion of a number field as
   an infinite place, obtained by defining a uniform space structure inherited from ℂ via the
   embedding associated to an infinite place.

## Main results
 - `NumberField.InfinitePlace.Completion.locallyCompactSpace` : the Archimedean completion
   of a number field is locally compact.

## Tags
number field, embeddings, places, infinite places
-/
noncomputable section

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K] (v : InfinitePlace K)

/- The normed field structure of a number field coming from the embedding asociated to
an infinite place. -/
def normedField : NormedField K :=
  inferInstanceAs (NormedField (WithAbs v.1))

theorem embedding_eq_comp :
    v.1 = (IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ)).comp v.embedding.injective := by
  rw [← v.2.choose_spec]; rfl

/-- The completion of a number field at an infinite place. -/
def completion := v.1.completion

namespace Completion

instance : NormedField v.completion :=
  letI := (WithAbs.uniformInducing_of_comp v.embedding_eq_comp).completableTopField
  UniformSpace.Completion.instNormedField (WithAbs v.1)

instance : CompleteSpace v.completion :=
  inferInstanceAs (CompleteSpace v.1.completion)

instance : Inhabited v.completion :=
  inferInstanceAs (Inhabited v.1.completion)

instance : Coe K v.completion :=
  inferInstanceAs (Coe (WithAbs v.1) v.1.completion)

instance : Algebra K v.completion :=
  inferInstanceAs (Algebra (WithAbs v.1) v.1.completion)

/-- The embedding associated to an infinite place extended to an embedding `v.completion →+* ℂ`. -/
def extensionEmbedding : v.completion →+* ℂ :=
  UniformSpace.Completion.extensionHom _
    (WithAbs.uniformInducing_of_comp v.embedding_eq_comp).uniformContinuous.continuous

variable {v}

/-- The embedding `v.completion →+* ℂ` preserves distances. -/
theorem extensionEmbedding_dist_eq (x y : v.completion) :
    dist (extensionEmbedding v x) (extensionEmbedding v y) =
      dist x y := by
  refine (UniformSpace.Completion.induction_on₂ x y ?_ (fun x y => ?_))
  · refine isClosed_eq ?_ continuous_dist
    · exact (continuous_iff_continuous_dist.1 (UniformSpace.Completion.continuous_extension))
  · rw [extensionEmbedding, UniformSpace.Completion.extensionHom, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, UniformSpace.Completion.dist_eq]
    simp only [UniformSpace.Completion.extension_coe
      (WithAbs.uniformInducing_of_comp v.embedding_eq_comp).uniformContinuous]
    exact Isometry.dist_eq (WithAbs.isometry_of_comp v.embedding_eq_comp) _ _

variable (v)

/-- The embedding `v.completion →+* ℂ` is an isometry. -/
theorem isometry_extensionEmbedding : Isometry (extensionEmbedding v) :=
  Isometry.of_dist_eq extensionEmbedding_dist_eq

/-- The embedding `v.completion →+* ℂ` is a closed embedding. -/
theorem closedEmbedding_extensionEmbedding: ClosedEmbedding (extensionEmbedding v) :=
  (isometry_extensionEmbedding v).closedEmbedding

/-- The completion of a number field at an infinite place is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (v.completion) :=
  (closedEmbedding_extensionEmbedding v).locallyCompactSpace

end Completion

end NumberField.InfinitePlace
