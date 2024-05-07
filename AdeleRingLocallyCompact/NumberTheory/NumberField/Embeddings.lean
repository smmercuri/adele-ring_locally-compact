/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# Embeddings of number fields

This file defines the completion of a number field with respect to an infinite place.

## Main definitions
 - `NumberField.InfinitePlace.completion` is the Archimedean completion of a number field as
   an infinite place, obtained by embedding as a subfield of ℂ and completing this subfield.

## Main results
 - `NumberField.InfinitePlace.Completion.locallyCompactSpace` : the Archimedean completion
   of a number field is locally compact.

## Implementation notes
 - There are two main choices for formalising the completion of a number field `K` at
  an infinite place `v`. One is to complete `K` directly using `UniformSpace.Completion`
  and the uniform space induced by the absolute value associated to `v`. To show that
  the resultant completion is a field requires one to prove that `K` has a
  `completableTopField` instance. Alternatively, and the approach taken here, is to
  note that the absolute values associated to infinite places are given by composing
  the various embeddings of `K →+* ℂ` with the usual complex absolute value. So we
  can first embed `K` into a `Subfield ℂ` type, and then complete the embedding
  using `UniformSpace.Completion` with respect to the usual complex absolute value.
  `Subfield ℂ` already has instances such as `completableTopField`.
 - By splitting out the embedding from the completion, the consequence of this approach
  is that the inferred absolute value on `v.completion K` is just the complex absolute value.
  In the literature, the absolute value is the composition of the embedding with the complex
  absolute value. Therefore, we define the coercion from `K → v.completion K` using the
  embedding associated to `v` to align the two approaches.

## Tags
number field, embeddings, places, infinite places
-/
noncomputable section

namespace NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

instance : Inhabited (InfinitePlace K) :=
  ⟨Classical.choice (instNonemptyInfinitePlace K)⟩

section DerivedInstances

variable {K}

def normedDivisionRing : NormedDivisionRing K :=
  NormedDivisionRing.induced _ _ v.embedding v.embedding.injective

instance uniformSpace : UniformSpace K := UniformSpace.comap v.embedding inferInstance

instance uniformAddGroup : @UniformAddGroup K v.uniformSpace _ :=
  UniformAddGroup.comap v.embedding

instance topologicalSpace : TopologicalSpace K := v.uniformSpace.toTopologicalSpace

instance topologicalDivisionRing : @TopologicalDivisionRing K _ v.topologicalSpace :=
  v.normedDivisionRing.to_topologicalDivisionRing

instance topologicalRing : @TopologicalRing K v.topologicalSpace _ :=
  @TopologicalDivisionRing.toTopologicalRing _ _ v.topologicalSpace _

end DerivedInstances

variable {K}

theorem embedding_uniformInducing : @UniformInducing _ _ v.uniformSpace _ v.embedding := by
  rw [@uniformInducing_iff_uniformSpace]; rfl

instance pseudoMetricSpace : PseudoMetricSpace K :=
  @UniformInducing.comapPseudoMetricSpace _ _ v.uniformSpace _ _ v.embedding_uniformInducing

theorem topEmbedding : @Embedding _ _ v.topologicalSpace _ (v.embedding) := by
  rw [@embedding_iff, @inducing_iff]
  exact ⟨rfl, v.embedding.injective⟩

theorem isometry : @Isometry _ _ v.pseudoMetricSpace.toPseudoEMetricSpace _ (v.embedding) :=
  @Embedding.to_isometry _ _ v.topologicalSpace _ _ v.topEmbedding

theorem embedding_uniformContinuous : @UniformContinuous _ _ v.uniformSpace _ v.embedding :=
  @UniformInducing.uniformContinuous _ _ v.uniformSpace _ _ v.embedding_uniformInducing

theorem embedding_continuous : @Continuous _ _ v.topologicalSpace _ v.embedding :=
  @UniformContinuous.continuous _ _ v.uniformSpace _ _ v.embedding_uniformContinuous

instance t0Space : @T0Space K v.topologicalSpace :=
  @t0Space_of_injective_of_continuous _ _ v.topologicalSpace _ _ v.embedding.injective v.embedding_continuous _

instance completableTopField : @CompletableTopField K _ v.uniformSpace := by
  apply @CompletableTopField.mk _ _ v.uniformSpace
  intro F F_cau inf_F
  have h_cau_i := @UniformInducing.cauchy_map_iff _ _ v.uniformSpace _ _ v.embedding_uniformInducing
  rw [← h_cau_i] at F_cau ⊢
  have h_comm : (v.embedding ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ v.embedding := by
    ext; simp only [Function.comp_apply, map_inv₀, Subfield.coe_inv]
  rw [Filter.map_comm h_comm]
  apply CompletableTopField.nice _ F_cau
  rw [← Filter.push_pull', ← map_zero v.embedding]
  have h_inducing := (@UniformInducing.inducing _ _ v.uniformSpace _ _ v.embedding_uniformInducing)
  have h_nhds := @Inducing.nhds_eq_comap _ _ _ v.topologicalSpace _ h_inducing
  rw [← h_nhds, inf_F, Filter.map_bot]

variable (K)

def completion := @UniformSpace.Completion K v.uniformSpace

namespace Completion

instance : UniformSpace (v.completion K) :=
  @UniformSpace.Completion.uniformSpace _ v.uniformSpace

instance : CompleteSpace (v.completion K) :=
  @UniformSpace.Completion.completeSpace _ v.uniformSpace

instance : Field (v.completion K) :=
  @UniformSpace.Completion.instField _ _ v.uniformSpace v.topologicalDivisionRing _ _

instance : Inhabited (v.completion K) :=
  ⟨0⟩

instance : TopologicalRing (v.completion K) :=
  @UniformSpace.Completion.topologicalRing K _ v.uniformSpace _ v.uniformAddGroup

instance : Dist (v.completion K) :=
  @UniformSpace.Completion.instDistCompletionToUniformSpace _ v.pseudoMetricSpace

instance : T0Space (v.completion K) :=
  @UniformSpace.Completion.t0Space _ v.uniformSpace

instance metricSpace : MetricSpace (v.completion K) :=
  @UniformSpace.Completion.instMetricSpace _ v.pseudoMetricSpace

def extensionEmbedding :=
  @UniformSpace.Completion.extensionHom K _ v.uniformSpace v.topologicalRing v.uniformAddGroup
    ℂ _ _ _ _ v.embedding v.embedding_continuous _ _

theorem extensionEmbedding_injective : Function.Injective (extensionEmbedding K v) :=
  (extensionEmbedding K v).injective

variable {K v}

/- The embedding `Kᵥ → ℂ` preserves distances. -/
theorem extensionEmbedding_dist_eq (x y : v.completion K) :
    dist (extensionEmbedding K v x) (extensionEmbedding K v y) =
      dist x y := by
  set p : v.completion K → v.completion K → Prop :=
    λ x y => dist (extensionEmbedding K v x) (extensionEmbedding K v y) = dist x y
  refine @UniformSpace.Completion.induction_on₂ _ v.uniformSpace _ v.uniformSpace p x y ?_ (λ x y => ?_)
  · apply isClosed_eq
    · refine continuous_iff_continuous_dist.1 (@UniformSpace.Completion.continuous_extension _ v.uniformSpace _ _ _ _)
    · exact @continuous_dist _ (metricSpace K v).toPseudoMetricSpace
  · simp [p, extensionEmbedding, UniformSpace.Completion.extensionHom]
    rw [@UniformSpace.Completion.extension_coe _ v.uniformSpace _ _ _ _ v.embedding_uniformContinuous]
    rw [@UniformSpace.Completion.extension_coe _ v.uniformSpace _ _ _ _ v.embedding_uniformContinuous]
    rw [@UniformSpace.Completion.dist_eq _ v.pseudoMetricSpace]
    rw [@Isometry.dist_eq _ _ v.pseudoMetricSpace _ _ (v.isometry) _ _]

variable (K v)

theorem embedding_isometry : @Isometry _ _ (metricSpace K v).toPseudoEMetricSpace _ (extensionEmbedding K v) :=
  Isometry.of_dist_eq extensionEmbedding_dist_eq

/- The embedding `Kᵥ → ℂ` is uniform inducing. -/
theorem embedding_uniformInducing :
    UniformInducing (extensionEmbedding K v) :=
  (embedding_isometry K v).uniformInducing

/-- The embedding `Kᵥ → ℂ` is a closed embedding. -/
theorem closedEmbedding : ClosedEmbedding (extensionEmbedding K v) :=
  (embedding_isometry K v).closedEmbedding

/-- The completion of a number field at an Archimedean place is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (v.completion K) :=
  (closedEmbedding K v).locallyCompactSpace

end Completion

end NumberField.InfinitePlace
