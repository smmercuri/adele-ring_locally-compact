/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib
import AdeleRingLocallyCompact.Topology.UniformSpace.Basic

/-!
# Embeddings of number fields

This file defines the completion of a number field with respect to an infinite place.

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

instance completableTopField : @CompletableTopField K _ v.uniformSpace :=
  UniformSpace.comap_completableTopField

variable (K)

def completion := @UniformSpace.Completion K v.uniformSpace

namespace Completion

section DerivedInstances

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

end DerivedInstances

def coeRingHom : K →+* v.completion K :=
  @UniformSpace.Completion.coeRingHom _ _ v.uniformSpace _ v.uniformAddGroup

def extensionEmbedding :=
  @UniformSpace.Completion.extensionHom K _ v.uniformSpace v.topologicalRing v.uniformAddGroup
    _ _ _ _ _ v.embedding v.embedding_continuous _ _

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
    · exact continuous_iff_continuous_dist.1 (@UniformSpace.Completion.continuous_extension _ v.uniformSpace _ _ _ _)
    · exact @continuous_dist _ (metricSpace K v).toPseudoMetricSpace
  · simp only [extensionEmbedding, UniformSpace.Completion.extensionHom, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, p]
    simp only [@UniformSpace.Completion.extension_coe _ v.uniformSpace _ _ _ _ v.embedding_uniformContinuous]
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
