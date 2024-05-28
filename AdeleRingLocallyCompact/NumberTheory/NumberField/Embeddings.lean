/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib
import AdeleRingLocallyCompact.Topology.UniformSpace.Basic

/-!
# Embeddings of number fields

This file defines the main approach to the completion of a number field with respect to an infinite place.

## Main definitions
 - `NumberField.InfinitePlace.completion` is the Archimedean completion of a number field as
   an infinite place, obtained by defining a uniform space structure inherited from ℂ via the
   embedding associated to an infinite place.

## Main results
 - `NumberField.InfinitePlace.Completion.locallyCompactSpace` : the Archimedean completion
   of a number field is locally compact.

## Implementation notes
 - We have identified two approaches for formalising the completion of a number field `K` at
   an infinite place `v`. One is to define an appropriate uniform structure on `K` directly,
   and apply the `UniformSpace.Completion` functor to this. To show that
   the resultant completion is a field requires one to prove that `K` has a
   `completableTopField` instance with this uniform space. This approach is taken
   in this file, namely we pullback the uniform structure on `ℂ` via the embedding
   associated to an infinite place, through `UniformSpace.comap`. In such a scenario,
   the completable topological field instance from `ℂ` transfers to `K`, which we show in
   [Topology/UniformSpace/UniformEmbedding.lean](AdeleRingLocallyCompact/Topology/UniformSpace/Basic.lean)
 - The alternative approach is to use the embedding associated to an infinite place to embed
   `K` to a `Subfield ℂ` term, which already has a `CompletableTopField` instance. We complete
   `K` indirectly by applying the `UniformSpace.Completion` functor to the `Subfield ℂ` term.
   This is the approach taken in [EmbeddingsAlt.lean](AdeleRingLocallyCompact/NumberTheory/NumberField/EmbeddingsAlt.lean).
   It leads to an isomorphic field completion to the direct approach, since both define abstract
   completions. However, the API for the alternative approach is deficient, because we lose any
   `UniformSpace.Completion` constructions which transfer properties of the base field `K` to its completion;
   for example, `UniformSpace.Completion.extension` which extends a uniform continuous map on `K` to one
   on its completion. These would have to be re-established.

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

instance uniformSpace : UniformSpace K :=
  UniformSpace.comap v.embedding inferInstance

instance uniformAddGroup : @UniformAddGroup K v.uniformSpace _ :=
  UniformAddGroup.comap v.embedding

instance topologicalSpace : TopologicalSpace K := v.uniformSpace.toTopologicalSpace

instance topologicalDivisionRing : @TopologicalDivisionRing K _ v.topologicalSpace :=
  v.normedDivisionRing.to_topologicalDivisionRing

instance topologicalRing : @TopologicalRing K v.topologicalSpace _ :=
  @TopologicalDivisionRing.toTopologicalRing _ _ v.topologicalSpace _

end DerivedInstances

variable {K}

theorem uniformEmbedding : @UniformEmbedding _ _ v.uniformSpace _ v.embedding := by
  rw [@uniformEmbedding_iff, @uniformInducing_iff_uniformSpace]
  exact ⟨rfl, v.embedding.injective⟩

theorem uniformInducing : @UniformInducing _ _ v.uniformSpace _ v.embedding :=
  @UniformEmbedding.toUniformInducing _ _ v.uniformSpace _ _ v.uniformEmbedding

instance pseudoMetricSpace : PseudoMetricSpace K :=
  @UniformInducing.comapPseudoMetricSpace _ _ v.uniformSpace _ _ v.uniformInducing

theorem isometry : @Isometry _ _ v.pseudoMetricSpace.toPseudoEMetricSpace _ (v.embedding) :=
  @UniformEmbedding.to_isometry _ _ v.uniformSpace _ _ v.uniformEmbedding

theorem uniformContinuous : @UniformContinuous _ _ v.uniformSpace _ v.embedding :=
  @UniformInducing.uniformContinuous _ _ v.uniformSpace _ _ v.uniformInducing

theorem continuous : @Continuous _ _ v.topologicalSpace _ v.embedding :=
  @UniformContinuous.continuous _ _ v.uniformSpace _ _ v.uniformContinuous

instance t0Space : @T0Space K v.topologicalSpace :=
  @t0Space_of_injective_of_continuous _ _ v.topologicalSpace _ _
    v.embedding.injective v.continuous _

instance completableTopField : @CompletableTopField K _ v.uniformSpace :=
  UniformSpace.comap_completableTopField

variable (K)

/-- The completion of a number field at an infinite place. -/
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

/-- The embedding associated to an infinite place extended to `v.completion K →+* ℂ`. -/
def extensionEmbedding :=
  @UniformSpace.Completion.extensionHom K _ v.uniformSpace v.topologicalRing v.uniformAddGroup
    _ _ _ _ _ v.embedding v.continuous _ _

theorem extensionEmbedding_injective : Function.Injective (extensionEmbedding K v) :=
  (extensionEmbedding K v).injective

variable {K v}

/-- The embedding `v.completion K → ℂ` is an isometry. -/
theorem extensionEmbedding_dist_eq (x y : v.completion K) :
    dist (extensionEmbedding K v x) (extensionEmbedding K v y) =
      dist x y := by
  set p : v.completion K → v.completion K → Prop :=
    λ x y => dist (extensionEmbedding K v x) (extensionEmbedding K v y) = dist x y
  refine (@UniformSpace.Completion.induction_on₂ _
    v.uniformSpace _ v.uniformSpace p x y ?_ (λ x y => ?_))
  · apply isClosed_eq
    · exact (continuous_iff_continuous_dist.1
        (@UniformSpace.Completion.continuous_extension _ v.uniformSpace _ _ _ _))
    · exact @continuous_dist _ (metricSpace K v).toPseudoMetricSpace
  · simp only [extensionEmbedding, UniformSpace.Completion.extensionHom, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, p]
    simp only [@UniformSpace.Completion.extension_coe _ v.uniformSpace _ _ _ _ v.uniformContinuous]
    rw [@UniformSpace.Completion.dist_eq _ v.pseudoMetricSpace]
    rw [@Isometry.dist_eq _ _ v.pseudoMetricSpace _ _ (v.isometry) _ _]

variable (K v)

/-- The embedding `v.completion K → ℂ` is an isometry. -/
theorem extensionEmbedding_isometry :
    @Isometry _ _ (metricSpace K v).toPseudoEMetricSpace _ (extensionEmbedding K v) :=
  Isometry.of_dist_eq extensionEmbedding_dist_eq

/-- The embedding `v.completion K → ℂ` is uniform inducing. -/
theorem extensionEmbedding_uniformInducing :
    UniformInducing (extensionEmbedding K v) :=
  (extensionEmbedding_isometry K v).uniformInducing

/-- The embedding `v.completion K → ℂ` is a closed embedding. -/
theorem closedEmbedding : ClosedEmbedding (extensionEmbedding K v) :=
  (extensionEmbedding_isometry K v).closedEmbedding

/-- The completion of a number field at an infinite place is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (v.completion K) :=
  (closedEmbedding K v).locallyCompactSpace

end Completion

end NumberField.InfinitePlace
