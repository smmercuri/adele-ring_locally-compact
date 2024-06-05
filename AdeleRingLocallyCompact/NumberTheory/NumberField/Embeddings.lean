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

variable {K : Type*} [Field K] [NumberField K] (v : InfinitePlace K)

instance : Inhabited (InfinitePlace K) :=
  ⟨Classical.choice (instNonemptyInfinitePlace K)⟩

/-- The normed field structure of a number field coming from the norm asociated to
an infinite place. -/
noncomputable def normedField : NormedField K :=
  NormedField.induced _ _ v.embedding v.embedding.injective

/-- The normed division ring structure of a number field coming from the norm associated
to an infinite place. -/
noncomputable def normedDivisionRing : NormedDivisionRing K :=
  v.normedField.toNormedDivisionRing

/-- The uniform structure of a number field at an infinite place. -/
noncomputable def uniformSpace : UniformSpace K :=
  v.normedField.toUniformSpace

/-- The topology of a number field infuced by an infinite place. -/
noncomputable def topologicalSpace : TopologicalSpace K :=
  v.uniformSpace.toTopologicalSpace

noncomputable def topologicalDivisionRing :
    @TopologicalDivisionRing K _ v.topologicalSpace :=
  v.normedDivisionRing.to_topologicalDivisionRing

/-- The topological ring structure of a number field induced by an infinite place. -/
noncomputable def topologicalRing : @TopologicalRing K v.topologicalSpace _ :=
  @TopologicalDivisionRing.toTopologicalRing _ _ v.topologicalSpace
    v.topologicalDivisionRing

/-- The embedding associated to an infinite place is a uniform embedding. -/
theorem uniformEmbedding : @UniformEmbedding _ _ v.uniformSpace _ v.embedding := by
  rw [@uniformEmbedding_iff, @uniformInducing_iff_uniformSpace]
  exact ⟨rfl, v.embedding.injective⟩

/-- The embedding associated to an infinite palce is uniform inducing. -/
theorem uniformInducing : @UniformInducing _ _ v.uniformSpace _ v.embedding :=
  @UniformEmbedding.toUniformInducing _ _ v.normedDivisionRing.toUniformSpace _ _ v.uniformEmbedding

/-- The uniform additive group structure of a number field induced by an infinite place. -/
def uniformAddGroup : @UniformAddGroup K v.uniformSpace _ :=
  @UniformInducing.uniformAddGroup _ _ _ _ _ _ v.uniformSpace _ _ _ _ v.uniformInducing

/-- The embedding associated to an infinite place of a number field is an isometry. -/
theorem isometry : @Isometry _ _ v.normedField.toPseudoEMetricSpace _ (v.embedding) :=
  @UniformEmbedding.to_isometry _ _ v.uniformSpace _ _ v.uniformEmbedding

/-- The embedding associated to an infinite place of a number field is uniform continuous. -/
theorem uniformContinuous : @UniformContinuous _ _ v.uniformSpace _ v.embedding :=
  @UniformInducing.uniformContinuous _ _ v.uniformSpace _ _ v.uniformInducing

/-- The embedding associated to an infinite place of a number field is continuous. -/
theorem continuous : @Continuous _ _ v.topologicalSpace _ v.embedding :=
  @UniformContinuous.continuous _ _ v.uniformSpace _ _ v.uniformContinuous

/-- The uniform structure induced by an infinite place of a number field defines a
completable topological field. -/
instance completableTopField : @CompletableTopField K _ v.uniformSpace :=
  @UniformSpace.comap_completableTopField _ _ _ _ _ _ v.normedField.instT0Space _

/-- The completion of a number field at an infinite place. -/
def completion := @UniformSpace.Completion K v.normedDivisionRing.toUniformSpace

namespace Completion

noncomputable instance : UniformSpace v.completion :=
  @UniformSpace.Completion.uniformSpace _ v.uniformSpace

instance : CompleteSpace v.completion :=
  @UniformSpace.Completion.completeSpace _ v.uniformSpace

noncomputable instance : Field (v.completion) :=
  @UniformSpace.Completion.instField _ _ v.normedDivisionRing.toUniformSpace
    v.topologicalDivisionRing _ v.uniformAddGroup

noncomputable instance : Inhabited v.completion :=
  ⟨0⟩

noncomputable instance : TopologicalRing v.completion :=
  @UniformSpace.Completion.topologicalRing K _ v.uniformSpace
    v.topologicalRing v.uniformAddGroup

noncomputable instance metricSpace : MetricSpace (v.completion) :=
  @UniformSpace.Completion.instMetricSpace _ v.normedDivisionRing.toPseudoMetricSpace

def coeRingHom : K →+* v.completion :=
  @UniformSpace.Completion.coeRingHom _ _ v.uniformSpace
    v.topologicalRing v.uniformAddGroup

/-- The embedding associated to an infinite place extended to `v.completion →+* ℂ`. -/
noncomputable def extensionEmbedding : v.completion →+* ℂ :=
  @UniformSpace.Completion.extensionHom K _
    v.uniformSpace v.topologicalRing v.uniformAddGroup
    _ _ _ _ _ v.embedding v.continuous _ T1Space.t0Space

theorem extensionEmbedding_injective : Function.Injective (extensionEmbedding v) :=
  (extensionEmbedding v).injective

variable {v}

/-- The embedding `v.completion → ℂ` preserved distances. -/
theorem extensionEmbedding_dist_eq (x y : v.completion) :
    dist (extensionEmbedding v x) (extensionEmbedding v y) =
      dist x y := by
  set p : v.completion → v.completion → Prop :=
    fun x y => dist (extensionEmbedding v x) (extensionEmbedding v y) = dist x y
  refine (@UniformSpace.Completion.induction_on₂ _
    v.uniformSpace _ v.uniformSpace p x y ?_ (fun x y => ?_))
  · apply isClosed_eq
    · exact (continuous_iff_continuous_dist.1
        (@UniformSpace.Completion.continuous_extension _ v.uniformSpace _ _ _ _))
    · exact @continuous_dist _ (metricSpace v).toPseudoMetricSpace
  · simp only [extensionEmbedding, UniformSpace.Completion.extensionHom, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, p]
    rw [@UniformSpace.Completion.dist_eq _ v.normedDivisionRing.toPseudoMetricSpace]
    simp only [@UniformSpace.Completion.extension_coe _ v.uniformSpace _ _ _
      T1Space.t0Space v.uniformContinuous]
    rw [@Isometry.dist_eq _ _ v.normedDivisionRing.toPseudoMetricSpace _ _ (v.isometry) _ _]

variable (K v)

/-- The embedding `v.completion → ℂ` is an isometry. -/
theorem extensionEmbedding_isometry :
    @Isometry _ _ (metricSpace v).toPseudoEMetricSpace _ (extensionEmbedding v) :=
  Isometry.of_dist_eq extensionEmbedding_dist_eq

/-- The embedding `v.completion K → ℂ` is uniform inducing. -/
theorem extensionEmbedding_uniformInducing :
    UniformInducing (extensionEmbedding v) :=
  (extensionEmbedding_isometry K v).uniformInducing

/-- The embedding `v.completion K → ℂ` is a closed embedding. -/
theorem closedEmbedding : ClosedEmbedding (extensionEmbedding v) :=
  (extensionEmbedding_isometry K v).closedEmbedding

/-- The completion of a number field at an infinite place is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (v.completion) :=
  (closedEmbedding K v).locallyCompactSpace

end Completion

end NumberField.InfinitePlace
