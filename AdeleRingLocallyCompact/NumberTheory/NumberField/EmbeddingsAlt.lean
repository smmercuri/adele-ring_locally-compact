/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# Embeddings of number fields

This file defines an indirect approach to the completion of a number field with respect to an infinite place.
While this suffices for the proof of the local compactness of the adele ring, we have identified deficiencies
with this approach, detailed in the implementation notes below. We keep this approach here for reference.

## Main definitions
 - `NumberField.InfinitePlace.completion'` is the (indirect) Archimedean completion of a number field as
   an infinite place, obtained by embedding as a subfield of ℂ and completing this subfield.

## Main results
 - `NumberField.InfinitePlace.Completion.locallyCompactSpace'` : the (indirect) Archimedean completion
   of a number field is locally compact.

## Implementation notes
 - We have identified two approaches for formalising the completion of a number field `K` at
   an infinite place `v`. One is to define an appropriate uniform structure on `K` directly,
   and apply the `UniformSpace.Completion` functor to this. To show that
   the resultant completion is a field requires one to prove that `K` has a
   `completableTopField` instance with this uniform space. This approach is the principal approach taken
   in [Embeddings.lean](AdeleRingLocallyCompact/NumberTheory/NumberField/Embeddings.lean),
   namely we pullback the uniform structure on `ℂ` via the embedding
   associated to an infinite place, through `UniformSpace.comap`. We show that
   the embedding is uniform inducing. In such a scenario, the completable topological
   field instance from `ℂ` transfers to `K`, which we show in
   [Topology/UniformSpace/UniformEmbedding.lean](AdeleRingLocallyCompact/Topology/UniformSpace/UniformEmbedding.lean)
 - The alternative approach is to use the embedding associated to an infinite place to embed
   `K` to a `Subfield ℂ` term, which already has a `CompletableTopField` instance. We complete
   `K` indirectly by applying the `UniformSpace.Completion` functor to the `Subfield ℂ` term.
   This is the approach taken in this file.
   It leads to an isomorphic field completion to the direct approach, since both define abstract
   completions. However, the API for the alternative approach in this file is deficient, because we lose any
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

/-- The embedding of K as a subfield in ℂ using the embedding associated to the infinite place
`v`. -/
def subfield (v : InfinitePlace K) : Subfield ℂ where
  toSubring := v.embedding.range
  inv_mem' _ := by intro ⟨y, hy⟩; exact ⟨y⁻¹, by simp only [map_inv₀, hy]⟩

/-- The embedding sending a number field to its subfield in ℂ.-/
def toSubfield : K →+* v.subfield K where
  toFun := fun x => ⟨v.embedding x, Set.mem_range_self x⟩
  map_one' := by simp only [map_one, Submonoid.mk_eq_one]
  map_mul' x y := by simp only [v.embedding.map_mul' x y, map_mul]; rfl
  map_zero' := by simp only [map_zero]; rfl
  map_add' x y := by simp only [v.embedding.map_add' x y, map_add]; rfl

theorem toSubfield_injective : Function.Injective (v.toSubfield K) := (v.toSubfield K).injective

theorem toSubfield_surjective : Function.Surjective (v.toSubfield K) := by
  rw [← RingHom.range_top_iff_surjective, Subring.eq_top_iff']
  exact λ ⟨_, ⟨y, hy⟩⟩ => ⟨y, Subtype.val_inj.1 hy⟩

def subfieldEquiv : K ≃+* v.subfield K :=
  RingEquiv.ofBijective _ ⟨toSubfield_injective K v, toSubfield_surjective K v⟩

instance subfield_uniformSpace : UniformSpace (v.subfield K) := inferInstance

/-- The completion of a number field at an Archimedean place. -/
def completion' := (subfield_uniformSpace K v).Completion

namespace Completion

instance : UniformSpace (v.completion' K) :=
  @UniformSpace.Completion.uniformSpace _ (subfield_uniformSpace K v)

instance : CompleteSpace (v.completion' K) :=
  @UniformSpace.Completion.completeSpace _ (subfield_uniformSpace K v)

instance : NormedDivisionRing (subfield K v) :=
  NormedDivisionRing.induced _ _ (Subfield.subtype (subfield K v)) Subtype.val_injective

instance : Field (v.completion' K) := UniformSpace.Completion.instField

instance : Inhabited (v.completion' K) :=
  ⟨0⟩

instance : TopologicalRing (v.completion' K) :=
  UniformSpace.Completion.topologicalRing

instance : Dist (v.completion' K) :=
  UniformSpace.Completion.instDistCompletionToUniformSpace

instance : T0Space (v.completion' K) :=
  @UniformSpace.Completion.t0Space _ (subfield_uniformSpace K v)

instance : Coe (subfield K v) (v.completion' K) :=
  (inferInstance : Coe (subfield K v) (@UniformSpace.Completion (subfield K v) (subfield_uniformSpace K v)))

instance : Coe K (v.completion' K) where
  coe := (↑) ∘ v.toSubfield K

def coeRingHom' : K →+* v.completion' K :=
  RingHom.comp UniformSpace.Completion.coeRingHom (v.toSubfield K)

/-- The embedding `Kᵥ → ℂ` of a completion of a number field at an Archimedean
place into `ℂ`. -/
def extensionEmbedding' :=
  UniformSpace.Completion.extensionHom (Subfield.subtype (subfield K v)) continuous_subtype_val

theorem extensionEmbedding_injective' : Function.Injective (extensionEmbedding' K v) :=
  (extensionEmbedding' K v).injective

variable {K v}

/-- The embedding `Kᵥ → ℂ` preserves distances. -/
theorem extensionEmbedding_dist_eq' (x y : v.completion' K) :
    dist (extensionEmbedding' K v x) (extensionEmbedding' K v y) =
      dist x y := by
  set p : v.completion' K → v.completion' K → Prop :=
    λ x y => dist (extensionEmbedding' K v x) (extensionEmbedding' K v y) = dist x y
  refine @UniformSpace.Completion.induction_on₂ (subfield K v) _ (subfield K v) _ p x y ?_ (λ x y => ?_)
  · apply isClosed_eq
    · exact continuous_iff_continuous_dist.1 UniformSpace.Completion.continuous_extension
    · exact continuous_dist
  · simp only [extensionEmbedding', UniformSpace.Completion.extensionHom, Subfield.coe_subtype,
      RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, p, @UniformSpace.Completion.dist_eq (v.subfield K) _]
    have h_val : UniformContinuous (subfield K v).subtype := uniformContinuous_subtype_val
    have h_val_ext := UniformSpace.Completion.extension_coe h_val
    simp only [Subfield.coe_subtype] at h_val_ext
    rw [h_val_ext x, h_val_ext y]
    rfl

variable (K v)

/-- The embedding `Kᵥ → ℂ` is an isometry. -/
theorem embedding_isometry' : Isometry (extensionEmbedding' K v) :=
  Isometry.of_dist_eq extensionEmbedding_dist_eq'

/-- The embedding `Kᵥ → ℂ` is uniform inducing. -/
theorem embedding_uniformInducing' :
    UniformInducing (extensionEmbedding' K v) :=
  (embedding_isometry' K v).uniformInducing

/-- The embedding `Kᵥ → ℂ` is a closed embedding. -/
theorem closedEmbedding' : ClosedEmbedding (extensionEmbedding' K v) :=
  (embedding_isometry' K v).closedEmbedding

/-- The completion of a number field at an Archimedean place is locally compact. -/
instance locallyCompactSpace' : LocallyCompactSpace (v.completion' K) :=
  (closedEmbedding' K v).locallyCompactSpace

end Completion

end NumberField.InfinitePlace
