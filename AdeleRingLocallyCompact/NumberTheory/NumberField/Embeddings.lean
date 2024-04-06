/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib
import AdeleRingLocallyCompact.Topology.Homeomorph

/-!
# Embeddings of number fields

This file defines the completion of a number field with respect to an infinite place.

## Main definitions
 - `NumberField.InfinitePlace.completion` is the Archimedean completion of a number field as
   an infinite place, obtained by embedding as a subfield of ℂ and completing this subfield.

## Main results
 - `NumberField.InfinitePlace.Completion.locallyCompactSpace` : the Archimedean completion
   of a number field is locally compact.

## Tags
number field, embeddings, places, infinite places
-/

noncomputable section

namespace NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

/-- The embedding of K as a subfield in ℂ using the embedding associated to the infinite place
`v`. -/
def subfield (v : InfinitePlace K) : Subfield ℂ where
  toSubring := v.embedding.range
  inv_mem' _ := by intro ⟨y, hy⟩; exact ⟨y⁻¹, by simp only [map_inv₀, hy]⟩

/-- The embedding sending a number field to its subfield in ℂ. -/
def toSubfield : K →+* v.subfield K where
  toFun := fun x => ⟨v.embedding x, Set.mem_range_self x⟩
  map_one' := by simp only [map_one, Submonoid.mk_eq_one]
  map_mul' x y := by simp only [v.embedding.map_mul' x y, map_mul]; rfl
  map_zero' := by simp only [map_zero]; rfl
  map_add' x y := by simp only [v.embedding.map_add' x y, map_add]; rfl

theorem toSubfield_injective : Function.Injective (v.toSubfield K) := (v.toSubfield K).injective

instance subfield_uniformSpace : UniformSpace (v.subfield K) := inferInstance

/-- The completion of a number field at an Archimedean place. -/
def completion := (subfield_uniformSpace K v).Completion

namespace Completion

instance : UniformSpace (v.completion K) :=
  @UniformSpace.Completion.uniformSpace _ (subfield_uniformSpace K v)

instance : CompleteSpace (v.completion K) :=
  @UniformSpace.Completion.completeSpace _ (subfield_uniformSpace K v)

instance : Coe (subfield K v) (v.completion K) :=
  (inferInstance : Coe (subfield K v) (@UniformSpace.Completion (subfield K v) (subfield_uniformSpace K v)))

instance : Coe K (v.completion K) where
  coe := (↑) ∘ v.toSubfield K

instance : NormedDivisionRing (subfield K v) :=
  NormedDivisionRing.induced _ _ (Subfield.subtype (subfield K v)) Subtype.val_injective

instance : Field (v.completion K) := UniformSpace.Completion.instField

instance : Inhabited (v.completion K) :=
  ⟨0⟩

instance : TopologicalRing (v.completion K) := UniformSpace.Completion.topologicalRing

/-- The embedding of a completion of a number field at an Archimedean place into `ℂ`. -/
def extensionEmbedding :=
  UniformSpace.Completion.extensionHom (Subfield.subtype (subfield K v)) continuous_subtype_val

theorem embedding_uniformInducing :
  UniformInducing (extensionEmbedding K v) := by
  rw [uniformInducing_iff]
  ext S
  rw [UniformSpace.Completion.mem_uniformity_dist]
  rw [Filter.mem_comap]
  sorry

theorem closedEmbedding : ClosedEmbedding (extensionEmbedding K v) := by
  apply ClosedEmbedding.mk
  · apply Embedding.mk
    · exact (embedding_uniformInducing K v).inducing
    · exact (extensionEmbedding K v).injective
  · apply IsComplete.isClosed
    rw [← completeSpace_iff_isComplete_range]
    · infer_instance
    · exact embedding_uniformInducing K v

/-- The completion of a number field at an Archimedean place is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (v.completion K) :=
  (closedEmbedding K v).locallyCompactSpace

end Completion

end NumberField.InfinitePlace
