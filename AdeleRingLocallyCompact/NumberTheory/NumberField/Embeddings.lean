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
def completion := (subfield_uniformSpace K v).Completion

namespace Completion

instance : UniformSpace (v.completion K) :=
  @UniformSpace.Completion.uniformSpace _ (subfield_uniformSpace K v)

instance : CompleteSpace (v.completion K) :=
  @UniformSpace.Completion.completeSpace _ (subfield_uniformSpace K v)

instance : NormedDivisionRing (subfield K v) :=
  NormedDivisionRing.induced _ _ (Subfield.subtype (subfield K v)) Subtype.val_injective

instance : Field (v.completion K) := UniformSpace.Completion.instField

instance : Inhabited (v.completion K) :=
  ⟨0⟩

instance : TopologicalRing (v.completion K) := UniformSpace.Completion.topologicalRing

instance HDist : Dist (v.completion K) :=
  UniformSpace.Completion.instDistCompletionToUniformSpace

instance : T0Space (v.completion K) :=
  @UniformSpace.Completion.t0Space _ (subfield_uniformSpace K v)

instance : Coe (subfield K v) (v.completion K) :=
  (inferInstance : Coe (subfield K v) (@UniformSpace.Completion (subfield K v) (subfield_uniformSpace K v)))

instance : Coe K (v.completion K) where
  coe := (↑) ∘ v.toSubfield K

def coeRingHom : K →+* v.completion K :=
  RingHom.comp UniformSpace.Completion.coeRingHom (v.toSubfield K)

/-- The embedding `Kᵥ → ℂ` of a completion of a number field at an Archimedean
place into `ℂ`. -/
def extensionEmbedding :=
  UniformSpace.Completion.extensionHom (Subfield.subtype (subfield K v)) continuous_subtype_val

theorem extensionEmbedding_injective : Function.Injective (extensionEmbedding K v) :=
  (extensionEmbedding K v).injective

variable {K v}

/-- The embedding `Kᵥ → ℂ` preserves distances. -/
theorem extensionEmbedding_dist_eq (x y : v.completion K) :
    dist (extensionEmbedding K v x) (extensionEmbedding K v y) =
      (HDist K v).dist x y := by
  set p : v.completion K → v.completion K → Prop :=
    λ x y => dist (extensionEmbedding K v x) (extensionEmbedding K v y) = (HDist K v).dist x y
  have h := @UniformSpace.Completion.induction_on₂ (subfield K v) _ (subfield K v) _ p x y
  apply h
  · apply isClosed_eq
    · rw [← continuous_iff_continuous_dist]
      exact UniformSpace.Completion.continuous_extension
    · exact continuous_dist
  · intro x y
    simp only [extensionEmbedding, UniformSpace.Completion.extensionHom, Subfield.coe_subtype,
      RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, p]
    rw [@UniformSpace.Completion.dist_eq (v.subfield K) _]
    have hf : UniformContinuous (subfield K v).subtype := uniformContinuous_subtype_val
    have h' := UniformSpace.Completion.extension_coe hf
    simp only [Subfield.coe_subtype, Subtype.forall] at h'
    rw [h' x, h' y]
    rfl

variable (K v)

/-- The embedding `Kᵥ → ℂ` is uniform inducing. -/
theorem embedding_uniformInducing :
  UniformInducing (extensionEmbedding K v) := by
  rw [Filter.HasBasis.uniformInducing_iff Metric.uniformity_basis_dist Metric.uniformity_basis_dist]
  simp only [Set.mem_setOf_eq, extensionEmbedding_dist_eq, and_self]
  exact fun ε hε => ⟨ε, hε, λ _ _ h => h⟩

/-- The embedding `Kᵥ → ℂ` is a closed embedding. -/
theorem closedEmbedding : ClosedEmbedding (extensionEmbedding K v) := by
  apply ClosedEmbedding.mk
  · exact ⟨(embedding_uniformInducing K v).inducing, extensionEmbedding_injective K v⟩
  · apply IsComplete.isClosed
    exact ((completeSpace_iff_isComplete_range (embedding_uniformInducing K v))).1 inferInstance

/-- The completion of a number field at an Archimedean place is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (v.completion K) :=
  (closedEmbedding K v).locallyCompactSpace

end Completion

end NumberField.InfinitePlace
