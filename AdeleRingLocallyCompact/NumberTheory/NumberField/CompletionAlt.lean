/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib
import AdeleRingLocallyCompact.NumberTheory.NumberField.Completion
import AdeleRingLocallyCompact.Topology.UniformSpace.Basic

/-!
# The completion of a number field at an infinite place

This file defines an indirect approach to the completion of a number field with respect to
an infinite place. While this suffices for the proof of the local compactness of the adele ring,
we have identified deficiencies with this approach, detailed in the implementation notes below.
We keep this approach here for reference.

## Main definitions
 - `NumberField.InfinitePlace.completion'` is the (indirect) Archimedean completion of a number
   field as an infinite place, obtained by embedding as a subfield of ℂ and completing
   this subfield.

## Main results
 - `NumberField.InfinitePlace.Completion.locallyCompactSpace'` : the (indirect) Archimedean
   completion of a number field is locally compact.

## Implementation notes
 - We have identified two approaches for formalising the completion of a number field `K` at
   an infinite place `v`. One is to define an appropriate uniform structure on `K` directly,
   and apply the `UniformSpace.Completion` functor to this. To show that
   the resultant completion is a field requires one to prove that `K` has a
   `completableTopField` instance with this uniform space. This approach is the principal
   approach taken in
   [Completion.lean](AdeleRingLocallyCompact/NumberTheory/NumberField/Completion.lean),
   by defining a normed field instance coming from the absolute value associated to an infinite
   place. In such a scenario, the completable topological field instance from `ℂ` transfers to `K`
   because the uniform structure of the absolute value is shown to be equivalent to the pullback
   uniform structure of `ℂ` along the embedding associated to an infinite place. We show that
   the pullback of a completable topological field is a completable topological field here:
   [Topology/UniformSpace/Basic.lean](AdeleRingLocallyCompact/Topology/UniformSpace/Basic.lean)
 - The alternative approach (in this file) is to use the embedding associated to an infinite place
   to embed `K` to a `Subfield ℂ` term, which already has a `CompletableTopField` instance. We
   complete `K` indirectly by applying the `UniformSpace.Completion` functor to the `Subfield ℂ`
   term. This is the approach taken in this file. It leads to an isomorphic field completion to
   the approach described above, since both define abstract completions. However, the API for
   the alternative approach in this file is deficient, because we lose any `UniformSpace.Completion`
   constructions which transfer properties of the base field `K` to its completion; for example,
   `UniformSpace.Completion.extension` which extends a uniform continuous map on `K` to one on its
   completion. These would have to be re-established.

## Tags
number field, embeddings, places, infinite places
-/

noncomputable section

namespace AbsoluteValue

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-! ## Alternative approach using dependent constructors -/

instance normedField₀ : NormedField K where
  norm := v
  dist_eq _ _ := rfl
  dist_self x := by simp only [sub_self, MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom, map_zero]
  dist_comm := v.map_sub
  dist_triangle := v.sub_le
  edist_dist x y := rfl
  norm_mul' x y := v.1.map_mul x y
  eq_of_dist_eq_zero := by simp only [MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom,
    AbsoluteValue.map_sub_eq_zero_iff, imp_self, implies_true]

abbrev completion₀ :=
  letI := v.normedField₀
  UniformSpace.Completion K

end AbsoluteValue

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K] (v : InfinitePlace K)

abbrev completion₀ := v.1.completion₀

theorem uniformInducing_embedding₀ :
    letI := v.1.normedField₀ -- Requires signalling to find uniform space
    UniformInducing v.embedding :=
  WithAbs.uniformInducing_of_comp v.norm_embedding_eq

instance : Field (v.completion₀) :=
  letI := v.1.normedField₀ -- Requires signalling to find uniform space
  letI : CompletableTopField K := v.uniformInducing_embedding₀.completableTopField
  UniformSpace.Completion.instField

namespace Completion

def extensionEmbedding₀ :=
  letI := v.1.normedField₀ -- Requires signalling to find uniform space
  UniformSpace.Completion.extension v.embedding

end NumberField.InfinitePlace.Completion

/-! ## Alternative approach using data-carrying type class -/

class WithAbsReal (R : Type*) [Semiring R] where
  v : AbsoluteValue R ℝ

namespace AbsoluteValue

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

instance [WithAbsReal K] : NormedField K := WithAbsReal.v.normedField₀

abbrev completion₁ :=
  letI := WithAbsReal.mk v
  UniformSpace.Completion K

end AbsoluteValue

namespace NumberField.InfinitePlace

open AbsoluteValue

variable {K : Type*} [Field K] (v : InfinitePlace K)

abbrev completion₁ := v.1.completion₁

theorem uniformInducing_embedding₁ :
    letI := WithAbsReal.mk v.1 -- Requires signalling to find uniform space
    UniformInducing v.embedding :=
  WithAbs.uniformInducing_of_comp v.norm_embedding_eq

instance : Field (v.completion₁) :=
  letI := WithAbsReal.mk v.1 -- Requires signalling to find uniform space
  letI : CompletableTopField K := v.uniformInducing_embedding₁.completableTopField
  UniformSpace.Completion.instField

namespace Completion

def extensionEmbedding₁ :=
  letI := WithAbsReal.mk v.1 -- Requires signalling to find uniform space
  UniformSpace.Completion.extension v.embedding

end NumberField.InfinitePlace.Completion

/-! ## Alternative approach via subfields -/

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K] (v : InfinitePlace K)

/-- The embedding of K as a subfield in ℂ using the embedding associated to the infinite place
`v`. -/
def subfield : Subfield ℂ where
  toSubring := v.embedding.range
  inv_mem' _ :=  fun ⟨y, hy⟩ => ⟨y⁻¹, by simp only [map_inv₀, hy]⟩

/-- The embedding sending a number field to its subfield in ℂ.-/
def toSubfield : K →+* v.subfield where
  toFun := fun x => ⟨v.embedding x, Set.mem_range_self x⟩
  map_one' := by simp only [map_one, Submonoid.mk_eq_one]
  map_mul' x y := by simp only [v.embedding.map_mul' x y, map_mul]; rfl
  map_zero' := by simp only [map_zero]; rfl
  map_add' x y := by simp only [v.embedding.map_add' x y, map_add]; rfl

theorem toSubfield_surjective : Function.Surjective v.toSubfield := by
  rw [← RingHom.range_top_iff_surjective, Subring.eq_top_iff']
  exact fun ⟨_, ⟨y, hy⟩⟩ => ⟨y, Subtype.val_inj.1 hy⟩

def subfieldEquiv : K ≃+* v.subfield :=
  RingEquiv.ofBijective _ ⟨v.toSubfield.injective, v.toSubfield_surjective⟩

/-- The completion of a number field's image within ℂ at an infinite place. -/
abbrev completion₂ := UniformSpace.Completion v.subfield

namespace Completion

instance : NormedField v.subfield :=
  NormedField.induced _ _ v.subfield.subtype Subtype.val_injective

instance : Field v.completion₂ := inferInstance

instance : Inhabited v.completion₂ := ⟨0⟩

instance : Coe K v.completion₂ where
  coe := (UniformSpace.Completion.coe' v.subfield) ∘ v.toSubfield

def coeRingHom₂ : K →+* v.completion₂ :=
  RingHom.comp UniformSpace.Completion.coeRingHom v.toSubfield

/-- The embedding `v.completion₂ : K →+* ℂ` of a completion of a number field at an infinite
place into `ℂ`. -/
def extensionEmbedding₂ :=
  UniformSpace.Completion.extensionHom v.subfield.subtype continuous_subtype_val

theorem extensionEmbedding_injective₂ : Function.Injective (extensionEmbedding₂ v) :=
  (extensionEmbedding₂ v).injective

variable {v}

/-- The embedding `v.completion₂ : K →+* ℂ` preserves distances. -/
theorem extensionEmbedding_dist_eq₂ (x y : v.completion₂) :
    dist (extensionEmbedding₂ v x) (extensionEmbedding₂ v y) =
      dist x y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ (fun x y => ?_)
  · apply isClosed_eq
    · exact continuous_iff_continuous_dist.1 UniformSpace.Completion.continuous_extension
    · exact continuous_dist
  · simp only [extensionEmbedding₂, UniformSpace.Completion.extensionHom, Subfield.coe_subtype,
      RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, UniformSpace.Completion.dist_eq]
    have h_val : UniformContinuous v.subfield.subtype := uniformContinuous_subtype_val
    have h_val_ext := UniformSpace.Completion.extension_coe h_val
    simp only [Subfield.coe_subtype] at h_val_ext
    rw [h_val_ext x, h_val_ext y]
    rfl

variable (v)

/-- The embedding `v.completion₂ : K →+* ℂ` is an isometry. -/
theorem isometry_extensionEmbedding₂ : Isometry (extensionEmbedding₂ v) :=
  Isometry.of_dist_eq extensionEmbedding_dist_eq₂

/-- The embedding `v.completion₂ : K →+* ℂ` is a closed embedding. -/
theorem closedEmbedding_extensionEmbedding₂ : ClosedEmbedding (extensionEmbedding₂ v) :=
  (isometry_extensionEmbedding₂ v).closedEmbedding

/-- The indirect completion of a number field at an infinite place is locally compact. -/
instance locallyCompactSpace₂ : LocallyCompactSpace v.completion₂ :=
  (closedEmbedding_extensionEmbedding₂ v).locallyCompactSpace

end NumberField.InfinitePlace.Completion
