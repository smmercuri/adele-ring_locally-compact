/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib
import AdeleRingLocallyCompact.Algebra.Field.Subfield
import AdeleRingLocallyCompact.Analysis.NormedSpace.Completion
import AdeleRingLocallyCompact.Topology.Algebra.UniformRing
import AdeleRingLocallyCompact.Topology.UniformSpace.Basic
import AdeleRingLocallyCompact.Topology.Instances.Real

/-!
# The completion of a number field at an infinite place

This file contains the completion of a number field at its infinite places.

This is ultimately achieved by applying the `UniformSpace.Completion` functor, however each
infinite place induces its own `UniformSpace` instance on the number field, so the inference system
cannot automatically infer these. A common approach to handle the ambiguity that arises from having
multiple sources of instances is through the use of type synonyms. In this case, we define a
type synonym `WithAbs` for a semiring. In particular this type synonym depends on an
absolute value. This provides a systematic way of assigning and inferring instances of the semiring
that also depend on an absolute value. In our application, relevant instances and the completion
of a number field `K` are first defined at the level of `AbsoluteValue` by using the type synonym
`WithAbs` of `K`, and then derived downstream for `InfinitePlace` (which is a subtype of
`AbsoluteValue`). Namely, if `v` is an infinite place of `K`, then `v.completion` defines
the completion of `K` at `v`.

The embedding `v.embedding : K →+* ℂ` associated to an `v` enjoys useful properties
within the uniform structure defined by `v`; namely, it is a uniform embedding and an isometry.
This is because the absolute value associated to `v` factors through `v.embedding`. This allows
us to show that the completion of `K` at an infinite place is locally compact. Moreover, we can
extend `v.embedding` to a embedding `v.completion →+* ℂ`. We show that if `v` is real (i.e.,
`v.embedding (K) ⊆ ℝ`) then the extended embedding gives an isomorphism `v.completion ≃+* ℝ`,
else the extended embedding gives an isomorphism `v.completion ≃+* ℂ`.

## Main definitions
 - `WithAbs` : type synonym for a semiring which depends on an absolute value. This is
  a function that takes an absolute value on a semiring and returns the semiring. We use this
  to assign and infer instances on a semiring that depend on absolute values.
 - `AbsoluteValue.completion` : the uniform space completion of a field `K` equipped with real
  absolute value.
 - `NumberField.InfinitePlace.completion` : the completion of a number field `K` at an infinite
  place, obtained by completing `K` with respect to the absolute value associated to the infinite
  place.
 - `NumberField.InfinitePlace.Completion.extensionEmbedding` : the embedding `v.embedding : K →+* ℂ`
  extended to `v.completion →+* ℂ`.
 - `NumberField.InfinitePlace.Completion.extensionEmbedding_of_isReal` : if the infinite place `v`
  is real, then this extends the embedding `v.embedding_of_isReal : K →+* ℝ` to
  `v.completion →+* ℝ`.
 - `NumberField.InfinitePlace.Completion.ringEquiv_real_of_isReal` : the ring isomorphism
  `v.completion ≃+* ℝ` when `v` is a real infinite place; the forward direction of this is
  `extensionEmbedding_of_isReal`.
 - `NumberField.InfinitePlace.Completion.ringEquiv_complex_of_isComplex` : the ring isomorphism
  `v.completion ≃+* ℂ` when `v` is a complex infinite place; the forward direction of this is
  `extensionEmbedding`.

## Main results
 - `NumberField.Completion.locallyCompactSpace` : the completion of a number field at
  an infinite place is locally compact.
 - `NumberField.Completion.isometry_extensionEmbedding` : the embedding `v.completion →+* ℂ` is
  an isometry. See also `isometry_extensionEmbedding_of_isReal` for the corresponding result on
  `v.completion →+* ℝ` when `v` is real.
 - `NumberField.Completion.bijective_extensionEmbedding_of_isComplex` : the embedding
  `v.completion →+* ℂ` is bijective when `v` is complex. See also
  `bijective_extensionEmebdding_of_isReal` for the corresponding result for `v.completion →+* ℝ`
  when `v` is real.

## Tags
number field, embeddings, infinite places, completion
-/
noncomputable section

/-- Type synonym for a semiring which depends on an absolute value. This is a function that takes
an absolute value on a semiring and returns the semiring. We use this to assign and infer instances
on a semiring that depend on absolute values. -/
@[nolint unusedArguments]
def WithAbs {R S} [Semiring R] [OrderedSemiring S] : AbsoluteValue R S → Type _ := fun _ => R

namespace WithAbs

instance [Ring R] (v : AbsoluteValue R ℝ) : NormedRing (WithAbs v) where
  toRing := inferInstanceAs (Ring R)
  norm := v
  dist_eq _ _ := rfl
  dist_self x := by simp only [sub_self, MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom, map_zero]
  dist_comm := v.map_sub
  dist_triangle := v.sub_le
  edist_dist x y := rfl
  norm_mul x y := (v.map_mul x y).le
  eq_of_dist_eq_zero := by simp only [MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom,
    AbsoluteValue.map_sub_eq_zero_iff, imp_self, implies_true]

variable {K} [Field K] (v : AbsoluteValue K ℝ)

instance normedField : NormedField (WithAbs v) where
  toField := inferInstanceAs (Field K)
  __ := inferInstanceAs (NormedRing (WithAbs v))
  norm_mul' := v.map_mul

instance : Inhabited (WithAbs v) := ⟨0⟩

variable {L : Type*} [NormedField L] {f : WithAbs v →+* L} {v}

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
`f` is an isometry. -/
theorem isometry_of_comp (h : ∀ x, ‖f x‖ = v x) : Isometry f :=
  Isometry.of_dist_eq <| fun x y => by simp only [‹NormedField L›.dist_eq, ← f.map_sub, h]; rfl

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
the pseudo metric space associated to the absolute value is the same as the pseudo metric space
induced by `f`. -/
theorem pseudoMetricSpace_induced_of_comp (h : ∀ x, ‖f x‖ = v x) :
     PseudoMetricSpace.induced f inferInstance = (normedField v).toPseudoMetricSpace := by
  ext; exact isometry_of_comp h |>.dist_eq _ _

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
the uniform structure associated to the absolute value is the same as the uniform structure
induced by `f`. -/
theorem uniformSpace_comap_eq_of_comp (h : ∀ x, ‖f x‖ = v x) :
    UniformSpace.comap f inferInstance = (normedField v).toUniformSpace := by
  simp only [← pseudoMetricSpace_induced_of_comp h, PseudoMetricSpace.toUniformSpace]

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
`f` is uniform inducing. -/
theorem uniformInducing_of_comp (h : ∀ x, ‖f x‖ = v x) : UniformInducing f :=
  uniformInducing_iff_uniformSpace.2 <| uniformSpace_comap_eq_of_comp h

end WithAbs

namespace AbsoluteValue

open WithAbs

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-- The completion of a field with respect to a real absolute value. -/
abbrev completion := UniformSpace.Completion (WithAbs v)

namespace Completion

instance : Coe K v.completion :=
  inferInstanceAs (Coe (WithAbs v) (UniformSpace.Completion (WithAbs v)))

variable {L : Type*} [NormedField L] [CompleteSpace L] {f : WithAbs v →+* L} {v}

/-- If the absolute value of a normed field factors through an embedding into another normed field
`L`, then we can extend that embedding to an embedding on the completion `v.completion →+* L`. -/
abbrev extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x) : v.completion →+* L :=
  UniformSpace.Completion.extensionHom _
    (WithAbs.uniformInducing_of_comp h).uniformContinuous.continuous

theorem extensionEmbedding_of_comp_coe (h : ∀ x, ‖f x‖ = v x) (x : K) :
    extensionEmbedding_of_comp h x = f x := by
  rw [← UniformSpace.Completion.extensionHom_coe f
    (WithAbs.uniformInducing_of_comp h).uniformContinuous.continuous]

/-- If the absolute value of a normed field factors through an embedding into another normed field,
then the extended embedding `v.completion →+* L` preserves distances. -/
theorem extensionEmbedding_dist_eq_of_comp (h : ∀ x, ‖f x‖ = v x) (x y : v.completion) :
    dist (extensionEmbedding_of_comp h x) (extensionEmbedding_of_comp h y) =
      dist x y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ (fun x y => ?_)
  · refine isClosed_eq ?_ continuous_dist
    exact continuous_iff_continuous_dist.1 UniformSpace.Completion.continuous_extension
  · simp only [extensionEmbedding_of_comp_coe]
    exact UniformSpace.Completion.dist_eq x y ▸ (WithAbs.isometry_of_comp h).dist_eq _ _

/-- If the absolute value of a normed field factors through an embedding into another normed field,
then the extended embedding `v.completion →+* L` is an isometry. -/
theorem isometry_extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x) :
    Isometry (extensionEmbedding_of_comp h) :=
  Isometry.of_dist_eq <| extensionEmbedding_dist_eq_of_comp h

/-- If the absolute value of a normed field factors through an embedding into another normed field,
then the extended embedding `v.completion →+* L` is a closed embedding. -/
theorem closedEmbedding_extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x) :
    ClosedEmbedding (extensionEmbedding_of_comp h) :=
  (isometry_extensionEmbedding_of_comp h).closedEmbedding

/-- If the absolute value of a normed field factors through an embedding into another normed field
that is locally compact, then the completion of the first normed field is also locally compact. -/
theorem locallyCompactSpace [LocallyCompactSpace L] (h : ∀ x, ‖f x‖ = v x) :
    LocallyCompactSpace (v.completion) :=
  (closedEmbedding_extensionEmbedding_of_comp h).locallyCompactSpace

end AbsoluteValue.Completion

namespace NumberField.InfinitePlace

open AbsoluteValue.Completion

variable {K : Type*} [Field K] (v : InfinitePlace K)

/-- The completion of a number field at an infinite place. -/
abbrev completion := v.1.completion

namespace Completion

instance : NormedField v.completion :=
  letI := (WithAbs.uniformInducing_of_comp v.norm_embedding_eq).completableTopField
  UniformSpace.Completion.instNormedFieldOfCompletableTopField (WithAbs v.1)

instance : Algebra K v.completion :=
  inferInstanceAs (Algebra (WithAbs v.1) v.1.completion)

/-- The completion of a number field at an infinite place is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace v.completion :=
  AbsoluteValue.Completion.locallyCompactSpace v.norm_embedding_eq

/-- The embedding associated to an infinite place extended to an embedding `v.completion →+* ℂ`. -/
def extensionEmbedding : v.completion →+* ℂ := extensionEmbedding_of_comp v.norm_embedding_eq

/-- The embedding `K →+* ℝ` associated to a real infinite place extended to `v.completion →+* ℝ`. -/
def extensionEmbedding_of_isReal {v : InfinitePlace K} (hv : IsReal v) : v.completion →+* ℝ :=
  extensionEmbedding_of_comp <| v.norm_embedding_of_isReal hv

@[simp]
theorem extensionEmbedding_coe (x : K) : extensionEmbedding v x = v.embedding x :=
  extensionEmbedding_of_comp_coe v.norm_embedding_eq x

@[simp]
theorem extensionEmbedding_of_isReal_coe {v : InfinitePlace K} (hv : IsReal v) (x : K) :
    extensionEmbedding_of_isReal hv x = embedding_of_isReal hv x :=
  extensionEmbedding_of_comp_coe (v.norm_embedding_of_isReal hv) x

/-- The embedding `v.completion →+* ℂ` is an isometry. -/
theorem isometry_extensionEmbedding : Isometry (extensionEmbedding v) :=
  Isometry.of_dist_eq (extensionEmbedding_dist_eq_of_comp v.norm_embedding_eq)

/-- The embedding `v.completion →+* ℝ` at a real infinite palce is an isometry. -/
theorem isometry_extensionEmbedding_of_isReal {v : InfinitePlace K} (hv : IsReal v) :
    Isometry (extensionEmbedding_of_isReal hv) :=
  Isometry.of_dist_eq (extensionEmbedding_dist_eq_of_comp <| v.norm_embedding_of_isReal hv)

/-- The embedding `v.completion →+* ℂ` has closed image inside `ℂ`. -/
theorem isClosed_image_extensionEmbedding : IsClosed (Set.range (extensionEmbedding v)) :=
  (closedEmbedding_extensionEmbedding_of_comp v.norm_embedding_eq).isClosed_range

/-- The embedding `v.completion →+* ℝ` associated to a real infinite place has closed image
inside `ℝ`. -/
theorem isClosed_image_extensionEmbedding_of_isReal {v : InfinitePlace K} (hv : IsReal v) :
    IsClosed (Set.range (extensionEmbedding_of_isReal hv)) :=
  (closedEmbedding_extensionEmbedding_of_comp <| v.norm_embedding_of_isReal hv).isClosed_range

theorem subfield_ne_real_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    (extensionEmbedding v).fieldRange ≠ Complex.ofReal.fieldRange := by
  contrapose! hv
  simp only [not_isComplex_iff_isReal, isReal_iff]
  ext x
  obtain ⟨r, hr⟩ := hv ▸ extensionEmbedding_coe v x ▸ RingHom.mem_fieldRange_self _ _
  simp only [ComplexEmbedding.conjugate_coe_eq, ← hr, Complex.ofReal_eq_coe, Complex.conj_ofReal]

/-- If `v` is a complex infinite place, then the embedding `v.completion →+* ℂ` is surjective. -/
theorem surjective_extensionEmbedding_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    Function.Surjective (extensionEmbedding v) := by
  rw [← RingHom.fieldRange_eq_top_iff]
  refine (Complex.subfield_eq_of_closed <| ?_).resolve_left <|
    subfield_ne_real_of_isComplex hv
  exact isClosed_image_extensionEmbedding v

/-- If `v` is a complex infinite place, then the embedding `v.completion →+* ℂ` is bijective. -/
theorem bijective_extensionEmbedding_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    Function.Bijective (extensionEmbedding v) :=
  ⟨(extensionEmbedding v).injective, surjective_extensionEmbedding_of_isComplex hv⟩

/-- The ring isomorphism `v.completion ≃+* ℂ`, when `v` is complex, given by the bijection
`v.completion →+* ℂ`. -/
def ringEquiv_complex_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    v.completion ≃+* ℂ :=
  RingEquiv.ofBijective _ (bijective_extensionEmbedding_of_isComplex hv)

/-- If the infinite place `v` is complex, then `v.completion` is isometric to `ℂ`. -/
def isometryEquiv_complex_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    v.completion ≃ᵢ ℂ where
  toEquiv := ringEquiv_complex_of_isComplex hv
  isometry_toFun := isometry_extensionEmbedding v

/-- If `v` is a real infinite place, then the embedding `v.completion →+* ℝ` is surjective. -/
theorem surjective_extensionEmbedding_of_isReal {v : InfinitePlace K} (hv : IsReal v) :
    Function.Surjective (extensionEmbedding_of_isReal hv) := by
  rw [← RingHom.fieldRange_eq_top_iff, ← Real.subfield_eq_of_closed]
  exact isClosed_image_extensionEmbedding_of_isReal hv

/-- If `v` is a real infinite place, then the embedding `v.completion →+* ℝ` is bijective. -/
theorem bijective_extensionEmbedding_of_isReal {v : InfinitePlace K} (hv : IsReal v) :
    Function.Bijective (extensionEmbedding_of_isReal hv) :=
  ⟨(extensionEmbedding_of_isReal hv).injective, surjective_extensionEmbedding_of_isReal hv⟩

/-- The ring isomorphism `v.completion ≃+* ℝ`, when `v` is real, given by the bijection
`v.completion →+* ℝ`. -/
def ringEquiv_real_of_isReal {v : InfinitePlace K} (hv : IsReal v) : v.completion ≃+* ℝ :=
  RingEquiv.ofBijective _ (bijective_extensionEmbedding_of_isReal hv)

/-- If the infinite place `v` is real, then `v.completion` is isometric to `ℝ`. -/
def isometryEquiv_real_of_isReal {v : InfinitePlace K} (hv : IsReal v) : v.completion ≃ᵢ ℝ where
  toEquiv := ringEquiv_real_of_isReal hv
  isometry_toFun := isometry_extensionEmbedding_of_isReal hv

end NumberField.InfinitePlace.Completion
