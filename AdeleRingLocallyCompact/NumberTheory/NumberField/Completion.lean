/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.NumberTheory.NumberField.Embeddings
import AdeleRingLocallyCompact.Algebra.Field.Subfield
import AdeleRingLocallyCompact.Algebra.Ring.Equiv
import AdeleRingLocallyCompact.Analysis.Normed.Module.Completion
import AdeleRingLocallyCompact.Analysis.Normed.Ring.WithAbs
import AdeleRingLocallyCompact.FromMathlib.Algebra.Algebra.Pi
import AdeleRingLocallyCompact.NumberTheory.NumberField.Embeddings
import AdeleRingLocallyCompact.NumberTheory.NumberField.WeakApproximation
import AdeleRingLocallyCompact.Topology.Algebra.Algebra
import AdeleRingLocallyCompact.Topology.Algebra.UniformRing
import AdeleRingLocallyCompact.Topology.UniformSpace.Basic
import AdeleRingLocallyCompact.Topology.Instances.Real
import AdeleRingLocallyCompact.Topology.Algebra.UniformRing

open scoped Classical TensorProduct

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

variable {w : AbsoluteValue L ℝ} {g : WithAbs v →+* WithAbs w}

abbrev map_of_comp (h : ∀ x, w (g x) = v x) : v.completion →+* w.completion :=
    UniformSpace.Completion.mapRingHom g
      (WithAbs.uniformInducing_of_comp h).uniformContinuous.continuous

theorem map_of_comp_coe (h : ∀ x, w (g x) = v x) (x : K) : map_of_comp h x = g x :=
  UniformSpace.Completion.mapRingHom_coe
    (WithAbs.uniformInducing_of_comp h).uniformContinuous x

theorem map_of_comp_dist_eq (h : ∀ x, w (g x) = v x) (x y : v.completion) :
    dist (map_of_comp h x) (map_of_comp h y) = dist x y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ (fun x y => ?_)
  · refine isClosed_eq ?_ continuous_dist
    exact continuous_iff_continuous_dist.1 UniformSpace.Completion.continuous_extension
  · simp only [map_of_comp_coe, UniformSpace.Completion.dist_eq]
    exact UniformSpace.Completion.dist_eq x y ▸
      (WithAbs.isometry_of_comp (L := WithAbs w) h).dist_eq x y

theorem isometry_map_of_comp (h : ∀ x, w (g x) = v x) : Isometry (map_of_comp h) :=
  Isometry.of_dist_eq <| map_of_comp_dist_eq h

end AbsoluteValue.Completion

namespace NumberField.InfinitePlace

open AbsoluteValue.Completion

open WithAbs

variable {K : Type*} [Field K]
variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
  (v : InfinitePlace K) (w : InfinitePlace L)

/-- The completion of a number field at an infinite place. -/
abbrev completion := v.1.completion

theorem abs_eq_of_comap {v : InfinitePlace K} {w : InfinitePlace L}
    (h : w.comap (algebraMap _ _) = v) :
    ∀ x, w.1 (algebraMap (WithAbs v.1) (WithAbs w.1) x) = v.1 x := by
  rw [← h]
  intro x
  rfl

namespace Completion

instance : NormedField v.completion :=
  letI := (WithAbs.uniformInducing_of_comp v.norm_embedding_eq).completableTopField
  UniformSpace.Completion.instNormedFieldOfCompletableTopField (WithAbs v.1)

instance : Algebra K v.completion :=
  inferInstanceAs (Algebra (WithAbs v.1) v.1.completion)

instance : IsScalarTower K v.completion v.completion := IsScalarTower.right

theorem algebraMap_eq_coe :
    ⇑(algebraMap K v.completion) = ((↑) : K → v.completion) := rfl

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

@[simp]
theorem ringEquiv_complex_of_isComplex_apply {v : InfinitePlace K} (hv : IsComplex v)
    (x : v.completion) : ringEquiv_complex_of_isComplex hv x = extensionEmbedding v x := rfl

@[simp]
theorem ringEquiv_complex_of_isComplex_coe {v : InfinitePlace K} (hv : IsComplex v) (k : K) :
    ringEquiv_complex_of_isComplex hv k = embedding v k := by
  rw [ringEquiv_complex_of_isComplex_apply, extensionEmbedding_coe]

/-- If the infinite place `v` is complex, then `v.completion` is isometric to `ℂ`. -/
def isometryEquiv_complex_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    v.completion ≃ᵢ ℂ where
  toEquiv := ringEquiv_complex_of_isComplex hv
  isometry_toFun := isometry_extensionEmbedding v

def algEquiv_complex_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    letI : Algebra v.completion ℂ := RingHom.toAlgebra <| ringEquiv_complex_of_isComplex hv
    v.completion ≃ₐ[v.completion] ℂ :=
  letI : Algebra v.completion ℂ := RingHom.toAlgebra <| ringEquiv_complex_of_isComplex hv
  AlgEquiv.ofRingEquiv (fun _ => rfl)

def starAlgEquiv_complex_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    letI : Algebra v.completion ℂ :=
      RingHom.toAlgebra <| (starRingAut).toRingHom.comp
        (ringEquiv_complex_of_isComplex hv).toRingHom
    v.completion ≃ₐ[v.completion] ℂ := by
  letI : Algebra v.completion ℂ :=
      RingHom.toAlgebra <| (starRingAut).toRingHom.comp
        (ringEquiv_complex_of_isComplex hv).toRingHom
  let f := (ringEquiv_complex_of_isComplex hv).trans starRingAut
  have hf : ∀ (x : v.completion), f ((algebraMap v.completion v.completion) x) =
      (algebraMap v.completion _) x := by
    intro x
    simp [f, RingHom.algebraMap_toAlgebra]
  exact AlgEquiv.ofRingEquiv hf

@[simp]
theorem algEquiv_complex_of_isComplex_apply {v : InfinitePlace K} (hv : IsComplex v)
    (x : v.completion) :
    algEquiv_complex_of_isComplex hv x = extensionEmbedding v x := by
  rw [algEquiv_complex_of_isComplex]
  simp only [AlgEquiv.ofRingEquiv_apply, ringEquiv_complex_of_isComplex_apply]

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

@[simp]
theorem ringEquiv_real_of_isReal_apply {v : InfinitePlace K} (hv : IsReal v) (x : v.completion) :
    ringEquiv_real_of_isReal hv x = extensionEmbedding_of_isReal hv x := rfl

@[simp]
theorem ringEquiv_real_of_isReal_coe {v : InfinitePlace K} (hv : IsReal v) (k : K) :
    ringEquiv_real_of_isReal hv k = embedding_of_isReal hv k := by
  rw [ringEquiv_real_of_isReal_apply, extensionEmbedding_of_isReal_coe]

/-- If the infinite place `v` is real, then `v.completion` is isometric to `ℝ`. -/
def isometryEquiv_real_of_isReal {v : InfinitePlace K} (hv : IsReal v) : v.completion ≃ᵢ ℝ where
  toEquiv := ringEquiv_real_of_isReal hv
  isometry_toFun := isometry_extensionEmbedding_of_isReal hv

def algEquiv_real_of_isReal {v : InfinitePlace K} (hv : IsReal v) :
    letI : Algebra v.completion ℝ := RingHom.toAlgebra <| ringEquiv_real_of_isReal hv
    v.completion ≃ₐ[v.completion] ℝ :=
  letI : Algebra v.completion ℝ := RingHom.toAlgebra <| ringEquiv_real_of_isReal hv
  AlgEquiv.ofRingEquiv (fun _ => rfl)

instance {v : InfinitePlace K} : NontriviallyNormedField (v.completion) where
  toNormedField := InfinitePlace.Completion.instNormedFieldCompletion v
  non_trivial := by
    simp only [← dist_zero_right]
    have h := InfinitePlace.Completion.isometry_extensionEmbedding v |>.dist_eq
    use 2
    simp only [← h 2 0, map_ofNat, map_zero, dist_zero_right, RCLike.norm_ofNat, Nat.one_lt_ofNat]

instance : Algebra K (WithAbs w.1) := ‹Algebra K L›

instance : UniformContinuousConstSMul K (WithAbs w.1) :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _

instance : IsScalarTower K L (WithAbs w.1) := inferInstanceAs (IsScalarTower K L L)

instance : SMulCommClass K v.completion v.completion := Algebra.to_smulCommClass

noncomputable instance : Algebra K (w.completion) where
  toFun k := algebraMap L w.completion (algebraMap K L k)
  map_one' := by simp only [map_one]
  map_mul' k₁ k₂ := by simp only [map_mul]
  map_zero' := by simp only [map_zero]
  map_add' k₁ k₂ := by simp only [map_add]
  commutes' k lhat := mul_comm _ _
  smul_def' k lhat := by
    rw [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, UniformSpace.Completion.smul_def,
    ← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq,
    UniformSpace.Completion.map_smul_eq_mul_coe, UniformSpace.Completion.algebraMap_def]

theorem algebraMap_comp (k : K) : algebraMap K w.completion k =
    algebraMap L w.completion (algebraMap K L k) :=
  rfl

namespace ExtensionPlace

variable (wv : ExtensionPlace L v)
variable {v}

instance : Nonempty (ExtensionPlace L v) := by
  have : Function.Surjective fun (v : NumberField.InfinitePlace L) => v.comap (algebraMap K L) :=
    NumberField.InfinitePlace.comap_surjective
  let ⟨w, h⟩ := this v
  exact ⟨w, h⟩

instance : Nontrivial
    ((w : ExtensionPlace L v) → w.1.completion) :=
  instNonemptyExtensionPlace.elim fun w => Pi.nontrivial_at w

def comap_ringHom :
    v.completion →+* wv.1.completion :=
  map_of_comp (L := WithAbs wv.1.1) (NumberField.InfinitePlace.abs_eq_of_comap wv.2)

variable {wv}

instance : Algebra v.completion wv.1.completion := RingHom.toAlgebra <|
  comap_ringHom wv

instance : IsScalarTower v.completion wv.1.completion wv.1.completion :=
  IsScalarTower.right

variable (wv)

@[simp]
theorem algebraMap_def :
      algebraMap v.completion wv.1.completion =
    map_of_comp (L := WithAbs wv.1.1) (abs_eq_of_comap wv.2) :=
  rfl

@[simp]
theorem algebraMap_apply (x : v.completion) :
    algebraMap v.completion wv.1.completion x = UniformSpace.Completion.map
      (algebraMap (WithAbs v.1) (WithAbs wv.1.1)) x :=
  rfl

@[simp]
theorem algebraMap_coe (k : K) :
    algebraMap v.completion wv.1.completion k = algebraMap (WithAbs v.1) (WithAbs wv.1.1) k := by
  rw [algebraMap_apply]
  exact UniformSpace.Completion.map_coe (WithAbs.uniformContinuous_algebraMap v.1 wv.1.1
    (abs_eq_of_comap wv.2)) _

@[simp]
theorem smul_def (x : v.completion) (y : wv.1.completion) :
    x • y = algebraMap _ _ x * y :=
  rfl

theorem algebraMap_comp (k : K) :
    algebraMap K wv.1.completion k =
      algebraMap v.completion wv.1.completion (algebraMap K v.completion k) := by
  simp only [UniformSpace.Completion.algebraMap_def]
  rw [algebraMap_coe _]
  rfl

instance : IsScalarTower K v.completion wv.1.completion :=
  IsScalarTower.of_algebraMap_eq (algebraMap_comp wv)

instance : NormedSpace v.completion wv.1.completion where
  norm_smul_le x y := by
    rw [smul_def, norm_mul, algebraMap_def]
    have := AbsoluteValue.Completion.isometry_map_of_comp (L := WithAbs wv.1.1)
      (abs_eq_of_comap wv.2)
    rw [this.norm_map_of_map_zero (map_zero _)]

noncomputable instance : FiniteDimensional v.completion wv.1.completion :=
  FiniteDimensional.of_locallyCompactSpace v.completion

/-! `Kᵥ`-algebra isomorphisms between `L_w` and `ℝ` or `ℂ` whenever `w` lies above `v` in each
of the following four cases:
* `L_w ≃ₐ[Kᵥ] ℝ` when `v` is real and `w` is unramified.
* `L_w ≃ₐ[Kᵥ] ℂ` when `v` is real and `w` is ramified.
* `L_v ≃ₐ[Kᵥ] ℂ` when `v` is complex and the embedding of `w` extends the embedding of `v`.
* `L_v ≃ₐ[Kᵥ] ℂ` when `v` is complex and the conjugate embedding of `w` extends the embedding
of `v`.

The last two need to be treated separately even though the underlying ring equivalences
are the same because the induced `Kᵥ`-algebras on `L_v` are different.
-/

variable {wv : ExtensionPlace L v}

theorem ringEquiv_real_of_isReal_comap_coe (hv : v.IsReal) (hw : wv.1.IsReal) (k : K) :
    ringEquiv_real_of_isReal hw (algebraMap _ _ k) = ringEquiv_real_of_isReal hv k := by
  simp only [ringEquiv_real_of_isReal_apply, extensionEmbedding_of_isReal_coe, algebraMap_comp,
    algebraMap_eq_coe]
  rw [algebraMap_def, map_of_comp]
  rw [UniformSpace.Completion.mapRingHom_coe
    (uniformContinuous_algebraMap _ _ (abs_eq_of_comap wv.2))]
  simp only [extensionEmbedding_of_isReal_coe]
  apply Complex.ofReal_injective
  simp only [embedding_of_isReal_apply]
  rw [← wv.isReal_extends hv]
  rfl

theorem ringEquiv_real_of_isReal_comap
    (hv : v.IsReal) (hw : wv.1.IsReal) (x : v.completion) :
    ringEquiv_real_of_isReal hw (comap_ringHom wv x) = ringEquiv_real_of_isReal hv x := by
  apply UniformSpace.Completion.induction_on
    (p := fun x => (ringEquiv_real_of_isReal hw).toRingHom
        ((algebraMap v.completion wv.1.completion) x) =
      (ringEquiv_real_of_isReal hv).toRingHom x)
  · apply isClosed_eq
    · apply Continuous.comp
      · simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
        exact UniformSpace.Completion.continuous_extension
      · exact UniformSpace.Completion.continuous_map
    · exact UniformSpace.Completion.continuous_extension
  · intro a
    have : algebraMap v.completion (wv.1.completion) (a) =
        algebraMap v.completion (wv.1.completion) ((algebraMap K v.completion) a) :=
      rfl
    rw [this]
    rw [← algebraMap_comp]
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [ringEquiv_real_of_isReal_comap_coe hv hw]

def algEquivRealOfIsUnramifiedIsReal (hw : wv.1.IsUnramified K) (hv : v.IsReal) :
    letI : Algebra v.completion ℝ := (ringEquiv_real_of_isReal hv).toRingHom.toAlgebra
    wv.1.completion ≃ₐ[v.completion] ℝ := by
  have hr : wv.1.IsReal := hw.isReal_of_isReal hv
  letI : Algebra v.completion ℝ := (ringEquiv_real_of_isReal hv).toRingHom.toAlgebra
  letI : Algebra wv.1.completion ℝ := (ringEquiv_real_of_isReal hr).toRingHom.toAlgebra
  letI : IsScalarTower v.completion wv.1.completion ℝ := by
    apply IsScalarTower.mk
    intro x y r
    simp only [Algebra.smul_def]
    simp only [RingHom.algebraMap_toAlgebra, map_mul, mul_assoc, RingEquiv.toRingHom_eq_coe]
    simp only [RingHom.coe_coe]
    rw [ringEquiv_real_of_isReal_comap hv hr]
  exact algEquiv_real_of_isReal hr |>.restrictScalars v.completion

theorem ringEquiv_real_of_isComplex_comap_coe (hv : v.IsReal) (hw : wv.1.IsComplex) (k : K) :
    ringEquiv_complex_of_isComplex hw (algebraMap _ _ k) =
      Complex.ofReal (ringEquiv_real_of_isReal hv k) := by
  rw [ringEquiv_complex_of_isComplex_apply, ringEquiv_real_of_isReal_apply,
    extensionEmbedding_of_isReal_coe, algebraMap_comp,
    algebraMap_eq_coe]
  rw [algebraMap_def, map_of_comp]
  rw [UniformSpace.Completion.mapRingHom_coe
    (uniformContinuous_algebraMap _ _ (abs_eq_of_comap wv.2))]
  simp only [extensionEmbedding_coe]
  simp only [Complex.ofReal_eq_coe, embedding_of_isReal_apply]
  rw [← wv.isReal_extends hv]
  rfl

theorem ringEquiv_complex_of_isReal_comap (hv : v.IsReal) (hw : wv.1.IsComplex) (x : v.completion) :
    ringEquiv_complex_of_isComplex hw (comap_ringHom wv x) =
      Complex.ofReal (ringEquiv_real_of_isReal hv x) := by
  apply UniformSpace.Completion.induction_on
    (p := fun x => (ringEquiv_complex_of_isComplex hw).toRingHom
        ((algebraMap v.completion wv.1.completion) x) = _)
  · apply isClosed_eq
    · apply Continuous.comp
      · simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
        exact UniformSpace.Completion.continuous_extension
      · exact UniformSpace.Completion.continuous_map
    · apply Continuous.comp
      · exact Complex.continuous_ofReal
      · exact UniformSpace.Completion.continuous_extension
  · intro a
    have : algebraMap v.completion (wv.1.completion) (a) =
        algebraMap v.completion (wv.1.completion) ((algebraMap K v.completion) a) :=
      rfl
    rw [this]
    rw [← algebraMap_comp]
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [ringEquiv_real_of_isComplex_comap_coe hv hw]

def algEquivComplexOfIsRamified (hw : wv.1.IsRamified K) (hv : v.IsReal) :
    letI : Algebra v.completion ℂ := RingHom.toAlgebra <|
      (algebraMap ℝ ℂ).comp (ringEquiv_real_of_isReal hv)
    wv.1.completion ≃ₐ[v.completion] ℂ := by
  have hw : wv.1.IsComplex := hw.isComplex
  letI : Algebra wv.1.completion ℂ := (ringEquiv_complex_of_isComplex hw).toRingHom.toAlgebra
  letI : Algebra v.completion ℂ := RingHom.toAlgebra <|
      (algebraMap ℝ ℂ).comp (ringEquiv_real_of_isReal hv)
  letI : IsScalarTower v.completion wv.1.completion ℂ := by
    apply IsScalarTower.mk
    intro x y r
    simp only [Algebra.smul_def]
    simp only [RingHom.algebraMap_toAlgebra, map_mul, mul_assoc, RingEquiv.toRingHom_eq_coe]
    simp only [RingHom.coe_coe]
    rw [ringEquiv_complex_of_isReal_comap hv hw]
    rfl
  exact algEquiv_complex_of_isComplex hw |>.restrictScalars v.completion

theorem ringEquiv_complex_of_isComplex_coe_of_extends (hv : v.IsComplex)
    (hw : wv.1.IsComplex)
    (he : wv.1.embedding.comp (algebraMap K L) = v.embedding)
    (k : K) :
    (ringEquiv_complex_of_isComplex hw (algebraMap _ _ k) =
      ringEquiv_complex_of_isComplex hv k) := by
  simp only [ringEquiv_complex_of_isComplex_apply, extensionEmbedding_coe, algebraMap_comp,
    algebraMap_eq_coe]
  rw [algebraMap_def, map_of_comp]
  simp [UniformSpace.Completion.mapRingHom_coe
    (uniformContinuous_algebraMap _ _ (abs_eq_of_comap wv.2))]
  rw [← he]
  rfl

theorem ringEquiv_complex_of_isComplex_apply_of_extends
    (hv : v.IsComplex) (hw : wv.1.IsComplex)
    (he : wv.1.embedding.comp (algebraMap K L) = v.embedding)
    (x : v.completion) :
    ringEquiv_complex_of_isComplex hw (comap_ringHom wv x) =
      ringEquiv_complex_of_isComplex hv x := by
  apply UniformSpace.Completion.induction_on
    (p := fun x => (ringEquiv_complex_of_isComplex hw).toRingHom
        ((algebraMap v.completion wv.1.completion) x) =
      (ringEquiv_complex_of_isComplex hv).toRingHom x)
  · apply isClosed_eq
    · apply Continuous.comp
      · simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
        exact UniformSpace.Completion.continuous_extension
      · exact UniformSpace.Completion.continuous_map
    · exact UniformSpace.Completion.continuous_extension
  intro a
  have : algebraMap v.completion (wv.1.completion) a =
      algebraMap v.completion (wv.1.completion) ((algebraMap K v.completion) a) :=
    rfl
  rw [this]
  rw [← algebraMap_comp]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← ringEquiv_complex_of_isComplex_coe_of_extends hv hw he]

def algEquivComplexOfIsComplexExtension  (hv : v.IsComplex)
    (he : wv.1.embedding.comp (algebraMap K L) = v.embedding) :
    letI : Algebra v.completion ℂ := RingHom.toAlgebra <| ringEquiv_complex_of_isComplex hv
    wv.1.completion ≃ₐ[v.completion] ℂ := by
  have hw := wv.isComplex_of_isComplex hv
  letI : Algebra v.completion ℂ := (ringEquiv_complex_of_isComplex hv).toRingHom.toAlgebra
  letI : Algebra wv.1.completion ℂ := (ringEquiv_complex_of_isComplex hw).toRingHom.toAlgebra
  letI : IsScalarTower v.completion wv.1.completion ℂ := by
    apply IsScalarTower.mk
    intro x y r
    simp only [Algebra.smul_def]
    simp only [RingHom.algebraMap_toAlgebra, map_mul, mul_assoc, RingEquiv.toRingHom_eq_coe]
    simp only [RingHom.coe_coe]
    rw [ringEquiv_complex_of_isComplex_apply_of_extends hv hw he]
  exact algEquiv_complex_of_isComplex hw |>.restrictScalars v.completion

theorem ringEquiv_complex_of_isComplex_coe_of_extends_conjugate (hv : v.IsComplex)
    (hw : wv.1.IsComplex)
    (he : (ComplexEmbedding.conjugate wv.1.embedding).comp (algebraMap K L) = v.embedding)
    (k : K) :
    ringEquiv_complex_of_isComplex hw (algebraMap _ _ k) =
      starRingEnd ℂ (ringEquiv_complex_of_isComplex hv k) := by
  simp only [ringEquiv_complex_of_isComplex_apply, extensionEmbedding_coe, algebraMap_comp,
    algebraMap_eq_coe]
  rw [algebraMap_def, map_of_comp]
  simp [UniformSpace.Completion.mapRingHom_coe
    (uniformContinuous_algebraMap _ _ (abs_eq_of_comap wv.2))]
  have := RingHom.congr_fun he k
  simp at this
  rw [← this]
  simp
  rfl

theorem ringEquiv_complex_of_isComplex_apply_of_conjugate_extends (hv : v.IsComplex)
    (hw : wv.1.IsComplex)
    (he : (ComplexEmbedding.conjugate wv.1.embedding).comp (algebraMap K L) = v.embedding)
    (x : v.completion) :
    ringEquiv_complex_of_isComplex hw (comap_ringHom wv x) =
        starRingEnd ℂ (ringEquiv_complex_of_isComplex hv x) := by
  apply UniformSpace.Completion.induction_on
    (p := fun x => (ringEquiv_complex_of_isComplex hw).toRingHom
        ((algebraMap v.completion wv.1.completion) x) = _)
  · apply isClosed_eq
    · apply Continuous.comp
      · exact UniformSpace.Completion.continuous_extension
      · exact UniformSpace.Completion.continuous_map
    · apply Continuous.comp
      · continuity
      · exact UniformSpace.Completion.continuous_extension
  intro a
  have : algebraMap v.completion (wv.1.completion) a =
      algebraMap v.completion (wv.1.completion) ((algebraMap K v.completion) a) :=
    rfl
  rw [this]
  rw [← algebraMap_comp]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← ringEquiv_complex_of_isComplex_coe_of_extends_conjugate hv hw he]

def algEquivComplexOfIsComplexConjugateExtension (hv : v.IsComplex)
    (he : (ComplexEmbedding.conjugate wv.1.embedding).comp (algebraMap K L) = v.embedding) :
    letI : Algebra v.completion ℂ := RingHom.toAlgebra <|
      (starRingEnd ℂ).comp (ringEquiv_complex_of_isComplex hv).toRingHom
    wv.1.completion ≃ₐ[v.completion] ℂ := by
  have hw := wv.isComplex_of_isComplex hv
  letI : Algebra v.completion ℂ :=
    ((starRingEnd ℂ).comp (ringEquiv_complex_of_isComplex hv).toRingHom).toAlgebra
  letI : Algebra wv.1.completion ℂ := (ringEquiv_complex_of_isComplex hw).toRingHom.toAlgebra
  letI : IsScalarTower v.completion wv.1.completion ℂ := by
    apply IsScalarTower.mk
    intro x y r
    simp only [Algebra.smul_def]
    simp only [RingHom.algebraMap_toAlgebra, map_mul, mul_assoc, RingEquiv.toRingHom_eq_coe]
    simp only [RingHom.coe_coe]
    rw [ringEquiv_complex_of_isComplex_apply_of_conjugate_extends wv hv hw he]
    rfl
  exact algEquiv_complex_of_isComplex hw |>.restrictScalars v.completion

end ExtensionPlace

open ExtensionPlace

variable [NumberField K]

theorem comap_prod_finrank : FiniteDimensional.finrank v.completion
      ((wv : ExtensionPlace L v) → wv.1.completion) =
    FiniteDimensional.finrank K L := by
  rw [FiniteDimensional.finrank_pi_fintype v.completion (ι := ExtensionPlace L v)]
  by_cases hv : v.IsReal
  · have h₀ (wv : ExtensionPlace L v) (hw : IsUnramified K wv.1) :
        FiniteDimensional.finrank v.completion wv.1.completion = 1 := by
      letI : Algebra v.completion ℝ := (ringEquiv_real_of_isReal hv).toRingHom.toAlgebra
      have := (algEquivRealOfIsUnramifiedIsReal hw hv).toLinearEquiv.finrank_eq
      rw [this]
      rw [← algEquiv_real_of_isReal hv |>.toLinearEquiv.finrank_eq]
      exact FiniteDimensional.finrank_self _
    have h₁ (wv : ExtensionPlace L v) (hw : ¬IsUnramified K wv.1) :
        FiniteDimensional.finrank v.completion wv.1.completion = 2 := by
      letI : Algebra v.completion ℝ := (ringEquiv_real_of_isReal hv).toRingHom.toAlgebra
      have := (algEquivComplexOfIsRamified hw hv).toLinearEquiv.finrank_eq
      rw [this]
      have := algEquiv_real_of_isReal hv |>.toLinearEquiv.finrank_eq
      rw [← FiniteDimensional.finrank_mul_finrank v.completion ℝ ℂ, ← this,
        FiniteDimensional.finrank_self _]
      norm_num
    convert ExtensionPlace.sum_ramificationIdx_eq K L v
    have h₃ (wv : ExtensionPlace L v) (hw : IsUnramified K wv.1) := hw.isReal_of_isReal hv
    have h₄ (wv : ExtensionPlace L v) (hw : IsRamified K wv.1) := hw.isComplex
    rename_i wv _
    by_cases hw : IsUnramified K wv.1
    · simp [ExtensionPlace.ramificationIdx, hw, h₃ wv hw, h₀ wv hw]
    · simp [ExtensionPlace.ramificationIdx, InfinitePlace.not_isComplex_iff_isReal.2 hv, hw,
        h₄ wv hw, h₁ wv hw]
  · simp at hv
    have h (wv : ExtensionPlace L v) :
        FiniteDimensional.finrank v.completion wv.1.completion = 1 := by
      cases wv.extends_or_conjugate_extends with
      | inl h =>
        letI : Algebra v.completion ℂ := (ringEquiv_complex_of_isComplex hv).toRingHom.toAlgebra
        have := algEquiv_complex_of_isComplex hv |>.toLinearEquiv.finrank_eq
        have := algEquivComplexOfIsComplexExtension hv h |>.toLinearEquiv.finrank_eq
        rw [this]
        rw [← algEquiv_complex_of_isComplex hv |>.toLinearEquiv.finrank_eq]
        exact FiniteDimensional.finrank_self _
      | inr h =>
        have := letI : Algebra v.completion ℂ :=
            ((starRingEnd ℂ).comp (ringEquiv_complex_of_isComplex hv).toRingHom).toAlgebra
          algEquivComplexOfIsComplexConjugateExtension hv h
            |>.toLinearEquiv.finrank_eq
        rw [this]
        have := letI : Algebra v.completion ℂ :=
          RingHom.toAlgebra <| ((starRingAut (R := ℂ)).toRingHom.comp
            (ringEquiv_complex_of_isComplex hv).toRingHom)
          starAlgEquiv_complex_of_isComplex hv |>.toLinearEquiv.finrank_eq
        rw [FiniteDimensional.finrank_self] at this
        rw [this]
    convert ExtensionPlace.sum_ramificationIdx_eq K L v
    rw [h]
    rename_i wv _
    simp [ExtensionPlace.ramificationIdx, InfinitePlace.isUnramified_iff.2 (Or.inr <| wv.2 ▸ hv),
      wv.isComplex_of_isComplex hv]

variable (L)

theorem comap_prod_finrank_eq_finrank_tensorProduct :
    FiniteDimensional.finrank v.completion ((w : ExtensionPlace L v) → w.1.completion) =
      FiniteDimensional.finrank v.completion (v.completion ⊗[K] L) := by
  rw [FiniteDimensional.finrank_tensorProduct, FiniteDimensional.finrank_self,
    comap_prod_finrank, one_mul]

/-! # Base change for infinite completions of number fields

Base change for infinite completions of number fields is the continuous algebra equivalence
`Kᵥ ⊗[K] L ≃A[Kᵥ] ∏ (v | w), L_w`.
-/

variable (wv : ExtensionPlace L v)
variable {L v}

def comap_continuousAlgHom :
    v.completion →A[v.completion] wv.1.completion :=
  ({
    __ := comap_ringHom wv
    commutes' := by
      intro r
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe, comap_ringHom, UniformSpace.Completion.mapRingHom_apply]
      rw [algebraMap_eq_coe, UniformSpace.Completion.map_coe] ; rfl
      exact WithAbs.uniformContinuous_algebraMap v.1 wv.1.1
        (abs_eq_of_comap wv.2)
    cont := UniformSpace.Completion.continuous_map} : v.completion →A[K] wv.1.completion)
      |>.extendScalars v.completion

variable (K L v)

abbrev sigmaExtensionEquiv :
    ((v : InfinitePlace K) × ExtensionPlace L v )≃ InfinitePlace L :=
  Equiv.sigmaFiberEquiv _

variable {K}

def comap_pi_continuousAlgHom :
    v.completion →A[v.completion] ((wv : ExtensionPlace L v) → wv.1.completion) :=
  Pi.continuousAlgHom _ <| (fun wv => comap_continuousAlgHom wv)

def algebraMap_pi : L →ₐ[K] ((wv : ExtensionPlace L v) → wv.1.completion) :=
    (Pi.algHom _ <| fun ⟨_, _⟩ => ⟨algebraMap _ _, fun _ => rfl⟩)

def baseChange_algHom :
    v.completion ⊗[K] L →ₐ[v.completion] ((wv : ExtensionPlace L v) → wv.1.completion) :=
  Algebra.TensorProduct.lift (comap_pi_continuousAlgHom L v)
    (algebraMap_pi L v) (fun _ _ => mul_comm _ _)

instance : TopologicalSpace (v.completion ⊗[K] L) :=
  TopologicalSpace.induced (baseChange_algHom L v) inferInstance

def baseChangeAlgHom :
    v.completion ⊗[K] L →A[v.completion] ((wv : ExtensionPlace L v) → wv.1.completion) where
  __ := baseChange_algHom L v

-- TODO generalise this
theorem matrix_det_approx {n : ℕ}
    (B : Basis (Fin n) v.completion ((w : ExtensionPlace L v) → w.1.completion))
    (h : ∀ r, r > 0 → ∃ α : Fin n → L, ∀ i,
      dist (B i) (algebraMap _ ((w : ExtensionPlace L v) → w.1.completion) (α i)) < r)
    (ε : ℝ)
    (hε : ε > 0) :
    ∃ β : Fin n → L,
      dist (B.toMatrix B).det
        (B.toMatrix (fun i => algebraMap _
          ((w : ExtensionPlace L v) → w.1.completion) (β i))).det < ε := by
  let X := (Fin n) → (w : ExtensionPlace L v) → w.1.completion
  let f : X → Matrix (Fin n) (Fin n) v.completion := fun α => B.toMatrix fun i => α i
  have hf : Continuous f :=
    B.toMatrixEquiv.toLinearMap.continuous_of_finiteDimensional
  have := Continuous.matrix_det hf
  rw [Metric.continuous_iff] at this
  have hc (b : X) := this b ε hε
  choose δ hδ using hc B
  specialize h δ hδ.1
  let ⟨α, hα⟩ := h
  use α
  rw [dist_comm]
  apply hδ.2
  rw [dist_comm, dist_eq_norm]
  simp_rw [dist_eq_norm] at hα
  rw [Pi.norm_def]
  have := Finset.sup_lt_iff
    (f := fun i => ‖B i - algebraMap L ((w : ExtensionPlace L v) → w.1.completion) (α i)‖₊)
    (a := ⟨δ, le_of_lt hδ.1⟩) (s := Finset.univ) hδ.1
  exact this.2 fun i _ => hα i

theorem matrix_approx {n : ℕ}
    (B : Basis (Fin n) v.completion ((w : ExtensionPlace L v) → w.1.completion))
    (h : ∀ r, r > 0 → ∃ α : Fin n → L, ∀ i,
      dist (B i) (algebraMap _ ((w : ExtensionPlace L v) → w.1.completion) (α i)) < r) :
    ∃ β : Fin n → L,
      IsUnit (B.det (fun (i : Fin n) => baseChange_algHom L v (1 ⊗ₜ β i))) := by
  let M := ((w : ExtensionPlace L v) → w.1.completion)
  obtain ⟨β, h⟩ := matrix_det_approx L v B h (1 / 2) (by linarith)
  use β
  rw [isUnit_iff_ne_zero, Basis.det_apply]
  rw [← Basis.det_apply, B.det_self] at h
  intro hc
  simp_rw [baseChange_algHom, Algebra.TensorProduct.lift_tmul] at hc
  have : (comap_pi_continuousAlgHom L v : v.completion →ₐ[v.completion] M) 1 = 1 :=
    map_one (comap_pi_continuousAlgHom L v)
  simp_rw [this, one_mul] at hc
  have (x : _) : algebraMap_pi L v x = algebraMap L M x := rfl
  simp [this] at hc
  rw [hc] at h
  rw [dist_zero_right, norm_one] at h
  linarith

theorem weak_approx {p : InfinitePlace K → Prop} [Nonempty {v // p v}] :
    DenseRange <| algebraMap K ((v : {v : InfinitePlace K // p v}) → v.1.completion) := by
  have hd : DenseRange (Pi.map (fun (v : {v  // p v}) (x : WithAbs v.1.1) =>
    (x : v.1.completion))) :=
    DenseRange.piMap (fun _ => UniformSpace.Completion.denseRange_coe)
  have : algebraMap K ((v : {v : InfinitePlace K // p v}) → v.1.completion) =
    (Pi.map (fun (v : {v  // p v}) (x : WithAbs v.1.1) => (x : v.1.completion))) ∘
      algebraMap K ((v : {v : InfinitePlace K // p v}) → WithAbs v.1.1) := rfl
  rw [this]
  apply DenseRange.comp hd (InfinitePlace.weak_approx' K)
    <| Continuous.piMap (fun _ => UniformSpace.Completion.continuous_coe _)

theorem baseChange_surjective :
    Function.Surjective (baseChange_algHom L v) := by
  let n := (FiniteDimensional.finrank v.completion (v.completion ⊗[K] L))
  let Bw := FiniteDimensional.finBasisOfFinrankEq v.completion
    ((w : ExtensionPlace L v) → w.1.completion) (comap_prod_finrank_eq_finrank_tensorProduct L v)
  have := weak_approx (p := fun w : InfinitePlace L => w.comap (algebraMap K L) = v)
  have hr (r : _) (hr : r > 0) : ∃ (α : Fin n → L),
      ∀ i : Fin n, dist (Bw i) (algebraMap _ _ (α i)) < r := by
    exact ⟨fun i => Classical.choose (this.exists_dist_lt (Bw i) hr),
        fun i => Classical.choose_spec (this.exists_dist_lt (Bw i) hr)⟩
  have := matrix_approx L v Bw hr
  let ⟨α, h⟩ := this
  have := is_basis_iff_det Bw
    (v := (fun (i : Fin n) => baseChange_algHom L v (1 ⊗ₜ α i)))
  rw [← this] at h
  rw [← LinearMap.range_eq_top]
  rw [← top_le_iff]
  rw [← h.2]
  rw [Submodule.span_le]
  intro x hx
  rw [SetLike.mem_coe]
  rw [LinearMap.mem_range]
  obtain ⟨i, hi⟩ := hx
  rw [← hi]
  use 1 ⊗ₜ[K] α i

def baseChange_linearEquiv :
    v.completion ⊗[K] L ≃ₗ[v.completion] ((w : ExtensionPlace L v) → w.1.completion) :=
  LinearEquiv.ofBijective _ ⟨
    LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (comap_prod_finrank_eq_finrank_tensorProduct L v).symm |>.2 (baseChange_surjective L v),
        baseChange_surjective L v⟩

def baseChange_algEquiv :
    v.completion ⊗[K] L ≃ₐ[v.completion] ((w : ExtensionPlace L v) → w.1.completion) := by
  apply AlgEquiv.ofLinearEquiv (baseChange_linearEquiv L v)
  · exact map_one (baseChange_algHom L v)
  · intro x y
    exact map_mul (baseChange_algHom L v) _ _

def baseChange :
    v.completion ⊗[K] L ≃A[v.completion] ((w : ExtensionPlace L v) → w.1.completion) where
  __ := baseChange_algEquiv L v
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    convert (baseChange_algEquiv L v).toEquiv.coinduced_symm ▸ continuous_coinduced_rng

end NumberField.InfinitePlace.Completion
