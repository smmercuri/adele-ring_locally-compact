/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.NumberTheory.NumberField.Embeddings
import AdeleRingLocallyCompact.Algebra.Field.Subfield
import AdeleRingLocallyCompact.Algebra.Ring.Equiv
import AdeleRingLocallyCompact.Analysis.Normed.Module.Completion
import AdeleRingLocallyCompact.Topology.Algebra.Algebra
import AdeleRingLocallyCompact.Topology.Algebra.UniformRing
import AdeleRingLocallyCompact.Topology.UniformSpace.Basic
import AdeleRingLocallyCompact.Topology.Instances.Real
import AdeleRingLocallyCompact.Topology.Algebra.UniformRing

open scoped Classical

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
  dist_eq := (inferInstanceAs (NormedRing (WithAbs v))).dist_eq
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

instance {L : Type*} [Field L] [Algebra K L] (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) :
    Algebra (WithAbs v) (WithAbs w) :=
  inferInstanceAs (Algebra K L)

theorem norm_eq (v : AbsoluteValue K ℝ) (x : WithAbs v) : ‖x‖ = v x := rfl

theorem uniformContinuous_algebraMap {L : Type*} [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v x) :
    UniformContinuous (algebraMap (WithAbs v) (WithAbs w)) :=
  (WithAbs.uniformInducing_of_comp (L := WithAbs w) h).uniformContinuous

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

variable {K : Type*} [Field K] (v : InfinitePlace K)
variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
  (w : InfinitePlace L)

local notation "Σ_" v => {w : InfinitePlace L // w.comap (algebraMap K L) = v}

/-- The completion of a number field at an infinite place. -/
abbrev completion := v.1.completion

theorem abs_eq_of_comap {v : InfinitePlace K} {w : InfinitePlace L}
    (h : w.comap (algebraMap _ _) = v) :
    ∀ x, w.1 (algebraMap (WithAbs v.1) (WithAbs w.1) x) = v.1 x := by
  rw [← h]
  intro x
  rfl

theorem isComplex_iff_mult_eq_two {v : InfinitePlace K} : v.IsComplex ↔ v.mult = 2 := by
  simp only [mult, ite_eq_right_iff, OfNat.one_ne_ofNat, imp_false, not_isReal_iff_isComplex]

theorem mult_le_two (v : InfinitePlace K) : v.mult ≤ 2 := by
  simp only [mult]
  by_cases h : v.IsReal
  · simp only [h, if_true, Nat.one_le_ofNat]
  · simp only [h, if_false, le_rfl]

theorem IsReal.comap_of_isUnramified {v : InfinitePlace K} {w : Σ_v}  (hv : v.IsReal)
    (hw : w.1.IsUnramified K) : w.1.IsReal := by
  refine (InfinitePlace.isUnramified_iff.1 hw).resolve_right ?_
  convert w.2 ▸ not_isComplex_iff_isReal.2 hv

theorem comap_of_not_isUnramified {v : InfinitePlace K} {w : Σ_v}
    (hw : ¬w.1.IsUnramified K) : w.1.IsComplex := by
  rw [isUnramified_iff] at hw
  simp at hw
  exact hw.1

theorem IsComplex.comap_isComplex {v : InfinitePlace K} (w : Σ_v)
    (h : v.IsComplex) : w.1.IsComplex := by
  rw [isComplex_iff_mult_eq_two] at *
  have := h ▸ w.2 ▸ w.1.mult_comap_le _
  exact le_antisymm w.1.mult_le_two this

abbrev IsTower {v : InfinitePlace K} (w : Σ_v) : Prop :=
  w.1.embedding ∘ algebraMap K L = v.embedding

abbrev IsConjugateTower {v : InfinitePlace K} (w : Σ_v) : Prop :=
  w.1.embedding ∘ algebraMap K L = ComplexEmbedding.conjugate v.embedding

theorem isTower_or_isConjugateTower {v : InfinitePlace K} (w : Σ_v) :
    IsTower w ∨ IsConjugateTower w := by
  have h := w.2
  rw [← mk_embedding w.1, comap_mk] at h
  have := mk_embedding v
  nth_rw 2 [← h] at this
  rw [mk_eq_iff] at this
  cases this with
  | inl h =>
    left
    rw [IsTower, h]
    rfl
  | inr h =>
    right
    rw [IsConjugateTower, h]
    rfl

theorem isConjugateTower_of_not_isTower {v : InfinitePlace K} {w : Σ_v} (hw : ¬IsTower w) :
    IsConjugateTower w :=
  isTower_or_isConjugateTower w |>.resolve_left hw

/-- I need this lower down for embeddings, because Classical.choose is causing headaches -/

def IsExtension (f : K →+* ℂ) (g : L →+* ℂ) := g.comp (algebraMap K L) = f

variable (L)

abbrev Extends (f : K →+* ℂ) := { g : L →+* ℂ //  g.comp (algebraMap K L) = f }

variable {L}
def IsRamifiedExtension (f : K →+* ℂ) (g : Extends L f) :=
    ComplexEmbedding.IsReal f ∧ ¬ComplexEmbedding.IsReal g.1

theorem comap_mk_of_isExtension {v : InfinitePlace K} (ψ : L →+* ℂ)
    (hψ : IsExtension v.embedding ψ) :
    (InfinitePlace.mk ψ).comap (algebraMap K L) = v := by
  rw [comap_mk, hψ, mk_embedding]

theorem isExtension_of_comap_not_isUnramified {v : InfinitePlace K} {w : InfinitePlace L}
    (h : ¬IsUnramified K w) (h' : w.comap (algebraMap _ _) = v) :
    IsExtension v.embedding w.embedding := by
  rw [← InfinitePlace.mk_embedding w] at h h'
  rw [not_isUnramified_iff] at h
  rw [comap_mk] at h h'
  rw [isComplex_mk_iff, isReal_mk_iff] at h
  have := InfinitePlace.embedding_mk_eq_of_isReal h.2
  rw [IsExtension]
  rw [← this]
  rw [h']

theorem isExtension_conj_of_comap_not_isUnramified {v : InfinitePlace K} {w : InfinitePlace L}
    (h : ¬IsUnramified K w) (h' : w.comap (algebraMap _ _) = v) :
    IsExtension v.embedding (ComplexEmbedding.conjugate w.embedding) := by
  rw [← InfinitePlace.mk_embedding w] at h h'
  rw [not_isUnramified_iff] at h
  rw [comap_mk] at h h'
  rw [isComplex_mk_iff, isReal_mk_iff] at h
  have := InfinitePlace.embedding_mk_eq_of_isReal h.2
  rw [IsExtension]
  ext k
  simp
  rw [← h']
  rw [this]
  nth_rw 2 [ComplexEmbedding.isReal_iff] at h
  have := RingHom.congr_fun h.2 k
  rw [← this]
  rfl

def toExtends {v : InfinitePlace K} {w : InfinitePlace L} (h : ¬IsUnramified K w)
  (h' : w.comap (algebraMap _ _) = v) :
  Extends L v.embedding := ⟨w.embedding, isExtension_of_comap_not_isUnramified h h'⟩

def toExtends_conj {v : InfinitePlace K} {w : InfinitePlace L} (h : ¬IsUnramified K w)
  (h' : w.comap (algebraMap _ _) = v) :
  Extends L v.embedding :=
    ⟨ComplexEmbedding.conjugate w.embedding, isExtension_conj_of_comap_not_isUnramified h h'⟩

theorem not_isUnramified_of_isRamifiedExtension {v : InfinitePlace K} {ψ : Extends L v.embedding}
    (h : IsRamifiedExtension v.embedding ψ) :
    ¬IsUnramified K (InfinitePlace.mk ψ.1) := by
  rw [not_isUnramified_iff]
  rw [IsRamifiedExtension] at h
  have := ψ.2
  rw [isComplex_iff, comap_mk, isReal_iff]
  simp_rw [this]
  rw [embedding_mk_eq_of_isReal h.1]
  refine ⟨?_, h.1⟩
  cases embedding_mk_eq ψ.1 with
  | inl hψ =>
    rw [hψ]; exact h.2
  | inr hψ =>
    rw [hψ, ComplexEmbedding.isReal_conjugate_iff]
    exact h.2

theorem isRamifiedExtension_of_not_isUnramified {v : InfinitePlace K} {w : InfinitePlace L}
    (h : ¬IsUnramified K w) (h' : w.comap (algebraMap _ _) = v) :
    IsRamifiedExtension v.embedding (toExtends h h') := by
  rw [← InfinitePlace.mk_embedding w] at h h'
  rw [not_isUnramified_iff] at h
  rw [comap_mk] at h h'
  rw [isComplex_mk_iff, isReal_mk_iff] at h
  have := InfinitePlace.embedding_mk_eq_of_isReal h.2
  rw [IsRamifiedExtension]
  refine ⟨?_, h.1⟩
  convert h.2
  rw [← this]
  rw [h']

theorem isRamifiedExtension_of_not_isUnramified_conj {v : InfinitePlace K} {w : InfinitePlace L}
    (h : ¬IsUnramified K w) (h' : w.comap (algebraMap _ _) = v) :
    IsRamifiedExtension v.embedding (toExtends_conj h h') := by
  rw [← InfinitePlace.mk_embedding w] at h h'
  rw [not_isUnramified_iff] at h
  rw [comap_mk] at h h'
  rw [isComplex_mk_iff, isReal_mk_iff] at h
  have := InfinitePlace.embedding_mk_eq_of_isReal h.2
  rw [IsRamifiedExtension]
  refine ⟨?_, not_congr ComplexEmbedding.isReal_conjugate_iff |>.2 h.1⟩
  convert h.2
  rw [← this]
  rw [h']

def sum_not_isUnramified_equiv_IsRamifiedExtension {v : InfinitePlace K} :
      { w : Σ_v // ¬IsUnramified K w.1} ⊕ { w : Σ_v // ¬IsUnramified K w.1} ≃
        { ψ : Extends L v.embedding // IsRamifiedExtension v.embedding ψ } := by

  let g₁ : { w : Σ_v // ¬IsUnramified K w.1 } →
    { ψ : Extends L v.embedding // IsRamifiedExtension v.embedding ψ }
    := fun ⟨w, h⟩ => ⟨toExtends h w.2, isRamifiedExtension_of_not_isUnramified h w.2⟩

  let g₂ : { w : Σ_v // ¬IsUnramified K w.1 } →
      { ψ : Extends L v.embedding // IsRamifiedExtension v.embedding ψ }
    := fun ⟨w, h⟩ => ⟨toExtends_conj h w.2,
      isRamifiedExtension_of_not_isUnramified_conj h w.2⟩
  let f := Sum.elim g₁ g₂

  have hg₁_inj : g₁.Injective := by
    simp [g₁, g₂]
    intro a b h
    simp at h ⊢
    ext
    rw [← mk_embedding a.1.1, ← mk_embedding b.1.1]
    simp [toExtends] at h
    rw [h]
  have hg₂_inj : g₂.Injective := by
    simp [g₁, g₂]
    intro a b h
    simp at h ⊢
    ext
    rw [← mk_embedding a.1.1, ← mk_embedding b.1.1]
    simp [toExtends_conj] at h
    rw [h]
  have hg_ne (a : _) (b : _) : g₁ a ≠ g₂ b := by
    simp [g₁, g₂, toExtends, toExtends_conj]
    by_cases hab : a = b
    · rw [hab]
      have := b.2
      rw [not_isUnramified_iff] at this
      rw [isComplex_iff] at this
      rw [ComplexEmbedding.isReal_iff] at this
      exact Ne.symm this.1
    · contrapose! hab
      have : a.1.1 = b.1.1 := by
        rw [← mk_embedding a.1.1, ← mk_embedding b.1.1]
        rw [hab]
        simp only [mk_conjugate_eq, mk_embedding]
      let ⟨⟨a, _⟩, _⟩ := a
      let ⟨⟨b, _⟩, _⟩ := b
      congr

  have hf_inj : f.Injective := hg₁_inj.sum_elim hg₂_inj hg_ne

  have hf_surj : f.Surjective := by
    intro ⟨ψ, h⟩
    have h' : (mk ψ.1).comap (algebraMap _ _) = v := by
      rw [comap_mk, ψ.2, mk_embedding]
    have : ¬IsUnramified K (mk ψ.1) := not_isUnramified_of_isRamifiedExtension h
    let w : Σ_v := ⟨mk ψ.1, h'⟩
    cases embedding_mk_eq ψ.1 with
    | inl h =>
      use Sum.inl ⟨w, this⟩
      simp [f, g₁, toExtends, h]
    | inr h =>
      use Sum.inr ⟨w, this⟩
      simp [f, g₂, toExtends_conj]
      simp [h]

  apply Equiv.ofBijective _ ⟨hf_inj, hf_surj⟩

theorem isExtension_or_conjugate_isExtension {v : InfinitePlace K} {w : Σ_v} :
    IsExtension v.embedding w.1.embedding ∨
      IsExtension v.embedding (ComplexEmbedding.conjugate w.1.embedding) := by
  have := w.2
  rw [← mk_embedding w.1, comap_mk] at this
  have := congrArg InfinitePlace.embedding this
  have := embedding_mk_eq (w.1.embedding.comp (algebraMap K L))
  cases this with
  | inl h =>
    rw [h] at this
    left
    exact this
  | inr h =>
    rw [h] at this
    right
    exact this

theorem not_isRamifiedExtension_of_isUnramified {v : InfinitePlace K} {w : Σ_v}
    (h : IsUnramified K w.1) (h' : IsExtension v.embedding w.1.embedding) :
    ¬IsRamifiedExtension v.embedding ⟨w.1.embedding, h'⟩ := by
  have := w.2
  rw [← mk_embedding w.1] at this
  rw [comap_mk] at this
  contrapose! h
  rw [not_isUnramified_iff]
  rw [IsRamifiedExtension] at h
  rw [isComplex_iff]
  use h.2
  rw [isReal_iff]
  rw [← mk_embedding w.1, comap_mk, h', mk_embedding]
  exact h.1

theorem not_isRamifiedExtension_of_isUnramified' {v : InfinitePlace K} {w : Σ_v}
    (h : IsUnramified K w.1)
    (h' : IsExtension v.embedding (ComplexEmbedding.conjugate w.1.embedding)) :
    ¬IsRamifiedExtension v.embedding ⟨ComplexEmbedding.conjugate w.1.embedding, h'⟩ := by
  have := w.2
  rw [← mk_embedding w.1] at this
  rw [comap_mk] at this
  contrapose! h
  rw [not_isUnramified_iff]
  rw [IsRamifiedExtension] at h
  rw [isComplex_iff]
  rw [← NumberField.ComplexEmbedding.isReal_conjugate_iff]
  use h.2
  rw [isReal_iff]
  rw [← mk_embedding w.1, comap_mk]
  convert h.1

theorem isUnramified_of_not_isRamifiedExtension {v : InfinitePlace K} {ψ : L →+* ℂ}
    (h : IsExtension v.embedding ψ) (h' : ¬IsRamifiedExtension v.embedding ⟨ψ, h⟩) :
    IsUnramified K (mk ψ) := by
  rw [isUnramified_iff]
  rw [IsRamifiedExtension] at h'
  simp at h'
  by_cases h'' : ComplexEmbedding.IsReal v.embedding
  · rw [isReal_iff]
    left
    specialize h' h''
    rwa [embedding_mk_eq_of_isReal h']
  · right
    contrapose! h''
    simp only [comap_mk, not_isComplex_iff_isReal] at h''
    rw [isReal_iff, ComplexEmbedding.isReal_iff] at h''
    rw [ComplexEmbedding.isReal_iff]
    ext k
    rw [IsExtension] at h
    simp
    have := RingHom.congr_fun h'' k
    simp at this
    rw [h] at this
    simp at this
    exact this

def isUnramified_equiv_not_isRamifiedExtension {v : InfinitePlace K} :
    { w : Σ_v // IsUnramified K w.1} ≃
      { ψ : Extends L v.embedding // ¬IsRamifiedExtension v.embedding ψ } := by
  set f : { w : Σ_v // IsUnramified K w.1} →
    { ψ : Extends L v.embedding // ¬IsRamifiedExtension v.embedding ψ } :=
      fun ⟨w, h⟩ =>
        if h' : IsExtension v.embedding w.1.embedding then
          ⟨⟨w.1.embedding, h'⟩, not_isRamifiedExtension_of_isUnramified h h'⟩ else
          ⟨⟨ComplexEmbedding.conjugate w.1.embedding,
            isExtension_or_conjugate_isExtension.resolve_left h'⟩,
              not_isRamifiedExtension_of_isUnramified' h (
                isExtension_or_conjugate_isExtension.resolve_left h')⟩

  have hf_inj : f.Injective := by
    intro ⟨⟨ψ₁, h₁⟩, h₁'⟩ ⟨⟨ψ₂, h₂⟩, h₂'⟩ h
    simp [f] at h
    simp only [Subtype.mk.injEq]
    by_cases hv : ComplexEmbedding.IsReal v.embedding
    · have : ComplexEmbedding.conjugate ψ₁.embedding = ψ₁.embedding := by
        have := IsReal.comap_of_isUnramified (w := ⟨ψ₁, h₁⟩) (isReal_iff.2 hv) h₁'
        rw [isReal_iff] at this
        simp at this
        exact this
      simp [this] at h
      have : ComplexEmbedding.conjugate ψ₂.embedding = ψ₂.embedding := by
        have := IsReal.comap_of_isUnramified (w := ⟨ψ₂, h₂⟩) (isReal_iff.2 hv) h₂'
        rw [isReal_iff] at this
        simp at this
        exact this
      simp [this] at h
      split_ifs at h <;>
      · simp at h
        rw [← mk_embedding ψ₁, h, mk_embedding]
    · split_ifs at h
      · simp at h
        rw [← mk_embedding ψ₁, h, mk_embedding]
      · simp at h
        rw [← mk_embedding ψ₁, h]
        simp only [mk_conjugate_eq, mk_embedding]
      · simp at h
        rw [← mk_embedding ψ₂, ← h, mk_conjugate_eq, mk_embedding]
      · simp at h
        rw [← mk_embedding ψ₁, h, mk_embedding]

  have hf_surj : f.Surjective := by
    intro ⟨ψ, hψ⟩
    have h' : (mk ψ.1).comap (algebraMap _ _) = v := comap_mk_of_isExtension _ ψ.2
    have : IsUnramified K (mk ψ.1) := by
      apply isUnramified_of_not_isRamifiedExtension ψ.2 hψ
    by_cases hv : ComplexEmbedding.IsReal v.embedding
    · have hψ' : ComplexEmbedding.IsReal ψ.1 := by
        rw [IsRamifiedExtension] at hψ
        simp at hψ
        exact hψ hv
      let w : Σ_v := ⟨mk ψ.1, h'⟩
      use ⟨w, this⟩
      have := embedding_mk_eq_of_isReal hψ'
      simp [f, this]
      have : IsExtension v.embedding ψ.1 := ψ.2
      simp [this]
    cases embedding_mk_eq ψ.1 with
    | inl h =>
      let w : Σ_v := ⟨mk ψ.1, h'⟩
      use ⟨w, this⟩
      simp only [f, h, hψ]
      have : IsExtension v.embedding ψ.1 := ψ.2
      simp [this]
    | inr h =>
      let φ := ComplexEmbedding.conjugate ψ.1
      have h' : (mk φ).comap (algebraMap _ _) = v := by
        rw [← mk_conjugate_eq]
        have := comap_mk_of_isExtension _ ψ.2
        simpa only [φ, star_star]
      have : IsUnramified K (mk φ) := by
        rw [← mk_conjugate_eq]
        simp only [φ, star_star]
        apply isUnramified_of_not_isRamifiedExtension ψ.2 hψ
      let w : Σ_v := ⟨mk φ, h'⟩
      use ⟨w, this⟩
      simp [f]
      have : ¬IsExtension v.embedding (mk φ).embedding := by
        rw [← mk_conjugate_eq]
        simp only [φ, star_star, h]
        rw [ComplexEmbedding.isReal_iff] at hv
        have := ψ.2
        --rw [IsExtension] at this ⊢
        intro h
        have := congrArg ComplexEmbedding.conjugate this
        have h' := congrArg ComplexEmbedding.conjugate h
        simp at h'
        have h'' : ComplexEmbedding.conjugate (ψ.1.comp (algebraMap K L)) =
          (ComplexEmbedding.conjugate ψ).comp (algebraMap K L) := rfl
        rw [h'', h'] at this
        exact hv <| Eq.symm this

      simp [this]
      have : (mk ψ.1).embedding = φ := by rw [h]
      simp_rw [← this]
      simp
      simp_rw [h]
      simp only [star_star]

  exact Equiv.ofBijective _ ⟨hf_inj, hf_surj⟩

theorem IsReal.isTower {v : InfinitePlace K} (hv : v.IsReal) (w : Σ_v) :
    IsTower w := by
  have h := w.2
  rw [← mk_embedding w.1, comap_mk] at h
  have := mk_embedding v
  nth_rw 2 [← h] at this
  rw [mk_eq_iff] at this
  cases this with
  | inl h => rw [IsTower, h]; rfl
  | inr h => rw [conjugate_embedding_eq_of_isReal hv] at h; rw [IsTower, h]; rfl

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

def comap_ringHom {v : InfinitePlace K} (w : Σ_v) :
    v.completion →+* w.1.completion :=
  map_of_comp (L := WithAbs w.1.1) (NumberField.InfinitePlace.abs_eq_of_comap w.2)

instance : UniformContinuousConstSMul K (WithAbs w.1) :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _

instance : IsScalarTower K L (WithAbs w.1) := inferInstanceAs (IsScalarTower K L L)

instance : SMulCommClass K v.completion v.completion := Algebra.to_smulCommClass

instance (w : Σ_v) : Algebra v.completion w.1.completion := RingHom.toAlgebra <|
  comap_ringHom w

instance (w : Σ_v) : IsScalarTower v.completion w.1.completion w.1.completion := IsScalarTower.right

@[simp]
theorem algebraMap_def' {v : InfinitePlace K} (w : Σ_v) : algebraMap v.completion w.1.completion =
    map_of_comp (L := WithAbs w.1.1) (abs_eq_of_comap w.2) :=
  rfl

@[simp]
theorem algebraMap_apply' {v : InfinitePlace K} (w : Σ_v) (x : v.completion) :
    algebraMap v.completion w.1.completion x = UniformSpace.Completion.map
      (algebraMap (WithAbs v.1) (WithAbs w.1.1)) x :=
  rfl

@[simp]
theorem algebraMap_coe' {v : InfinitePlace K} (w : Σ_v) (k : K) :
    algebraMap v.completion w.1.completion k = algebraMap (WithAbs v.1) (WithAbs w.1.1) k := by
  rw [algebraMap_apply']
  exact UniformSpace.Completion.map_coe (WithAbs.uniformContinuous_algebraMap v.1 w.1.1
    (abs_eq_of_comap w.2)) _

@[simp]
theorem smul_def {v : InfinitePlace K} (w : Σ_v) (x : v.completion) (y : w.1.completion) :
    x • y = algebraMap _ _ x * y :=
  rfl

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

theorem algebraMap_comp'  {v : InfinitePlace K} (w : Σ_v) (k : K) : algebraMap K w.1.completion k =
    algebraMap v.completion w.1.completion (algebraMap K v.completion k) := by
  simp only [UniformSpace.Completion.algebraMap_def]
  rw [algebraMap_coe' w _]
  rfl

instance (w : Σ_v) : IsScalarTower K v.completion w.1.completion :=
  IsScalarTower.of_algebraMap_eq (algebraMap_comp' w)

instance (w : Σ_v) : NormedSpace v.completion w.1.completion where
  norm_smul_le x y := by
    rw [smul_def, norm_mul, algebraMap_def']
    have := AbsoluteValue.Completion.isometry_map_of_comp (L := WithAbs w.1.1)
      (abs_eq_of_comap w.2)
    rw [this.norm_map_of_map_zero (map_zero _)]

noncomputable instance (w : Σ_v) : FiniteDimensional v.completion w.1.completion :=
  FiniteDimensional.of_locallyCompactSpace v.completion

def comap {v : InfinitePlace K} (w : Σ_v) :
    v.completion →A[K] w.1.completion where
  __ := comap_ringHom w
  commutes' := by
    intro r
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, comap_ringHom, UniformSpace.Completion.mapRingHom_apply]
    rw [algebraMap_eq_coe, UniformSpace.Completion.map_coe] ; rfl
    exact WithAbs.uniformContinuous_algebraMap v.1 w.1.1
      (abs_eq_of_comap w.2)
  cont := UniformSpace.Completion.continuous_map

variable {v}

theorem ringEquiv_real_of_isReal_comap_coe {v : InfinitePlace K} {w : Σ_v} (hv : v.IsReal)
    (hw : w.1.IsReal) (k : K) :
    ringEquiv_real_of_isReal hw (algebraMap _ _ k) = ringEquiv_real_of_isReal hv k := by
  simp only [ringEquiv_real_of_isReal_apply, extensionEmbedding_of_isReal_coe, algebraMap_comp',
    algebraMap_eq_coe]
  rw [algebraMap_def', map_of_comp]
  rw [UniformSpace.Completion.mapRingHom_coe
    (uniformContinuous_algebraMap _ _ (abs_eq_of_comap w.2))]
  simp only [extensionEmbedding_of_isReal_coe]
  apply Complex.ofReal_injective
  simp only [embedding_of_isReal_apply]
  rw [← hv.isTower w]
  rfl

theorem ringEquiv_real_of_isReal_comap {v : InfinitePlace K} {w : Σ_v} (hv : v.IsReal)
    (hw : w.1.IsReal) (x : v.completion) :
    ringEquiv_real_of_isReal hw (comap_ringHom w x) = ringEquiv_real_of_isReal hv x := by
  apply UniformSpace.Completion.induction_on
    (p := fun x => (ringEquiv_real_of_isReal hw).toRingHom
        ((algebraMap v.completion w.1.completion) x) =
      (ringEquiv_real_of_isReal hv).toRingHom x)
  · apply isClosed_eq
    · apply Continuous.comp
      · simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
        exact UniformSpace.Completion.continuous_extension
      · exact UniformSpace.Completion.continuous_map
    · exact UniformSpace.Completion.continuous_extension
  · intro a
    have : algebraMap v.completion (w.1.completion) (a) =
        algebraMap v.completion (w.1.completion) ((algebraMap K v.completion) a) :=
      rfl
    rw [this]
    rw [← algebraMap_comp']
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [ringEquiv_real_of_isReal_comap_coe hv hw]

def of_isUnramified_isReal (w : Σ_v) (hw : w.1.IsUnramified K)
    (hv : v.IsReal) :
    letI : Algebra v.completion ℝ := (ringEquiv_real_of_isReal hv).toRingHom.toAlgebra
    w.1.completion ≃ₐ[v.completion] ℝ := by
  have hr : w.1.IsReal := hv.comap_of_isUnramified hw
  letI : Algebra v.completion ℝ := (ringEquiv_real_of_isReal hv).toRingHom.toAlgebra
  letI : Algebra w.1.completion ℝ := (ringEquiv_real_of_isReal hr).toRingHom.toAlgebra
  letI : IsScalarTower v.completion w.1.completion ℝ := by
    apply IsScalarTower.mk
    intro x y r
    simp only [Algebra.smul_def]
    simp only [RingHom.algebraMap_toAlgebra, map_mul, mul_assoc, RingEquiv.toRingHom_eq_coe]
    simp only [RingHom.coe_coe]
    rw [ringEquiv_real_of_isReal_comap hv hr]
  exact algEquiv_real_of_isReal hr |>.restrictScalars v.completion

theorem ringEquiv_real_of_isComplex_comap_coe {v : InfinitePlace K} {w : Σ_v} (hv : v.IsReal)
    (hw : w.1.IsComplex) (k : K) :
    ringEquiv_complex_of_isComplex hw (algebraMap _ _ k) =
      Complex.ofReal (ringEquiv_real_of_isReal hv k) := by
  rw [ringEquiv_complex_of_isComplex_apply, ringEquiv_real_of_isReal_apply,
    extensionEmbedding_of_isReal_coe, algebraMap_comp',
    algebraMap_eq_coe]
  rw [algebraMap_def', map_of_comp]
  rw [UniformSpace.Completion.mapRingHom_coe
    (uniformContinuous_algebraMap _ _ (abs_eq_of_comap w.2))]
  simp only [extensionEmbedding_coe]
  simp only [Complex.ofReal_eq_coe, embedding_of_isReal_apply]
  rw [← hv.isTower w]
  rfl

theorem ringEquiv_complex_of_isReal_comap {v : InfinitePlace K} {w : Σ_v} (hv : v.IsReal)
    (hw : w.1.IsComplex) (x : v.completion) :
    ringEquiv_complex_of_isComplex hw (comap_ringHom w x) =
      Complex.ofReal (ringEquiv_real_of_isReal hv x) := by
  apply UniformSpace.Completion.induction_on
    (p := fun x => (ringEquiv_complex_of_isComplex hw).toRingHom
        ((algebraMap v.completion w.1.completion) x) = _)
  · apply isClosed_eq
    · apply Continuous.comp
      · simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
        exact UniformSpace.Completion.continuous_extension
      · exact UniformSpace.Completion.continuous_map
    · apply Continuous.comp
      · exact Complex.continuous_ofReal
      · exact UniformSpace.Completion.continuous_extension
  · intro a
    have : algebraMap v.completion (w.1.completion) (a) =
        algebraMap v.completion (w.1.completion) ((algebraMap K v.completion) a) :=
      rfl
    rw [this]
    rw [← algebraMap_comp']
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [ringEquiv_real_of_isComplex_comap_coe hv hw]

def of_not_isUnramified_isReal (w : Σ_v) (hw : ¬w.1.IsUnramified K)
    (hv : v.IsReal) :
    letI : Algebra v.completion ℂ := RingHom.toAlgebra <|
      (algebraMap ℝ ℂ).comp (ringEquiv_real_of_isReal hv)
    w.1.completion ≃ₐ[v.completion] ℂ := by
  have hw : w.1.IsComplex := comap_of_not_isUnramified hw
  letI : Algebra w.1.completion ℂ := (ringEquiv_complex_of_isComplex hw).toRingHom.toAlgebra
  letI : Algebra v.completion ℂ := RingHom.toAlgebra <|
      (algebraMap ℝ ℂ).comp (ringEquiv_real_of_isReal hv)
  letI : IsScalarTower v.completion w.1.completion ℂ := by
    apply IsScalarTower.mk
    intro x y r
    simp only [Algebra.smul_def]
    simp only [RingHom.algebraMap_toAlgebra, map_mul, mul_assoc, RingEquiv.toRingHom_eq_coe]
    simp only [RingHom.coe_coe]
    rw [ringEquiv_complex_of_isReal_comap hv hw]
    rfl
  exact algEquiv_complex_of_isComplex hw |>.restrictScalars v.completion

theorem IsTower.ringEquiv_complex_coe {v : InfinitePlace K} {w : Σ_v} (hv : v.IsComplex)
    (hw : w.1.IsComplex) (h : IsTower w) (k : K) :
    (ringEquiv_complex_of_isComplex hw (algebraMap _ _ k) =
      ringEquiv_complex_of_isComplex hv k) := by
  simp only [ringEquiv_complex_of_isComplex_apply, extensionEmbedding_coe, algebraMap_comp',
    algebraMap_eq_coe]
  rw [algebraMap_def', map_of_comp]
  simp [UniformSpace.Completion.mapRingHom_coe
    (uniformContinuous_algebraMap _ _ (abs_eq_of_comap w.2))]
  rw [IsTower] at h
  rw [← h]
  rfl

theorem IsTower.ringEquiv_complex {v : InfinitePlace K} {w : Σ_v}
    (hv : v.IsComplex) (hw : w.1.IsComplex) (h : IsTower w) (x : v.completion) :
    ringEquiv_complex_of_isComplex hw (comap_ringHom w x) =
      ringEquiv_complex_of_isComplex hv x := by
  apply UniformSpace.Completion.induction_on
    (p := fun x => (ringEquiv_complex_of_isComplex hw).toRingHom
        ((algebraMap v.completion w.1.completion) x) =
      (ringEquiv_complex_of_isComplex hv).toRingHom x)
  · apply isClosed_eq
    · apply Continuous.comp
      · simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
        exact UniformSpace.Completion.continuous_extension
      · exact UniformSpace.Completion.continuous_map
    · exact UniformSpace.Completion.continuous_extension
  intro a
  have : algebraMap v.completion (w.1.completion) a =
      algebraMap v.completion (w.1.completion) ((algebraMap K v.completion) a) :=
    rfl
  rw [this]
  rw [← algebraMap_comp']
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← IsTower.ringEquiv_complex_coe hv hw h]

theorem IsConjugateTower.ringEquiv_complex_coe
    {v : InfinitePlace K} {w : Σ_v} (hv : v.IsComplex)
    (hw : w.1.IsComplex) (h : IsConjugateTower w) (k : K) :
    ringEquiv_complex_of_isComplex hw (algebraMap _ _ k) =
      starRingEnd ℂ (ringEquiv_complex_of_isComplex hv k) := by
  simp only [ringEquiv_complex_of_isComplex_apply, extensionEmbedding_coe, algebraMap_comp',
    algebraMap_eq_coe]
  rw [algebraMap_def', map_of_comp]
  simp [UniformSpace.Completion.mapRingHom_coe
    (uniformContinuous_algebraMap _ _ (abs_eq_of_comap w.2))]
  rw [IsConjugateTower] at h
  have := congrFun h k
  rw [ComplexEmbedding.conjugate_coe_eq] at this
  rw [← this]
  rfl

theorem IsConjugateTower.ringEquiv_complex {v : InfinitePlace K} {w : Σ_v}
    (hv : v.IsComplex) (hw : w.1.IsComplex) (h : IsConjugateTower w) (x : v.completion) :
    ringEquiv_complex_of_isComplex hw (comap_ringHom w x) =
        starRingEnd ℂ (ringEquiv_complex_of_isComplex hv x) := by
  apply UniformSpace.Completion.induction_on
    (p := fun x => (ringEquiv_complex_of_isComplex hw).toRingHom
        ((algebraMap v.completion w.1.completion) x) = _)
  · apply isClosed_eq
    · apply Continuous.comp
      · exact UniformSpace.Completion.continuous_extension
      · exact UniformSpace.Completion.continuous_map
    · apply Continuous.comp
      · continuity
      · exact UniformSpace.Completion.continuous_extension
  intro a
  have : algebraMap v.completion (w.1.completion) a =
      algebraMap v.completion (w.1.completion) ((algebraMap K v.completion) a) :=
    rfl
  rw [this]
  rw [← algebraMap_comp']
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← IsConjugateTower.ringEquiv_complex_coe hv hw h]

def IsTower.of_isComplex {w : Σ_v} (hv : v.IsComplex) (h : IsTower w) :
    letI : Algebra v.completion ℂ := RingHom.toAlgebra <| ringEquiv_complex_of_isComplex hv
    w.1.completion ≃ₐ[v.completion] ℂ := by
  have hw := hv.comap_isComplex w
  letI : Algebra v.completion ℂ := (ringEquiv_complex_of_isComplex hv).toRingHom.toAlgebra
  letI : Algebra w.1.completion ℂ := (ringEquiv_complex_of_isComplex hw).toRingHom.toAlgebra
  letI : IsScalarTower v.completion w.1.completion ℂ := by
    apply IsScalarTower.mk
    intro x y r
    simp only [Algebra.smul_def]
    simp only [RingHom.algebraMap_toAlgebra, map_mul, mul_assoc, RingEquiv.toRingHom_eq_coe]
    simp only [RingHom.coe_coe]
    rw [IsTower.ringEquiv_complex hv hw h]
  exact algEquiv_complex_of_isComplex hw |>.restrictScalars v.completion

@[simp]
theorem IsTower.of_isComplex_apply {w : Σ_v} (hv : v.IsComplex) (h : IsTower w)
    (x : v.completion) :
    IsTower.of_isComplex hv h (comap_ringHom w x) = extensionEmbedding v x := by
  simp only [RingEquiv.toRingHom_eq_coe, of_isComplex]
  simp only [AlgEquiv.coe_restrictScalars']
  simp only [algEquiv_complex_of_isComplex_apply]
  apply UniformSpace.Completion.induction_on
    (p := fun x => (extensionEmbedding w.1 (comap_ringHom w x)) = _)
  · apply isClosed_eq
    · apply Continuous.comp
      · exact (UniformSpace.Completion.continuous_extension)
      · exact UniformSpace.Completion.continuous_map
    · exact UniformSpace.Completion.continuous_extension
  intro a
  simp only [extensionEmbedding_coe]
  rw [IsTower] at h
  rw [comap_ringHom, UniformSpace.Completion.mapRingHom_coe
    (uniformContinuous_algebraMap _ _ (abs_eq_of_comap w.2))]
  rw [extensionEmbedding_coe]
  rw [← h]
  rfl

def IsConjugateTower.of_isComplex {w : Σ_v} (hv : v.IsComplex) (h : IsConjugateTower w) :
    letI : Algebra v.completion ℂ := RingHom.toAlgebra <|
      (starRingEnd ℂ).comp (ringEquiv_complex_of_isComplex hv).toRingHom
    w.1.completion ≃ₐ[v.completion] ℂ := by
  have hw := hv.comap_isComplex w
  letI : Algebra v.completion ℂ :=
    ((starRingEnd ℂ).comp (ringEquiv_complex_of_isComplex hv).toRingHom).toAlgebra
  letI : Algebra w.1.completion ℂ := (ringEquiv_complex_of_isComplex hw).toRingHom.toAlgebra
  letI : IsScalarTower v.completion w.1.completion ℂ := by
    apply IsScalarTower.mk
    intro x y r
    simp only [Algebra.smul_def]
    simp only [RingHom.algebraMap_toAlgebra, map_mul, mul_assoc, RingEquiv.toRingHom_eq_coe]
    simp only [RingHom.coe_coe]
    rw [IsConjugateTower.ringEquiv_complex hv hw h]
    rfl
  exact algEquiv_complex_of_isComplex hw |>.restrictScalars v.completion

@[simp]
theorem IsConjugateTower.of_isComplex_apply {w : Σ_v} (hv : v.IsComplex) (h : IsConjugateTower w)
    (x : v.completion) :
    IsConjugateTower.of_isComplex hv h (comap_ringHom w x) =
      starRingEnd ℂ (extensionEmbedding v x) := by
  simp only [RingEquiv.toRingHom_eq_coe, of_isComplex]
  simp only [AlgEquiv.coe_restrictScalars']
  simp only [algEquiv_complex_of_isComplex_apply]
  rw [IsConjugateTower] at h
  apply UniformSpace.Completion.induction_on
    (p := fun x => (extensionEmbedding w.1 (comap_ringHom w x)) = _)
  · apply isClosed_eq
    · apply Continuous.comp
      · exact (UniformSpace.Completion.continuous_extension)
      · exact UniformSpace.Completion.continuous_map
    · apply Continuous.comp
      · continuity
      · exact UniformSpace.Completion.continuous_extension
  intro a
  simp only [extensionEmbedding_coe]
  rw [comap_ringHom, UniformSpace.Completion.mapRingHom_coe
    (uniformContinuous_algebraMap _ _ (abs_eq_of_comap w.2))]
  rw [extensionEmbedding_coe]
  have := congrFun h a
  simp only [Function.comp_apply, ComplexEmbedding.conjugate_coe_eq] at this
  rw [← this]
  rfl

variable (L)
variable (K v)
variable [NumberField K]

def ramificationIdx (w : Σ_v) := if IsUnramified K w.1 then 1 else 2

def equiv_comap :
    InfinitePlace L ≃ ((v : InfinitePlace K) × Σ_v) :=
  (Equiv.sigmaFiberEquiv _).symm

theorem comap_card : Fintype.card ({w : Σ_v // w.1.IsUnramified K}) +
    2 * Fintype.card ({w : Σ_v // ¬w.1.IsUnramified K}) = FiniteDimensional.finrank K L := by
  letI : Algebra K ℂ := v.embedding.toAlgebra
  rw [← AlgHom.card K L ℂ]
  -- The idea is this: InfinitePlace.comap is a surjective function from InfinitePlace L
  -- to InfinitePlace K. That is every embedding L →+* ℂ defines an embedding K →+* ℂ.
  -- This is not injective. It is one-to-[L : k] if w is Unramified, otherwise it is
  -- one-to-2*[L : K].
  -- The key here is that ℂ has v.embedding as it's K-algebra. So L →ₐ[K] ℂ is precisely
  -- all algHom σ such that σ(k) = v.embedding k. i.e., w.comap (algebraMap K L) = v
  -- But there are two more in L →ₐ[K] ℂ when ¬w.1.IsUnramified as there are in
  -- InfinitePlace L because of complex conjugate.
  have (φ : L →ₐ[K] ℂ) : φ.toRingHom.comp (algebraMap K L) = v.embedding := by
    have := Function.funext_iff.2 φ.commutes'
    rw [RingHom.algebraMap_toAlgebra] at this
    simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.commutes,
      DFunLike.coe_fn_eq] at this
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower]

  let g : (L →ₐ[K] ℂ) → Extends L v.embedding :=
    fun φ => ⟨φ.toRingHom, this φ⟩

  have hg_inj : g.Injective := by
    intro φ₁ φ₂ h
    simp [g] at h
    exact AlgHom.coe_ringHom_injective h

  have {σ : L →+* ℂ} (h : σ.comp (algebraMap K L) = v.embedding) :
      ∀ (r : K), σ.toFun (algebraMap K L r) = algebraMap K ℂ r := by
    intro k
    rw [RingHom.algebraMap_toAlgebra, ← h]
    rfl

  have hg_surj : g.Surjective := by
    intro ⟨σ, h⟩
    use {
      __ := σ
      commutes' := this h
    }

  have : (L →ₐ[K] ℂ) ≃ Extends L v.embedding :=
    Equiv.ofBijective _ ⟨hg_inj, hg_surj⟩

  rw [Fintype.card_eq.2 ⟨this⟩]

  have : Extends L v.embedding ≃
    { ψ : Extends L v.embedding // IsRamifiedExtension v.embedding ψ } ⊕
      { ψ : Extends L v.embedding // ¬IsRamifiedExtension v.embedding ψ } :=
        (Equiv.sumCompl _).symm

  rw [Fintype.card_eq.2 ⟨this⟩]
  rw [Fintype.card_sum]
  rw [Fintype.card_eq.2 ⟨sum_not_isUnramified_equiv_IsRamifiedExtension.symm⟩]
  rw [Fintype.card_sum]
  rw [Fintype.card_eq.2 ⟨isUnramified_equiv_not_isRamifiedExtension.symm⟩]
  ring

def e : (Σ_v) ≃ {w : Σ_v // w.1.IsUnramified K} ⊕ {w : Σ_v // ¬w.1.IsUnramified K} :=
  (Equiv.sumCompl _).symm

theorem sum_mult_eq' :
    ∑ (w : Σ_v), ramificationIdx K v L w = FiniteDimensional.finrank K L := by
  rw [Fintype.sum_equiv (e K v L) _ ((fun (w : Σ_v) => ramificationIdx K v L w) ∘ (e K v L).symm)
    (fun _ => by simp only [Function.comp_apply, Equiv.symm_apply_apply])]
  simp only [Function.comp_apply, Fintype.sum_sum_type, e, Equiv.symm_symm,
    Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
  have (x : { w : Σ_v // IsUnramified K w.1 }) : ramificationIdx K v L x.1 = 1 := by
    rw [ramificationIdx]; simp [x.2]
  simp_rw [this]
  have (x : { w : Σ_v // ¬IsUnramified K w.1 }) : ramificationIdx K v L x.1 = 2 := by
    rw [ramificationIdx]; simp [x.2]
  simp_rw [this]
  rw [Finset.sum_const, Finset.sum_const, ← Fintype.card, ← Fintype.card, smul_eq_mul, mul_one,
    smul_eq_mul, mul_comm, comap_card]

theorem comap_prod_finrank : FiniteDimensional.finrank v.completion ((w : Σ_v) → w.1.completion) =
    FiniteDimensional.finrank K L := by
  rw [FiniteDimensional.finrank_pi_fintype v.completion (ι := Σ_v)]
  by_cases hv : v.IsReal
  · have h₀ (w : Σ_v) (hw : IsUnramified K w.1) :
        FiniteDimensional.finrank v.completion w.1.completion = 1 := by
      letI : Algebra v.completion ℝ := (ringEquiv_real_of_isReal hv).toRingHom.toAlgebra
      have := (of_isUnramified_isReal w hw hv).toLinearEquiv.finrank_eq
      rw [this]
      rw [← algEquiv_real_of_isReal hv |>.toLinearEquiv.finrank_eq]
      exact FiniteDimensional.finrank_self _
    have h₁ (w : Σ_v) (hw : ¬IsUnramified K w.1) :
        FiniteDimensional.finrank v.completion w.1.completion = 2 := by
      letI : Algebra v.completion ℝ := (ringEquiv_real_of_isReal hv).toRingHom.toAlgebra
      have := (of_not_isUnramified_isReal w hw hv).toLinearEquiv.finrank_eq
      rw [this]
      have := algEquiv_real_of_isReal hv |>.toLinearEquiv.finrank_eq
      rw [← FiniteDimensional.finrank_mul_finrank v.completion ℝ ℂ, ← this,
        FiniteDimensional.finrank_self _]
      norm_num
    convert sum_mult_eq' K v L
    have h₃ (w : Σ_v) (hw : IsUnramified K w.1) := IsReal.comap_of_isUnramified hv hw
    have h₄ (w : Σ_v) (hw : ¬IsUnramified K w.1) := comap_of_not_isUnramified hw
    rename_i w _
    by_cases hw : IsUnramified K w.1
    · simp [ramificationIdx, hw, h₃ w hw, h₀ w hw]
    · simp [ramificationIdx, InfinitePlace.not_isComplex_iff_isReal.2 hv, hw, h₄ w hw, h₁ w hw]
  · simp at hv
    have h (w : Σ_v) : FiniteDimensional.finrank v.completion w.1.completion = 1 := by
      by_cases hw : IsTower w
      · letI : Algebra v.completion ℂ := (ringEquiv_complex_of_isComplex hv).toRingHom.toAlgebra
        have := IsTower.of_isComplex hv hw |>.toLinearEquiv.finrank_eq
        rw [this]
        rw [← algEquiv_complex_of_isComplex hv |>.toLinearEquiv.finrank_eq]
        exact FiniteDimensional.finrank_self _
      · have := letI : Algebra v.completion ℂ :=
            ((starRingEnd ℂ).comp (ringEquiv_complex_of_isComplex hv).toRingHom).toAlgebra
          IsConjugateTower.of_isComplex hv (isConjugateTower_of_not_isTower hw)
          |>.toLinearEquiv.finrank_eq
        rw [this]
        have := letI : Algebra v.completion ℂ :=
          RingHom.toAlgebra <| ((starRingAut (R := ℂ)).toRingHom.comp
            (ringEquiv_complex_of_isComplex hv).toRingHom)
          starAlgEquiv_complex_of_isComplex hv |>.toLinearEquiv.finrank_eq
        rw [FiniteDimensional.finrank_self] at this
        rw [this]
    convert sum_mult_eq' K v L
    rw [h]
    rename_i w _
    have := IsComplex.comap_isComplex w hv
    simp [ramificationIdx, InfinitePlace.isUnramified_iff.2 (Or.inr <| w.2 ▸ hv), this]

end NumberField.InfinitePlace.Completion
