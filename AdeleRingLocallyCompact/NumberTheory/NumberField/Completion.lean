/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib
import AdeleRingLocallyCompact.Analysis.NormedSpace.Completion
import AdeleRingLocallyCompact.Topology.UniformSpace.Basic

noncomputable section

def WithAbs {R S} [Semiring R] [OrderedSemiring S] : AbsoluteValue R S → Type _ := fun _ ↦ R

namespace WithAbs

instance {R} [Ring R] (v : AbsoluteValue R ℝ) : NormedRing (WithAbs v) where
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

instance {R} [Ring R] [Nontrivial R] (v : AbsoluteValue R ℝ) : NormOneClass (WithAbs v) where
  norm_one := v.map_one

variable {K} [Field K] (v : AbsoluteValue K ℝ)

instance instNormedFieldWithAbs : NormedField (WithAbs v) where
  toField := inferInstanceAs (Field K)
  __ := inferInstanceAs (NormedRing (WithAbs v))
  norm_mul' := v.map_mul

variable {A : Type*} [NormedField A] {f : WithAbs v →+* A} {v}

theorem dist_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) :
    dist x y = dist (f x) (f y) := by
  rw [(instNormedFieldWithAbs v).dist_eq, (inferInstanceAs <| NormedField A).dist_eq,
    ← f.map_sub, h]; rfl

instance : Inhabited (WithAbs v) := ⟨0⟩

theorem pseudoMetricSpace_induced_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) :
    letI := inferInstanceAs (PseudoMetricSpace (WithAbs v));
    (instNormedFieldWithAbs v).toPseudoMetricSpace = PseudoMetricSpace.induced f inferInstance := by
  ext; exact dist_of_comp h

theorem uniformSpace_eq_comap_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) :
    (instNormedFieldWithAbs v).toUniformSpace = UniformSpace.comap f inferInstance := by
  rw [pseudoMetricSpace_induced_of_comp h]; rfl

theorem uniformInducing_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) :
    UniformInducing f :=
  uniformInducing_iff_uniformSpace.2 (Eq.symm (uniformSpace_eq_comap_of_comp h))

theorem uniformEmbedding
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) :
    UniformEmbedding f :=
  (uniformInducing_of_comp h).uniformEmbedding

theorem isometry_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) :
    Isometry f :=
  Isometry.of_dist_eq <| fun x y => by rw [pseudoMetricSpace_induced_of_comp h]; rfl

end WithAbs

namespace AbsoluteValue

open WithAbs

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

def completion := UniformSpace.Completion (WithAbs v)

namespace Completion

instance : NormedRing v.completion :=
  UniformSpace.Completion.instNormedRingCompletionToUniformSpaceToPseudoMetricSpace _

instance [CompletableTopField (WithAbs v)] : NormedField v.completion :=
  UniformSpace.Completion.instNormedField (WithAbs v)

instance : CompleteSpace v.completion :=
  UniformSpace.Completion.completeSpace (WithAbs v)

instance : Inhabited v.completion :=
  UniformSpace.Completion.inhabited _

instance : Coe K v.completion :=
  inferInstanceAs (Coe (WithAbs v) (UniformSpace.Completion (WithAbs v)))

instance : Algebra (WithAbs v) v.completion :=
  UniformSpace.Completion.algebra (WithAbs v) _

variable {A : Type*} [NormedField A] [CompleteSpace A] {f : WithAbs v →+* A} {v}

/-- If the absolute value of a normed field factors through an embedding into another normed field
`A`, then this extends that embedding to `v.completion →+* A`. -/
def extensionEmbedding_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) :
    v.completion →+* A :=
  UniformSpace.Completion.extensionHom _
    (WithAbs.uniformInducing_of_comp h).uniformContinuous.continuous

/-- If the absolute value of a normed field factors through a normed embedding, then the extended
embedding `v.completion →+* A` preserves distances. -/
theorem extensionEmbedding_dist_eq_of_comp
      (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective)
      (x y : v.completion) :
    dist (extensionEmbedding_of_comp h x) (extensionEmbedding_of_comp h y) =
      dist x y := by
  refine (UniformSpace.Completion.induction_on₂ x y ?_ (fun x y => ?_))
  · refine isClosed_eq ?_ continuous_dist
    · exact (continuous_iff_continuous_dist.1 (UniformSpace.Completion.continuous_extension))
  · rw [extensionEmbedding_of_comp, UniformSpace.Completion.extensionHom, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, UniformSpace.Completion.dist_eq]
    simp only [UniformSpace.Completion.extension_coe
      (WithAbs.uniformInducing_of_comp h).uniformContinuous]
    exact Isometry.dist_eq (WithAbs.isometry_of_comp h) _ _

/-- If the absolute value of a normed field factors through a normed embedding, then the
extended embedding `v.completion →+* A` is an isometry. -/
theorem isometry_extensionEmbedding_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) :
    Isometry (extensionEmbedding_of_comp h) :=
  Isometry.of_dist_eq <| extensionEmbedding_dist_eq_of_comp h

/-- If the absolute value of a normed field factors through a normed embedding, then the
extended embedding `v.completion →+* A` is a closed embedding. -/
theorem closedEmbedding_extensionEmbedding_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) :
    ClosedEmbedding (extensionEmbedding_of_comp h) :=
  (isometry_extensionEmbedding_of_comp h).closedEmbedding

/-- The completion of any normed field with an absolute value, such that the absolute value
factors through an embedding into a normed locally compact field, is also locally compact. -/
theorem locallyCompactSpace [LocallyCompactSpace A]
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective)  :
    LocallyCompactSpace (v.completion) :=
  (closedEmbedding_extensionEmbedding_of_comp h).locallyCompactSpace

end AbsoluteValue.Completion

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K] (v : InfinitePlace K)

/- The normed field structure of a number field coming from the absolute value associated to
an infinite place. -/
def normedField : NormedField K :=
  inferInstanceAs (NormedField (WithAbs v.1))

theorem abs_eq_comp :
    v.1 = (IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ)).comp v.embedding.injective := by
  rw [← v.2.choose_spec]; rfl

theorem abs_of_isReal_eq_comp (hv : IsReal v) :
    v.1 = (IsAbsoluteValue.toAbsoluteValue (norm : ℝ → ℝ)).comp (v.embedding_of_isReal hv).injective := by
  ext x
  have := v.2.choose_spec
  unfold place at this
  rw [← v.2.choose_spec]
  unfold place
  sorry

/-- The completion of a number field at an infinite place. -/
def completion := v.1.completion

namespace Completion

instance : NormedField v.completion :=
  letI := (WithAbs.uniformInducing_of_comp v.abs_eq_comp).completableTopField
  UniformSpace.Completion.instNormedField (WithAbs v.1)

instance : CompleteSpace v.completion :=
  inferInstanceAs (CompleteSpace v.1.completion)

instance : Inhabited v.completion :=
  inferInstanceAs (Inhabited v.1.completion)

instance : Coe K v.completion :=
  inferInstanceAs (Coe (WithAbs v.1) v.1.completion)

instance algebra : Algebra K v.completion :=
  inferInstanceAs (Algebra (WithAbs v.1) v.1.completion)

/-- The embedding associated to an infinite place extended to an embedding `v.completion →+* ℂ`. -/
def extensionEmbedding :=
  AbsoluteValue.Completion.extensionEmbedding_of_comp v.abs_eq_comp

def extensionEmbedding_of_isReal (hv : IsReal v) :=
  AbsoluteValue.Completion.extensionEmbedding_of_comp <| v.abs_of_isReal_eq_comp hv

/-- The embedding `v.completion →+* ℂ` is an isometry. -/
theorem isometry_extensionEmbedding : Isometry (extensionEmbedding v) :=
  Isometry.of_dist_eq (AbsoluteValue.Completion.extensionEmbedding_dist_eq_of_comp v.abs_eq_comp)

theorem injective_extensionEmbedding : Function.Injective (extensionEmbedding v) := by
  letI : DivisionRing v.1.completion := (instNormedFieldCompletion v).toDivisionRing
  exact (extensionEmbedding v).injective

theorem injective_extensionEmbedding_of_isReal (hv : IsReal v) : Function.Injective (extensionEmbedding_of_isReal v hv) := by
  letI : DivisionRing v.1.completion := (instNormedFieldCompletion v).toDivisionRing
  exact (extensionEmbedding_of_isReal v hv).injective

/-- The completion of a number field at an infinite place is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (v.completion) :=
  AbsoluteValue.Completion.locallyCompactSpace v.abs_eq_comp

theorem isClosed_image_extensionEmbedding : IsClosed (Set.range (extensionEmbedding v)) := by
  have h := AbsoluteValue.Completion.closedEmbedding_extensionEmbedding_of_comp v.abs_eq_comp
  exact ((closedEmbedding_iff _).1 h).2

theorem isClosed_image_extensionEmbedding_of_isReal (hv : IsReal v) : IsClosed (Set.range (extensionEmbedding_of_isReal v hv)) := by
  have h := AbsoluteValue.Completion.closedEmbedding_extensionEmbedding_of_comp (v.abs_of_isReal_eq_comp hv)
  exact ((closedEmbedding_iff _).1 h).2

private def subfield_of_isReal (hv : IsReal v) : Subfield ℝ where
  toSubring := (extensionEmbedding_of_isReal v hv).range
  inv_mem' := by
    letI : NormedField (AbsoluteValue.completion v.1) := instNormedFieldCompletion v
    exact fun _ ⟨x, hx⟩ => ⟨x⁻¹, by simp only [map_inv₀, hx]⟩

private def subfield : Subfield ℂ where
  toSubring := (extensionEmbedding v).range
  inv_mem' := by
    letI : NormedField (AbsoluteValue.completion v.1) := instNormedFieldCompletion v
    exact fun _ ⟨x, hx⟩ => ⟨x⁻¹, by simp only [map_inv₀, hx]⟩

private theorem isClosed_image_extensionEmbedding_subfield : IsClosed (subfield v : Set ℂ) :=
  isClosed_image_extensionEmbedding v

private theorem isClosed_image_extensionEmbedding_of_isReal_subfield (hv : IsReal v) : IsClosed (subfield_of_isReal v hv : Set ℝ) :=
  isClosed_image_extensionEmbedding_of_isReal v hv

open Complex

private theorem subfield_ne_real_of_isComplex (hv : IsComplex v) : subfield v ≠ ofReal.fieldRange := by
  sorry

open Set

theorem Real.subfield_eq_of_closed {K : Subfield ℝ} (hc : IsClosed (K : Set ℝ)) : K = ⊤ := by
  suffices Set.univ ⊆ (K : Set ℝ) by
    rw [eq_top_iff]
    exact fun _ _ => this (mem_univ _)
  suffices Set.univ ⊆ closure (Set.range ((↑) : ℚ → ℝ)) by
    refine subset_trans this ?_
    rw [← IsClosed.closure_eq hc]
    apply closure_mono
    rintro _ ⟨_, rfl⟩
    simp only [Function.comp_apply, ofReal_rat_cast, SetLike.mem_coe, SubfieldClass.coe_rat_mem]
  rw [DenseRange.closure_range Rat.denseEmbedding_coe_real.dense]

theorem equivReal_of_isReal (hv : IsReal v) : v.completion ≃+* ℝ := by
  have h := Real.subfield_eq_of_closed <| isClosed_image_extensionEmbedding_of_isReal_subfield v hv
  have h' := @Subfield.topEquiv ℝ _
  apply RingEquiv.trans _ h'
  rw [← h]
  have h' := @RingHom.quotientKerEquivRange v.completion _ _ _ (extensionEmbedding_of_isReal v hv)
  have h_inj := injective_extensionEmbedding_of_isReal v hv
  rw [RingHom.injective_iff_ker_eq_bot] at h_inj
  rw [h_inj] at h'
  have h'' := RingEquiv.trans (RingEquiv.quotientBot _).symm h'
  apply RingEquiv.trans h''
  rfl

theorem equivComplex_of_isComplex (hv : IsComplex v) : v.completion ≃+* ℂ := by
  have h := (Complex.subfield_eq_of_closed <| isClosed_image_extensionEmbedding_subfield v).resolve_left <| subfield_ne_real_of_isComplex v hv
  have h' := @Subfield.topEquiv ℂ _
  apply RingEquiv.trans _ h'
  rw [← h]
  have h' := @RingHom.quotientKerEquivRange v.completion _ _ _ (extensionEmbedding v)
  have h_inj := injective_extensionEmbedding v
  rw [RingHom.injective_iff_ker_eq_bot] at h_inj
  rw [h_inj] at h'
  have h'' := RingEquiv.trans (RingEquiv.quotientBot _).symm h'
  apply RingEquiv.trans h''
  rfl

end NumberField.InfinitePlace.Completion
