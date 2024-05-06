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

section DerivedInstances

instance : NormedDivisionRing (subfield K v) :=
  NormedDivisionRing.induced _ _ (Subfield.subtype (subfield K v)) Subtype.val_injective

instance : NormedDivisionRing K :=
  NormedDivisionRing.induced _ _ (toSubfield K v) (toSubfield_injective K v)

instance : NormedRing K := (instNormedDivisionRing K v).toNormedRing

instance : NonUnitalNormedRing K := (instNormedRing K v).toNonUnitalNormedRing

instance : NormedAddCommGroup K := (instNonUnitalNormedRing K v).toNormedAddCommGroup

instance : SeminormedAddCommGroup K := (instNormedAddCommGroup K v).toSeminormedAddCommGroup

instance : PseudoMetricSpace K := (instNormedDivisionRing K v).toPseudoMetricSpace

instance topologicalSpace : TopologicalSpace K := (instPseudoMetricSpace K v).toUniformSpace.toTopologicalSpace

instance topologicalDivisionRing : @TopologicalDivisionRing K _ (topologicalSpace K v) :=
  (instNormedDivisionRing K v).to_topologicalDivisionRing

instance topologicalRing : @TopologicalRing K (topologicalSpace K v) _ :=
  @TopologicalDivisionRing.toTopologicalRing _ _ (topologicalSpace K v) _

instance topologicalAddGroup : @TopologicalAddGroup K (topologicalSpace K v) _ :=
  @TopologicalRing.to_topologicalAddGroup _ _ (topologicalSpace K v) _

instance uniformSpace : UniformSpace K := (instPseudoMetricSpace K v).toUniformSpace

instance uniformAddGroup : @UniformAddGroup K (uniformSpace K v) _ :=
  (instSeminormedAddCommGroup K v).to_uniformAddGroup

-- TODO: Why do I have to re-establish these instances for ℂ and ℝ? Getting timeouts otherwise
instance : MetricSpace ℂ := inferInstance

instance : T0Space ℂ := instMetricSpaceComplex.instT0Space

instance : NormedDivisionRing ℂ := Complex.instNormedFieldComplex.toNormedDivisionRing

instance : TopologicalDivisionRing ℂ := instNormedDivisionRingComplex.to_topologicalDivisionRing

instance : TopologicalRing ℂ := instTopologicalDivisionRingComplexToDivisionRingInstNormedDivisionRingComplexToTopologicalSpaceToUniformSpaceToPseudoMetricSpaceToSeminormedRingToSeminormedCommRingToNormedCommRingInstNormedFieldComplex.toTopologicalRing

instance : NormedRing ℂ := instNormedDivisionRingComplex.toNormedRing

instance : NonUnitalNormedRing ℂ := instNormedRingComplex.toNonUnitalNormedRing

instance : NormedAddCommGroup ℂ  := instNonUnitalNormedRingComplex.toNormedAddCommGroup

instance : SeminormedAddCommGroup ℂ := instNormedAddCommGroupComplex.toSeminormedAddCommGroup

instance : UniformAddGroup ℂ := instSeminormedAddCommGroupComplex.to_uniformAddGroup

instance : CompletableTopField ℂ := completableTopField_of_complete ℂ

instance : TopologicalSpace ℝ := Real.pseudoMetricSpace.toUniformSpace.toTopologicalSpace

instance : UniformSpace ℝ := Real.pseudoMetricSpace.toUniformSpace

instance : TopologicalSpace.MetrizableSpace ℝ := Real.metricSpace.toMetrizableSpace

instance : T2Space ℝ := TopologicalSpace.t2Space_of_metrizableSpace

end DerivedInstances

theorem embedding' : @Embedding _ _ (v.topologicalSpace K) _ (v.toSubfield K) := by
  rw [@embedding_iff]
  refine ⟨?_, v.toSubfield_injective⟩
  rw [@inducing_iff]
  rfl

theorem toSubfield_isometry : @Isometry _ _ (instPseudoMetricSpace K v).toPseudoEMetricSpace _ (toSubfield K v) :=
  @Embedding.to_isometry _ _ (v.topologicalSpace K) _ _ v.embedding'

theorem uniformInducing : @UniformInducing _ _ (v.uniformSpace K) _ (toSubfield K v).toFun :=
  @Isometry.uniformInducing _ _ (instPseudoMetricSpace K v).toPseudoEMetricSpace _ _ (v.toSubfield_isometry K)

theorem uniformContinuous : @UniformContinuous _ _ (v.uniformSpace K) _ (toSubfield K v).toFun :=
  @UniformInducing.uniformContinuous _ _ (v.uniformSpace K) _ _ (v.uniformInducing K)

instance : @CompletableTopField K _ (v.uniformSpace K) := by
  apply @CompletableTopField.mk _ _ (v.uniformSpace K)
  intro F F_cau inf_F
  let σ := toSubfield K v
  let i : K →+* ℂ := RingHom.comp (subfield K v).subtype σ
  have hi : @UniformInducing _ _ (v.uniformSpace K) _ i :=
    @UniformInducing.comp _ _ _ (v.uniformSpace K) _ _ _ uniformEmbedding_subtype_val.toUniformInducing _ (v.uniformInducing K)
  have h_cau_i := @UniformInducing.cauchy_map_iff _ _ (v.uniformSpace K) _ _ hi
  rw [← h_cau_i] at F_cau ⊢
  have h_comm : (i ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ i := by
    ext
    simp only [Function.comp_apply, map_inv₀, Subfield.coe_inv]

  rw [Filter.map_comm h_comm]
  apply CompletableTopField.nice _ F_cau
  rw [← Filter.push_pull', ← map_zero i]
  have h := (@UniformInducing.inducing _ _ (v.uniformSpace K) _ _ hi)
  have h' := @Inducing.nhds_eq_comap _ _ _ (v.topologicalSpace K) _ h
  rw [← h', inf_F, Filter.map_bot]

def completion := @UniformSpace.Completion K (v.uniformSpace K)

namespace Completion

instance : UniformSpace (v.completion K) :=
  @UniformSpace.Completion.uniformSpace _ (v.uniformSpace K)

instance : CompleteSpace (v.completion K) :=
  @UniformSpace.Completion.completeSpace _ (v.uniformSpace K)

instance : Field (v.completion K) :=
  @UniformSpace.Completion.instField _ _ (v.uniformSpace K) (v.topologicalDivisionRing K) _ _

instance : Inhabited (v.completion K) :=
  ⟨0⟩

instance : TopologicalRing (v.completion K) :=
  @UniformSpace.Completion.topologicalRing K _ (v.uniformSpace K) _ (v.uniformAddGroup K)

instance : Dist (v.completion K) :=
  @UniformSpace.Completion.instDistCompletionToUniformSpace _ (instPseudoMetricSpace K v)

instance : T0Space (v.completion K) :=
  @UniformSpace.Completion.t0Space _ (v.uniformSpace K)

theorem embedding_uniformContinuous : @UniformContinuous _ _ (v.uniformSpace K) _ v.embedding := by
  convert v.uniformContinuous K; simp [embedding, toSubfield];
  constructor
  · intro h
    apply @UniformContinuous.subtype_mk _ _ _ _ (v.uniformSpace K)
    exact h
  · intro h
    have h' := @UniformContinuous.comp _ _ _ (v.uniformSpace K) _ _ _ _ uniformContinuous_subtype_val h
    exact h'

theorem embedding_continuous : @Continuous _ _ (v.topologicalSpace K) _ v.embedding :=
  @UniformContinuous.continuous _ _ (v.uniformSpace K) _ _ (embedding_uniformContinuous K v)

def extensionEmbedding :=
  @UniformSpace.Completion.extensionHom K _ (v.uniformSpace K) (v.topologicalRing K) (v.uniformAddGroup K) ℂ _ _ _ _ v.embedding (embedding_continuous K v) _ _

theorem extensionEmbedding_injective : Function.Injective (extensionEmbedding K v) := (extensionEmbedding K v).injective


variable {K v}

/-- The embedding `Kᵥ → ℂ` preserves distances. -/
theorem extensionEmbedding_dist_eq (x y : v.completion K) :
    dist (extensionEmbedding K v x) (extensionEmbedding K v y) =
      dist x y := by
  set p : v.completion K → v.completion K → Prop :=
    λ x y => dist (extensionEmbedding K v x) (extensionEmbedding K v y) = dist x y
  refine @UniformSpace.Completion.induction_on₂ _ (instPseudoMetricSpace K v).toUniformSpace _ (instPseudoMetricSpace K v).toUniformSpace p x y ?_ (λ x y => ?_)
  · apply isClosed_eq
    · refine continuous_iff_continuous_dist.1 (@UniformSpace.Completion.continuous_extension _ (v.uniformSpace K) _ _ _ _)
    · convert continuous_dist
  · simp [p, extensionEmbedding, UniformSpace.Completion.extensionHom]
    rw [@UniformSpace.Completion.extension_coe _ (v.uniformSpace K) _ _ _ _ (embedding_uniformContinuous K v)]
    rw [@UniformSpace.Completion.extension_coe _ (v.uniformSpace K) _ _ _ _ (embedding_uniformContinuous K v)]
    rw [@UniformSpace.Completion.dist_eq _ (v.instPseudoMetricSpace K)]
    exact @Isometry.dist_eq _ _ (v.instPseudoMetricSpace K) _ _ (v.toSubfield_isometry K) _ _

variable (K v)

theorem embedding_isometry : Isometry (extensionEmbedding K v) :=
  Isometry.of_dist_eq extensionEmbedding_dist_eq

/-- The embedding `Kᵥ → ℂ` is uniform inducing. -/
theorem embedding_uniformInducing :
    UniformInducing (extensionEmbedding K v) :=
  (embedding_isometry K v).uniformInducing

/-- The embedding `Kᵥ → ℂ` is a closed embedding. -/
theorem closedEmbedding : ClosedEmbedding (extensionEmbedding K v) :=
  (embedding_isometry K v).closedEmbedding

/-- The completion of a number field at an Archimedean place is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (v.completion K) :=
  (closedEmbedding K v).locallyCompactSpace

end Completion

end NumberField.InfinitePlace
