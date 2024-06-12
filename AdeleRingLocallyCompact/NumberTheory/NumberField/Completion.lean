/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib
import AdeleRingLocallyCompact.Analysis.NormedSpace.Completion

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
