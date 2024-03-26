/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib
import AdeleRingLocallyCompact.NumberTheory.NumberField.Basic

/-!
# Infinite adele ring

This file ports and develops further the Lean 3 formalization of the infinite adele ring found in
[https://github.com/mariainesdff/ideles/blob/e6646cd462c86a8813ca04fb82e84cdc14a59ad4/src/adeles_K.lean#L45].
While the infinite adele ring there is given the coinduced topology by the linear map `ℝⁿ →ₗ[ℝ] ℝ ⊗[ℚ] K`, where
`n` is the degree of the field extension `K/ℚ`, in this file we show that this is actually a linear equivalence
`ℝ ⊗[ℚ] K ≃ₗ[ℝ] ℝⁿ` and instead we give the infinite adele ring the induced topology under the forward
direction of this equivalence. This is equivalent to the coinduced topology on the reverse direction, so
the topology is the same as in the prior formalization, however we found working directly with the induced
topology to be easier in later proofs.

## Main definitions
 - `DedekindDomain.infiniteAdeleRing` of a number field `K` is defined as the tensor product `ℝ ⊗[ℚ] K`.
 - `DedekindDomain.InfiniteAdeleRing.real_tensorProduct_piRat_equiv` is the linear equivalence `ℝ ⊗[ℚ] ℚⁿ ≃ ℝⁿ`.
 - `DedekindDomain.InfiniteAdeleRing.real_tensorProduct_numberField_equiv` is the linear equivalence
   `infiniteAdeleRing K ≃ ℝⁿ`, where `K` is a number field and `n` is the degree of the field extension
   of `K` over `ℚ`.
 - `DedekindDomain.InfiniteAdeleRing.topologicalSpace` is the induced topology of the infinite adele ring along
   the linear equivalence `DedekindDomain.InfiniteAdeleRing.real_tensorProduct_numberField_equiv`.

## Main results
 - `DedekindDomain.InfiniteAdeleRing.locallyCompactSpace` : the infinite adele ring is a locally compact space
   since it's topology is induced from a finite product of locally compact spaces.

## References
 * [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
 * [M.I. de Frutos-Fernàndez, *Formalizing the Ring of Adèles of a Global Field*][defrutosfernandez2022]

## Tags
infinite adele ring, number field

## TODO
 - `DedekindDomain.InfiniteAdeleRing.real_tensorProduct_piRat_equiv` should be abstracted to a general linear
   equivalence along the lines of `RingTheory.TensorProduct.rid`. It actually follows directly from `rid` using
   distributativity of tensor product over `pi`.
 - `DedekindDomain.InfiniteAdeleRing.locallyCompactSpace` should be abstracted to a general result since all it
   relies on is that the infinite adeles have a topology that is induced by a linear equivalence to a locally compact
   space.
-/

noncomputable section

open DedekindDomain IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

open scoped TensorProduct

namespace DedekindDomain

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

def infiniteAdeleRing := (ℝ ⊗[ℚ] K)

namespace InfiniteAdeleRing

section DerivedInstances

instance : Ring (Fin n → ℝ) := Pi.ring
instance piReal_topologicalSpace : TopologicalSpace (Fin n → ℝ) := Pi.topologicalSpace
instance : CommRing (infiniteAdeleRing K) := Algebra.TensorProduct.instCommRing

end DerivedInstances

def real_tensorProduct_piRat_to_piReal : (ℝ ⊗[ℚ] (Fin n → ℚ)) →ₗ[ℝ] (Fin n → ℝ)
  := (Algebra.TensorProduct.basis ℝ (Pi.basisFun _ _)).constr ℝ (Pi.basisFun _ _)

def piReal_to_real_tensorProduct_piRat : (Fin n → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] (Fin n → ℚ))
  := (Pi.basisFun _ _).constr ℝ (Algebra.TensorProduct.basis ℝ (Pi.basisFun ℚ (Fin n)))

/-- TODO : This can be abstracted and simplified to a general result along the lines of
`RingTheory.TensorProduct.rid` [https://github.com/leanprover-community/mathlib4/blob/f5373eed0a601d313dd9b5723fc486548619ac45/Mathlib/RingTheory/TensorProduct/Basic.lean#L764].
Or, we may make use of `rid` directly if we show that the tensor product distributes over
`Fin n → ℚ` (unless this is already in Mathlib).
-/
theorem real_tensorProduct_piRat_equiv : (ℝ ⊗[ℚ] (Fin n → ℚ)) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun := real_tensorProduct_piRat_to_piReal n
  invFun := piReal_to_real_tensorProduct_piRat n
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LinearMap.coe_comp, ← @LinearMap.id_coe ℝ]
    have h : piReal_to_real_tensorProduct_piRat n ∘ₗ real_tensorProduct_piRat_to_piReal n = LinearMap.id := by
      apply Basis.ext (Algebra.TensorProduct.basis ℝ (Pi.basisFun _ _))
      intro i
      simp only [LinearMap.comp_apply, Algebra.TensorProduct.basis_apply, Pi.basisFun_apply,
        LinearMap.id_coe, id_eq, piReal_to_real_tensorProduct_piRat, real_tensorProduct_piRat_to_piReal
      ,
        Basis.constr_apply_fintype, Basis.equivFun_apply,
        Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply, Pi.basisFun_repr,
        LinearMap.stdBasis_apply', RingHom.map_ite_one_zero, Pi.basisFun_apply, ite_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.basisFun_equivFun,
        LinearEquiv.refl_apply, Algebra.TensorProduct.basis_apply]
    rw [h]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LinearMap.coe_comp, ← @LinearMap.id_coe ℝ]
    have h : real_tensorProduct_piRat_to_piReal n ∘ₗ piReal_to_real_tensorProduct_piRat n = LinearMap.id := by
      apply Basis.ext (Pi.basisFun _ _)
      intro i
      simp only [LinearMap.comp_apply, Algebra.TensorProduct.basis_apply, Pi.basisFun_apply,
        LinearMap.id_coe, id_eq, piReal_to_real_tensorProduct_piRat, real_tensorProduct_piRat_to_piReal
      ,
        Basis.constr_apply_fintype, Basis.equivFun_apply,
        Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply, Pi.basisFun_repr,
        LinearMap.stdBasis_apply', RingHom.map_ite_one_zero, Pi.basisFun_apply, ite_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.basisFun_equivFun,
        LinearEquiv.refl_apply, Algebra.TensorProduct.basis_apply]
    rw [h]
  map_add' := by simp only [map_add, forall_const]
  map_smul' := by simp only [map_smul, RingHom.id_apply, forall_const]

private def to_piReal :
  ℝ ⊗[ℚ] K →ₗ[ℝ] (Fin (FiniteDimensional.finrank ℚ K) → ℝ) :=
  LinearMap.comp
    (real_tensorProduct_piRat_to_piReal
   (FiniteDimensional.finrank ℚ K))
    (LinearMap.baseChange ℝ (ratBasis_equiv K).symm)

private def of_piReal :
  (Fin (FiniteDimensional.finrank ℚ K) → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] K) :=
  LinearMap.comp
    (LinearMap.baseChange ℝ (ratBasis_equiv K).toLinearMap)
    (piReal_to_real_tensorProduct_piRat (FiniteDimensional.finrank ℚ K))

/-- The linear equivalence between the infinite adele ring and a product of ℝ. -/
theorem real_tensorProduct_numberField_equiv : (ℝ ⊗[ℚ] K) ≃ₗ[ℝ] (Fin (FiniteDimensional.finrank ℚ K) → ℝ) where
  toFun := to_piReal K
  invFun := of_piReal K
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LinearMap.coe_comp,
      of_piReal, to_piReal]
    simp only [LinearMap.coe_comp, Function.comp.assoc]
    nth_rewrite 2 [← Function.comp.assoc]
    have h := Function.leftInverse_iff_comp.1 (real_tensorProduct_piRat_equiv (FiniteDimensional.finrank ℚ K)).left_inv
    unfold real_tensorProduct_piRat_equiv at h
    rw [h, Function.id_comp, ← LinearMap.coe_comp, ← LinearMap.baseChange_comp, LinearEquiv.comp_coe,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.baseChange_id, LinearMap.id_coe]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LinearMap.coe_comp,
      of_piReal, to_piReal]
    simp only [LinearMap.coe_comp, Function.comp.assoc]
    nth_rewrite 2 [← Function.comp.assoc]
    have h := Function.rightInverse_iff_comp.1 (real_tensorProduct_piRat_equiv (FiniteDimensional.finrank ℚ K)).right_inv
    unfold real_tensorProduct_piRat_equiv at h
    rw [← LinearMap.coe_comp, ← LinearMap.baseChange_comp, LinearMap.baseChange, LinearEquiv.comp_coe,
      LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, TensorProduct.AlgebraTensorModule.map_id,
      LinearMap.id_coe, Function.id_comp, h]
  map_add' := by simp only [map_add, forall_const]
  map_smul' := by simp only [map_smul, RingHom.id_apply, forall_const]

instance topologicalSpace : TopologicalSpace (infiniteAdeleRing K)
  := TopologicalSpace.induced
    (real_tensorProduct_numberField_equiv K)
    (piReal_topologicalSpace (FiniteDimensional.finrank ℚ K))

/-- A finite product of ℝ is locally compact. -/
theorem piReal_locallyCompact : LocallyCompactSpace (Fin n → ℝ) := Pi.locallyCompactSpace_of_finite

/-- The infinite adele ring is locally compact. -/
theorem locallyCompactSpace : LocallyCompactSpace (infiniteAdeleRing K) := by
    refine LocallyCompactSpace.mk (λ x N hN => ?_)
    simp only [nhds_induced, Filter.mem_comap] at hN
    obtain ⟨M, hM, hMN⟩ := hN
    have h := (piReal_locallyCompact (FiniteDimensional.finrank ℚ K)).local_compact_nhds
    obtain ⟨T, hT, hTM, hT_compact⟩ := h ((InfiniteAdeleRing.real_tensorProduct_numberField_equiv K) x) M hM
    use (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K) ⁻¹' T
    refine ⟨?_, subset_trans ?_ hMN, ?_⟩
    · rw [nhds_induced, Filter.mem_comap]
      use T
    · rw [← LinearEquiv.coe_toEquiv]
      exact (Equiv.preimage_subset
        (LinearEquiv.toEquiv (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K)) _ _).2 hTM
    · rw [← LinearEquiv.image_symm_eq_preimage (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K) T]
      apply IsCompact.image hT_compact
      have h_topology : InfiniteAdeleRing.topologicalSpace K =
        TopologicalSpace.induced
          (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K).toEquiv
          (InfiniteAdeleRing.piReal_topologicalSpace (FiniteDimensional.finrank ℚ K)) := rfl
      rw [← Equiv.coinduced_symm (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K).toEquiv] at h_topology
      rw [h_topology]
      exact continuous_coinduced_rng

end InfiniteAdeleRing

end DedekindDomain
