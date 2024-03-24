import Mathlib

noncomputable section

open DedekindDomain IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped TensorProduct

namespace DedekindDomain

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

def infiniteAdeleRing := (ℝ ⊗[ℚ] K)

namespace InfiniteAdeleRing

def ratBasis_equiv : (Fin (FiniteDimensional.finrank ℚ K) → ℚ) ≃ₗ[ℚ] K :=
  LinearEquiv.symm (Basis.equivFun (FiniteDimensional.finBasis ℚ K))

def real_tensorProduct_rat_toFun : (ℝ ⊗[ℚ] (Fin n → ℚ)) →ₗ[ℝ] (Fin n → ℝ)
  := (Algebra.TensorProduct.basis ℝ (Pi.basisFun _ _)).constr ℝ (Pi.basisFun _ _)

def real_tensorProduct_rat_invFun : (Fin n → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] (Fin n → ℚ))
  := (Pi.basisFun _ _).constr ℝ (Algebra.TensorProduct.basis ℝ (Pi.basisFun ℚ (Fin n)))

theorem real_tensorProduct_rat_equiv : (ℝ ⊗[ℚ] (Fin n → ℚ)) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun := real_tensorProduct_rat_toFun n
  invFun := real_tensorProduct_rat_invFun n
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LinearMap.coe_comp, ← @LinearMap.id_coe ℝ]
    have h : real_tensorProduct_rat_invFun n ∘ₗ real_tensorProduct_rat_toFun n = LinearMap.id := by
      apply Basis.ext (Algebra.TensorProduct.basis ℝ (Pi.basisFun _ _))
      intro i
      simp only [LinearMap.comp_apply, Algebra.TensorProduct.basis_apply, Pi.basisFun_apply,
        LinearMap.id_coe, id_eq, real_tensorProduct_rat_invFun, real_tensorProduct_rat_toFun,
        Basis.constr_apply_fintype, Basis.equivFun_apply,
        Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply, Pi.basisFun_repr,
        LinearMap.stdBasis_apply', RingHom.map_ite_one_zero, Pi.basisFun_apply, ite_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.basisFun_equivFun,
        LinearEquiv.refl_apply, Algebra.TensorProduct.basis_apply]
    rw [h]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LinearMap.coe_comp, ← @LinearMap.id_coe ℝ]
    have h : real_tensorProduct_rat_toFun n ∘ₗ real_tensorProduct_rat_invFun n = LinearMap.id := by
      apply Basis.ext (Pi.basisFun _ _)
      intro i
      simp only [LinearMap.comp_apply, Algebra.TensorProduct.basis_apply, Pi.basisFun_apply,
        LinearMap.id_coe, id_eq, real_tensorProduct_rat_invFun, real_tensorProduct_rat_toFun,
        Basis.constr_apply_fintype, Basis.equivFun_apply,
        Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply, Pi.basisFun_repr,
        LinearMap.stdBasis_apply', RingHom.map_ite_one_zero, Pi.basisFun_apply, ite_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.basisFun_equivFun,
        LinearEquiv.refl_apply, Algebra.TensorProduct.basis_apply]
    rw [h]
  map_add' := by simp only [map_add, forall_const]
  map_smul' := by simp only [map_smul, RingHom.id_apply, forall_const]

def real_tensorProduct_numberField_toFun :
  (ℝ ⊗[ℚ] K) →ₗ[ℝ] (Fin (FiniteDimensional.finrank ℚ K) → ℝ) :=
  LinearMap.comp
    (real_tensorProduct_rat_toFun (FiniteDimensional.finrank ℚ K))
    (LinearMap.baseChange ℝ (ratBasis_equiv K).symm)

def real_tensorProduct_numberField_invFun :
  (Fin (FiniteDimensional.finrank ℚ K) → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] K) :=
  LinearMap.comp
    (LinearMap.baseChange ℝ (ratBasis_equiv K).toLinearMap)
    (real_tensorProduct_rat_invFun (FiniteDimensional.finrank ℚ K))

theorem real_tensorProduct_numberField_equiv : (ℝ ⊗[ℚ] K) ≃ₗ[ℝ] (Fin (FiniteDimensional.finrank ℚ K) → ℝ) where
  toFun := real_tensorProduct_numberField_toFun K
  invFun := real_tensorProduct_numberField_invFun K
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LinearMap.coe_comp]
    rw [real_tensorProduct_numberField_invFun, real_tensorProduct_numberField_toFun]
    simp only [LinearMap.coe_comp, Function.comp.assoc]
    nth_rewrite 2 [← Function.comp.assoc]
    have h := Function.leftInverse_iff_comp.1 (real_tensorProduct_rat_equiv (FiniteDimensional.finrank ℚ K)).left_inv
    unfold real_tensorProduct_rat_equiv at h
    rw [h, Function.id_comp, ← LinearMap.coe_comp, ← LinearMap.baseChange_comp, LinearEquiv.comp_coe,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.baseChange_id, LinearMap.id_coe]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LinearMap.coe_comp]
    rw [real_tensorProduct_numberField_invFun, real_tensorProduct_numberField_toFun]
    simp only [LinearMap.coe_comp, Function.comp.assoc]
    nth_rewrite 2 [← Function.comp.assoc]
    have h := Function.rightInverse_iff_comp.1 (real_tensorProduct_rat_equiv (FiniteDimensional.finrank ℚ K)).right_inv
    unfold real_tensorProduct_rat_equiv at h
    rw [← LinearMap.coe_comp, ← LinearMap.baseChange_comp, LinearMap.baseChange, LinearEquiv.comp_coe,
      LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, TensorProduct.AlgebraTensorModule.map_id,
      LinearMap.id_coe, Function.id_comp, h]
  map_add' := by simp only [map_add, forall_const]
  map_smul' := by simp only [map_smul, RingHom.id_apply, forall_const]

section DerivedInstances

instance : Ring (Fin n → ℝ) := Pi.ring
instance piReal_topologicalSpace : TopologicalSpace (Fin n → ℝ) := Pi.topologicalSpace
instance : CommRing (infiniteAdeleRing K) := Algebra.TensorProduct.instCommRing

end DerivedInstances

instance topologicalSpace : TopologicalSpace (infiniteAdeleRing K)
  := TopologicalSpace.induced
    (real_tensorProduct_numberField_equiv K)
    (piReal_topologicalSpace (FiniteDimensional.finrank ℚ K))

theorem piReal_locallyCompact : LocallyCompactSpace (Fin n → ℝ) := Pi.locallyCompactSpace_of_finite

theorem locallyCompactSpace : LocallyCompactSpace (infiniteAdeleRing K) := by
    refine' LocallyCompactSpace.mk (λ x N hN => _)
    simp only [nhds_induced, Filter.mem_comap] at hN
    obtain ⟨M, hM, hMN⟩ := hN

    have h := (piReal_locallyCompact (FiniteDimensional.finrank ℚ K)).local_compact_nhds
    obtain ⟨T, hT, hTM, hT_compact⟩ := h ((InfiniteAdeleRing.real_tensorProduct_numberField_equiv K) x) M hM
    use (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K) ⁻¹' T
    refine' ⟨_, subset_trans _ hMN, _⟩
    {
      rw [nhds_induced, Filter.mem_comap]
      use T
    }
    {
      rw [← LinearEquiv.coe_toEquiv]
      exact (Equiv.preimage_subset
        (LinearEquiv.toEquiv (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K)) _ _).2 hTM
    }
    {
      rw [← LinearEquiv.image_symm_eq_preimage (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K) T]
      apply IsCompact.image hT_compact
      have h_topology : InfiniteAdeleRing.topologicalSpace K =
        TopologicalSpace.induced
          (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K).toEquiv
          (InfiniteAdeleRing.piReal_topologicalSpace (FiniteDimensional.finrank ℚ K)) := rfl
      rw [← Equiv.coinduced_symm (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K).toEquiv] at h_topology
      rw [h_topology]
      exact continuous_coinduced_rng
    }

end InfiniteAdeleRing

end DedekindDomain
