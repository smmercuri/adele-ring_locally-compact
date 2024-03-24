import Mathlib

noncomputable section

open DedekindDomain IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped TensorProduct

namespace DedekindDomain

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K] [NumberField K] [Algebra R K]
  [IsFractionRing R K] (n : ℕ)

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
    rw [Function.leftInverse_iff_comp]
    rw [← LinearMap.coe_comp, ← @LinearMap.id_coe ℝ]
    have h : real_tensorProduct_rat_invFun n ∘ₗ real_tensorProduct_rat_toFun n = LinearMap.id := by
      apply Basis.ext (Algebra.TensorProduct.basis ℝ (Pi.basisFun _ _))
      intro i
      rw [LinearMap.comp_apply]
      simp
      rw [real_tensorProduct_rat_invFun, real_tensorProduct_rat_toFun]
      --have h := (Basis.constr_basis (Algebra.TensorProduct.basis ℝ (Pi.basisFun ℚ (Fin n))) ℝ (Pi.basisFun ℝ (Fin n)) i)
      --rw [h]
      --rw [RealBasis.funLike] at h
      --simp at h
      --simp --[h]
      --unfold RatBasis.to_tensorBasis_funLike
      simp
    rw [h]
  right_inv := by
    rw [Function.rightInverse_iff_comp]
    rw [← LinearMap.coe_comp, ← @LinearMap.id_coe ℝ]
    have h : real_tensorProduct_rat_toFun n ∘ₗ real_tensorProduct_rat_invFun n = LinearMap.id := by
      apply Basis.ext (Pi.basisFun _ _)
      intro i
      simp
      rw [real_tensorProduct_rat_invFun, real_tensorProduct_rat_toFun]
      simp
      /-have h := (Basis.constr_basis (Pi.basisFun ℝ (Fin n)) ℝ (RatBasis.to_tensorBasis_funLike n) i)
      rw [RatBasis.to_tensorBasis_funLike] at h
      simp at h
      simp [h]-/
    rw [h]

  map_add' := by simp
  map_smul' := by simp

def real_tensorProduct_numberField_toFun :  (ℝ ⊗[ℚ] K) →ₗ[ℝ] (Fin (FiniteDimensional.finrank ℚ K) → ℝ) :=
  LinearMap.comp (real_tensorProduct_rat_toFun (FiniteDimensional.finrank ℚ K)) (LinearMap.baseChange ℝ (ratBasis_equiv K).symm)

def real_tensorProduct_numberField_invFun : (Fin (FiniteDimensional.finrank ℚ K) → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] K) :=
  LinearMap.comp (LinearMap.baseChange ℝ (ratBasis_equiv K).toLinearMap) (real_tensorProduct_rat_invFun (FiniteDimensional.finrank ℚ K))

theorem real_tensorProduct_numberField_equiv : (ℝ ⊗[ℚ] K) ≃ₗ[ℝ] (Fin (FiniteDimensional.finrank ℚ K) → ℝ) where
  toFun := real_tensorProduct_numberField_toFun K
  invFun := real_tensorProduct_numberField_invFun K
  left_inv := by
    simp
    rw [Function.leftInverse_iff_comp]
    rw [← LinearMap.coe_comp]
    rw [real_tensorProduct_numberField_invFun, real_tensorProduct_numberField_toFun]
    simp
    rw [Function.comp.assoc]
    nth_rewrite 2 [← Function.comp.assoc]
    have h := Function.leftInverse_iff_comp.1 (real_tensorProduct_rat_equiv (FiniteDimensional.finrank ℚ K)).left_inv
    unfold real_tensorProduct_rat_equiv at h
    simp at h
    rw [h]
    simp
    rw [← LinearMap.coe_comp]
    rw [← LinearMap.baseChange_comp]
    simp
    --ext x
    --unfold LinearMap.baseChange
    --simp
  right_inv := by
    simp
    rw [Function.rightInverse_iff_comp]
    rw [← LinearMap.coe_comp]
    rw [real_tensorProduct_numberField_invFun, real_tensorProduct_numberField_toFun]
    simp
    rw [Function.comp.assoc]
    nth_rewrite 2 [← Function.comp.assoc]
    have h := Function.rightInverse_iff_comp.1 (real_tensorProduct_rat_equiv (FiniteDimensional.finrank ℚ K)).right_inv
    unfold real_tensorProduct_rat_equiv at h
    simp at h
    rw [← LinearMap.coe_comp]
    rw [← LinearMap.baseChange_comp]
    unfold LinearMap.baseChange
    simp
    rw [h]
    --unfold LinearMap.baseChange
    --simp
    --rw [h]

  map_add' := by simp
  map_smul' := by simp

section DerivedInstances

instance : Ring (Fin n → ℝ) := Pi.ring
instance piReal_topologicalSpace : TopologicalSpace (Fin n → ℝ) := Pi.topologicalSpace
--instance : ContinuousAdd (Fin n → ℝ) := Pi.continuousAdd
--instance : ContinuousMul (Fin n → ℝ) := Pi.continuousMul
instance : TopologicalRing (Fin n → ℝ) := Pi.instTopologicalRing
instance : CommRing (infiniteAdeleRing K) := Algebra.TensorProduct.instCommRing

--noncomputable def ringTopology : RingTopology (infiniteAdeleRing K) := RingTopology.coinduced (real_tensorProduct_numberField_equiv K B C).symm

instance topologicalSpace : TopologicalSpace (infiniteAdeleRing K)
  := TopologicalSpace.induced
    (real_tensorProduct_numberField_equiv K)
    (piReal_topologicalSpace (FiniteDimensional.finrank ℚ K))
--noncomputable instance : @TopologicalRing (infiniteAdeleRing K) (topologicalSpace K B C) _ := (ringTopology K B C).toTopologicalRing

theorem piReal_locallyCompact : LocallyCompactSpace (Fin n → ℝ) := Pi.locallyCompactSpace_of_finite

theorem locallyCompactSpace : LocallyCompactSpace (infiniteAdeleRing K) := by
    have h := (@piReal_locallyCompact (FiniteDimensional.finrank ℚ K)).local_compact_nhds
    apply LocallyCompactSpace.mk
    intro x N hN
    rw [nhds_induced] at hN
    simp at hN
    obtain ⟨M, hM, hMN⟩ := hN
    obtain ⟨T, hT, hTM, hTC⟩ := h ((InfiniteAdeleRing.real_tensorProduct_numberField_equiv K) x) M hM
    use (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K) ⁻¹' T
    refine' ⟨_, _, _⟩
    {
      rw [nhds_induced]
      simp
      use T
    }
    {
      apply subset_trans _ hMN
      rw [← LinearEquiv.coe_toEquiv]
      exact (Equiv.preimage_subset (LinearEquiv.toEquiv (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K)) _ _).2 hTM
    }
    {
      rw [← LinearEquiv.image_symm_eq_preimage (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K) T]
      apply IsCompact.image hTC--_ _ _ (InfiniteAdeleRing.topologicalSpace K) _ _ hTC
      have h' : InfiniteAdeleRing.topologicalSpace K = TopologicalSpace.induced (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K).toEquiv (InfiniteAdeleRing.piReal_topologicalSpace (FiniteDimensional.finrank ℚ K)) := rfl
      rw [← Equiv.coinduced_symm (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K).toEquiv] at h'
      rw [h']
      exact continuous_coinduced_rng
    }

end DerivedInstances

end InfiniteAdeleRing

end DedekindDomain
