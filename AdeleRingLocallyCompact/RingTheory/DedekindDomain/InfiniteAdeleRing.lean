import Mathlib

open DedekindDomain IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped TensorProduct

namespace DedekindDomain

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K] [NumberField K] [Algebra R K]
  [IsFractionRing R K] (n : ℕ) (B : (n : ℕ) → Basis (Fin n) ℚ (Fin n → ℚ)) (C : (n : ℕ) → Basis (Fin n) ℝ (Fin n → ℝ))

def infiniteAdeleRing := (ℝ ⊗[ℚ] K)

namespace InfiniteAdeleRing

noncomputable def RatBasis.equiv : (Fin (FiniteDimensional.finrank ℚ K) → ℚ) ≃ₗ[ℚ] K :=
  LinearEquiv.symm (Basis.equivFun (FiniteDimensional.finBasis ℚ K))

noncomputable def RatBasis.to_tensorBasis_funLike : Fin n → (ℝ ⊗[ℚ] (Fin n → ℚ))
  := λ i => TensorProduct.mk _ _ _ (1 : ℝ) (B n i)

noncomputable def RealBasis.funLike : Fin n → (Fin n → ℝ)
  := λ i => C n i

noncomputable def real_tensorProduct_rat_toFun : (ℝ ⊗[ℚ] (Fin n → ℚ)) →ₗ[ℝ] (Fin n → ℝ)
  := (Algebra.TensorProduct.basis ℝ (B _)).constr ℝ (RealBasis.funLike n C)

noncomputable def real_tensorProduct_rat_invFun : (Fin n → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] (Fin n → ℚ))
  := (C _).constr ℝ (RatBasis.to_tensorBasis_funLike n B)

theorem real_tensorProduct_rat_equiv : (ℝ ⊗[ℚ] (Fin n → ℚ)) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun := real_tensorProduct_rat_toFun n B C
  invFun := real_tensorProduct_rat_invFun n B C
  left_inv := by
    rw [Function.leftInverse_iff_comp]
    rw [← LinearMap.coe_comp, ← @LinearMap.id_coe ℝ]
    have h : real_tensorProduct_rat_invFun n B C ∘ₗ real_tensorProduct_rat_toFun n B C = LinearMap.id := by
      apply Basis.ext (Algebra.TensorProduct.basis ℝ (B _))
      intro i
      rw [LinearMap.comp_apply]
      simp
      rw [real_tensorProduct_rat_invFun, real_tensorProduct_rat_toFun]
      have h := (Basis.constr_basis (Algebra.TensorProduct.basis ℝ (B n)) ℝ (RealBasis.funLike n C) i)
      rw [RealBasis.funLike] at h
      simp at h
      simp [h]
      rfl
    rw [h]
  right_inv := by
    rw [Function.rightInverse_iff_comp]
    rw [← LinearMap.coe_comp, ← @LinearMap.id_coe ℝ]
    have h : real_tensorProduct_rat_toFun n B C ∘ₗ real_tensorProduct_rat_invFun n B C = LinearMap.id := by
      apply Basis.ext (C _)
      intro i
      simp
      rw [real_tensorProduct_rat_invFun, real_tensorProduct_rat_toFun]
      have h := (Basis.constr_basis (C n) ℝ (RatBasis.to_tensorBasis_funLike n B) i)
      rw [RatBasis.to_tensorBasis_funLike] at h
      simp at h
      simp [h]
      simp [Finsupp.single_apply]
      rfl
    rw [h]

  map_add' := by simp
  map_smul' := by simp

noncomputable def real_tensorProduct_numberField_toFun :  (ℝ ⊗[ℚ] K) →ₗ[ℝ] (Fin (FiniteDimensional.finrank ℚ K) → ℝ) :=
  LinearMap.comp (real_tensorProduct_rat_toFun (FiniteDimensional.finrank ℚ K) B C) (LinearMap.baseChange ℝ (RatBasis.equiv K).symm)

noncomputable def real_tensorProduct_numberField_invFun : (Fin (FiniteDimensional.finrank ℚ K) → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] K) :=
  LinearMap.comp (LinearMap.baseChange ℝ (RatBasis.equiv K).toLinearMap) (real_tensorProduct_rat_invFun (FiniteDimensional.finrank ℚ K) B C)

theorem real_tensorProduct_numberField_equiv : (ℝ ⊗[ℚ] K) ≃ₗ[ℝ] (Fin (FiniteDimensional.finrank ℚ K) → ℝ) where
  toFun := real_tensorProduct_numberField_toFun K B C
  invFun := real_tensorProduct_numberField_invFun K B C
  left_inv := by
    simp
    rw [Function.leftInverse_iff_comp]
    rw [← LinearMap.coe_comp]
    rw [real_tensorProduct_numberField_invFun, real_tensorProduct_numberField_toFun]
    simp
    rw [Function.comp.assoc]
    nth_rewrite 2 [← Function.comp.assoc]
    have h := Function.leftInverse_iff_comp.1 (real_tensorProduct_rat_equiv (FiniteDimensional.finrank ℚ K) B C).left_inv
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
    have h := Function.rightInverse_iff_comp.1 (real_tensorProduct_rat_equiv (FiniteDimensional.finrank ℚ K) B C).right_inv
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
noncomputable instance : CommRing (infiniteAdeleRing K) := Algebra.TensorProduct.instCommRing

--noncomputable def ringTopology : RingTopology (infiniteAdeleRing K) := RingTopology.coinduced (real_tensorProduct_numberField_equiv K B C).symm

noncomputable instance topologicalSpace : TopologicalSpace (infiniteAdeleRing K)
  := TopologicalSpace.induced
    (real_tensorProduct_numberField_equiv K B C)
    (piReal_topologicalSpace (FiniteDimensional.finrank ℚ K))
--noncomputable instance : @TopologicalRing (infiniteAdeleRing K) (topologicalSpace K B C) _ := (ringTopology K B C).toTopologicalRing

theorem piReal_locallyCompact : LocallyCompactSpace (Fin n → ℝ) := Pi.locallyCompactSpace_of_finite

theorem locallyCompactSpace : @LocallyCompactSpace (infiniteAdeleRing K) (InfiniteAdeleRing.topologicalSpace K B C) := by
    have h := (@piReal_locallyCompact (FiniteDimensional.finrank ℚ K)).local_compact_nhds
    apply @LocallyCompactSpace.mk _ (InfiniteAdeleRing.topologicalSpace K B C)
    intro x N hN
    rw [nhds_induced] at hN
    simp at hN
    obtain ⟨M, hM, hMN⟩ := hN
    obtain ⟨T, hT, hTM, hTC⟩ := h ((InfiniteAdeleRing.real_tensorProduct_numberField_equiv K B C) x) M hM
    use (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K B C) ⁻¹' T
    refine' ⟨_, _, _⟩
    {
      rw [nhds_induced]
      simp
      use T
    }
    {
      apply subset_trans _ hMN
      rw [← LinearEquiv.coe_toEquiv]
      exact (Equiv.preimage_subset (LinearEquiv.toEquiv (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K B C)) _ _).2 hTM
    }
    {
      rw [← LinearEquiv.image_symm_eq_preimage (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K B C) T]
      apply @IsCompact.image _ _ _ (InfiniteAdeleRing.topologicalSpace K B C) _ _ hTC
      have h' : InfiniteAdeleRing.topologicalSpace K B C = TopologicalSpace.induced (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K B C).toEquiv (InfiniteAdeleRing.piReal_topologicalSpace (FiniteDimensional.finrank ℚ K)) := rfl
      rw [← Equiv.coinduced_symm (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K B C).toEquiv] at h'
      rw [h']
      exact continuous_coinduced_rng
    }

end DerivedInstances

end InfiniteAdeleRing

end DedekindDomain
