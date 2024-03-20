import Mathlib

open DedekindDomain IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped TensorProduct
open scoped Classical

namespace DedekindDomain

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K] [NumberField K] [Algebra R K]
  [IsFractionRing R K] (n : ℕ) (B : (n : ℕ) → Basis (Fin n) ℚ (Fin n → ℚ)) (C : (n : ℕ) → Basis (Fin n) ℝ (Fin n → ℝ))

namespace LinearMap

noncomputable def ratBasis.equivFun : (Fin (FiniteDimensional.finrank ℚ K) → ℚ) ≃ₗ[ℚ] K :=
  LinearEquiv.symm (Basis.equivFun (FiniteDimensional.finBasis ℚ K))

noncomputable def basis_to : Fin n → (ℝ ⊗[ℚ] (Fin n → ℚ)) := λ i => TensorProduct.mk _ _ _ (1 : ℝ) (B n i)
noncomputable def basis_from : Fin n → (Fin n → ℝ) := λ i => C n i
noncomputable def piReal_to_realTensor_piRat : (Fin n → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] (Fin n → ℚ)) := (C _).constr ℝ (basis_to n B)
noncomputable def realTensor_piRat_to_piReal : (ℝ ⊗[ℚ] (Fin n → ℚ)) →ₗ[ℝ] (Fin n → ℝ) := (Algebra.TensorProduct.basis ℝ (B _)).constr ℝ (basis_from n C)

noncomputable def piReal_to_realTensor_numberField : (Fin (FiniteDimensional.finrank ℚ K) → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] K) :=
  LinearMap.comp (LinearMap.baseChange ℝ (ratBasis.equivFun K).toLinearMap) (piReal_to_realTensor_piRat (FiniteDimensional.finrank ℚ K) B C)

noncomputable def realTensor_numberField_to_piReal :  (ℝ ⊗[ℚ] K) →ₗ[ℝ] (Fin (FiniteDimensional.finrank ℚ K) → ℝ) :=
  LinearMap.comp (realTensor_piRat_to_piReal (FiniteDimensional.finrank ℚ K) B C) (LinearMap.baseChange ℝ (ratBasis.equivFun K).symm)

theorem piReal_to_realTensor_piRat.equiv : (ℝ ⊗[ℚ] (Fin n → ℚ)) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun := realTensor_piRat_to_piReal n B C
  invFun := piReal_to_realTensor_piRat n B C
  left_inv := by
    rw [Function.leftInverse_iff_comp]
    rw [← LinearMap.coe_comp, ← @LinearMap.id_coe ℝ]
    have h : piReal_to_realTensor_piRat n B C ∘ₗ realTensor_piRat_to_piReal n B C = LinearMap.id := by
      apply Basis.ext (Algebra.TensorProduct.basis ℝ (B _))
      intro i
      rw [LinearMap.comp_apply]
      simp
      rw [piReal_to_realTensor_piRat, realTensor_piRat_to_piReal]
      have h := (Basis.constr_basis (Algebra.TensorProduct.basis ℝ (B n)) ℝ (basis_from n C) i)
      rw [basis_from] at h
      simp at h
      simp [h]
      rfl
    rw [h]
  right_inv := by
    rw [Function.rightInverse_iff_comp]
    rw [← LinearMap.coe_comp, ← @LinearMap.id_coe ℝ]
    have h : realTensor_piRat_to_piReal n B C ∘ₗ piReal_to_realTensor_piRat n B C = LinearMap.id := by
      apply Basis.ext (C _)
      intro i
      simp
      rw [piReal_to_realTensor_piRat, realTensor_piRat_to_piReal]
      have h := (Basis.constr_basis (C n) ℝ (basis_to n B) i)
      rw [basis_to] at h
      simp at h
      simp [h]
      simp [Finsupp.single_apply]
      rfl
    rw [h]

  map_add' := by simp
  map_smul' := by simp

theorem piReal_to_realTensor_numberField.equiv : (ℝ ⊗[ℚ] K) ≃ₗ[ℝ] (Fin (FiniteDimensional.finrank ℚ K) → ℝ) where
  toFun := realTensor_numberField_to_piReal K B C
  invFun := piReal_to_realTensor_numberField K B C
  left_inv := by
    simp
    rw [Function.leftInverse_iff_comp]
    rw [← LinearMap.coe_comp]
    rw [piReal_to_realTensor_numberField, realTensor_numberField_to_piReal]
    simp
    rw [Function.comp.assoc]
    nth_rewrite 2 [← Function.comp.assoc]
    have h := Function.leftInverse_iff_comp.1 (piReal_to_realTensor_piRat.equiv (FiniteDimensional.finrank ℚ K) B C).left_inv
    unfold piReal_to_realTensor_piRat.equiv at h
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
    rw [piReal_to_realTensor_numberField, realTensor_numberField_to_piReal]
    simp
    rw [Function.comp.assoc]
    nth_rewrite 2 [← Function.comp.assoc]
    have h := Function.rightInverse_iff_comp.1 (piReal_to_realTensor_piRat.equiv (FiniteDimensional.finrank ℚ K) B C).right_inv
    unfold piReal_to_realTensor_piRat.equiv at h
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

end LinearMap

def infiniteAdeleRing := (ℝ ⊗[ℚ] K)

namespace InfiniteAdeleRing

open LinearMap

section DerivedInstances

instance : Ring (Fin n → ℝ) := Pi.ring
instance piReal_topologicalSpace : TopologicalSpace (Fin n → ℝ) := Pi.topologicalSpace
instance : ContinuousAdd (Fin n → ℝ) := Pi.continuousAdd
instance : ContinuousMul (Fin n → ℝ) := Pi.continuousMul
instance : TopologicalRing (Fin n → ℝ) := TopologicalRing.mk
noncomputable instance : CommRing (infiniteAdeleRing K) := Algebra.TensorProduct.instCommRing

--noncomputable def ringTopology : RingTopology (infiniteAdeleRing K) := RingTopology.coinduced (piReal_to_realTensor_numberField.equiv K B C)
noncomputable instance topologicalSpace : TopologicalSpace (infiniteAdeleRing K) := TopologicalSpace.induced (piReal_to_realTensor_numberField.equiv K B C) (piReal_topologicalSpace (FiniteDimensional.finrank ℚ K))
--noncomputable instance : TopologicalRing (infiniteAdeleRing K) := (ringTopology K).toTopologicalRing

end DerivedInstances

end InfiniteAdeleRing

end DedekindDomain
