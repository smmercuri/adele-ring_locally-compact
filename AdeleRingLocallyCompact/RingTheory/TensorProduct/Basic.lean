import Mathlib

open scoped TensorProduct

noncomputable section

namespace Algebra

namespace TensorProduct

universe uR uS uA uB uC uD uE uF

variable (R : Type uR)  (A : Type uA)  (S : Type uS)
 [CommSemiring R] [CommSemiring S]  [Algebra R S]  [Semiring A]
  [Algebra R A] [Algebra S A]  [IsScalarTower R S A]
  (ι : Type uι) [Finite ι]
/-
private def rid_pi_toFun :
  A ⊗[R] (ι → R) →ₗ[S] (ι → A) :=
  (Algebra.TensorProduct.basis A (Pi.basisFun R ι)).constr S (Pi.basisFun A ι)

private def rid_pi_invFun :
  (ι → A) →ₗ[S] A ⊗[R] (ι → R) :=
  (Pi.basisFun A ι).constr S (Algebra.TensorProduct.basis A (Pi.basisFun R ι))
-/
def rid_pi :
  A ⊗[R] (ι → R) ≃ₗ[A] (ι → A)
  := Basis.equiv (Algebra.TensorProduct.basis A (Pi.basisFun R ι)) (Pi.basisFun A ι) (Equiv.refl ι)
  /-
  toFun := rid_pi_toFun R A S ι
  invFun := rid_pi_invFun R A S ι
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LinearMap.coe_comp, ← @LinearMap.id_coe S]
    rw [rid_pi_toFun,rid_pi_invFun]

    apply Basis.ext (Algebra.TensorProduct.basis A (Pi.basisFun R ι))
    have h : rid_pi_toFun R A S ι ∘ₗ rid_pi_invFun R A S ι = LinearMap.id:= by
      apply Basis.ext (Algebra.TensorProduct.basis A (Pi.basisFun R ι))
      apply h

      intro i
      simp only [LinearMap.comp_apply, Algebra.TensorProduct.basis_apply, Pi.basisFun_apply,
        LinearMap.id_coe, id_eq, piReal_to_real_tensorProduct_piRat, real_tensorProduct_piRat_to_piReal,
        Basis.constr_apply_fintype, Basis.equivFun_apply,
        Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply, Pi.basisFun_repr,
        LinearMap.stdBasis_apply', RingHom.map_ite_one_zero, Pi.basisFun_apply, ite_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.basisFun_equivFun,
        LinearEquiv.refl_apply, Algebra.TensorProduct.basis_apply]
    rw [h]-/

end TensorProduct

end Algebra
