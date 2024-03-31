/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# The tensor product of R-algebras

In this file we give some additional required results on tensor products of R-algebras,
supplementing the current mathlib library.

## Main definitions
 - `Algebra.TensorProduct.rid_pi` : `A ⊗[R] (ι → R) ≃ₗ[A] (ι → A)`
 - `LinaraMap.baseChange_equiv` : If `e : M ≃ₗ[R] N` then this is the linear equivalence
   `A ⊗[R] M ≃ₗ[A] A ⊗[R] N` given by `LinearMap.baseChange A e`.
-/

open scoped TensorProduct

noncomputable section

namespace Algebra

namespace TensorProduct

universe uR uS uA uB uC uD uE uF

variable (R : Type uR)  (A : Type uA)  (S : Type uS)
 [CommSemiring R] [CommSemiring S]  [Algebra R S]  [Semiring A]
  [Algebra R A] [Algebra S A]  [IsScalarTower R S A]
  (ι : Type uι) [Finite ι]

def rid_pi :
  A ⊗[R] (ι → R) ≃ₗ[A] (ι → A)
  := Basis.equiv (Algebra.TensorProduct.basis A (Pi.basisFun R ι)) (Pi.basisFun A ι) (Equiv.refl ι)

end TensorProduct

end Algebra

namespace LinearMap

variable {R A M N : Type*} [CommSemiring R]
variable [Semiring A] [Algebra R A]
variable [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]
variable (e : M ≃ₗ[R] N)
variable (A)

def baseChange_equiv : A ⊗[R] M ≃ₗ[A] A ⊗[R] N where
  toLinearMap := LinearMap.baseChange A e
  invFun := LinearMap.baseChange A e.symm
  left_inv := by
    rw [Function.leftInverse_iff_comp]
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    rw [← LinearMap.coe_comp]
    rw [← LinearMap.baseChange_comp]
    simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
      LinearMap.baseChange_id, LinearMap.id_coe]
  right_inv := by
    rw [Function.rightInverse_iff_comp]
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    rw [← LinearMap.coe_comp]
    rw [← LinearMap.baseChange_comp]
    simp only [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
      LinearMap.baseChange_id, LinearMap.id_coe]

end LinearMap
