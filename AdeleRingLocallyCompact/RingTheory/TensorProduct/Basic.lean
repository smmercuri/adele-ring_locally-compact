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
 - `Algebra.TensorProduct.rid_pi` : `A ⊗[R] (ι → R) ≃ₗ[A] (ι → A)` given by constructing a
   linear map from the basis map sending `1 ⊗ e i ↦ e i`, where `e i` is the standard basis in `Pi`.
 - `LinaraMap.baseChange_equiv` : If `e : M ≃ₗ[R] N` then this is the linear equivalence
   `A ⊗[R] M ≃ₗ[A] A ⊗[R] N` given by `LinearMap.baseChange A e`.
-/

open scoped TensorProduct

noncomputable section

namespace Algebra

namespace TensorProduct

universe uR uS uA uB uC uD uE uF

variable (R : Type uR)  (A : Type uA)
 [CommSemiring R] [Semiring A] [Algebra R A]
  (ι : Type uι) [Finite ι]

/-- Constructive _linear_ right identity for the tensor product of an algebra with a finite product of
commutative rings.

This is the linear map which sends the standard basis `1 ⊗ e i` to `e i`.-/
def rid_pi_linearEquiv :
  A ⊗[R] (ι → R) ≃ₗ[A] (ι → A)
  := Basis.equiv (Algebra.TensorProduct.basis A (Pi.basisFun R ι)) (Pi.basisFun A ι) (Equiv.refl ι)

end TensorProduct

end Algebra

namespace LinearMap

variable {R A M N : Type*} [CommSemiring R] [Semiring A]
  [Algebra R A] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  [Module R N]
variable (e : M ≃ₗ[R] N)
variable (A)

/-- The base change equivalence `A ⊗[R] M ≃ₗ[A] A ⊗[R] N` induced by the linear equivalance `e : M ≃ₗ[R] N`.-/
def baseChange_equiv : A ⊗[R] M ≃ₗ[A] A ⊗[R] N where
  toLinearMap := LinearMap.baseChange A e
  invFun := LinearMap.baseChange A e.symm
  left_inv := by
    simp only [Function.leftInverse_iff_comp, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      ← LinearMap.coe_comp, ← LinearMap.baseChange_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.baseChange_id, LinearMap.id_coe]
  right_inv := by
    simp only [Function.rightInverse_iff_comp, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
    ← LinearMap.coe_comp, ← LinearMap.baseChange_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
    LinearEquiv.refl_toLinearMap, LinearMap.baseChange_id, LinearMap.id_coe]

end LinearMap
