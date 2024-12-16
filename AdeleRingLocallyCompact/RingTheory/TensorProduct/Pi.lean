import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.TensorProduct.Basic
import AdeleRingLocallyCompact.FromMathlib.LinearAlgebra.TensorProduct.Pi
import AdeleRingLocallyCompact.Topology.Algebra.Algebra

open scoped TensorProduct

noncomputable section

def Algebra.TensorProduct.piRight (R S A : Type*) {ι : Type*}  (B : ι → Type*) [CommSemiring R]
    [CommSemiring S] [Algebra R S] [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [(i : ι) → Semiring (B i)] [(i : ι) → Algebra R (B i)] [Fintype ι] [DecidableEq ι] :
    A ⊗[R] ((i : ι) → B i) ≃ₐ[S] (i : ι) → A ⊗[R] (B i) := by
  set f : @LinearEquiv S S _ _ _ _ _ _ _ ((i : ι) → A ⊗[R] B i) _
      NonUnitalNonAssocSemiring.toAddCommMonoid _ Algebra.toModule :=
        (_root_.TensorProduct.piRight R S A B)
  apply Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct f
  · intro a₁ a₂ b₁ b₂
    simp only [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, f]
    simp_rw [Pi.mul_apply]
    rw [Pi.mul_def]
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul]
  · rfl

def Algebra.TensorProduct.piLeft (R A : Type*) {ι : Type*}  (B : ι → Type*) [CommSemiring R]
    [Semiring A] [Algebra R A]
    [(i : ι) → Semiring (B i)] [(i : ι) → Algebra R (B i)]
    [Fintype ι] [DecidableEq ι] :
    ((i : ι) → B i) ⊗[R] A ≃ₐ[R] (i : ι) → B i ⊗[R] A :=
  (Algebra.TensorProduct.comm _ _ _).trans <| (piRight _ _ _ _).trans
    <| AlgEquiv.piCongrRight <| fun _ => Algebra.TensorProduct.comm _ _ _

def Algebra.TensorProduct.piLeftContinuousAlgEquiv (R A : Type*) {ι : Type*}  (B : ι → Type*)
    [CommSemiring R] [Semiring A] [Algebra R A]
    [(i : ι) → Semiring (B i)] [(i : ι) → Algebra R (B i)]
    [(i : ι) → TopologicalSpace (B i ⊗[R] A)]
    [Fintype ι] [DecidableEq ι] :
    letI : TopologicalSpace (((i : ι) → B i) ⊗[R] A) :=
      TopologicalSpace.induced (piLeft R A B) inferInstance
    ((i : ι) → B i) ⊗[R] A ≃A[R] (i : ι) → B i ⊗[R] A :=
  letI : TopologicalSpace (((i : ι) → B i) ⊗[R] A) :=
    TopologicalSpace.induced (piLeft R A B) inferInstance
  {
    __ := piLeft R A B
    continuous_toFun := continuous_induced_dom
    continuous_invFun := by
      convert (Algebra.TensorProduct.piLeft R A B).toEquiv.coinduced_symm ▸ continuous_coinduced_rng
  }
