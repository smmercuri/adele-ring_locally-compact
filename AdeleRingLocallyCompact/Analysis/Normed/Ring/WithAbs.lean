/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Completion

/-!
# WithAbs

`WithAbs v` is a type synonym for a semiring `R` which depends on an absolute value. The point of
this is to allow the type class inference system to handle multiple sources of instances that
arise from absolute values. See `NumberTheory.NumberField.Completion` for an example of this
being used to define Archimedean completions of a number field.

## Main definitions
 - `WithAbs` : type synonym for a semiring which depends on an absolute value. This is
  a function that takes an absolute value on a semiring and returns the semiring. This can be used
  to assign and infer instances on a semiring that depend on absolute values.
 - `WithAbs.equiv v` : the canonical (type) equivalence between `WithAbs v` and `R`.
 - `WithAbs.ringEquiv v` : The canonical ring equivalence between `WithAbs v` and `R`.
 - `AbsoluteValue.Completion` : the uniform space completion of a field `K` according to the
  uniform structure defined by the specified real absolute value.
-/

variable {R S K : Type*} [Semiring R] [OrderedSemiring S] [Field K]

/-- Type synonym for a semiring which depends on an absolute value. This is a function that takes
an absolute value on a semiring and returns the semiring. We use this to assign and infer instances
on a semiring that depend on absolute values. -/
@[nolint unusedArguments]
def WithAbs : AbsoluteValue R S → Type _ := fun _ => R

namespace WithAbs

variable (v : AbsoluteValue R ℝ)

/-- Canonical equivalence between `WithAbs v` and `R`. -/
def equiv : WithAbs v ≃ R := Equiv.refl (WithAbs v)

instance instNonTrivial [Nontrivial R] : Nontrivial (WithAbs v) := inferInstanceAs (Nontrivial R)

instance instUnique [Unique R] : Unique (WithAbs v) := inferInstanceAs (Unique R)

instance instSemiring : Semiring (WithAbs v) := inferInstanceAs (Semiring R)

instance instRing [Ring R] : Ring (WithAbs v) := inferInstanceAs (Ring R)

instance instInhabited : Inhabited (WithAbs v) := ⟨0⟩

noncomputable instance {R : Type*} [Ring R] (v : AbsoluteValue R ℝ): NormedRing (WithAbs v) where
  norm := v
  dist_eq _ _ := rfl
  dist_self x := by simp only [sub_self, MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom, map_zero]
  dist_comm := v.map_sub
  dist_triangle := v.sub_le
  edist_dist x y := rfl
  norm_mul x y := (v.map_mul x y).le
  eq_of_dist_eq_zero := by simp only [MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom,
    AbsoluteValue.map_sub_eq_zero_iff, imp_self, implies_true]

noncomputable instance normedField {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    NormedField (WithAbs v) where
  toField := inferInstanceAs (Field K)
  __ := instNormedRingReal v
  norm_mul' := v.map_mul

/-! `WithAbs.equiv` preserves the ring structure. -/

variable (x y : WithAbs v) (r s : R)
@[simp]
theorem equiv_zero : WithAbs.equiv v 0 = 0 := rfl

@[simp]
theorem equiv_symm_zero : (WithAbs.equiv v).symm 0 = 0 := rfl

@[simp]
theorem equiv_add : WithAbs.equiv v (x + y) = WithAbs.equiv v x + WithAbs.equiv v y := rfl

@[simp]
theorem equiv_symm_add :
    (WithAbs.equiv v).symm (r + s) = (WithAbs.equiv v).symm r + (WithAbs.equiv v).symm s :=
  rfl

@[simp]
theorem equiv_sub [Ring R] : WithAbs.equiv v (x - y) = WithAbs.equiv v x - WithAbs.equiv v y := rfl

@[simp]
theorem equiv_symm_sub [Ring R] :
    (WithAbs.equiv v).symm (r - s) = (WithAbs.equiv v).symm r - (WithAbs.equiv v).symm s :=
  rfl

@[simp]
theorem equiv_neg [Ring R] : WithAbs.equiv v (-x) = - WithAbs.equiv v x := rfl

@[simp]
theorem equiv_symm_neg [Ring R] : (WithAbs.equiv v).symm (-r) = - (WithAbs.equiv v).symm r := rfl

@[simp]
theorem equiv_mul : WithAbs.equiv v (x * y) = WithAbs.equiv v x * WithAbs.equiv v y := rfl

@[simp]
theorem equiv_symm_mul :
    (WithAbs.equiv v).symm (x * y) = (WithAbs.equiv v).symm x * (WithAbs.equiv v).symm y :=
  rfl

/-- `WithAbs.equiv` as a ring equivalence. -/
def ringEquiv : WithAbs v ≃+* R := RingEquiv.refl _

/-! The completion of a field at an absolute value. -/

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
  {L : Type*} [NormedField L] {f : WithAbs v →+* L}

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
`f` is an isometry. -/
theorem isometry_of_comp (h : ∀ x, ‖f x‖ = v x) : Isometry f :=
  Isometry.of_dist_eq <| fun x y => by simp only [‹NormedField L›.dist_eq, ← f.map_sub, h]; rfl

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
the pseudo metric space associated to the absolute value is the same as the pseudo metric space
induced by `f`. -/
theorem pseudoMetricSpace_induced_of_comp (h : ∀ x, ‖f x‖ = v x) :
    PseudoMetricSpace.induced f inferInstance = (normedField v).toPseudoMetricSpace := by
  ext; exact isometry_of_comp h |>.dist_eq _ _

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
the uniform structure associated to the absolute value is the same as the uniform structure
induced by `f`. -/
theorem uniformSpace_comap_eq_of_comp (h : ∀ x, ‖f x‖ = v x) :
    UniformSpace.comap f inferInstance = (normedField v).toUniformSpace := by
  simp only [← pseudoMetricSpace_induced_of_comp h, PseudoMetricSpace.toUniformSpace]

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
`f` is uniform inducing. -/
theorem uniformInducing_of_comp (h : ∀ x, ‖f x‖ = v x) : UniformInducing f :=
  uniformInducing_iff_uniformSpace.2 <| uniformSpace_comap_eq_of_comp h

instance {L : Type*} [Field L] [Algebra K L] (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) :
    Algebra (WithAbs v) (WithAbs w) :=
  inferInstanceAs (Algebra K L)

instance {w : AbsoluteValue L ℝ} [Algebra K L] : Algebra K (WithAbs w) := ‹Algebra K L›

theorem norm_eq (v : AbsoluteValue K ℝ) (x : WithAbs v) : ‖x‖ = v x := rfl

theorem uniformContinuous_algebraMap {L : Type*} [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v x) :
    UniformContinuous (algebraMap (WithAbs v) (WithAbs w)) :=
  (uniformInducing_of_comp (L := WithAbs w) h).uniformContinuous

end WithAbs
