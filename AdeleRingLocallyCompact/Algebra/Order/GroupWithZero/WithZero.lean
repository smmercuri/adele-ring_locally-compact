/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# Adjoining a zero to a group


-/

namespace WithZero
variable {α : Type*} [Group α] {γ : (WithZero α)ˣ}

@[simp]
theorem unitsWithZeroEquiv_units_val : γ.val = ↑(unitsWithZeroEquiv γ) := by
  simp only [WithZero.unitsWithZeroEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk, WithZero.coe_unzero]

namespace Multiplicative

variable {α : Type*} [AddGroup α] [Preorder α] [One α] {γ : (WithZero (Multiplicative α))ˣ}
theorem toAdd_le_of_units_val_le {m : (WithZero (Multiplicative α))} (hm : m ≠ 0) (hγ : γ.val ≤ m) :
    Multiplicative.toAdd (unitsWithZeroEquiv γ) ≤ Multiplicative.toAdd (m.unzero hm) := by
  rw [ ← Multiplicative.ofAdd_le, ofAdd_toAdd, ← coe_le_coe, unitsWithZeroEquiv, MulEquiv.coe_mk,
    Equiv.coe_fn_mk, coe_unzero]
  apply le_trans hγ
  rw [ofAdd_toAdd, coe_unzero]

theorem toAdd_le_one_of_units_val_le [ZeroLEOneClass α] (hγ : γ.val ≤ 1) :
    Multiplicative.toAdd (unitsWithZeroEquiv γ) ≤ 1 := by
  have := toAdd_le_of_units_val_le (one_ne_zero) hγ
  apply le_trans this
  simp only [unzero_coe, One.one, toAdd_ofAdd]
  exact zero_le_one

end Multiplicative

end WithZero
