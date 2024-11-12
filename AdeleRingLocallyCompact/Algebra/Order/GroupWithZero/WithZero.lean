/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# Adjoining a zero to a group

This file contains basic inequality results on the unit subgroup of a group with an adjoined
zero.
-/

namespace WithZero

open Multiplicative

variable {α : Type*} [Group α] {γ : (WithZero α)ˣ}

@[simp]
theorem unitsWithZeroEquiv_units_val : γ.val = ↑(unitsWithZeroEquiv γ) := by
  simp only [WithZero.unitsWithZeroEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk, WithZero.coe_unzero]

variable {α : Type*} [AddGroup α] [Preorder α] [One α] {γ : (WithZero (Multiplicative α))ˣ}
  [CovariantClass α α (fun x x_1 => x + x_1) fun x x_1 => x ≤ x_1]

theorem units_toAdd_le_of_le {m : (WithZero (Multiplicative α))} (hm : m ≠ 0) (hγ : γ.val ≤ m) :
    toAdd (unitsWithZeroEquiv γ) ≤ toAdd (m.unzero hm) := by
  rw [← ofAdd_le, ofAdd_toAdd, ← coe_le_coe, unitsWithZeroEquiv, MulEquiv.coe_mk,
    Equiv.coe_fn_mk, coe_unzero]
  apply le_trans hγ
  rw [ofAdd_toAdd, coe_unzero]

theorem units_toAdd_neg_add_of_le {m : (WithZero (Multiplicative α))} (hm : m ≠ 0)
    (hγ : γ.val ≤ m) :
    0 ≤ - toAdd (unitsWithZeroEquiv γ) + toAdd (m.unzero hm) := by
  apply le_neg_add_of_add_le
  rw [add_zero]
  exact units_toAdd_le_of_le hm hγ

theorem units_toAdd_neg_add_one [ZeroLEOneClass α] (hγ : γ.val ≤ 1) :
    0 ≤ - Multiplicative.toAdd (unitsWithZeroEquiv γ) + 1 :=
  le_trans (units_toAdd_neg_add_of_le one_ne_zero hγ) <| add_le_add_left zero_le_one _

end WithZero
