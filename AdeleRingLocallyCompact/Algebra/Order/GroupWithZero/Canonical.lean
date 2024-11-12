/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# Linearly ordered commutative groups and monoids with a zero element adjoined

In this file we provide some basic inequality results for groups with zero.
-/

variable {α : Type*} [LinearOrderedCommGroupWithZero α] {a b c d : α} {m n : ℕ}

theorem mul_inv_lt_iff₀ (hc : c ≠ 0) : a * c⁻¹ < b ↔ a < b * c := by
  refine ⟨fun h ↦ ?_, mul_inv_lt_of_lt_mul₀⟩
  have := mul_lt_mul_of_lt_of_le₀ le_rfl hc h
  rwa [mul_comm a c⁻¹, ← mul_assoc, mul_inv_cancel hc, one_mul, mul_comm c b] at this

theorem inv_mul_lt_iff₀ (hc : c ≠ 0) : c⁻¹ * a < b ↔ a < b * c :=
  mul_comm c⁻¹ a ▸ mul_inv_lt_iff₀ hc

theorem inv_mul_lt_one_iff₀ (hc : c ≠ 0) : c⁻¹ * a < 1 ↔ a < c := by
  nth_rewrite 2 [← one_mul c]
  exact inv_mul_lt_iff₀ hc
