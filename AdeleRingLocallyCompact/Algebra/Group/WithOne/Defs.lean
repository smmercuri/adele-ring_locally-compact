/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio, Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio, Salvatore Mercuri
-/
import Mathlib

namespace Multiplicative

/-- [https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/for_mathlib/with_zero.lean#L129]-/
theorem ofAdd_neg_one_lt_one : Multiplicative.ofAdd (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
  exact neg_one_lt_zero

end Multiplicative
