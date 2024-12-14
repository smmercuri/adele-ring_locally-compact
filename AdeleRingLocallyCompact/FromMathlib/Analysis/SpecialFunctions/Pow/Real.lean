import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem Real.self_lt_rpow_of_one_lt {x y : ℝ} (h₁ : 1 < x) (h₂ : 1 < y) : x  < x ^ y := by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_lt h₁ h₂

theorem Real.rpow_lt_self_of_one_lt {x y : ℝ} (h₁ : 1 < x) (h₂ : y < 1) : x ^ y < x := by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_lt h₁ h₂

lemma Real.rpow_inv_log (hx₀ : 0 < x) (hx₁ : x ≠ 1) : x ^ (log x)⁻¹ = exp 1 := by
  rw [rpow_def_of_pos hx₀, mul_inv_cancel]
  exact log_ne_zero.2 ⟨hx₀.ne', hx₁, (hx₀.trans' <| by norm_num).ne'⟩
