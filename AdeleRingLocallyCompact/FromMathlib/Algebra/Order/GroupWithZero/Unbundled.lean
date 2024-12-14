import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Group.Defs

theorem one_le_pow₀ {M₀ : Type*}
    [MonoidWithZero M₀] [Preorder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀]
    (ha : 1 ≤ a) : ∀ {n : ℕ}, 1 ≤ a ^ n
  | 0 => by rw [pow_zero]
  | n + 1 => by
    simpa only [pow_succ', mul_one]
      using mul_le_mul ha (one_le_pow₀ ha) zero_le_one (zero_le_one.trans ha)
