/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández, Filippo A. E. Nuccio.
All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-! Results imported from [LocalClassFieldTheory](https://github.com/mariainesdff/LocalClassFieldTheory/tree/master)

This file contains several helper results imported from an older Lean 3 version of
[LocalClassFieldTheory](https://github.com/mariainesdff/LocalClassFieldTheory/tree/master).
Note that many of these results have been generalised to discrete valuation rings
in the latest version, but we include them here as specialisations to the `v`-adic completion
of the field of fractions of a Dedekind domain.

Links to precise commits from the old repository are included alongside each result.
Results without any links are new. -/

noncomputable section

namespace Multiplicative

/-- [https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/for_mathlib/with_zero.lean#L129](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/for_mathlib/with_zero.lean#L129)-/
theorem ofAdd_neg_one_lt_one :
    Multiplicative.ofAdd (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
  exact neg_one_lt_zero

end Multiplicative

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K] {v : HeightOneSpectrum R}

namespace HeightOneSpectrum.AdicCompletion

/-- An element `π ∈ v.adicCompletion K` is a uniformizer if it has valuation `ofAdd(-1)`.

[https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L137](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L137) -/
def IsUniformizer (π : v.adicCompletion K) : Prop :=
  Valued.v π = Multiplicative.ofAdd (-1 : ℤ)

variable (K v)

/-- Uniformizers exist in the field completion `v.adicCompletion K`.

[https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/complete.lean#L95](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/complete.lean#L95) -/
theorem exists_uniformizer :
    ∃ (π : v.adicCompletion K), IsUniformizer π := by
  obtain ⟨x, hx⟩ := valuation_exists_uniformizer K v
  refine ⟨↑x, ?_⟩
  simp only [IsUniformizer, valuedAdicCompletion_def, ← hx, Valued.extension_extends]
  rfl

variable {K v}

theorem ne_zero_iff_valuation_ne_zero (x : v.adicCompletion K) :
    x ≠ 0 ↔ Valued.v x ≠ 0 := by simp only [ne_eq, map_eq_zero]

theorem isUnit_of_valuation_eq_one {x : v.adicCompletion K} (hx : Valued.v x = 1) : IsUnit x := by
  rw [isUnit_iff_ne_zero, ne_zero_iff_valuation_ne_zero, hx]
  exact one_ne_zero

/-- A uniformizer is non-zero in `Kᵥ`. -/
theorem isUniformizer_ne_zero {π : v.adicCompletion K} (h : IsUniformizer π) :
    π ≠ 0 := by
  contrapose! h
  simp only [h, IsUniformizer, ZeroMemClass.coe_zero, map_zero, Int.reduceNeg, ofAdd_neg,
    WithZero.coe_inv, zero_eq_inv, WithZero.zero_ne_coe, not_false_eq_true]

end AdicCompletion

namespace AdicCompletionIntegers

open AdicCompletion

variable (K v)

/-- Uniformizers exist in the ring of `v`-adic integers.

[https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/complete.lean#L79](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/complete.lean#L79)-/
theorem exists_uniformizer :
    ∃ (π : v.adicCompletionIntegers K), IsUniformizer π.val := by
  obtain ⟨π, hπ⟩ := valuation_exists_uniformizer K v
  refine ⟨⟨π, ?_⟩, ?_⟩
  · simp only [mem_adicCompletionIntegers, valuedAdicCompletion_def, Valued.extension_extends]
    exact le_trans (hπ.symm ▸ (le_of_lt <| Multiplicative.ofAdd_neg_one_lt_one)) le_rfl
  · simp only [IsUniformizer, ← hπ, valuedAdicCompletion_def, Valued.extension_extends]
    rfl

variable {K v}

/-- The valuation of a unit is `1`. -/
theorem valuation_eq_one_of_isUnit {x : v.adicCompletionIntegers K} (hx : IsUnit x) :
    Valued.v x.val = 1 := by
  obtain ⟨u, hu⟩ := hx
  apply le_antisymm ((v.mem_adicCompletionIntegers K).1 x.property)
  rw [← @Valuation.map_one (v.adicCompletion K) (WithZero (Multiplicative ℤ)) _ _ Valued.v,
    ← Submonoid.coe_one, ← u.mul_inv, hu, Submonoid.coe_mul, Valued.v.map_mul]
  nth_rewrite 2 [← mul_one (Valued.v x.val)]
  exact mul_le_mul_left' ((v.mem_adicCompletionIntegers K).1 (u⁻¹.val.property)) _

/-- A `v`-adic integer with valuation `1` is a unit. -/
theorem isUnit_of_valuation_eq_one {x : v.adicCompletionIntegers K}
    (hx : Valued.v (x : v.adicCompletion K) = 1) :
    IsUnit x := by
  obtain ⟨u, hu⟩ := AdicCompletion.isUnit_of_valuation_eq_one hx
  have hu_inv_le : Valued.v u⁻¹.val ≤ 1 := by
    rw [← one_mul (Valued.v _), ← hx, ← hu, ← Valued.v.map_mul, u.mul_inv, hu, hx, Valued.v.map_one]
  let w := (⟨u.val, hu ▸ x.2⟩ : v.adicCompletionIntegers K)
  have hwx : w = x := by simp only [w, hu]
  rw [← hwx, isUnit_iff_exists]
  use ⟨u⁻¹.val, hu_inv_le⟩
  have h₁ : u * u⁻¹ = (1 : v.adicCompletion K) := by
    simp only [Units.mul_inv_eq_one]
  have h₂ : (1 : v.adicCompletionIntegers K) =
      ⟨(1 : v.adicCompletion K), (v.adicCompletionIntegers K).one_mem⟩ := rfl
  exact ⟨by simp only [h₂, ← h₁]; rfl, by simp only [h₂, ← h₁, hwx, hu, mul_comm]; rfl⟩

/-- A `v`-adic integer is a unit if and only if it has valuation `1`.

[https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L97](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L97) -/
theorem isUnit_iff_valuation_eq_one (x : v.adicCompletionIntegers K) :
    IsUnit x ↔ Valued.v x.val = 1 :=
  ⟨valuation_eq_one_of_isUnit, isUnit_of_valuation_eq_one⟩

/-- A `v`-adic integer is not a unit if and only if it has valuation `< 1`.

[https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L116](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L116)-/
theorem not_isUnit_iff_valuation_lt_one (x : v.adicCompletionIntegers K) :
    ¬IsUnit x ↔ Valued.v x.val < 1 := by
  rw [← not_le, not_iff_not, isUnit_iff_valuation_eq_one, le_antisymm_iff]
  exact and_iff_right x.2

/-- A uniformizer is non-zero in `Oᵥ`.

[https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L178](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L178)-/
theorem isUniformizer_ne_zero {π : v.adicCompletionIntegers K} (h : IsUniformizer π.val) :
    π ≠ 0 := by
  convert AdicCompletion.isUniformizer_ne_zero h
  simp only [ZeroMemClass.coe_eq_zero]

/-- A uniformizer is non-zero inside `Kᵥ`.

[https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L185](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L185)-/
theorem isUniformizer_ne_zero' {π : v.adicCompletionIntegers K} (h : IsUniformizer π.val) :
    (π : v.adicCompletion K) ≠ 0 := by
  simp only [ne_eq, ZeroMemClass.coe_eq_zero]
  exact isUniformizer_ne_zero h

/-- A uniformizer is not a unit in the `v`-adic integers.

[https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L191](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L191)-/
theorem isUniformizer_not_isUnit {π : v.adicCompletionIntegers K} (h : IsUniformizer π.val) :
    ¬IsUnit π := by
  rw [IsUniformizer] at h
  simp only [not_isUnit_iff_valuation_lt_one, h, ← WithZero.coe_one, ← ofAdd_zero,
    WithZero.coe_lt_coe, Multiplicative.ofAdd_lt, Left.neg_neg_iff, zero_lt_one]

/-- Any `v`-adic integer can be written as a unit multiplied by a power of a uniformizer.

[https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L259](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L259)-/
theorem eq_pow_uniformizer_mul_unit {x π : v.adicCompletionIntegers K} (hx : x.val ≠ 0)
    (hπ : IsUniformizer π.val) :
    ∃ (n : ℕ) (u : (v.adicCompletionIntegers K)ˣ), x = π ^ n * u := by
  let m := - Multiplicative.toAdd (WithZero.unzero <| (ne_zero_iff_valuation_ne_zero _).1 hx)
  have hm₀ : 0 ≤ m := by
    simp_rw [m, Right.nonneg_neg_iff, ← toAdd_one, Multiplicative.toAdd_le]
    rw [← WithZero.coe_le_coe]; exact (WithZero.coe_unzero _).symm ▸ x.2
  have hpow : Valued.v (π ^ (-m) * x.val) = 1 := by
    rw [Valued.v.map_mul, map_zpow₀, hπ, ofAdd_neg, WithZero.coe_inv, inv_zpow', neg_neg,
      ← WithZero.coe_zpow, ← Int.ofAdd_mul, one_mul, ofAdd_neg, ofAdd_toAdd, WithZero.coe_inv,
      WithZero.coe_unzero, inv_mul_cancel <| (ne_zero_iff_valuation_ne_zero _).1 hx]
  let a : v.adicCompletionIntegers K := ⟨π ^ (-m) * x.val, le_of_eq hpow⟩
  refine ⟨Int.toNat m, (isUnit_of_valuation_eq_one hpow : IsUnit a).unit, Subtype.ext ?_⟩
  simp only [IsUnit.unit_spec, Submonoid.coe_mul, Subsemiring.coe_toSubmonoid,
    Subring.coe_toSubsemiring, SubmonoidClass.coe_pow, zpow_neg, ← zpow_natCast,
    Int.toNat_of_nonneg hm₀, ← mul_assoc]
  rw [mul_inv_cancel (zpow_ne_zero _ <| isUniformizer_ne_zero' hπ), one_mul]

/-- A uniformizer generates the maximal ideal of the `v`-adic integers.

[https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L295](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L295)-/
theorem isUniformizer_is_generator {π : v.adicCompletionIntegers K} (hπ : IsUniformizer π.val) :
    Valued.maximalIdeal (v.adicCompletion K) = Ideal.span {π} := by
  refine (LocalRing.maximalIdeal.isMaximal _).eq_of_le
    (Ideal.span_singleton_ne_top (isUniformizer_not_isUnit hπ)) (fun x hx => ?_)
  by_cases hx₀ : x.val = 0
  · simp only [ZeroMemClass.coe_eq_zero] at hx₀
    simp only [hx₀, Ideal.zero_mem]
  · obtain ⟨n, ⟨u, hu⟩⟩ := eq_pow_uniformizer_mul_unit hx₀ hπ
    have hn : ¬(IsUnit x) := fun h =>
      (LocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ hx h)
    replace hn : n ≠ 0 := fun h => by {rw [hu, h, pow_zero, one_mul] at hn; exact hn u.isUnit}
    simpa [Ideal.mem_span_singleton, hu, IsUnit.dvd_mul_right, Units.isUnit] using dvd_pow_self _ hn

/-- The residue field of the `v`-adic integers is finite. -/
instance residueField_finite : Finite (Valued.ResidueField (v.adicCompletion K)) :=
  sorry
