/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib
import AdeleRingLocallyCompact.Algebra.Group.WithOne.Defs
import AdeleRingLocallyCompact.Algebra.Order.GroupWithZero.WithZero
import AdeleRingLocallyCompact.RingTheory.Ideal.Quotient
import AdeleRingLocallyCompact.Topology.Compactness.LocallyCompact

set_option linter.longLine false
/-!
# Adic valuations on Dedekind domains

Let `R` be a Dedekind domain of Krull dimension 1, `K` its field of fractions and `v`
a maximal ideal of `R`. In this file we prove compactness results for the `v`-adic
completion of `K` and its ring of integers.

We import required Lean 3 results from the work of María Inés de Frutos-Fernández
and Filippo A. E. Nuccio concerning the uniformizers of the ring of integers and
the finiteness of its residue field, which are
referenced appropriately in the docstrings.

Note that one of the main results is not proved here, since the proof is already
given elsewhere in Lean 3 by María Inés de Frutos-Fernández, Filippo A. E. Nuccio
in [https://github.com/mariainesdff/local_fields_journal/](https://github.com/mariainesdff/local_fields_journal/).

## Main definitions
 - `IsDedekindDomain.HeightOneSpectrum.AdicCompletionIntegers.ofFiniteCoeffs π n`
   constructs a `v`-adic integer from an `n`-tuple of `v`-adic integers by using
   them as coefficients in a finite `v`-adic expansionin the uniformizer `π`.
 - `IsDedekindDomain.HeightOneSpectrum.AdicCompletionIntegers.toFiniteCoeffs π n`
   gives the first `n` coefficients in the `v`-adic expansion in `π` of a `v`-adic
   integer modulo the `n`th power of the maximal ideal.

## Main results
 - `IsDedekindDomain.HeightOneSpectrum.AdicCompletionIntegers.residueField_finite` : the
   residue field of the `v`-adic ring of integers is finite.
 - `IsDedekindDomain.HeightOneSpectrum.AdicCompletionIntegers.quotient_maximalIdeal_pow_finite` :
   the quotient of the `v`-adic ring of integers by a power of the maximal ideal is finite.
 - `IsDedekindDomain.HeightOneSpectrum.AdicCompletionIntegers.isCompact` : the `v`-adic ring
   of integers is compact.
 - `IsDedekindDomain.HeightOneSpectrum.locallyCompactSpace` : the `v`-adic Completion of `K`
   is locally compact.

## References
 * [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
 * [M.I. de Frutos-Fernández, F.A.E. Nuccio, *A Formalization of Complete Discrete Valuation Rings and Local Fields*][defrutosfernandez2023]

## Tags
dedekind domain, dedekind ring, adic valuation
-/

noncomputable section

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K] {v : HeightOneSpectrum R}

namespace HeightOneSpectrum

variable (K)

theorem algebraMap_valuation_ne_zero (v : HeightOneSpectrum R) (r : nonZeroDivisors R) :
    Valued.v (algebraMap _ (v.adicCompletion K) r.val) ≠ 0 := by
  rw [v.valuedAdicCompletion_eq_valuation, ne_eq, map_eq_zero, IsFractionRing.to_map_eq_zero_iff]
  exact nonZeroDivisors.coe_ne_zero _

local notation "μᵥ" => @WithZero.unitsWithZeroEquiv (Multiplicative ℤ)

namespace AdicCompletion

variable {K}

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

/-- Open balls at zero are open in the `v`-adic completion of `K`. -/
theorem isOpen_nhds_zero (γ : (WithZero (Multiplicative ℤ))ˣ) :
    IsOpen ({ y : v.adicCompletion K | Valued.v y < γ }) := by
  refine isOpen_iff_mem_nhds.2 (fun x hx => Valued.mem_nhds.2 ⟨γ, fun y hy => ?_⟩)
  rw [← sub_add_cancel y x]
  rw [Set.mem_setOf_eq] at hy
  exact lt_of_le_of_lt (Valued.v.map_add (y - x) x) (max_lt hy hx)

open Valued Set in
/-- Open balls at zero are closed in the `v`-adic completion of `K`. -/
theorem isClosed_nhds_zero (γ : (WithZero (Multiplicative ℤ))ˣ) :
    IsClosed ({ y : v.adicCompletion K | Valued.v y < γ }) := by
  refine isClosed_iff_nhds.2 fun x hx => ?_
  simp only [Set.mem_setOf_eq] at hx ⊢
  contrapose! hx
  have h : Valued.v x ≠ 0 := by contrapose! hx; simp only [hx, Units.zero_lt]
  refine ⟨{y | Valued.v y = Valued.v x}, loc_const h, subset_empty_iff.1 fun y hy => ?_⟩
  exact (not_le_of_lt <| mem_setOf.1 hy.2) <| hy.1.symm ▸ hx

variable {K v}

open WithZero in

theorem valuation_lt_one_mul_isUniformizer_pow_of_nhds_zero {γ : (WithZero (Multiplicative ℤ))ˣ}
    {x π : v.adicCompletion K} (hx : x ∈ { y : v.adicCompletion K | Valued.v y < γ })
    (hπ : IsUniformizer π) :
    Valued.v (π ^ (Multiplicative.toAdd (μᵥ γ)) * x) < 1 := by
  rw [Valued.v.map_mul, map_zpow₀, hπ, (Units.inv_mul' γ).symm]
  apply mul_lt_mul_of_lt_of_le₀ _ (inv_ne_zero γ.ne_zero) hx
  rw [ofAdd_neg, coe_inv, inv_zpow', zpow_neg, unitsWithZeroEquiv_units_val, ← coe_inv,
    ← coe_zpow, ← coe_inv, coe_le_coe, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]

/-- A uniformizer is non-zero in `Kᵥ`. -/
theorem isUniformizer_ne_zero {π : v.adicCompletion K} (h : IsUniformizer π) :
    π ≠ 0 := by
  contrapose! h
  simp only [h, IsUniformizer, ZeroMemClass.coe_zero, map_zero, Int.reduceNeg, ofAdd_neg,
    WithZero.coe_inv, zero_eq_inv, WithZero.zero_ne_coe, not_false_eq_true]

theorem valuation_lt_one_of_preimage_mul_isUniformizer_neg_pow {γ : (WithZero (Multiplicative ℤ))ˣ}
    {x π : v.adicCompletion K}
    (hπ : IsUniformizer π)
    (hx : π ^ (- Multiplicative.toAdd (μᵥ γ)) * x ∈ { y : v.adicCompletion K | Valued.v y < γ }) :
    Valued.v x < 1 := by
  convert valuation_lt_one_mul_isUniformizer_pow_of_nhds_zero hx hπ
  rw [← mul_assoc, ← zpow_add₀ <| isUniformizer_ne_zero hπ, add_right_neg, zpow_zero,
    one_mul]

open WithZero in
theorem image_mul_isUniformizer_neg_pow_of_maximalIdeal {γ : (WithZero (Multiplicative ℤ))ˣ}
    {x π : v.adicCompletion K}
    (hπ : IsUniformizer π)
    (hx : Valued.v x < 1) :
    π ^ (- Multiplicative.toAdd (μᵥ γ)) * x ∈ { y : v.adicCompletion K | Valued.v y < γ } := by
  rw [Set.mem_setOf_eq, Valued.v.map_mul, map_zpow₀, hπ, (show γ.val = γ.val * 1 by rw [mul_one])]
  apply mul_lt_mul_of_lt_of_le₀ ?_ γ.ne_zero hx
  simp only [ofAdd_neg, coe_inv, inv_zpow', zpow_neg, unitsWithZeroEquiv_units_val,
    ← coe_zpow, ← coe_inv, coe_le_coe, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_neg, ofAdd_toAdd,
    inv_inv, le_refl]

theorem hasBasis_nhds_zero : (nhds (0 : v.adicCompletion K)).HasBasis
    (fun (γ : (WithZero (Multiplicative ℤ))ˣ) => γ ≤ 1)
    (fun γ => { x : v.adicCompletion K | Valued.v x < γ }) := by
  have hq : ∀ (γ : (WithZero (Multiplicative ℤ))ˣ), True →
    ∃ (γ' : (WithZero (Multiplicative ℤ))ˣ), True ∧ γ' ≤ 1 ∧
      { x : v.adicCompletion K | Valued.v x < γ' } ⊆
        { x : v.adicCompletion K | Valued.v x < γ } := by
    intro γ _
    choose π _ using exists_uniformizer K v
    by_cases hγ : 1 < γ
    · exact ⟨1, trivial, le_refl _, fun _ hx => lt_trans (Set.mem_setOf.1 hx) hγ⟩
    · exact ⟨γ, trivial, not_lt.1 hγ, subset_rfl⟩
  convert (Valued.hasBasis_nhds_zero (v.adicCompletion K) (WithZero (Multiplicative ℤ))).restrict hq
  simp only [true_and]

/-- Neighbourhoods of zero can be shrunk to radius `< 1` by multiplying by an appropriate
power of a uniformizer. -/
theorem preimage_mul_left_pow_uniformizer_nhds_zero {π : v.adicCompletion K}
    (hπ : IsUniformizer π) (γ : (WithZero (Multiplicative ℤ))ˣ) :
    (fun y => π ^ (- Multiplicative.toAdd (μᵥ γ)) * y) ⁻¹'
      { y : v.adicCompletion K | Valued.v y < γ } = { y : v.adicCompletion K | Valued.v y < 1 } :=
  Set.ext (fun _ => ⟨valuation_lt_one_of_preimage_mul_isUniformizer_neg_pow hπ,
    image_mul_isUniformizer_neg_pow_of_maximalIdeal hπ⟩)

open WithZero in
/-- Given an integer `γ` and some centre `y ∈ Kᵥ` we can always find an element `x ∈ Kᵥ`
outide of the open ball at `y` of radius `γ`. -/
theorem exists_not_mem_of_nhds_zero
    (γ : (WithZero (Multiplicative ℤ))ˣ) (y : v.adicCompletion K) :
    ∃ x : v.adicCompletion K, Valued.v (x - y) > γ := by
  choose p hp using @valuation_exists_uniformizer R _ _ K _ _ _ v
  use p ^ (- Multiplicative.toAdd (μᵥ γ) - 1) + y
  simp only [add_sub_cancel_right, unitsWithZeroEquiv_units_val, map_zpow₀,
    Valued.valuedCompletion_apply, v.adicValued_apply, hp, gt_iff_lt, ← coe_zpow, coe_lt_coe,
    ← Multiplicative.toAdd_lt, ofAdd_neg, inv_zpow', neg_sub, sub_neg_eq_add, toAdd_zpow,
    toAdd_ofAdd, smul_eq_mul, mul_one, lt_add_iff_pos_left, zero_lt_one]

theorem ne_zero_iff_valuation_ne_zero (x : v.adicCompletion K) :
    x ≠ 0 ↔ Valued.v x ≠ 0 := by simp only [ne_eq, map_eq_zero]

theorem isUnit_of_valuation_eq_one {x : v.adicCompletion K} (hx : Valued.v x = 1) : IsUnit x := by
  rw [isUnit_iff_ne_zero, ne_zero_iff_valuation_ne_zero, hx]
  exact one_ne_zero

/-- If `x ∈ Kᵥ` has valuation at most that of `y ∈ Kᵥ`, then `x` is an integral
multiple of `y`. -/
theorem dvd_of_valued_le
    {x y : v.adicCompletion K} (h : Valued.v x ≤ Valued.v y) (hy : y ≠ 0):
    ∃ r : v.adicCompletionIntegers K, r * y = x := by
  have : Valued.v (x * y⁻¹) ≤ 1 := by
    rwa [Valued.v.map_mul, map_inv₀, mul_inv_le_iff₀ ((map_ne_zero _).2 hy), one_mul]
  exact ⟨⟨x * y⁻¹, this⟩, by rw [inv_mul_cancel_right₀ hy]⟩

end AdicCompletion

namespace AdicCompletionIntegers

open AdicCompletion

variable (v)

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

/-- A `v`-adic integer is a unit if and only if it has valuation `1`. -/
theorem isUnit_iff_valuation_eq_one (x : v.adicCompletionIntegers K) :
    IsUnit x ↔ Valued.v x.val = 1 :=
  ⟨valuation_eq_one_of_isUnit, isUnit_of_valuation_eq_one⟩

/-- A `v`-adic integer is not a unit if and only if it has valuation `< 1`.

[https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L116](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L116)-/
theorem not_isUnit_iff_valuation_lt_one (x : v.adicCompletionIntegers K) :
    ¬IsUnit x ↔ Valued.v x.val < 1 := by
  rw [← not_le, not_iff_not, isUnit_iff_valuation_eq_one, le_antisymm_iff]
  exact and_iff_right x.2

/-- A uniformizer is non-zero in `Oᵥ`. -/
theorem isUniformizer_ne_zero {π : v.adicCompletionIntegers K} (h : IsUniformizer π.val) :
    π ≠ 0 := by
  convert AdicCompletion.isUniformizer_ne_zero h
  simp only [ZeroMemClass.coe_eq_zero]

/-- A uniformizer is non-zero inside `Kᵥ`. -/
theorem isUniformizer_ne_zero' {π : v.adicCompletionIntegers K} (h : IsUniformizer π.val) :
    (π : v.adicCompletion K) ≠ 0 := by
  simp only [ne_eq, ZeroMemClass.coe_eq_zero]
  exact isUniformizer_ne_zero h

theorem isUniformizer_ne_zero_zpow' {π : v.adicCompletionIntegers K} (h : IsUniformizer π.val)
    (n : ℤ) :
    (π : v.adicCompletion K) ^ n ≠ 0 :=
  zpow_ne_zero n <| isUniformizer_ne_zero' h

/-- A uniformizer is not a unit in the `v`-adic integers. -/
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

/-- An element of the maximal ideal of the `v`-adic integers has valuation less than `1`. -/
theorem valuation_lt_one_of_maximalIdeal {x : Valued.integer (v.adicCompletion K)}
    (hx : x ∈ Valued.maximalIdeal (v.adicCompletion K)) :
    Valued.v (x : v.adicCompletion K) < 1 := by
  rw [Valued.maximalIdeal, LocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
  contrapose! hx
  exact isUnit_of_valuation_eq_one (le_antisymm x.property hx)

/-- An element of a positive power `n` of the maximal ideal of the `v`-adic integers has
valuation less than or equal to `-n`. -/
theorem valuation_le_pow_of_maximalIdeal {x : v.adicCompletionIntegers K} (n : ℕ)
    (hx : x ∈ Valued.maximalIdeal (v.adicCompletion K) ^ n) :
    Valued.v (x : v.adicCompletion K) ≤ Multiplicative.ofAdd (-n : ℤ) := by
  by_cases hn : n = 0
  · simp only [hn, pow_zero, Ideal.one_eq_top, Submodule.mem_top, CharP.cast_eq_zero, neg_zero,
      ofAdd_zero, WithZero.coe_one, forall_true_left];
    exact x.property
  · obtain ⟨π, hπ⟩ := exists_uniformizer K v
    rw [isUniformizer_is_generator hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨y, hxy⟩ := hx
    rw [hxy, Subring.coe_mul, Valued.v.map_mul, Subring.coe_pow, Valued.v.map_pow]
    have h_mul_le_mul :
      Valued.v (π : v.adicCompletion K) ^ n * Valued.v (y : v.adicCompletion K)
        ≤ Valued.v (π : v.adicCompletion K) ^ n * 1 := by
      apply (mul_le_mul_left₀ _).2 ((v.mem_adicCompletionIntegers _ _).1 y.2)
      exact (pow_ne_zero_iff hn).2 <| Valued.v.ne_zero_iff.2 <| isUniformizer_ne_zero' hπ
    apply le_trans h_mul_le_mul
    rw [mul_one, hπ, ← WithZero.coe_pow, WithZero.coe_le_coe, ofAdd_neg, ofAdd_neg, inv_pow,
      inv_le_inv_iff, ← one_mul (n : ℤ), Int.ofAdd_mul, zpow_natCast]

/-- The residue field of the `v`-adic integers is finite. -/
instance residueField_finite : Finite (Valued.ResidueField (v.adicCompletion K)) :=
  sorry

/-- Takes an `n`-tuple `(a₁, ..., aₙ)` and creates a `v`-adic integer using the `n`-tuple as
coefficients in a finite `v`-adic expansion in some fixed `v`-adic integer `π` as
`a₁ + a₂π + a₃π² + ...`. Note the definition does not require `π` to be a uniformizer. -/
def ofFiniteCoeffs (π : v.adicCompletionIntegers K) (n : ℕ) :
    (Fin n → v.adicCompletionIntegers K) → v.adicCompletionIntegers K :=
  fun x => ((List.ofFn x).mapIdx (fun i j => j * π^i)).sum

/-- Given a uniformizer `π` of the `v`-adic integers and a `v`-adic integer `x`, there exists
an `n`-tuple of representatives in the residue field of the `v`-adic integers such that `x` can
be written as a finite `v`-adic expansion in `π` with coefficients given by the `n`-tuple. -/
theorem finite_expansion {π : v.adicCompletionIntegers K} (n : ℕ) (x : v.adicCompletionIntegers K)
    (hπ : IsUniformizer π.val) :
    ∃ (a : Fin n → Valued.ResidueField (v.adicCompletion K)),
      x - ((List.ofFn a).mapIdx (fun i j => (Quotient.out' j) * π^i)).sum ∈
        Valued.maximalIdeal (v.adicCompletion K) ^ n := by
  induction n with
  | zero =>
    simp only [Nat.zero_eq, List.ofFn_zero, List.mapIdx_nil, List.sum_nil, pow_zero,
        Ideal.one_eq_top, Submodule.mem_top, exists_const]
  | succ d hd =>
    obtain ⟨b, hbx⟩ := hd
    rw [isUniformizer_is_generator hπ, Ideal.span_singleton_pow] at hbx ⊢
    rw [Ideal.mem_span_singleton'] at hbx
    obtain ⟨⟨z, h_int⟩, hz⟩ := hbx
    rw [mem_adicCompletionIntegers] at h_int
    set w : Valued.integer (v.adicCompletion K) := ⟨z, h_int⟩
    use Fin.snoc b (Ideal.Quotient.mk _ w)
    rw [List.ofFn_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append,
      List.mapIdx_append, List.length_ofFn, List.mapIdx_cons, zero_add, List.mapIdx_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    rw [← @sub_sub _ (inferInstanceAs (SubtractionCommMonoid (v.adicCompletionIntegers K))),
      ← hz, ← sub_mul, Ideal.mem_span_singleton, pow_succ, mul_comm]
    have h : π ∣ w - Quotient.out' (Ideal.Quotient.mk (Valued.maximalIdeal (v.adicCompletion K)) w) := by
      rw [← Ideal.Quotient.eq_zero_iff_dvd, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq,
        isUniformizer_is_generator hπ, Ideal.Quotient.mk_out']
      rfl
    exact mul_dvd_mul_right h (π ^ d)

/-- Given a uniformizer `π` of the `v`-adic integers and a `v`-adic integer `x` modulo a power of
the maximal ideal, gives the coefficients of `x` in the finite `v`-adic expansion in `π` as an
`n`-tuple of representatives in the residue field.
-/
def toFiniteCoeffs {π : v.adicCompletionIntegers K} (n : ℕ) (hπ : IsUniformizer π.val) :
    v.adicCompletionIntegers K ⧸ (Valued.maximalIdeal (v.adicCompletion K)) ^ n
      → (Fin n → Valued.ResidueField (v.adicCompletion K)) :=
  fun x => (Classical.choose (finite_expansion n (Quotient.out' x) hπ))

theorem toFiniteCoeffs_injective {π : v.adicCompletionIntegers K}
    (n : ℕ) (hπ : IsUniformizer π.val) :
    (toFiniteCoeffs n hπ).Injective := by
  intro x y hxy
  simp only [toFiniteCoeffs] at hxy
  let b := Classical.choose (finite_expansion n (Quotient.out' y) hπ)
  have hx := Classical.choose_spec (finite_expansion n (Quotient.out' x) hπ)
  have hy := Classical.choose_spec (finite_expansion n (Quotient.out' y) hπ)
  rw [hxy] at hx
  rw [← Quotient.out_eq' x, ← Quotient.out_eq' y,  ← sub_eq_zero]
  simp only [Submodule.Quotient.mk''_eq_mk, ← @Submodule.Quotient.mk_sub _ _ _ _ _
    (inferInstanceAs (AddCommGroup (v.adicCompletionIntegers K))), Submodule.Quotient.mk_eq_zero]
  rw [← sub_sub_sub_cancel_right _ _
      (List.sum (List.mapIdx (fun i j => Quotient.out' j * π ^ i) (List.ofFn b)))]
  exact Ideal.sub_mem _ hx hy

/-- The quotient of the `v`-adic integers with a power of the maximal ideal is finite. -/
instance quotient_maximalIdeal_pow_finite {π : v.adicCompletionIntegers K} (n : ℕ)
    (hπ : IsUniformizer π.val) :
    Finite (v.adicCompletionIntegers K ⧸ (Valued.maximalIdeal (v.adicCompletion K)) ^ n) :=
  Finite.of_injective _ (toFiniteCoeffs_injective n hπ)

variable (K v)

open Set Valued in
/-- The `v`-adic integers are closed in the `v`-adic completion of `K`. -/
theorem isClosed : IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  refine isClosed_iff_nhds.2 fun x hx => ?_
  simp only [isClosed_iff_nhds, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
    not_le] at hx ⊢
  contrapose! hx
  refine ⟨{y | Valued.v y = Valued.v x}, loc_const (ne_zero_of_lt hx),
    subset_empty_iff.1 fun y ⟨hy₁, hy₂⟩ => ?_⟩
  rw [SetLike.mem_coe, mem_adicCompletionIntegers] at hy₂
  exact (not_lt_of_le <| hy₂) <| hy₁.symm ▸ hx

/-- There is a finite covering of the `v`-adic integers of open balls of radius larger than one,
namely the single open ball centred at `0`. -/
theorem finite_subcover_of_nhds_zero_one_lt {γ : (WithZero (Multiplicative ℤ))ˣ} (hγ : 1 < γ.val) :
    ∃ t : Set (v.adicCompletion K), Set.Finite t ∧
      ↑(adicCompletionIntegers K v) ⊆ ⋃ y ∈ t,
        {x | (x, y) ∈ {p | Valued.v (p.2 - p.1) < γ.val}} := by
  refine ⟨{0}, Set.finite_singleton _, fun x hx => ?_⟩
  simp only [Set.mem_singleton_iff, Set.mem_setOf_eq, Set.iUnion_iUnion_eq_left, zero_sub,
    Valuation.map_neg]
  exact lt_of_le_of_lt hx hγ

open WithZero in
/-- There is a finite covering of the `v`-adic integers of open balls of radius less than one,
obtained by using the finite representatives in the quotient of the `v`-adic integers by an
appropriate power of the maximal ideal. -/
theorem finite_subcover_of_nhds_zero_le_one {γ : (WithZero (Multiplicative ℤ))ˣ} (hγ : γ.val ≤ 1) :
    ∃ t : Set (v.adicCompletion K), Set.Finite t ∧
      ↑(adicCompletionIntegers K v) ⊆ ⋃ y ∈ t,
        {x | (x, y) ∈ {p | Valued.v (p.2 - p.1) < γ.val}} := by
  let μ := μᵥ γ
  have hμ : γ.val = (μ : WithZero (Multiplicative ℤ)) := by
    simp only [μ, unitsWithZeroEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk, coe_unzero]
  let M := (Valued.maximalIdeal (v.adicCompletion K))^((-Multiplicative.toAdd μ + 1).toNat)
  let S := (v.adicCompletionIntegers K) ⧸ M
  let q := Ideal.Quotient.mk M
  obtain ⟨π, hπ⟩ := exists_uniformizer K v
  letI := quotient_maximalIdeal_pow_finite (-Multiplicative.toAdd μ + 1).toNat hπ
  have h : Fintype S := Fintype.ofFinite _
  let T := Quotient.out' '' (h.elems.toSet)
  refine ⟨T, (Set.Finite.image Subtype.val (Set.Finite.image Quotient.out'
    (Finset.finite_toSet h.elems))), fun x hx => ?_⟩
  simp only [Set.mem_iUnion]
  let y := (Quotient.out' (q ⟨x, hx⟩))
  have h_out_mk_mem : Subtype.val (Quotient.out' (q ⟨x, hx⟩)) ∈ Subtype.val '' T :=
    ⟨y, ⟨Set.mem_image_of_mem _ (Finset.mem_coe.2 (h.complete _)), rfl⟩⟩
  have h_sub_zero : y - ⟨x, hx⟩ ∈ M := by
    rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out']
  refine ⟨y, h_out_mk_mem, lt_of_le_of_lt (valuation_le_pow_of_maximalIdeal _ h_sub_zero) ?_⟩
  rw [hμ, coe_lt_coe, ← ofAdd_toAdd μ, Multiplicative.ofAdd_lt, ofAdd_toAdd]
  have h_nonneg : 0 ≤ - (Multiplicative.toAdd μ) + 1 := by
    rw [le_neg_add_iff_add_le, add_zero]
    exact Multiplicative.toAdd_le_one_of_units_val_le hγ
  rw [Int.toNat_of_nonneg h_nonneg, neg_add, neg_neg, add_lt_iff_neg_left, Left.neg_neg_iff]
  exact zero_lt_one

/-- The `v`-adic integers is a totally bounded set since they afford a finite subcover of
open balls, obtained by using the finite representatives of the quotient of the `v`-adic
integers by a power of the maximal ideal. -/
theorem totallyBounded :
    TotallyBounded (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  simp only [(Valued.hasBasis_uniformity _ _).totallyBounded_iff, forall_true_left]
  intro γ
  by_cases hγ : 1 < (γ : WithZero (Multiplicative ℤ))
  · exact finite_subcover_of_nhds_zero_one_lt K v hγ
  · exact finite_subcover_of_nhds_zero_le_one K v (le_of_not_lt hγ)

instance : CompleteSpace (v.adicCompletionIntegers K) :=
  IsClosed.completeSpace_coe (isClosed K v)

/-- The `v`-adic integers is compact. -/
theorem isCompact : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  isCompact_iff_totallyBounded_isComplete.2
    ⟨totallyBounded K v, IsClosed.isComplete (isClosed K v)⟩

/-- The maximal ideal is compact. -/
theorem isCompact_maximalIdeal : IsCompact { y : v.adicCompletion K | Valued.v y < 1 } :=
  IsCompact.of_isClosed_subset (isCompact K v) (isClosed_nhds_zero K v 1)
      <| fun _ hx => le_of_lt (lt_of_lt_of_le (Set.mem_setOf.1 hx) (le_refl _))

instance compactSpace : CompactSpace (v.adicCompletionIntegers K) :=
  CompactSpace.mk (isCompact_iff_isCompact_univ.1 (isCompact K v))

instance locallyCompactSpace : LocallyCompactSpace (v.adicCompletionIntegers K) := by
  letI : WeaklyLocallyCompactSpace (v.adicCompletionIntegers K) :=
    instWeaklyLocallyCompactSpaceOfCompactSpace
  letI : RegularSpace (v.adicCompletionIntegers K) := TopologicalAddGroup.regularSpace _
  letI : R1Space (v.adicCompletionIntegers K) := instR1Space
  exact WeaklyLocallyCompactSpace.locallyCompactSpace

end AdicCompletionIntegers

open AdicCompletion
open AdicCompletionIntegers

variable (v)

/-- Any open ball centred at zero in the `v`-adic completion of `K` is compact. -/
theorem isCompact_nhds_zero {γ : (WithZero (Multiplicative ℤ))ˣ} (hγ : γ ≤ 1) :
    IsCompact { y : v.adicCompletion K | Valued.v y < γ } :=
  IsCompact.of_isClosed_subset (isCompact K v) (isClosed_nhds_zero K v γ)
      <| fun _ hx => le_of_lt (lt_of_lt_of_le (Set.mem_setOf.1 hx) hγ)

/-- The `v`-adic completion of `K` is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (v.adicCompletion K) :=
  letI := (inferInstanceAs (UniformAddGroup (v.adicCompletion K))).to_topologicalAddGroup
  LocallyCompactSpace.of_hasBasis_nhds_zero hasBasis_nhds_zero
    (fun _ hγ => isCompact_nhds_zero K v hγ)

  end IsDedekindDomain.HeightOneSpectrum
