import Mathlib

open DedekindDomain IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Classical

namespace LocallyCompact

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K] [NumberField K] [Algebra R K]
  [IsFractionRing R K] (S : Finset (HeightOneSpectrum R)) (v : HeightOneSpectrum R)

/- From Maria's work -/
lemma adicCompletion_exists_uniformizer :
  ∃ (π : v.adicCompletion K), Valued.v π = (Multiplicative.ofAdd ((-1 : ℤ))) := by
  obtain ⟨x, hx⟩ := valuation_exists_uniformizer K v
  use ↑x
  rw [valuedAdicCompletion_def, ← hx]
  simp
  rfl

lemma ofAdd_neg_one_lt_one : Multiplicative.ofAdd (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
  exact neg_one_lt_zero

lemma adicCompletionIntegers_exists_uniformizer :
  ∃ (π : v.adicCompletionIntegers K), Valued.v (π : v.adicCompletion K) = (Multiplicative.ofAdd ((-1 : ℤ))) := by
  obtain ⟨x, hx⟩ := valuation_exists_uniformizer K v
  refine' ⟨⟨x, _⟩, _⟩
  {
    rw [mem_adicCompletionIntegers]
    rw [valuedAdicCompletion_def]
    simp
    have h := (le_of_lt (ofAdd_neg_one_lt_one))
    rw [← hx] at h
    apply le_trans h
    exact le_rfl
  }
  {
    simp_rw [← hx]
    rw [valuedAdicCompletion_def]
    simp
    rfl
  }

def IsUniformizer (π : v.adicCompletion K) : Prop := Valued.v π = Multiplicative.ofAdd (-1 : ℤ)

noncomputable def adicCompletionIntegers.maximalIdeal : Ideal (v.adicCompletionIntegers K) :=
  LocalRing.maximalIdeal (v.adicCompletionIntegers K)

theorem adicValuationIntegers_valuation_eq_one_of_isUnit (x : v.adicCompletionIntegers K) (hx : IsUnit x) :
  Valued.v x.val = 1 := by
  let ⟨u, hu⟩ := hx
  apply le_antisymm ((v.mem_adicCompletionIntegers K).1 x.property)
  have h := @Valuation.map_one (v.adicCompletion K) (WithZero (Multiplicative ℤ)) _ _ Valued.v
  have h' : (1 : v.adicCompletion K) = (1 : v.adicCompletionIntegers K) := rfl
  rw [← h, h', ← u.mul_inv, hu]
  simp
  nth_rewrite 2 [← mul_one (Valued.v x.val)]
  exact mul_le_mul_left' ((v.mem_adicCompletionIntegers K).1 (u⁻¹.val.property)) _

-- MINE
theorem adicValuationIntegers_isUnit_of_one (x : v.adicCompletionIntegers K) (hx : Valued.v (x : v.adicCompletion K) = 1)
  : IsUnit x := by
  have hx₀ : IsUnit (x : v.adicCompletion K) := by
    rw [isUnit_iff_ne_zero]
    contrapose hx
    push_neg at hx
    rw [hx]
    rw [Valuation.map_zero]
    exact zero_ne_one

  obtain ⟨u, hu⟩ := hx₀
  have hu₁ : Valued.v u.val ≤ 1 := by
    rw [hu]
    exact x.property
  have hu₂ : Valued.v u⁻¹.val ≤ 1 := by
    rw [← one_mul (Valued.v _), ← hx, ← hu, ← Valued.v.map_mul, u.mul_inv, hu, hx, Valued.v.map_one]
  set w := (⟨u.val, hu₁⟩ : v.adicCompletionIntegers K) with w_def
  have hwx : w = x := by
    rw [w_def]
    simp_rw [hu]
  rw [← hwx]
  rw [isUnit_iff_exists]
  use ⟨u⁻¹.val, hu₂⟩
  have h : 1 ∈ v.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers]
    simp
  have h₁ : (1 : v.adicCompletion K) = u * u⁻¹ := by simp
  have h₂ : (1 : v.adicCompletionIntegers K) = ⟨(1 : v.adicCompletion K), h⟩ := rfl
  refine' ⟨_, _⟩
  {
    rw [h₂]
    simp_rw [h₁]
    rfl
  }
  {
    rw [h₂]
    simp_rw [h₁]
    rw [mul_comm]
    rfl
  }

lemma isUnit_iff_valuation_eq_one (x : v.adicCompletionIntegers K) : IsUnit x ↔ Valued.v x.val = 1 :=
  ⟨adicValuationIntegers_valuation_eq_one_of_isUnit R K v x, adicValuationIntegers_isUnit_of_one R K v x⟩

lemma not_isUnit_iff_valuation_lt_one (x : v.adicCompletionIntegers K) :
  ¬IsUnit x ↔ Valued.v x.val < 1 := by
  rw [← not_le, not_iff_not, isUnit_iff_valuation_eq_one, le_antisymm_iff]
  exact and_iff_right x.2

lemma isUniformizer_ne_zero {π : v.adicCompletionIntegers K} (h : IsUniformizer R K v π)
  : π ≠ 0 := by
  contrapose h
  push_neg at h
  rw [h]
  unfold IsUniformizer
  simp

lemma pow_uniformizer {x π : v.adicCompletionIntegers K} (hx : x ≠ 0) (hπ : IsUniformizer R K v π) :
  ∃ (n : ℕ) (u : (v.adicCompletionIntegers K)ˣ), x = π^n * u := by
have hx₀ : Valued.v x.val ≠ 0 := by
  contrapose hx
  push_neg at hx ⊢
  simp at hx
  exact hx
set m := - Multiplicative.toAdd (WithZero.unzero hx₀)
have hm₀ : 0 ≤ m := by
  rw [Right.nonneg_neg_iff, ← toAdd_one, Multiplicative.toAdd_le, ← WithZero.coe_le_coe, WithZero.coe_unzero]
  exact x.property
use Int.toNat m
have hpow : Valued.v (π ^ (-m) * x.val) = 1 := by
  rw [Valued.v.map_mul, map_zpow₀, hπ, ofAdd_neg, WithZero.coe_inv, inv_zpow', neg_neg, ← WithZero.coe_zpow,
  ← Int.ofAdd_mul, one_mul, ofAdd_neg, ofAdd_toAdd, WithZero.coe_inv, WithZero.coe_unzero, inv_mul_cancel hx₀]
set a : v.adicCompletionIntegers K := ⟨π^(-m) * x.val, le_of_eq hpow⟩
have h_isUnit_a : IsUnit a := by
  apply adicValuationIntegers_isUnit_of_one R K v
  exact hpow

use h_isUnit_a.unit
ext
rw [IsUnit.unit_spec, Subring.coe_mul, Subring.coe_pow, Subtype.coe_mk, ← mul_assoc]
nth_rewrite 2 [← Int.toNat_of_nonneg hm₀]
rw [zpow_neg, zpow_coe_nat, mul_inv_cancel, one_mul]
apply pow_ne_zero
simp
exact isUniformizer_ne_zero R K v hπ

lemma isUniformizer_is_generator {π : v.adicCompletionIntegers K} (hπ : IsUniformizer R K v π) :
  adicCompletionIntegers.maximalIdeal R K v = Ideal.span {π} := by
  apply (LocalRing.maximalIdeal.isMaximal _).eq_of_le
  {
    intro h
    rw [Ideal.span_singleton_eq_top] at h
    rw [isUnit_iff_valuation_eq_one] at h
    apply (not_le_of_lt ofAdd_neg_one_lt_one)
    rw [← h, hπ]
  }
  {
    intro x hx
    by_cases hx₀ : x = 0
    {
      simp only [hx₀, Ideal.zero_mem]
    }
    {
      obtain ⟨n, ⟨u, hu⟩⟩ := pow_uniformizer R K v hx₀ hπ
      have hn : ¬(IsUnit x) := λ h => (LocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ hx h)
      replace hn : n ≠ 0 := λ h => by {rw [hu, h, pow_zero, one_mul] at hn; exact hn u.isUnit}
      simpa [Ideal.mem_span_singleton, hu, IsUnit.dvd_mul_right, Units.isUnit] using dvd_pow_self _ hn
    }
  }
