/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib
import LocalClassFieldTheory.DiscreteValuationRing.ResidueField
import LocalClassFieldTheory.DiscreteValuationRing.Complete
import LocalClassFieldTheory.DiscreteValuationRing.Extensions
import AdeleRingLocallyCompact.Algebra.Group.WithOne.Defs

/-!
# Adic valuations on Dedekind domains

Let `R` be a Dedekind domain of Krull dimension 1, `K` its field of fractions and `v` a maximal ideal of `R`.
In this file we prove compactness results for the `v`-adic completion of `K` and its ring of integers.

We import required Lean 3 results from the work of María Inés de Frutos-Fernández and Filippo A. E. Nuccio
concerning the uniformizers of the ring of integers and the finiteness of its residue field, which are
referenced appropriately in the docstrings.

Note that one of the main results is not proved here, since the proof is already given elsewhere in Lean 3
by María Inés de Frutos-Fernández, Filippo A. E. Nuccio in [https://github.com/mariainesdff/local_fields_journal/](https://github.com/mariainesdff/local_fields_journal/).

## Main definitions
 - `IsDedekindDomain.HeightOneSpectrum.AdicCompletionIntegers.maximalIdeal K v` is the maximal ideal of the
   ring of integers in the `v`-adic completion of `K`.
 - `IsDedekindDomain.HeightOneSpectrum.AdicCompletionIntegers.residueField K v` is the residue field of the
   ring of integers in the `v`-adic completion of `K`.
 - `IsDedekindDomain.HeightOneSpectrum.AdicCompletionIntegers.ofFiniteCoeffs π n` constructs a `v`-adic integer
   from an `n`-tuple of `v`-adic integers by using them as coefficients in a finite `v`-adic expansionin the
   uniformizer `π`.
 - `IsDedekindDomain.HeightOneSpectrum.AdicCompletionIntegers.toFiniteCoeffs π n` gives the first `n` coefficients
   in the `v`-adic expansion in `π` of a `v`-adic integer modulo the `n`th power of the maximal ideal.

## Main results
 - `IsDedekindDomain.HeightOneSpectrum.AdicCompletionIntegers.residueField_finite` : the residue field of
   the `v`-adic ring of integers is finite.
 - `IsDedekindDomain.HeightOneSpectrum.AdicCompletionIntegers.quotient_maximalIdeal_pow_fintype` : the quotient of
   the `v`-adic ring of integers by a power of the maximal ideal is finite.
 - `IsDedekindDomain.HeightOneSpectrum.AdicCompletionIntegers.isCompact` : the `v`-adic ring of integers is
   compact.
 - `IsDedekindDomain.HeightOneSpectrum.locallyCompactSpace` : the `v`-adic Completion of `K` is locally compact.

## References
 * [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
 * [M.I. de Frutos-Fernández, F.A.E. Nuccio, *A Formalization of Complete Discrete Valuation Rings and Local Fields*][defrutosfernandez2023]

## Tags
dedekind domain, dedekind ring, adic valuation

## TODO
 - Incorporate the proof that the `v`-adic ring of integers has finite residue field.
 - Use `UniformSpace.ball` instead of `openBall`.
-/

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K] {v : HeightOneSpectrum R}

namespace IsDedekindDomain.HeightOneSpectrum

local notation "μ_v" => @WithZero.unitsWithZeroEquiv (Multiplicative ℤ)

namespace AdicCompletion

/-- [https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L137](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L137) -/
def IsUniformizer (π : v.adicCompletion K) : Prop :=
  Valued.v π = Multiplicative.ofAdd (-1 : ℤ)

variable (K v)

def coeRingHom : K →+* v.adicCompletion K :=
  @UniformSpace.Completion.coeRingHom K _ v.adicValued.toUniformSpace _ _

/-- [https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/complete.lean#L95](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/complete.lean#L95) -/
theorem exists_uniformizer :
  ∃ (π : v.adicCompletion K), IsUniformizer π := by
  obtain ⟨x, hx⟩ := valuation_exists_uniformizer K v
  use ↑x
  simp only [IsUniformizer, valuedAdicCompletion_def, ← hx, Valued.extension_extends]
  rfl

def openBall (γ : (WithZero (Multiplicative ℤ))ˣ) : Set (v.adicCompletion K) :=
  setOf (λ y => Valued.v y < γ)

/-- Open balls are open in the `v`-adic Completion of `K`. -/
theorem openBall_isOpen (γ : (WithZero (Multiplicative ℤ))ˣ) : IsOpen (openBall K v γ) := by
  rw [isOpen_iff_mem_nhds]
  intros x hx
  rw [openBall, Set.mem_setOf_eq] at hx
  rw [Valued.mem_nhds, openBall]
  refine ⟨γ, λ y hy => ?_⟩
  rw [← sub_add_cancel y x]
  rw [Set.mem_setOf_eq] at hy
  exact lt_of_le_of_lt (Valued.v.map_add (y - x) x) (max_lt hy hx)

/-- Open balls are closed in the `v`-adic completion of `K`. -/
theorem openBall_isClosed (γ : (WithZero (Multiplicative ℤ))ˣ) : IsClosed (openBall K v γ) := by
  simp only [isClosed_iff_nhds, openBall, Set.mem_setOf_eq]
  intro x hx
  contrapose! hx
  have h : Valued.v x ≠ 0 := by contrapose! hx; simp only [hx, Units.zero_lt]
  use {y | Valued.v y = Valued.v x}, (Valued.loc_const h)
  rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_iff]
  intro y ⟨hy, hy'⟩
  rw [ Set.mem_setOf_eq] at hy'
  rw [← hy] at hx
  exact (not_le_of_lt hy') hx

/-- Small open balls are contained in the `v`-adic integers. -/
theorem openBall_of_le_one_subset_adicCompletionIntegers (γ : (WithZero (Multiplicative ℤ))ˣ) (hγ : γ ≤ 1) :
  openBall K v γ ⊆ v.adicCompletionIntegers K := by
  intro x hx
  rw [openBall, Set.mem_setOf_eq] at hx
  exact le_of_lt (lt_of_lt_of_le hx hγ)

/-- Open balls can be shrunk by multiplying by an appropriate power of a uniformizer. -/
theorem mem_openBall_mul_uniformizer_pow (x π : v.adicCompletion K) (hx : x ∈ openBall K v γ)
  (hπ : IsUniformizer π) :
  Valued.v (π^(Multiplicative.toAdd (μ_v γ)) * x) < 1 := by
  rw [Valued.v.map_mul, map_zpow₀, hπ]
  rw [openBall, Set.mem_setOf_eq] at hx
  have h_ne_zero : γ.val⁻¹ ≠ 0 := by simp_all only [ne_eq, inv_eq_zero, Units.ne_zero, not_false_eq_true]
  rw [(Units.inv_mul' γ).symm]
  apply mul_lt_mul_of_lt_of_le₀ _ h_ne_zero hx
  rw [ofAdd_neg, WithZero.coe_inv, inv_zpow', zpow_neg]
  have h_val : γ.val = (μ_v γ : WithZero (Multiplicative ℤ)) := by
    simp only [WithZero.unitsWithZeroEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk, WithZero.coe_unzero]
  rw [h_val, ← WithZero.coe_inv, ← WithZero.coe_zpow, ← WithZero.coe_inv,
    WithZero.coe_le_coe, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]

variable {K v}

theorem ne_zero_iff_valuation_ne_zero (x : v.adicCompletion K) :
  x ≠ 0 ↔ Valued.v x ≠ 0 := by simp only [ne_eq, map_eq_zero]

end AdicCompletion

namespace AdicCompletionIntegers

open AdicCompletion

variable (K v)

/-- [https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/complete.lean#L79](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/complete.lean#L79)-/
theorem exists_uniformizer :
  ∃ (π : v.adicCompletionIntegers K), IsUniformizer π.val := by
  obtain ⟨π, hπ⟩ := valuation_exists_uniformizer K v
  refine ⟨⟨π, ?_⟩, ?_⟩
  · rw [mem_adicCompletionIntegers, valuedAdicCompletion_def]
    simp only [Valued.extension_extends]
    have h_le := (le_of_lt (Multiplicative.ofAdd_neg_one_lt_one))
    rw [← hπ] at h_le
    exact le_trans h_le le_rfl
  · simp only [IsUniformizer, ← hπ, valuedAdicCompletion_def, Valued.extension_extends]
    rfl

/-- The maximal ideal of the `v`-adic ring of integers. -/
def maximalIdeal : Ideal (v.adicCompletionIntegers K) :=
  LocalRing.maximalIdeal (v.adicCompletionIntegers K)

/-- The residue field of the `v`-adic ring of integers. -/
def residueField := LocalRing.ResidueField (v.adicCompletionIntegers K)

variable {K v}

/-- The valuation of a unit is `1`. -/
theorem valuation_eq_one_of_isUnit {x : v.adicCompletionIntegers K} (hx : IsUnit x) :
  Valued.v x.val = 1 := by
  obtain ⟨u, hu⟩ := hx
  apply le_antisymm ((v.mem_adicCompletionIntegers K).1 x.property)
  rw [← @Valuation.map_one (v.adicCompletion K) (WithZero (Multiplicative ℤ)) _ _ Valued.v]
  have h_one : (1 : v.adicCompletion K) = (1 : v.adicCompletionIntegers K) := rfl
  rw [h_one, ← u.mul_inv, hu]
  simp only [Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, Subring.coe_toSubsemiring, map_mul,
    ge_iff_le]
  nth_rewrite 2 [← mul_one (Valued.v x.val)]
  exact mul_le_mul_left' ((v.mem_adicCompletionIntegers K).1 (u⁻¹.val.property)) _

/-- A `v`-adic integer with valuation `1` is a unit. -/
theorem isUnit_of_valuation_eq_one {x : v.adicCompletionIntegers K} (hx : Valued.v (x : v.adicCompletion K) = 1) :
  IsUnit x := by
  have hx_unit : IsUnit (x : v.adicCompletion K) := by
    simp only [isUnit_iff_ne_zero, ne_zero_iff_valuation_ne_zero, hx, ne_eq, one_ne_zero, not_false_eq_true]
  obtain ⟨u, hu⟩ := hx_unit
  have hu_le : Valued.v u.val ≤ 1 := by rw [hu]; exact x.property
  have hu_inv_le : Valued.v u⁻¹.val ≤ 1 := by
    rw [← one_mul (Valued.v _), ← hx, ← hu, ← Valued.v.map_mul, u.mul_inv, hu, hx, Valued.v.map_one]
  set w := (⟨u.val, hu_le⟩ : v.adicCompletionIntegers K)
  have hwx : w = x := by simp only [w, hu]
  rw [← hwx, isUnit_iff_exists]
  use ⟨u⁻¹.val, hu_inv_le⟩
  have h₁ : (1 : v.adicCompletion K) = u * u⁻¹ := by simp only [Units.val_inv_eq_inv_val,
    ne_eq, Units.ne_zero, not_false_eq_true, mul_inv_cancel]
  have h₂ : (1 : v.adicCompletionIntegers K) = ⟨(1 : v.adicCompletion K), (v.adicCompletionIntegers K).one_mem⟩ := rfl
  exact ⟨by simp only [h₂, h₁]; rfl, by simp only [h₂, h₁, mul_comm]; rfl⟩

/-- A `v`-adic integer is a unit if and only if it has valuation `1`. -/
theorem isUnit_iff_valuation_eq_one (x : v.adicCompletionIntegers K) : IsUnit x ↔ Valued.v x.val = 1 :=
  ⟨valuation_eq_one_of_isUnit, isUnit_of_valuation_eq_one⟩

/-- [https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L116](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L116)-/
theorem not_isUnit_iff_valuation_lt_one (x : v.adicCompletionIntegers K) :
  ¬IsUnit x ↔ Valued.v x.val < 1 := by
  rw [← not_le, not_iff_not, isUnit_iff_valuation_eq_one, le_antisymm_iff]
  exact and_iff_right x.2

/-- A uniformizer is non-zero. -/
theorem isUniformizer_ne_zero {π : v.adicCompletionIntegers K} (h : IsUniformizer π.val) : π ≠ 0 := by
  contrapose! h
  simp only [h, IsUniformizer, ZeroMemClass.coe_zero, map_zero, Int.reduceNeg, ofAdd_neg, WithZero.coe_inv,
    zero_eq_inv, WithZero.zero_ne_coe, not_false_eq_true]

/-- A uniformizer is not a unit in the `v`-adic integers. -/
theorem isUniformizer_not_isUnit {π : v.adicCompletionIntegers K} (h : IsUniformizer π.val) :
  ¬IsUnit π := by
  rw [IsUniformizer] at h
  simp only [not_isUnit_iff_valuation_lt_one, h, ← WithZero.coe_one, ← ofAdd_zero, WithZero.coe_lt_coe,
    Multiplicative.ofAdd_lt, Left.neg_neg_iff, zero_lt_one]

/- [https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L259](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L259)-/
theorem eq_pow_uniformizer_mul_unit {x π : v.adicCompletionIntegers K} (hx : x.val ≠ 0) (hπ : IsUniformizer π.val) :
  ∃ (n : ℕ) (u : (v.adicCompletionIntegers K)ˣ), x = π^n * u := by
  have hx₀ : Valued.v x.val ≠ 0 := (ne_zero_iff_valuation_ne_zero x.val).1 hx
  set m := - Multiplicative.toAdd (WithZero.unzero hx₀)
  have hm₀ : 0 ≤ m := by
    rw [Right.nonneg_neg_iff, ← toAdd_one, Multiplicative.toAdd_le, ← WithZero.coe_le_coe, WithZero.coe_unzero]
    exact x.property
  use Int.toNat m
  have hpow : Valued.v (π ^ (-m) * x.val) = 1 := by
    rw [Valued.v.map_mul, map_zpow₀, hπ, ofAdd_neg, WithZero.coe_inv, inv_zpow', neg_neg, ← WithZero.coe_zpow,
    ← Int.ofAdd_mul, one_mul, ofAdd_neg, ofAdd_toAdd, WithZero.coe_inv, WithZero.coe_unzero, inv_mul_cancel hx₀]
  set a : v.adicCompletionIntegers K := ⟨π^(-m) * x.val, le_of_eq hpow⟩
  have h_isUnit_a : IsUnit a := isUnit_of_valuation_eq_one hpow
  use h_isUnit_a.unit
  ext
  rw [IsUnit.unit_spec, Subring.coe_mul, Subring.coe_pow, Subtype.coe_mk, ← mul_assoc]
  nth_rewrite 2 [← Int.toNat_of_nonneg hm₀]
  rw [zpow_neg, zpow_natCast, mul_inv_cancel, one_mul]
  apply pow_ne_zero
  simp only [ne_eq, ZeroMemClass.coe_eq_zero]
  exact isUniformizer_ne_zero hπ

/- [https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L295](https://github.com/mariainesdff/local_fields_journal/blob/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3/src/discrete_valuation_ring/basic.lean#L295)-/
theorem isUniformizer_is_generator {π : v.adicCompletionIntegers K} (hπ : IsUniformizer π.val) :
  maximalIdeal K v = Ideal.span {π} := by
  apply (LocalRing.maximalIdeal.isMaximal _).eq_of_le (Ideal.span_singleton_ne_top (isUniformizer_not_isUnit hπ))
  intro x hx
  by_cases hx₀ : x.val = 0
  · simp only [ZeroMemClass.coe_eq_zero] at hx₀
    simp only [hx₀, Ideal.zero_mem]
  · obtain ⟨n, ⟨u, hu⟩⟩ := eq_pow_uniformizer_mul_unit hx₀ hπ
    have hn : ¬(IsUnit x) := λ h => (LocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ hx h)
    replace hn : n ≠ 0 := λ h => by {rw [hu, h, pow_zero, one_mul] at hn; exact hn u.isUnit}
    simpa [Ideal.mem_span_singleton, hu, IsUnit.dvd_mul_right, Units.isUnit] using dvd_pow_self _ hn

/-- An element of the maximal ideal of the `v`-adic integers has valuation less than `1`. -/
theorem valuation_lt_one_of_maximalIdeal {x : v.adicCompletionIntegers K} (hx : x ∈ maximalIdeal K v) :
  Valued.v (x : v.adicCompletion K) < 1 := by
  rw [AdicCompletionIntegers.maximalIdeal, LocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
  contrapose! hx
  exact isUnit_of_valuation_eq_one (le_antisymm x.property hx)

/-- An element of a positive power `n` of the maximal ideal of the `v`-adic integers has valuation less than
or equal to `-n`. -/
theorem valuation_le_pow_of_maximalIdeal {x : v.adicCompletionIntegers K} (n : ℕ) (hx : x ∈ (maximalIdeal K v)^n) :
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
      apply (mul_le_mul_left₀ _).2 ((mem_adicCompletionIntegers _ _ _).1 y.property)
      simp only [pow_ne_zero_iff hn, Valuation.ne_zero_iff, ne_eq, ZeroMemClass.coe_eq_zero]
      exact isUniformizer_ne_zero hπ
    apply le_trans h_mul_le_mul
    rw [mul_one, hπ, ← WithZero.coe_pow, WithZero.coe_le_coe, ofAdd_neg, ofAdd_neg, inv_pow, inv_le_inv_iff,
      ← one_mul (n : ℤ), Int.ofAdd_mul, zpow_natCast]

/-- The residue field of the `v`-adic integers is finite. -/
instance residueField_finite : Fintype (residueField K v) :=
  sorry

instance : CommRing (Fin n → LocalRing.ResidueField (v.adicCompletionIntegers K)) := inferInstance

/-- Takes an `n`-tuple `(a₁, ..., aₙ)` and creates a `v`-adic integer using the `n`-tuple as coefficients in
a finite `v`-adic expansion in some fixed `v`-adic integer `π` as `a₁ + a₂π + a₃π² + ...`.
Note the definition does not require `π` to be a uniformizer. -/
def ofFiniteCoeffs (π : v.adicCompletionIntegers K) (n : ℕ) :
  (Fin n → v.adicCompletionIntegers K) → v.adicCompletionIntegers K :=
  λ x => ((List.ofFn x).mapIdx (λ i j => j * π^i)).sum

/-- Given a uniformizer `π` of the `v`-adic integers and a `v`-adic integer `x`, there exists an `n`-tuple of
representatives in the residue field of the `v`-adic integers such that `x` can be written as a finite `v`-adic
expansion in `π` with coefficients given by the `n`-tuple. -/
theorem finiteExpansion {π : v.adicCompletionIntegers K} (n : ℕ) (x : v.adicCompletionIntegers K)
  (hπ : IsUniformizer π.val) :
  ∃ (a : Fin n → LocalRing.ResidueField (v.adicCompletionIntegers K)),
    x - ((List.ofFn a).mapIdx (λ i j => (Quotient.out' j) * π^i)).sum ∈ (maximalIdeal K v)^n := by
  induction' n with d hd;
  · simp only [Nat.zero_eq, List.ofFn_zero, List.mapIdx_nil, List.sum_nil, sub_zero, pow_zero,
        Ideal.one_eq_top, Submodule.mem_top, exists_const]
  · obtain ⟨b, hbx⟩ := hd
    rw [isUniformizer_is_generator hπ, Ideal.span_singleton_pow] at hbx ⊢
    rw [Ideal.mem_span_singleton'] at hbx
    obtain ⟨z, hz⟩ := hbx
    use Fin.snoc b (Ideal.Quotient.mk _ z)
    simp only [List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.mapIdx_append,
      List.length_ofFn, List.mapIdx_cons, zero_add, List.mapIdx_nil, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero, ← sub_sub, ← hz, ← sub_mul, Ideal.mem_span_singleton, pow_succ]
    have h : π ∣ z - Quotient.out' (Ideal.Quotient.mk (maximalIdeal K v) z) := by
      rw [isUniformizer_is_generator hπ, ← Ideal.mem_span_singleton, ← Submodule.Quotient.mk_eq_zero,
        Submodule.Quotient.mk_sub, Submodule.Quotient.mk, Quotient.out_eq', Submodule.Quotient.mk''_eq_mk,
        Ideal.Quotient.mk_eq_mk, sub_self]
    rw [mul_comm]
    exact mul_dvd_mul_right h (π^d)

/-- Given a uniformizer `π` of the `v`-adic integers and a `v`-adic integer `x` modulo a power of
the maximal ideal, gives the coefficients of `x` in the finite `v`-adic expansion in `π` as an `n`-tuple of
representatives in the residue field.
-/
def toFiniteCoeffs {π : v.adicCompletionIntegers K} (n : ℕ) (hπ : IsUniformizer π.val) :
  v.adicCompletionIntegers K ⧸ (maximalIdeal K v)^n
    → (Fin n → LocalRing.ResidueField (v.adicCompletionIntegers K)) :=
  λ x => (Classical.choose (finiteExpansion n (Quotient.out' x) hπ))

theorem toFiniteCoeffs_injective {π : v.adicCompletionIntegers K} (n : ℕ) (hπ : IsUniformizer π.val) :
  (toFiniteCoeffs n hπ).Injective := by
  intro x y hxy
  unfold toFiniteCoeffs at hxy
  set a := Classical.choose (finiteExpansion n (Quotient.out' x) hπ) with a_def
  set b := Classical.choose (finiteExpansion n (Quotient.out' y) hπ)
  have hx := Classical.choose_spec (finiteExpansion n (Quotient.out' x) hπ)
  have hy := Classical.choose_spec (finiteExpansion n (Quotient.out' y) hπ)
  rw [← a_def, hxy] at hx
  rw [← Quotient.out_eq' x, ← Quotient.out_eq' y, ← Submodule.Quotient.mk, ← sub_eq_zero,
    ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero,
    ← sub_sub_sub_cancel_right _ _ (List.sum (List.mapIdx (fun i j => Quotient.out' j * π ^ i) (List.ofFn b)))]
  exact Ideal.sub_mem _ hx hy

/-- The quotient of the `v`-adic integers with a power of the maximal ideal is finite. -/
theorem quotient_maximalIdeal_pow_fintype {π : v.adicCompletionIntegers K} (n : ℕ) (hπ : IsUniformizer π.val) :
  Fintype (v.adicCompletionIntegers K ⧸ (maximalIdeal K v)^n) := by
  haveI : Fintype (Fin n → residueField K v) := Pi.fintype
  unfold residueField at this
  exact Fintype.ofInjective _ (toFiniteCoeffs_injective n hπ)

variable (K v)

/-- The `v`-adic integers are closed in the `v`-adic completion of `K`. -/
theorem isClosed : IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  simp only [isClosed_iff_nhds, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, not_le]
  intro x hx
  contrapose! hx
  use {y | Valued.v y = Valued.v x}, (Valued.loc_const (ne_zero_of_lt hx))
  rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_iff]
  intro y ⟨hy, hy_int⟩
  rw [SetLike.mem_coe, mem_adicCompletionIntegers] at hy_int
  rw [← hy] at hx
  exact (not_lt_of_le hy_int) hx

/-- There is a finite covering of the `v`-adic integers of open balls of radius larger than one, namely
the single open ball centred at `0`. -/
theorem hasFiniteSubcover_of_openBall_one_lt {γ : (WithZero (Multiplicative ℤ))ˣ} (hγ : γ.val > 1) :
  ∃ t : Set (v.adicCompletion K),
    Set.Finite t ∧
    ↑(adicCompletionIntegers K v) ⊆ ⋃ y ∈ t, {x | (x, y) ∈ {p | Valued.v (p.2 - p.1) < γ.val}} := by
  use {0}
  simp only [Set.finite_singleton, Set.mem_singleton_iff, Set.mem_setOf_eq,
    Set.iUnion_iUnion_eq_left, zero_sub, Valuation.map_neg, true_and]
  intro x hx
  rw [SetLike.mem_coe, mem_adicCompletionIntegers] at hx
  exact lt_of_le_of_lt hx hγ

/-- There is a finite covering of the `v`-adic integers of open balls of radius equal to one, obtained
by using the finite representatives in the residue field. -/
theorem hasFiniteSubcover_of_openBall_eq_one {γ : (WithZero (Multiplicative ℤ))ˣ} (hγ : γ.val = 1) :
 ∃ t : Set (v.adicCompletion K),
    Set.Finite t ∧
    ↑(adicCompletionIntegers K v) ⊆ ⋃ y ∈ t, {x | (x, y) ∈ {p | Valued.v (p.2 - p.1) < γ.val}} := by
  set quotientMap : v.adicCompletionIntegers K → residueField K v := Submodule.Quotient.mk
  obtain ⟨π, hπ⟩ := exists_uniformizer K v
  have h := quotient_maximalIdeal_pow_fintype 1 hπ
  rw [pow_one] at h
  set T := Quotient.out' '' (h.elems.toSet)
  use T, (Set.Finite.image Subtype.val (Set.Finite.image Quotient.out' (Finset.finite_toSet h.elems)))
  intro x hx
  simp only [Set.mem_iUnion]
  set y := (Quotient.out' (quotientMap ⟨x, hx⟩))
  use y
  have h_out_mk_mem : Subtype.val (Quotient.out' (quotientMap ⟨x, hx⟩)) ∈ Subtype.val '' T :=
    ⟨y, Set.mem_image_of_mem Quotient.out' (Finset.mem_coe.2 (h.complete (quotientMap ⟨x, hx⟩))), rfl⟩
  use h_out_mk_mem
  have h_sub_zero : y - ⟨x, hx⟩ ∈ maximalIdeal K v := by
    rw [← Submodule.Quotient.eq, ← Submodule.Quotient.mk''_eq_mk, Quotient.out_eq']
  rw [hγ]
  exact valuation_lt_one_of_maximalIdeal h_sub_zero

/-- There is a finite covering of the `v`-adic integers of open balls of radius less than one, obtained
by using the finite representatives in the quotient of the `v`-adic integers by a power of the maximal
ideal. -/
theorem hasFiniteSubcover_of_openBall_lt_one {γ : (WithZero (Multiplicative ℤ))ˣ} (hγ : γ.val < 1) :
  ∃ t : Set (v.adicCompletion K),
      Set.Finite t ∧
      ↑(adicCompletionIntegers K v) ⊆ ⋃ y ∈ t, {x | (x, y) ∈ {p | Valued.v (p.2 - p.1) < γ.val}} := by
  have ho : ∃ μ : Multiplicative ℤ, γ.val = (μ : WithZero (Multiplicative ℤ)) := by
      use μ_v γ
      simp only [WithZero.unitsWithZeroEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk, WithZero.coe_unzero]
  obtain ⟨μ, hμ⟩ := ho
  set M := (maximalIdeal K v)^((-Multiplicative.toAdd μ + 1).toNat)
  set S := (v.adicCompletionIntegers K) ⧸ M
  set quotientMap : v.adicCompletionIntegers K → S := Submodule.Quotient.mk
  obtain ⟨π, hπ⟩ := exists_uniformizer K v
  have h : Fintype S := quotient_maximalIdeal_pow_fintype (-Multiplicative.toAdd μ + 1).toNat hπ
  set T := Quotient.out' '' (h.elems.toSet)
  use T, (Set.Finite.image Subtype.val (Set.Finite.image Quotient.out' (Finset.finite_toSet h.elems)))
  intro x hx
  simp only [Set.mem_iUnion]
  set y := (Quotient.out' (quotientMap ⟨x, hx⟩))
  use y
  have h_out_mk_mem : Subtype.val (Quotient.out' (quotientMap ⟨x, hx⟩)) ∈ Subtype.val '' T :=
    ⟨y, ⟨Set.mem_image_of_mem _ (Finset.mem_coe.2 (h.complete _)), rfl⟩⟩
  use h_out_mk_mem
  have h_sub_zero : y - ⟨x, hx⟩ ∈ M := by
    rw [← Submodule.Quotient.eq, ← Submodule.Quotient.mk''_eq_mk, Quotient.out_eq']
  have h_le := valuation_le_pow_of_maximalIdeal ((-Multiplicative.toAdd μ + 1).toNat) h_sub_zero
  apply lt_of_le_of_lt h_le
  rw [hμ, ← ofAdd_toAdd μ, WithZero.coe_lt_coe, Multiplicative.ofAdd_lt, ofAdd_toAdd]
  have h_nonneg : 0 ≤ - (Multiplicative.toAdd μ) + 1 := by
    rw [le_neg_add_iff_add_le, add_zero, ← Multiplicative.ofAdd_le, ofAdd_toAdd, ← WithZero.coe_le_coe, ← hμ]
    apply le_trans (le_of_lt hγ)
    rw [← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    exact zero_le_one
  rw [Int.toNat_of_nonneg h_nonneg, neg_add, neg_neg, add_lt_iff_neg_left, Left.neg_neg_iff]
  exact zero_lt_one

/-- The `v`-adic integers is a totally bounded set since they afford a finite subcover of open balls,
obtained by using the finite representatives of the quotient of the `v`-adic integers by a power of the
maximal ideal. -/
theorem isTotallyBounded : TotallyBounded (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  simp only [Filter.HasBasis.totallyBounded_iff (Valued.hasBasis_uniformity _ _), forall_true_left]
  intro γ
  by_cases hγ : (γ : WithZero (Multiplicative ℤ)) > 1; exact hasFiniteSubcover_of_openBall_one_lt K v hγ
  by_cases hγ' : (γ : WithZero (Multiplicative ℤ)) = 1; exact hasFiniteSubcover_of_openBall_eq_one K v hγ'
  exact hasFiniteSubcover_of_openBall_lt_one K v (lt_of_le_of_ne (le_of_not_gt hγ) hγ')

instance : CompleteSpace (v.adicCompletionIntegers K) := IsClosed.completeSpace_coe (isClosed K v)

/-- The `v`-adic integers is compact. -/
theorem isCompact : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  isCompact_iff_totallyBounded_isComplete.2 ⟨isTotallyBounded K v, IsClosed.isComplete (isClosed K v)⟩

instance compactSpace :  CompactSpace (v.adicCompletionIntegers K) :=
  by apply CompactSpace.mk (isCompact_iff_isCompact_univ.1 (isCompact K v))

instance : LocallyCompactSpace (v.adicCompletionIntegers K) := inferInstance

end AdicCompletionIntegers

open AdicCompletion
open AdicCompletionIntegers

variable (K v)

/-- Any open ball in the `v`-adic completion of `K` is compact. -/
theorem openBall_isCompact (γ : (WithZero (Multiplicative ℤ))ˣ) : IsCompact (openBall K v γ) := by
  by_cases hγ : γ ≤ 1
  · exact IsCompact.of_isClosed_subset (isCompact K v) (openBall_isClosed K v γ)
      (openBall_of_le_one_subset_adicCompletionIntegers K v γ hγ)
  · rw [not_le] at hγ
    obtain ⟨π, hπ⟩ := AdicCompletionIntegers.exists_uniformizer K v
    set f := λ x => π.val^(-Multiplicative.toAdd (μ_v γ)) * x with f_def
    have hπ_ne_zero : π.val ≠ 0 := by
      convert isUniformizer_ne_zero hπ
      rw [ZeroMemClass.coe_eq_zero]
    have h_range : openBall K v γ ⊆ Set.range f := by
      intro x _
      use π ^ (Multiplicative.toAdd (μ_v γ)) * x
      simp only [f_def, ← mul_assoc, ← zpow_add₀ hπ_ne_zero, add_left_neg,
        zpow_zero, one_mul]
    have h_preimage_subset : f⁻¹' (openBall K v γ) ⊆ (v.adicCompletionIntegers K) := by
      intro x hx
      rw [SetLike.mem_coe, mem_adicCompletionIntegers]
      have h_mul_π := mem_openBall_mul_uniformizer_pow K v (f x) π.val hx hπ
      rw [← mul_assoc, ← zpow_add₀ hπ_ne_zero, add_right_neg, zpow_zero, one_mul] at h_mul_π
      exact le_of_lt h_mul_π
    have h_image_f_closed :=
      continuous_iff_isClosed.1
        (continuous_mul_left (π.val^(-Multiplicative.toAdd (μ_v γ)))) _
        (openBall_isClosed K v γ)
    have h_image_preimage_f_compact :=
      IsCompact.image
        (IsCompact.of_isClosed_subset (isCompact K v) h_image_f_closed h_preimage_subset)
        (continuous_mul_left (π.val^(-Multiplicative.toAdd (μ_v γ))))
    rw [Set.image_preimage_eq_of_subset h_range] at h_image_preimage_f_compact
    exact h_image_preimage_f_compact

  /-- The `v`-adic completion of `K` is locally compact since the open balls give compact neighbourhoods. -/
  instance locallyCompactSpace : LocallyCompactSpace (v.adicCompletion K) := by
    refine LocallyCompactSpace.mk (λ x N hN => ?_)
    rw [Valued.mem_nhds] at hN
    obtain ⟨γ, hN⟩ := hN
    set f := λ y => y + x
    have h_image_f : f '' (openBall K v γ) = setOf (λ y => Valued.v (y - x) < γ) := by
      refine Set.ext (λ y => ?_)
      simp only [f]
      exact Iff.intro
        (λ ⟨a, ha, hay⟩ => by simp [← hay, Set.mem_setOf_eq, add_sub_cancel a x]; exact ha)
        (λ hy => by use (y - x); exact ⟨hy, by simp only [sub_add_cancel]⟩)
    have h_image_f_compact := IsCompact.image (openBall_isCompact K v γ) (continuous_add_right x)
    use (f '' (openBall K v γ))
    rw [Valued.mem_nhds]
    exact ⟨⟨γ, subset_of_eq (Eq.symm h_image_f)⟩, by rw [h_image_f]; exact hN, h_image_f_compact⟩

  end IsDedekindDomain.HeightOneSpectrum
