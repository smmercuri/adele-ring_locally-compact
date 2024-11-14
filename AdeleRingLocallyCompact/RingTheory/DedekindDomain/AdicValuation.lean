/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import AdeleRingLocallyCompact.Algebra.Order.GroupWithZero.WithZero
import AdeleRingLocallyCompact.RingTheory.Ideal.Quotient
import AdeleRingLocallyCompact.FromLocalClassFieldTheory.LocalClassFieldTheory

set_option linter.longLine false
/-!
# Adic valuations on Dedekind domains

Let `R` be a Dedekind domain of Krull dimension 1, `K` its field of fractions and `v`
a maximal ideal of `R`. In this file we prove that the `v`-adic completion of `K` is locally
compact and its ring of integers is compact.

## Main definitions
 - `IsDedekindDomain.HeightOneSpectrum.AdicCompletionIntegers.ofFiniteCoeffs π n`
   constructs a `v`-adic integer from an `n`-tuple of `v`-adic integers by using
   them as coefficients in a finite `v`-adic expansionin the uniformizer `π`.
 - `IsDedekindDomain.HeightOneSpectrum.AdicCompletionIntegers.toFiniteCoeffs π n`
   gives the first `n` coefficients in the `v`-adic expansion in `π` of a `v`-adic
   integer modulo the `n`th power of the maximal ideal.

## Main results
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

open scoped Classical

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K] {v : HeightOneSpectrum R}

namespace HeightOneSpectrum

variable (K)

theorem algebraMap_valuation_ne_zero (v : HeightOneSpectrum R) (r : nonZeroDivisors R) :
    Valued.v (algebraMap _ (v.adicCompletion K) r.val) ≠ 0 := by
  rw [v.valuedAdicCompletion_eq_valuation, ne_eq, map_eq_zero, IsFractionRing.to_map_eq_zero_iff]
  exact nonZeroDivisors.coe_ne_zero _

local notation "μ" => @WithZero.unitsWithZeroEquiv (Multiplicative ℤ)
local notation "ℤₘ₀" => WithZero (Multiplicative ℤ)

namespace AdicCompletion

variable (v)

open Valued Set in
/-- Open balls at zero are closed in the `v`-adic completion of `K`. -/
theorem isClosed_nhds_zero (γ : ℤₘ₀ˣ) :
    IsClosed ({ y : v.adicCompletion K | Valued.v y < γ }) := by
  refine isClosed_iff_nhds.2 fun x hx => ?_
  simp only [Set.mem_setOf_eq] at hx ⊢
  contrapose! hx
  have h : Valued.v x ≠ 0 := by contrapose! hx; simp only [hx, Units.zero_lt]
  refine ⟨{ y | Valued.v y = Valued.v x }, loc_const h, subset_empty_iff.1 fun y hy => ?_⟩
  exact (not_le_of_lt <| mem_setOf.1 hy.2) <| hy.1.symm ▸ hx

/-- There is a basis of neighbourhoods of zero in `Kᵥ` that are contained inside `Oᵥ`.
Note: this is true of any DVR (but not of any `Valued`). -/
theorem hasBasis_nhds_zero : (nhds (0 : v.adicCompletion K)).HasBasis
    (fun (γ : ℤₘ₀ˣ) => γ ≤ 1) (fun γ => { x : v.adicCompletion K | Valued.v x < γ }) := by
  have hq : ∀ (γ : ℤₘ₀ˣ), True →
    ∃ (γ' : ℤₘ₀ˣ), True ∧ γ' ≤ 1 ∧
      { x : v.adicCompletion K | Valued.v x < γ' } ⊆
        { x : v.adicCompletion K | Valued.v x < γ } := by
    intro γ _
    choose π _ using exists_uniformizer K v
    by_cases hγ : 1 < γ
    · exact ⟨1, trivial, le_refl _, fun _ hx => lt_trans (Set.mem_setOf.1 hx) hγ⟩
    · exact ⟨γ, trivial, not_lt.1 hγ, subset_rfl⟩
  convert (Valued.hasBasis_nhds_zero _ _).restrict hq
  simp only [true_and]

/-- There is a basis of uniformity of `Kᵥ` with radii less than or equal to one.
Note: this is true of any DVR. -/
theorem hasBasis_uniformity : (uniformity (v.adicCompletion K)).HasBasis
    (fun (γ : ℤₘ₀ˣ) => γ ≤ 1) (fun (γ : ℤₘ₀ˣ) => { p | Valued.v (p.2 - p.1) < γ }) := by
  have hq : ∀ (γ : ℤₘ₀ˣ), True →
    ∃ (γ' : ℤₘ₀ˣ), True ∧ γ' ≤ 1 ∧
      { p : v.adicCompletion K × _ | Valued.v (p.2 - p.1) < γ' } ⊆
        { p | Valued.v (p.2 - p.1) < γ } := by
    intro γ _
    choose π _ using exists_uniformizer K v
    by_cases hγ : 1 < γ
    · exact ⟨1, trivial, le_refl _, fun _ hx => lt_trans (Set.mem_setOf.1 hx) hγ⟩
    · exact ⟨γ, trivial, not_lt.1 hγ, subset_rfl⟩
  convert (Valued.hasBasis_uniformity _ _).restrict hq
  simp only [true_and]

variable {K v}

open WithZero in
/-- Given an integer `γ` and some centre `y ∈ Kᵥ` we can always find an element `x ∈ Kᵥ`
outide of the open ball at `y` of radius `γ`. -/
theorem exists_not_mem_of_nhds (γ : ℤₘ₀ˣ) (y : v.adicCompletion K) :
    ∃ x : v.adicCompletion K, Valued.v (x - y) > γ := by
  choose π hπ using valuation_exists_uniformizer K v
  use π ^ (- Multiplicative.toAdd (μ γ) - 1) + y
  simp only [add_sub_cancel_right, unitsWithZeroEquiv_units_val, map_zpow₀,
    Valued.valuedCompletion_apply, v.adicValued_apply, hπ, gt_iff_lt, ← coe_zpow, coe_lt_coe,
    ← Multiplicative.toAdd_lt, ofAdd_neg, inv_zpow', neg_sub, sub_neg_eq_add, toAdd_zpow,
    toAdd_ofAdd, smul_eq_mul, mul_one, lt_add_iff_pos_left, zero_lt_one]

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

variable {K}

/-- An element of a positive power `n` of the maximal ideal of the `v`-adic integers has
valuation less than or equal to `-n`. -/
theorem valuation_le_pow_of_maximalIdeal {x : v.adicCompletionIntegers K} (n : ℕ)
    (hx : x ∈ Valued.maximalIdeal (v.adicCompletion K) ^ n) :
    Valued.v (x : v.adicCompletion K) ≤ Multiplicative.ofAdd (-n : ℤ) := by
  obtain ⟨π, hπ⟩ := exists_uniformizer K v
  rw [isUniformizer_is_generator hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, hxy⟩ := hx
  rw [hxy, Subring.coe_mul, Valued.v.map_mul, Subring.coe_pow, Valued.v.map_pow]
  apply le_trans <| mul_le_of_le_one_right' <| (v.mem_adicCompletionIntegers _ _).1 y.2
  rw [hπ, ← WithZero.coe_pow, WithZero.coe_le_coe, ofAdd_neg, ofAdd_neg, inv_pow,
    inv_le_inv_iff, ← one_mul (n : ℤ), Int.ofAdd_mul, zpow_natCast]

/-- Takes an `n`-tuple `(a₁, ..., aₙ)` and creates a `v`-adic integer using the `n`-tuple as
coefficients in a finite `v`-adic expansion in some fixed `v`-adic integer `π` as
`a₁ + a₂π + a₃π² + ...`. Note the definition does not require `π` to be a uniformizer. -/
def ofFiniteCoeffs (π : v.adicCompletionIntegers K) (n : ℕ) :
    (Fin n → v.adicCompletionIntegers K) → v.adicCompletionIntegers K :=
  fun x => ((List.ofFn x).mapIdx (fun i j => j * π^i)).sum

set_option synthInstance.maxHeartbeats 40000 in
/-- Given a uniformizer `π` of the `v`-adic integers and a `v`-adic integer `x`, there exists
an `n`-tuple of representatives in the residue field of the `v`-adic integers such that `x` can
be written as a finite `v`-adic expansion in `π` with coefficients given by the `n`-tuple. -/
theorem finite_expansion {π : v.adicCompletionIntegers K} (n : ℕ) (x : v.adicCompletionIntegers K)
    (hπ : IsUniformizer π.val) :
    ∃ (a : Fin n → Valued.ResidueField _),
      x - ((List.ofFn a).mapIdx fun i j => j.out' * π ^ i).sum ∈
        Valued.maximalIdeal (v.adicCompletion K) ^ n := by
  induction n with
  | zero =>
    simp only [Nat.zero_eq, List.ofFn_zero, List.mapIdx_nil, List.sum_nil, pow_zero,
        Ideal.one_eq_top, Submodule.mem_top, exists_const]
  | succ d hd =>
    obtain ⟨b, hbx⟩ := hd
    rw [isUniformizer_is_generator hπ, Ideal.span_singleton_pow] at hbx ⊢
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hbx
    use Fin.snoc b (Ideal.Quotient.mk (Valued.maximalIdeal (v.adicCompletion K)) z)
    simp only [List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append,
      List.mapIdx_append, List.length_ofFn, List.mapIdx_cons, zero_add, List.mapIdx_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    rw [← sub_sub, ← hz, ← sub_mul, Ideal.mem_span_singleton, pow_succ, mul_comm]
    apply mul_dvd_mul_right
    exact dvd_sub_comm.2 <| Ideal.Quotient.out_sub_dvd z (isUniformizer_is_generator hπ)

/-- Given a uniformizer `π` of the `v`-adic integers and a `v`-adic integer `x` modulo a power of
the maximal ideal, gives the coefficients of `x` in the finite `v`-adic expansion in `π` as an
`n`-tuple of representatives in the residue field.
-/
def toFiniteCoeffs {π : v.adicCompletionIntegers K} (n : ℕ) (hπ : IsUniformizer π.val) :
    v.adicCompletionIntegers K ⧸ (Valued.maximalIdeal (v.adicCompletion K)) ^ n
      → (Fin n → Valued.ResidueField (v.adicCompletion K)) :=
  fun x => Classical.choose (finite_expansion n x.out' hπ)

theorem toFiniteCoeffs_injective {π : v.adicCompletionIntegers K}
    (n : ℕ) (hπ : IsUniformizer π.val) : (toFiniteCoeffs n hπ).Injective := by
  intro x y hxy
  simp only [toFiniteCoeffs] at hxy
  have hx := Classical.choose_spec (finite_expansion n (Quotient.out' x) hπ)
  have hy := Classical.choose_spec (finite_expansion n (Quotient.out' y) hπ)
  rw [← Ideal.Quotient.mk_out' x, ← Ideal.Quotient.mk_out' y, Ideal.Quotient.eq,
    ← sub_sub_sub_cancel_right]
  exact Ideal.sub_mem _ hx (hxy ▸ hy)

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
  simp only [isClosed_iff_nhds, SetLike.mem_coe, mem_adicCompletionIntegers, not_le] at hx ⊢
  contrapose! hx
  refine ⟨{y | Valued.v y = Valued.v x}, loc_const (ne_zero_of_lt hx),
    subset_empty_iff.1 fun y ⟨hy₁, hy₂⟩ => ?_⟩
  rw [SetLike.mem_coe, mem_adicCompletionIntegers] at hy₂
  exact (not_lt_of_le <| hy₂) <| hy₁.symm ▸ hx

open WithZero Multiplicative Ideal in
/-- There is a finite covering of the `v`-adic integers of open balls of radius less than one,
obtained by using the finite representatives in the quotient of the `v`-adic integers by an
appropriate power of the maximal ideal. -/
theorem finite_subcover_of_uniformity_basis {γ : ℤₘ₀ˣ} (hγ : γ.val ≤ 1) :
    ∃ t : Set (v.adicCompletion K), Set.Finite t ∧
      ↑(adicCompletionIntegers K v) ⊆ ⋃ y ∈ t,
        { x | (x, y) ∈ { p | Valued.v (p.2 - p.1) < γ.val } } := by
  let M := (Valued.maximalIdeal (v.adicCompletion K)) ^ (- toAdd (μ γ) + 1).toNat
  obtain ⟨π, hπ⟩ := exists_uniformizer K v
  letI := quotient_maximalIdeal_pow_finite (-toAdd (μ γ) + 1).toNat hπ
  have h : Fintype ((v.adicCompletionIntegers K) ⧸ M) := Fintype.ofFinite _
  let T := h.elems.image Quotient.out'
  refine ⟨T.toSet, (Set.Finite.image _ (Finset.finite_toSet _)), fun x hx => ?_⟩
  simp only [Set.mem_iUnion]
  let y := Quotient.out' <| Ideal.Quotient.mk M ⟨x, hx⟩
  have h_mem : (Ideal.Quotient.mk M ⟨x, hx⟩).out' ∈ T := Finset.mem_image_of_mem _ (h.complete _)
  refine ⟨y, Set.mem_image_of_mem _ h_mem,
    lt_of_le_of_lt (valuation_le_pow_of_maximalIdeal _ (Ideal.Quotient.out_sub M _)) ?_⟩
  rw [unitsWithZeroEquiv_units_val, coe_lt_coe, ← ofAdd_toAdd (μ γ), ofAdd_lt, ofAdd_toAdd,
    Int.toNat_of_nonneg (units_toAdd_neg_add_one hγ)]
  linarith

/-- The `v`-adic integers is a totally bounded set since they afford a finite subcover of
open balls, obtained by using the finite representatives of the quotient of the `v`-adic
integers by a power of the maximal ideal. -/
theorem totallyBounded : TotallyBounded (v.adicCompletionIntegers K).carrier :=
  (hasBasis_uniformity K v).totallyBounded_iff.2 <| fun _ hγ =>
    finite_subcover_of_uniformity_basis K v hγ

instance completeSpace : CompleteSpace (v.adicCompletionIntegers K) :=
  IsClosed.completeSpace_coe (isClosed K v)

/-- The `v`-adic integers is compact. -/
theorem isCompact : IsCompact (v.adicCompletionIntegers K).carrier :=
  isCompact_iff_totallyBounded_isComplete.2
    ⟨totallyBounded K v, IsClosed.isComplete (isClosed K v)⟩

instance compactSpace : CompactSpace (v.adicCompletionIntegers K) :=
  CompactSpace.mk (isCompact_iff_isCompact_univ.1 <| isCompact K v)

end AdicCompletionIntegers

namespace AdicCompletion

open AdicCompletionIntegers

variable (v)

/-- Any open ball centred at zero in the `v`-adic completion of `K` is compact. -/
theorem isCompact_nhds_zero {γ : ℤₘ₀ˣ} (hγ : γ ≤ 1) :
    IsCompact { y : v.adicCompletion K | Valued.v y < γ } :=
  (isCompact K v).of_isClosed_subset (isClosed_nhds_zero K v γ)
      <| fun _ hx => le_of_lt (lt_of_lt_of_le (Set.mem_setOf.1 hx) hγ)

set_option synthInstance.maxHeartbeats 80000 in
/-- The `v`-adic completion of `K` is locally compact.
Note: slow search for `TopologicalAddGroup` instance of `v.adicCompletion K`. -/
instance locallyCompactSpace : LocallyCompactSpace (v.adicCompletion K) :=
  (isCompact_nhds_zero K v le_rfl).locallyCompactSpace_of_mem_nhds_of_addGroup
    <| (hasBasis_nhds_zero K v).mem_of_mem le_rfl


  end IsDedekindDomain.HeightOneSpectrum.AdicCompletion
