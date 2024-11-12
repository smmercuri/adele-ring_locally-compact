/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.AdicValuation
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.Factorization

set_option linter.longLine false
/-!
# Finite adele ring

Let `R` be a Dedekind domain of Krull dimension 1, `K` its field of fractions. The finite adele
ring of `K` is defined as a topological ring in `Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing`.
In this file we supplement the theory by defining some local and global maps, and helper results
for working with the topological space of the the finite adele ring.

## Main definitions
 - `DedekindDomain.FiniteAdeleRing.localInclusion v` is the map sending an element `x` of the
   `v`-adic completion of `K` to the finite adele which has `x` in its `v`th place and `1`s
   everywhere else.

## Main results
 - `DedekindDomain.FiniteAdeleRing.dvd_of_valued_lt` : a finite adele is an `∏ v, Oᵥ` multiple of
   an integer `r` if the valuation of `x v` is less than the valuation of `r` for every `v`
   dividing `r`.
 - `DedekindDomain.FiniteAdeleRing.exists_not_mem_of_finite_nhds` : there exists a finite adele
   whose valuation is outside a finite collection of open balls.

## References
 * [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
 * [M.I. de Frutos-Fernàndez, *Formalizing the Ring of Adèles of a Global Field*][defrutosfernandez2022]

## Tags
finite adele ring, dedekind domain
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Classical

namespace DedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] (K : Type*)
  [Field K] [Algebra R K] [IsFractionRing R K]

namespace ProdAdicCompletions

def globalEmbedding : K →+* ProdAdicCompletions R K :=
  algebraMap K (ProdAdicCompletions R K)

@[simp]
theorem globalEmbedding_apply (x : K) : globalEmbedding R K x v = x := rfl

variable {R}

/-- Sends a local element to the product of all `adicCompletions` filled with `1`s elsewhere. -/
def localInclusion (v : HeightOneSpectrum R) :
    v.adicCompletion K → ProdAdicCompletions R K :=
  fun x =>
    (fun w =>
      if hw : w = v then
        congrArg (fun v => v.adicCompletion K) hw ▸ x else
        (1 : w.adicCompletion K)
    )

variable {K}

/-- The local inclusion of any element is a finite adele. -/
theorem localInclusion_isFiniteAdele (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    (localInclusion K v x).IsFiniteAdele := by
  rw [ProdAdicCompletions.IsFiniteAdele, Filter.eventually_cofinite]
  refine Set.Finite.subset (Set.finite_singleton v) (fun w hw => ?_)
  simp only [localInclusion, Set.mem_setOf_eq, Set.mem_singleton_iff] at hw ⊢
  contrapose! hw
  simp only [hw, ↓reduceDIte]
  exact (w.adicCompletionIntegers K).one_mem'

/-- The `v`th place of the local inclusion is the original element. -/
@[simp]
theorem localInclusion_apply (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    localInclusion K v x v = x := by
  simp only [localInclusion, dif_pos]

@[simp]
theorem localInclusion_apply' {v w : HeightOneSpectrum R} (x : v.adicCompletion K) (h : w ≠ v) :
    localInclusion K v x w = 1 := by
  simp only [localInclusion, h, ↓reduceDIte]

end ProdAdicCompletions

namespace FiniteAdeleRing

local notation "ℤₘ₀" => WithZero (Multiplicative ℤ)

variable {R}

@[simp]
theorem smul_apply (x : FiniteIntegralAdeles R K) (y : FiniteAdeleRing R K) :
    (x • y) v = x v * y v := rfl

@[simp]
theorem add_apply (x : FiniteAdeleRing R K) (y : FiniteAdeleRing R K) :
    (x + y) v = x v + y v := rfl

@[simp]
theorem sub_apply (x : FiniteAdeleRing R K) (y : FiniteAdeleRing R K) :
    (x - y) v = x v - y v := rfl

@[simp]
theorem mul_integer_apply (x : FiniteAdeleRing R K) (r : R) :
    (x * algebraMap _ _ r) v = x v * algebraMap _ _ r := rfl

/-- Sends a local element to a finite adele filled with `1`s elsewhere. -/
def localInclusion (v : HeightOneSpectrum R) : v.adicCompletion K → FiniteAdeleRing R K :=
  fun x => ⟨ProdAdicCompletions.localInclusion K v x,
          ProdAdicCompletions.localInclusion_isFiniteAdele v x⟩

variable {K}

/-- The `v`th place of the local inclusion is the original element. -/
@[simp]
theorem localInclusion_apply (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    (localInclusion K v x).val v = x := by
  simp only [localInclusion, ProdAdicCompletions.localInclusion_apply]

@[simp]
theorem localInclusion_apply' (v w : HeightOneSpectrum R) (x : v.adicCompletion K) (h : w ≠ v) :
    (localInclusion K v x).val w = 1 := by
  simp only [localInclusion, ProdAdicCompletions.localInclusion_apply' _ h]

def support (x : FiniteAdeleRing R K) := (Filter.eventually_cofinite.1 x.2).toFinset

/-- Given balls centred at `yᵥ` of radius `γᵥ` for a finite set of primes `v ∈ S`, we can find a
finite adele  `x` for which `xᵥ` is outside each open ball for `v ∈ S`. -/
theorem exists_not_mem_of_finite_nhds
    (S : Finset (HeightOneSpectrum R))
    (γ : (v : HeightOneSpectrum R) → ℤₘ₀ˣ)
    (y : FiniteAdeleRing R K) :
    ∃ (x : FiniteAdeleRing R K), ∀ v ∈ S, Valued.v (x v - y v) > γ v := by
  choose x hx using fun v => AdicCompletion.exists_not_mem_of_nhds (γ v) (y v)
  let y : ProdAdicCompletions R K := fun v => if v ∈ S then x v else 1
  have hy : y.IsFiniteAdele := by
    refine y.isFiniteAdele_iff.2 <| Set.Finite.subset S.finite_toSet (fun v hv => ?_)
    contrapose! hv
    simp only [Finset.mem_coe] at hv
    simp only [Set.mem_setOf_eq, not_not, y, hv, if_false, (v.adicCompletionIntegers K).one_mem]
  exact ⟨⟨y, hy⟩, fun v hv => by simp only [y, hv]; exact hx _⟩

/-- Clears the denominator of the subtraction of two finite adeles. -/
theorem sub_mul_nonZeroDivisor_mem_finiteIntegralAdeles
    (x y : FiniteAdeleRing R K) :
    ∃ (r : nonZeroDivisors R) (z : FiniteIntegralAdeles R K),
      (y - x) * algebraMap _ _ r.1 = algebraMap _ _ z := by
  choose r₁ s₁ hrs₁ using mul_nonZeroDivisor_mem_finiteIntegralAdeles y
  choose r₂ s₂ hrs₂ using mul_nonZeroDivisor_mem_finiteIntegralAdeles x
  refine ⟨r₁ * r₂, s₁ * algebraMap _ _ r₂.1 - s₂ * algebraMap _ _ r₁.1, ?_⟩
  rw [sub_mul, Submonoid.coe_mul, map_mul, ← mul_assoc, hrs₁]
  nth_rw 3 [mul_comm]
  rw [← mul_assoc, hrs₂]
  rfl

open AdicCompletion in
/-- Let `x` be a finite adele and let `r` be a non-zero integral divisor. If, for some finite
set of primes `v ∈ S` containing the factors of `r`, the valuation of `xᵥ` is less than the
valuation of `r`, then `x` is an integral multiple of the global embedding of `r`. -/
theorem dvd_of_valued_lt {x : FiniteAdeleRing R K} {r : nonZeroDivisors R}
    {S : Finset (HeightOneSpectrum R)}
    (hS : ∀ v, v.asIdeal ∣ Ideal.span {r.val} → v ∈ S)
    (hvS : ∀ v ∈ S, Valued.v (x v) < Valued.v (algebraMap _ (v.adicCompletion K) r.val))
    (hvnS : ∀ v ∉ S, x v ∈ v.adicCompletionIntegers K) :
    ∃ a : FiniteIntegralAdeles R K, a • (algebraMap _ _ r.val) = x := by
  have (v : HeightOneSpectrum R) :
      Valued.v (x v) ≤ Valued.v (algebraMap _ (v.adicCompletion K) r.val) := by
    by_cases hv : v ∈ S
    · exact le_of_lt <| hvS v hv
    · have : Valued.v (algebraMap _ (v.adicCompletion K) r.val) = 1 := by
        rw [v.valuedAdicCompletion_eq_valuation, v.valuation_eq_intValuationDef]
        exact le_antisymm (v.intValuation_le_one _)
          (not_lt.1 <| (v.intValuation_lt_one_iff_dvd _).1.mt <| (hS v).mt hv)
      exact this ▸ hvnS v hv
  choose a ha using fun v =>
    dvd_of_valued_le (this v) <| (map_ne_zero _).1 (v.algebraMap_valuation_ne_zero K r)
  exact ⟨a, FiniteAdeleRing.ext _ _ <| funext (fun v => ha v)⟩

@[simp]
theorem algebraMap_apply (x : K) : algebraMap K (FiniteAdeleRing R K) x v = x := rfl

theorem ext_iff {a₁ a₂ : FiniteAdeleRing R K} : a₁ = a₂ ↔ a₁.val = a₂.val := Subtype.ext_iff

variable (R K)

open ProdAdicCompletions in
theorem nontrivial_of_nonEmpty [i : Nonempty (HeightOneSpectrum R)] :
    Nontrivial (FiniteAdeleRing R K) := by
  obtain v := (Classical.inhabited_of_nonempty i).default
  exact ⟨0, algebraMap K _ 1, fun h => zero_ne_one (congrFun (ext_iff.1 h) v)⟩

theorem algebraMap_injective [i : Nonempty (HeightOneSpectrum R)] :
    Function.Injective (algebraMap K (FiniteAdeleRing R K)) := by
  letI := nontrivial_of_nonEmpty R K
  exact (algebraMap K _).injective

end FiniteAdeleRing

end DedekindDomain
