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
ring of `K` is defined in `Mathlib.RingTheory.DedekindDomain.finiteAdeleRing`
[https://github.com/leanprover-community/mathlib4/blob/1c0ac885c9b8aa4daa1830acb56b755140a8059f/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean#L274-L280](https://github.com/leanprover-community/mathlib4/blob/1c0ac885c9b8aa4daa1830acb56b755140a8059f/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean#L274-L280).
In this file we supplement the theory by defining some local maps and the topological space for
the finite adele ring.

## Main definitions
 - `DedekindDomain.FiniteAdeleRing.localInclusion v` is the map sending an element `x` of the
   `v`-adic completion of `K` to the finite adele which has `x` in its `v`th place and `1`s
   everywhere else.
 - `DedekindDomain.FiniteAdeleRing.generatingSet` is the generating set of the topology of
   the finite adele ring.

## Main results
 - `DedekindDomain.FiniteAdeleRing.continuous_if_factors₂` : Any map on the product
   of the finite adele ring to the finite adele ring is continuous if it factors through
   continuous maps at each place `v`, each of which preserve the integers.
 - `DedekindDomain.FiniteAdeleRing.topologicalRing` : the topological ring structure on the finite
   adele ring.

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
    localInclusion K v x v = x := by simp only [localInclusion, dif_pos]

@[simp]
theorem localInclusion_apply' {v w : HeightOneSpectrum R} (x : v.adicCompletion K) (h : w ≠ v) :
    localInclusion K v x w = 1 := by simp only [localInclusion, h, ↓reduceDIte]

end ProdAdicCompletions

namespace FiniteAdeleRing

variable {R}

@[simp]
theorem smul_apply (x : FiniteIntegralAdeles R K) (y : FiniteAdeleRing R K) :
    (x • y) v = x v * y v := rfl

@[simp]
theorem add_apply (x : FiniteAdeleRing R K) (y : FiniteAdeleRing R K) :
    (x + y) v = x v + y v := rfl

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

theorem exists_nmem_of_finite_open_balls
    (S : Finset (HeightOneSpectrum R))
    (γ : (v : HeightOneSpectrum R) → (WithZero (Multiplicative ℤ))ˣ)
    (y : FiniteAdeleRing R K) :
    ∃ (x : FiniteAdeleRing R K), ∀ v ∈ S, Valued.v (x v - y v) > γ v := by
  choose x hx using fun v => AdicCompletion.exists_nmem_of_open_ball (γ v) (y v)
  let y : ProdAdicCompletions R K := fun v => if v ∈ S then x v else 1
  have hy : y.IsFiniteAdele := by
    refine y.isFiniteAdele_iff.2 <| Set.Finite.subset S.finite_toSet (fun v hv => ?_)
    contrapose! hv
    simp only [Finset.mem_coe] at hv
    simp only [Set.mem_setOf_eq, not_not, y, hv, if_false, (v.adicCompletionIntegers K).one_mem]
  refine ⟨⟨y, hy⟩, fun v hv => ?_⟩
  simp only [y, hv, if_true]
  exact hx _

open AdicCompletion in
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

variable (R K)

open Valued ProdAdicCompletions in
/-- The element `(x)ᵥ` where `x ∈ K` is a finite adele.

[https://github.com/mariainesdff/ideles/blob/e6646cd462c86a8813ca04fb82e84cdc14a59ad4/src/adeles_R.lean#L685](https://github.com/mariainesdff/ideles/blob/e6646cd462c86a8813ca04fb82e84cdc14a59ad4/src/adeles_R.lean#L685)-/
theorem globalEmbedding_isFiniteAdele (x : K) :
    ProdAdicCompletions.IsFiniteAdele (ProdAdicCompletions.globalEmbedding R K x) := by
  let S := { v : HeightOneSpectrum R | (globalEmbedding R K) x v ∉ adicCompletionIntegers K v }
  obtain ⟨r, d, hx⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  have hsubset : S ⊆ (Ideal.factorsFinset_of_nonZeroDivisor d).toSet := by
    intro v hv
    simp only [S, mem_adicCompletionIntegers, not_le, not_lt, Set.mem_setOf_eq] at hv
    rw [Set.Finite.coe_toFinset]
    contrapose! hv
    simp only [IsFractionRing.mk'_eq_div] at hx
    simp only [globalEmbedding_apply, valuedCompletion_apply, adicValued_apply, ← hx, map_div₀]
    have h_val_d : v.valuation (algebraMap R K d) = 1 := by
      apply le_antisymm (v.valuation_le_one d)
      contrapose! hv
      exact (v.valuation_lt_one_iff_dvd _).1 hv
    rw [h_val_d, div_one]
    exact v.valuation_le_one _
  exact Set.Finite.subset (Finset.finite_toSet _) hsubset

/-- The global embedding sending an element `x ∈ K` to `(x)ᵥ` in the finite adele ring.

TODO : this can be changed to algebraMap K (FiniteAdeleRing R K). -/
def globalEmbedding : K →+* FiniteAdeleRing R K where
  toFun := fun x => ⟨ProdAdicCompletions.globalEmbedding R K x, globalEmbedding_isFiniteAdele R K x⟩
  map_one' := rfl
  map_zero' := rfl
  map_mul' x y := by simp only [map_mul]; rfl
  map_add' x y := by simp only [map_add]; rfl

@[simp]
theorem globalEmbedding_apply (x : K) : globalEmbedding R K x v = x := rfl

variable {R K}

theorem ext_iff {a₁ a₂ : FiniteAdeleRing R K} : a₁ = a₂ ↔ a₁.val = a₂.val :=
  Subtype.ext_iff

variable (R K)

open ProdAdicCompletions in
theorem nontrivial_of_nonEmpty [i : Nonempty (HeightOneSpectrum R)] :
    Nontrivial (FiniteAdeleRing R K) := by
  obtain v := (Classical.inhabited_of_nonempty i).default
  exact ⟨⟨0, IsFiniteAdele.zero⟩, globalEmbedding R K 1, fun h =>
    zero_ne_one (congrFun (ext_iff.1 h) v)⟩

theorem globalEmbedding_injective [i : Nonempty (HeightOneSpectrum R)] :
    Function.Injective (globalEmbedding R K) := by
  letI := nontrivial_of_nonEmpty
  exact (globalEmbedding R K).injective

end FiniteAdeleRing

end DedekindDomain
