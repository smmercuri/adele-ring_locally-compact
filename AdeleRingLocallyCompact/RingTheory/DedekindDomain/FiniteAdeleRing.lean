/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.AdicValuation

/-!
# Finite adele ring

Let `R` be a Dedekind domain of Krull dimension 1, `K` its field of fractions. The finite adele
ring of `K` is defined in `Mathlib.RingTheory.DedekindDomain.finiteAdeleRing`
[https://github.com/leanprover-community/mathlib4/blob/1c0ac885c9b8aa4daa1830acb56b755140a8059f/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean#L274-L280](https://github.com/leanprover-community/mathlib4/blob/1c0ac885c9b8aa4daa1830acb56b755140a8059f/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean#L274-L280).
In this file we supplement the theory by defining some local maps and the topological space for
the finite adele ring.

## Main definitions
 - `DedekindDomain.FiniteAdeleRing.projection v` is the map sending a finite adele `x` to its
   `v`th place `x v` in the `v`-adic completion of `K`.
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
  Pi.ringHom (fun v => AdicCompletion.coeRingHom K v)

variable {R}

/-- Sends an element of the product of all `adicCompletions` to a local place. -/
def projection (v : HeightOneSpectrum R) :
    ProdAdicCompletions R K →+* v.adicCompletion K :=
  Pi.evalRingHom _ v

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
theorem isFiniteAdele_localInclusion (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    (localInclusion K v x).IsFiniteAdele := by
  rw [ProdAdicCompletions.IsFiniteAdele, Filter.eventually_cofinite]
  have h : {w | localInclusion K v x w ∉ w.adicCompletionIntegers K} ⊆ {v} := by
    intro w hw
    simp only [localInclusion, Set.mem_setOf_eq, Set.mem_singleton_iff] at hw ⊢
    contrapose! hw
    simp only [hw, ↓reduceDIte]
    exact (w.adicCompletionIntegers K).one_mem'
  exact Set.Finite.subset (Set.finite_singleton _) h

/-- The `v`th place of the local inclusion is the original element. -/
theorem localInclusion_rfl (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    localInclusion K v x v = x := by simp only [localInclusion, dif_pos]

/-- The projection and local inclusions are inverses on `ProdAdicCompletions`. -/
theorem projection_localInclusion_eq (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    projection K v (localInclusion K v x) = x := by convert localInclusion_rfl v x

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

/-- Sends a finite adele to a local place. -/
def projection (v : HeightOneSpectrum R) : FiniteAdeleRing R K →+* v.adicCompletion K :=
  RingHom.comp (Pi.evalRingHom _ v) (FiniteAdeleRing.subalgebra R K).subtype

/-- Sends a local element to a finite adele filled with `1`s elsewhere. -/
def localInclusion (v : HeightOneSpectrum R) : v.adicCompletion K → FiniteAdeleRing R K :=
  fun x => ⟨ProdAdicCompletions.localInclusion K v x,
          ProdAdicCompletions.isFiniteAdele_localInclusion v x⟩

local notation "π" => projection K
local notation "ι" => localInclusion K

variable {K}

/-- The `v`th place of the local inclusion is the original element. -/
theorem localInclusion_rfl (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    (ι v x).val v = x := by
  simp only [localInclusion, ProdAdicCompletions.localInclusion_rfl]

/-- The projection and local inclusions are inverses on the finite adele ring. -/
theorem projection_localInclusion_eq (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    π v (ι v x) = x := by
  apply localInclusion_rfl v x

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
    simp only [Set.mem_setOf_eq, y, hv, if_false, one_mem, not_not]
  refine ⟨⟨y, hy⟩, fun v hv => ?_⟩
  simp only [y, hv, if_true]
  exact hx _

theorem dvd_of_valued_lt {x : FiniteAdeleRing R K} {r : nonZeroDivisors R}
    {S : Finset (HeightOneSpectrum R)}
    (hS : ∀ v, v.asIdeal ∣ Ideal.span {r.val} → v ∈ S)
    (h : ∀ v ∈ S, Valued.v (x v) < Valued.v (algebraMap _ (v.adicCompletion K) r.val))
    (h' : ∀ v ∉ S, x v ∈ v.adicCompletionIntegers K) :
    ∃ a : FiniteIntegralAdeles R K, a • (algebraMap _ _ r.val) = x := by
  have : ∀ v : HeightOneSpectrum R, Valued.v (x v) ≤ Valued.v (algebraMap _ (v.adicCompletion K) r.val) := by
    intro v
    by_cases hv : v ∈ S
    · exact le_of_lt <| h v hv
    · have : Valued.v (algebraMap _ (v.adicCompletion K) r.val) = 1 := by
        rw [v.valuedAdicCompletion_eq_valuation]
        rw [v.valuation_eq_intValuationDef]
        have := not_lt.1 <| (v.intValuation_lt_one_iff_dvd _).1.mt <| (hS v).mt hv
        exact le_antisymm (v.intValuation_le_one _) this
      rw [this]
      exact h' v hv
  have hr (v : HeightOneSpectrum R) : Valued.v ((algebraMap R (v.adicCompletion K)) r.val) ≠ 0 := by
    rw [v.valuedAdicCompletion_eq_valuation]
    simp only [ne_eq, map_eq_zero]
    rw [IsFractionRing.to_map_eq_zero_iff]
    exact nonZeroDivisors.coe_ne_zero _
  choose a ha using fun v => AdicCompletion.dvd_of_valued_le (this v) ((map_ne_zero _).1 (hr v))
  use a
  ext
  funext v
  exact ha v

variable (R K)

/-- The element `(x)ᵥ` where `x ∈ K` is a finite adele.

[https://github.com/mariainesdff/ideles/blob/e6646cd462c86a8813ca04fb82e84cdc14a59ad4/src/adeles_R.lean#L685](https://github.com/mariainesdff/ideles/blob/e6646cd462c86a8813ca04fb82e84cdc14a59ad4/src/adeles_R.lean#L685)-/
theorem globalEmbedding_isFiniteAdele (x : K) :
    ProdAdicCompletions.IsFiniteAdele (ProdAdicCompletions.globalEmbedding R K x) := by
  set supp := setOf (fun (v : HeightOneSpectrum R) =>
    (ProdAdicCompletions.globalEmbedding R K) x v ∉ adicCompletionIntegers K v
  )
  obtain ⟨r, ⟨d, hd⟩, hx⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  have hd_ne_zero : Ideal.span {d} ≠ (0 : Ideal R) := by

    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.ne_zero hd
  have hsubset : supp ⊆ { v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {d}} := by
    intro v hv
    simp only [supp, mem_adicCompletionIntegers, not_le, not_lt, Set.mem_setOf_eq] at hv
    rw [Set.mem_setOf_eq, ← intValuation_lt_one_iff_dvd]
    by_contra! h_one_le
    simp only [IsFractionRing.mk'_eq_div] at hx
    have h_val : Valued.v ((ProdAdicCompletions.globalEmbedding R K x v)) =
      Valued.v (x : v.adicCompletion K) := by
      have h : Pi.ringHom (λ v => AdicCompletion.coeRingHom K v) x v
          = (x : v.adicCompletion K) := by
        simp only [Pi.ringHom_apply]; rfl
      rw [← h, Pi.ringHom_apply]
      rfl
    simp only [h_val, Valued.valuedCompletion_apply, adicValued_apply,
      HeightOneSpectrum.valuation_def, ] at hv
    simp only [← hx, map_div₀, Valuation.extendToLocalization_apply_map_apply] at hv
    have h_val_d : intValuation v d = 1 :=
      by rw [← le_antisymm (v.intValuation_le_one d) h_one_le]; rfl
    rw [h_val_d, div_one] at hv
    exact not_lt.2 (v.intValuation_le_one r) hv
  exact Set.Finite.subset (Ideal.finite_factors hd_ne_zero) hsubset

/-- The global embedding sending an element `x ∈ K` to `(x)ᵥ` in the finite adele ring. -/
def globalEmbedding : K →+* FiniteAdeleRing R K where
  toFun := λ x => ⟨ProdAdicCompletions.globalEmbedding R K x, globalEmbedding_isFiniteAdele R K x⟩
  map_one' := rfl
  map_zero' := rfl
  map_mul' x y := by simp only [map_mul]; rfl
  map_add' x y := by simp only [map_add]; rfl

theorem nontrivial_of_nonEmpty [i : Nonempty (HeightOneSpectrum R)] :
    Nontrivial (FiniteAdeleRing R K) := by
  obtain v := (Classical.inhabited_of_nonempty i).default
  use ⟨0, DedekindDomain.ProdAdicCompletions.IsFiniteAdele.zero⟩, ι v 1
  simp only [localInclusion]
  intro h
  rw [Subtype.mk.injEq] at h
  have h := congrFun h v
  simp only [ProdAdicCompletions.localInclusion, dif_pos] at h
  exact zero_ne_one h

theorem globalEmbedding_injective [i : Nonempty (HeightOneSpectrum R)] :
    Function.Injective (globalEmbedding R K) := by
  letI := nontrivial_of_nonEmpty
  exact (globalEmbedding R K).injective

end FiniteAdeleRing

end DedekindDomain
