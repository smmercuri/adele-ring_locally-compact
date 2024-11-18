/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.AdicValuation
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.Factorization
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteAdeleRing

set_option linter.longLine false
/-!
# Finite adele ring

Let `R` be a Dedekind domain of Krull dimension 1, `K` its field of fractions. The finite adele
ring of `K` is defined as a topological ring in `Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing`.
The finite integral adeles is the product of the `v`-adic ring of integers as `v` ranges over the
primes of `R`, defined in `Mathlib.RingTheory.DedekindDomain.FiniteIntegralAdeles`.

This file contains a simplified proof that the finite adele ring is locally compact. This
uses the fact that the finite adele ring is a topological ring, so we need only show that
`0` has a compact neighbourhood. It suffices then to take `S = ∅` in the proof that uses
`FinsetAdeleRing R K S` in `FinsetAdeleRing.lean`. In this case, `FinsetAdeleRing R K ∅` is
simply the already defined `FiniteIntegralAdeles R K`. This is compact because we showed that
each of the ring of integers is compact. Moreover, it is a neighbourhood of zero because
the two topologies of the integral adeles when viewed as subspaces of `ProdAdicCompletions R K`
and of the finite adele ring are the same.

## Main results
 - `DedekindDomain.FiniteIntegralAdeles.algebraMap_inducing` : the map sending integral adeles to
   finite adeles is inducing; equivalently, the topology of the integral adeles when viewed as
   a subspace of the finite adele ring is equal to the topology when viewed as a subspace of
   `ProdAdicCompletions R K`.
 - `DedekindDomain.FiniteIntegralAdeles.compactSpace` : the integral adeles are locally
   compact.
 - `DedekindDomain.FiniteAdeleRing.locallyCompactSpace` : the finite adele ring is locally compact.

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

namespace FiniteIntegralAdeles

local notation "ι" => algebraMap (FiniteIntegralAdeles R K) (FiniteAdeleRing R K)

@[simp]
theorem mul_integer_apply (x : FiniteIntegralAdeles R K) (r : R) :
    (x * algebraMap _ _ r) v = x v * algebraMap _ _ r := rfl

theorem algebraMap_injective : Function.Injective ι := by
  intro x y hxy
  simp only [algebraMap, Algebra.toRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk] at hxy
  rw [Subtype.mk.injEq] at hxy
  funext v
  convert Function.funext_iff.1 hxy v
  rw [SetLike.coe_eq_coe]

theorem TopologicalAddGroup.inducing_iff_nhds_zero {G H : Type w} [AddGroup G] [TopologicalSpace G]
    [AddGroup H] [TopologicalAddGroup G] [TopologicalSpace H] [TopologicalAddGroup H] (f : G →+ H) :
    Inducing f ↔ nhds 0 = Filter.comap f (nhds 0) := by
  rw [inducing_iff_nhds]
  refine ⟨fun h => f.map_zero ▸ h 0, fun h x => ?_⟩
  rw [← nhds_translation_sub x, h, Filter.comap_comm, Filter.comap_comap,
    ← nhds_translation_sub (f x), Filter.comap_comap]
  exact Function.funext_iff.2 <| fun _ => by simp only [Function.comp_apply, map_sub]

theorem TopologicalRing.inducing_iff_nhds_zero {G H : Type w} [Ring G] [TopologicalSpace G]
    [Ring H] [TopologicalRing G] [TopologicalSpace H] [TopologicalRing H] (f : G →+* H) :
    Inducing f ↔ nhds 0 = Filter.comap f (nhds 0) := by
  rw [← AddMonoidHom.coe_coe, ← RingHom.toAddMonoidHom_eq_coe]
  exact TopologicalAddGroup.inducing_iff_nhds_zero (RingHom.toAddMonoidHom f)

variable {R}

local notation "ℤₘ₀" => WithZero (Multiplicative ℤ)

/-- Given a finite set of primes `v` and an open ball in each, we can find a global integer that
lies in each of the balls.
-/
theorem nonZeroDivisor_mem_finite_nhds_zero
    (S : Set (HeightOneSpectrum R))
    (hS : Set.Finite S)
    (γ : (v : HeightOneSpectrum R) → ℤₘ₀ˣ) :
    ∃ (r : nonZeroDivisors R), ∀ v ∈ S, Valued.v (algebraMap _ (v.adicCompletion K) r.1) < γ v := by
  choose s hs using fun v => AdicCompletion.nonZeroDivisor_mem_nhds_zero K v (γ v)
  refine ⟨hS.toFinset.prod s, fun v hv => ?_⟩
  simp only [Submonoid.coe_finset_prod, map_prod]
  rw [← hS.toFinset.prod_erase_mul _ (hS.mem_toFinset.2 hv)]
  refine mul_lt_of_le_one_of_lt (Finset.prod_le_one' (fun _ _ => ?_)) (hs v)
  rw [v.valuedAdicCompletion_eq_valuation]
  exact v.valuation_le_one _

variable (R)

/-- The embedding of the integral adeles into the finite adele ring preserves neighbourhoods. -/
theorem algebraMap_image_mem_nhds
    {U : Set (FiniteIntegralAdeles R K)} (h : U ∈ nhds 0) :
    ι '' U ∈ nhds 0 := by
  simp only [(RingSubgroupsBasis.hasBasis_nhds_zero _).mem_iff, true_and,
    Subtype.exists, exists_prop]
  rw [nhds_pi, Filter.mem_pi] at h
  obtain ⟨I, hI, V, hV, hVU⟩ := h
  simp_rw [mem_nhds_subtype] at hV
  choose V hV using fun v => hV v
  choose γ hγ using fun v => Valued.mem_nhds_zero.1 <| (hV v).1
  choose r hr using nonZeroDivisor_mem_finite_nhds_zero K I hI (fun v => (γ v))
  refine ⟨r, r.2, fun z hz => ?_⟩
  simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, Submodule.mem_span_singleton] at hz
  apply (Set.image_subset_image_iff (algebraMap_injective R K)).2 hVU
  obtain ⟨a, rfl⟩ := hz
  use a * (algebraMap _ _ r.1)
  refine ⟨fun v hv => (hV v).2 (hγ v ?_), rfl⟩
  rw [mul_integer_apply, Set.mem_setOf_eq, Submonoid.coe_mul, map_mul]
  apply lt_of_le_of_lt <| mul_le_mul_right' ((v.mem_adicCompletionIntegers R K).1 (a v).2) _
  rw [one_mul]
  exact hr v hv

open FiniteAdeleRing Ideal in
/-- The pullback of a neighbourhood in the finite adele ring is a neighbourhood in the
integral adeles. -/
theorem mem_nhds_comap_algebraMap
    {U : Set (FiniteIntegralAdeles R K)} (h : U ∈ Filter.comap ι (nhds 0)) :
    U ∈ nhds 0 := by
  rw [nhds_pi, Filter.mem_pi]
  simp only [Filter.mem_comap, (RingSubgroupsBasis.hasBasis_nhds_zero _).mem_iff, true_and] at h
  obtain ⟨t, ⟨r, hrt⟩, htU⟩ := h
  refine ⟨_, factors_finset_of_nonZeroDivisor r |>.finite_toSet, ?_, ?_⟩
  use fun v => { y | Valued.v y.1 < Valued.v (algebraMap _ (v.adicCompletion K) r.1) }
  let γr (v : HeightOneSpectrum R) :=
    (isUnit_iff_ne_zero.2 (v.algebraMap_valuation_ne_zero K r))
  refine ⟨?_, subset_trans (fun y hy => hrt ?_) htU⟩
  · intro v
    simp only [mem_nhds_subtype, Pi.zero_apply v, ZeroMemClass.coe_zero, Valued.mem_nhds_zero]
    refine ⟨{ x | Valued.v x < (γr v).unit }, ⟨(γr v).unit, subset_rfl⟩, ?_⟩
    simp only [SetLike.coe_sort_coe, Set.preimage_setOf_eq, Set.setOf_subset_setOf]
    exact fun _ h => h
  · simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, Submodule.mem_span_singleton]
    exact dvd_of_valued_lt (fun _ hv => (Set.Finite.mem_toFinset _).2 hv) hy (fun v _ => (y v).2)

open TopologicalRing in
/-- The topologies of the integral adeles when viewed as a subspace of
`ProdAdicCompletions R K` and as a subspace of the finite adele ring coincide. -/
theorem algebraMap_inducing : Inducing ι := by
  rw [inducing_iff_nhds_zero]
  refine Filter.ext (fun U => ⟨fun hU => ?_, mem_nhds_comap_algebraMap R K⟩)
  exact ⟨ι '' U, algebraMap_image_mem_nhds R K hU,
    by rw [(algebraMap_injective R K).preimage_image]⟩

/-- The integral adeles are compact. -/
theorem compactSpace : CompactSpace (FiniteIntegralAdeles R K) :=
  Pi.compactSpace

theorem isCompact : IsCompact (Set.range ι) := by
  rw [← Set.image_univ, ← (algebraMap_inducing R K).isCompact_iff]
  exact (compactSpace R K).isCompact_univ

end FiniteIntegralAdeles

namespace FiniteAdeleRing

open FiniteIntegralAdeles

local notation "ι" => algebraMap (FiniteIntegralAdeles R K) (FiniteAdeleRing R K)

/-- The image of the embedding from the finite integral adeles to the finite adele ring is
a neighbourhood of zero. -/
theorem algebraMap_range_mem_nhds' : Set.range ι ∈ nhds 0 :=
  Set.image_univ ▸ algebraMap_image_mem_nhds R K (Filter.univ_mem)

/-- The finite adele ring is locally compact. -/
theorem locallyCompactSpace' : LocallyCompactSpace (FiniteAdeleRing R K) :=
  IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup (isCompact R K)
    (algebraMap_range_mem_nhds' R K)

end DedekindDomain.FiniteAdeleRing
