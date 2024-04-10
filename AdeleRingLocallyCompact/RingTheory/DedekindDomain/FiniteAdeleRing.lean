/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.AdicValuation

/-!
# Finite adele ring

Let `R` be a Dedekind domain of Krull dimension 1, `K` its field of fractions. The finite adele ring of
`K` is defined in `Mathlib.RingTheory.DedekindDomain.finiteAdeleRing`
[https://github.com/leanprover-community/mathlib4/blob/1c0ac885c9b8aa4daa1830acb56b755140a8059f/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean#L274-L280](https://github.com/leanprover-community/mathlib4/blob/1c0ac885c9b8aa4daa1830acb56b755140a8059f/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean#L274-L280).
In this file we supplement the theory by defining some local maps and the topological space for the finite adele ring.

## Main definitions
 - `DedekindDomain.FiniteAdeleRing.projection v` is the map sending a finite adele `x` to its `v`th place `x v` in
   the `v`-adic completion of `K`.
 - `DedekindDomain.FiniteAdeleRing.localInclusion v` is the map sending an element `x` of the `v`-adic completion
   of `K` to the finite adele which has `x` in its `v`th place and `1`s everywhere else.
 - `DedekindDomain.FiniteAdeleRing.generatingSet` is the generating set of the topology of the finite adele ring.

## Main results
 - `DedekindDomain.FiniteAdeleRing.topologicalSpace` : the topological space on the finite adele ring.

## References
 * [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
 * [M.I. de Frutos-Fernàndez, *Formalizing the Ring of Adèles of a Global Field*][defrutosfernandez2022]

## Tags
finite adele ring, dedekind domain

## TODO
 - Show that the finite adele ring is a topological ring
-/

noncomputable section

open DedekindDomain IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Classical

namespace DedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] (K : Type*)
  [Field K] [Algebra R K] [IsFractionRing R K]

namespace ProdAdicCompletions

def globalEmbedding : K →+* ProdAdicCompletions R K :=
  Pi.ringHom (λ v => AdicCompletion.coeRingHom K v)

variable {R}

/-- Sends an element of the product of all `adicCompletions` to a local place. -/
def projection (v : HeightOneSpectrum R) :
  ProdAdicCompletions R K →+* v.adicCompletion K :=
  Pi.evalRingHom _ v

/-- Sends a local element to the product of all `adicCompletions` filled with `1`s elsewhere. -/
def localInclusion (v : HeightOneSpectrum R) :
  v.adicCompletion K → ProdAdicCompletions R K :=
  λ x =>
    (λ w =>
      if hw : w = v then
        congrArg (λ v => v.adicCompletion K) hw ▸ x else
        (1 : w.adicCompletion K)
    )

variable {K}

/-- The local inclusion of any element is a finite adele. -/
theorem isFiniteAdele_localInclusion (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
  (localInclusion K v x).IsFiniteAdele := by
  rw [ProdAdicCompletions.IsFiniteAdele, Filter.eventually_cofinite]
  have h : setOf (λ w => localInclusion K v x w ∉ w.adicCompletionIntegers K) ⊆ {v} := by
    intro w hw
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hw ⊢
    contrapose! hw
    rw [localInclusion]
    simp only [hw, ↓reduceDite]
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

/-- Sends a finite adele to a local place. -/
def projection (v : HeightOneSpectrum R) :
  finiteAdeleRing R K →+* v.adicCompletion K :=
  RingHom.comp (Pi.evalRingHom _ v) (Subring.subtype _)

/-- Sends a local element to a finite adele filled with `1`s elsewhere. -/
def localInclusion (v : HeightOneSpectrum R) :
  v.adicCompletion K → finiteAdeleRing R K :=
  λ x => ⟨ProdAdicCompletions.localInclusion K v x,
          ProdAdicCompletions.isFiniteAdele_localInclusion v x⟩

local notation "π" => projection K
local notation "ι" => localInclusion K

variable {K}

/-- The `v`th place of the local inclusion is the original element. -/
theorem localInclusion_rfl (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : (ι v x).val v = x := by
  simp only [localInclusion, ProdAdicCompletions.localInclusion_rfl]

/-- The projection and local inclusions are inverses on the finite adele ring. -/
theorem projection_localInclusion_eq (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : π v (ι v x) = x := by
  convert localInclusion_rfl v x

variable (R K)

/-- The generating set of the finite adele ring are all sets of the form `Πᵥ Vᵥ`, where
each `Vᵥ` is open in `Kᵥ` and for all but finitely many `v` we have that `Vᵥ` is the `v`-adic
ring of integers. -/
def generatingSet : Set (Set (finiteAdeleRing R K)) :=
  Set.preimage (Subtype.val) '' (Set.pi Set.univ '' (
    setOf (
      λ V =>
        (∀ v, IsOpen (V v)) ∧
        (∀ᶠ v in Filter.cofinite, V v = v.adicCompletionIntegers K)
    )
  ))

instance topologicalSpace : TopologicalSpace (finiteAdeleRing R K)
  := TopologicalSpace.generateFrom (generatingSet R K)

/-- [https://github.com/mariainesdff/ideles/blob/e6646cd462c86a8813ca04fb82e84cdc14a59ad4/src/adeles_R.lean#L469](https://github.com/mariainesdff/ideles/blob/e6646cd462c86a8813ca04fb82e84cdc14a59ad4/src/adeles_R.lean#L469)-/
theorem continuous_add' :
    Continuous (λ x : finiteAdeleRing R K × finiteAdeleRing R K => x.1 + x.2) := by
  rw [continuous_generateFrom_iff]
  intro U ⟨V, ⟨W, hW, hWV⟩, hVU⟩
  rw [isOpen_prod_iff]
  intro x y hxy

  have hxy' : ∀ v, (x.val v, y.val v) ∈
      (λ p : v.adicCompletion K × v.adicCompletion K => p.1 + p.2) ⁻¹' W v := by
    intro v
    rw [← hVU, ← hWV] at hxy
    simp only [Set.mem_preimage, Subsemiring.coe_add, Subring.coe_toSubsemiring,] at hxy ⊢
    rw [Set.mem_univ_pi] at hxy
    exact hxy v

  have hW' : ∀ v, IsOpen
      ((λ p : v.adicCompletion K × v.adicCompletion K => p.1 + p.2) ⁻¹' W v) := by
    exact λ v => Continuous.isOpen_preimage continuous_add (W v) (hW.1 v)

  set Sx := (mem_finiteAdeleRing_iff _).1 x.property
  set Sy := (mem_finiteAdeleRing_iff _).1 y.property
  rw [ProdAdicCompletions.IsFiniteAdele] at Sx Sy
  set Sxy := Sx.toFinset ∪ Sy.toFinset
  set SV := hW.2.toFinset
  set S := Sxy ∪ SV

  -- define Vx, nhd of x, which is Oᵥ outside S, and left preimage of Wᵥ inside S
  set Vx := λ v => ite (v ∈ S)
    (Classical.choose (isOpen_prod_iff.1 (hW' v) _ _ (hxy' v)))
    (v.adicCompletionIntegers K)

  -- define Vy, nhd of y, which is Oᵥ outside S, and right preimage of Wᵥ inside S
  set Vy := λ v => ite (v ∈ S)
    (Classical.choose (Classical.choose_spec (isOpen_prod_iff.1 (hW' v) _ _ (hxy' v))))
    (v.adicCompletionIntegers K)

  use Subtype.val ⁻¹' Set.pi Set.univ Vx, Subtype.val ⁻¹' Set.pi Set.univ Vy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- Vx and Vy are in the generating set so open
  · apply TopologicalSpace.isOpen_generateFrom_of_mem
    unfold generatingSet
    simp
    refine ⟨Vx, ⟨?_, ?_⟩, rfl⟩
    · intro v
      by_cases hv : v ∈ S
      · simp only [Vx, hv, if_true]
        exact (Classical.choose_spec (Classical.choose_spec (isOpen_prod_iff.1 (hW' v) (x.1 v) (y.1 v) (hxy' v)))).1
      · simp [Vx, hv]
        exact Valued.valuationSubring_isOpen (v.adicCompletion K)
    · apply Set.Finite.subset S.finite_toSet
      intro v hv
      simp at hv
      contrapose! hv
      simp [Vx]
      intro h
      exfalso
      exact hv h
  · apply TopologicalSpace.isOpen_generateFrom_of_mem
    unfold generatingSet
    simp
    refine ⟨Vy, ⟨?_, ?_⟩, rfl⟩
    · intro v
      by_cases hv : v ∈ S
      · simp only [Vy, hv, if_true]
        exact (Classical.choose_spec (Classical.choose_spec (isOpen_prod_iff.1 (hW' v) (x.1 v) (y.1 v) (hxy' v)))).2.1
      · simp [Vy, hv]
        exact Valued.valuationSubring_isOpen (v.adicCompletion K)
    · apply Set.Finite.subset S.finite_toSet
      intro v hv
      simp at hv
      contrapose! hv
      simp [Vy]
      intro h
      exfalso
      exact hv h
  -- Vx contains x
  · intro v _
    simp only [Vx]
    split_ifs with h
    · exact (Classical.choose_spec (Classical.choose_spec (isOpen_prod_iff.1 (hW' v) (x.1 v) (y.1 v) (hxy' v)))).2.2.1
    · rw [Finset.not_mem_union, Finset.not_mem_union, Set.Finite.mem_toFinset, Set.mem_compl_iff, not_not] at h
      exact h.1.1
  -- Vy contains y
  · intro v _
    simp only [Vy]
    split_ifs with h
    · exact (Classical.choose_spec (Classical.choose_spec (isOpen_prod_iff.1 (hW' v) (x.1 v) (y.1 v) (hxy' v)))).2.2.2.1
    · rw [Finset.not_mem_union, Finset.not_mem_union] at h
      simp only [Set.Finite.mem_toFinset, Set.mem_compl_iff, not_not] at h
      exact h.1.2
  -- direct product of Vx and Vy is in the preimage of U
  · intro p
    simp only [Set.mem_prod, Set.mem_preimage]
    intro ⟨hp₁, hp₂⟩
    rw [← hVU, ← hWV]
    intro v _
    have h := (Classical.choose_spec (Classical.choose_spec (isOpen_prod_iff.1 (hW' v) (x.1 v) (y.1 v) (hxy' v)))).2.2.2.2
    by_cases hv : v ∈ S
    · rw [Set.mem_univ_pi] at hp₁ hp₂
      specialize hp₁ v
      specialize hp₂ v
      simp only [Vx, hv, if_true] at hp₁
      simp only [Vy, hv, if_true] at hp₂
      simp
      rw [← Set.image_subset_iff] at h
      apply h
      simp only [Set.mem_image, Set.mem_prod, Prod.exists]
      exact ⟨_, _, ⟨hp₁, hp₂⟩, rfl⟩
    · rw [Set.mem_univ_pi] at hp₁ hp₂
      specialize hp₁ v
      specialize hp₂ v
      simp only [Vx, hv, if_false] at hp₁
      simp only [Vy, hv, if_false] at hp₂
      rw [Finset.not_mem_union] at hv
      simp only [SV, Set.Finite.mem_toFinset, Set.mem_compl_iff, not_not, Set.mem_setOf_eq] at hv
      rw [hv.2]
      simp
      rw [Pi.add_apply]
      simp at hp₁ hp₂
      exact (v.adicCompletionIntegers K).add_mem' hp₁ hp₂

theorem continuous_mul' :
    Continuous (λ x : finiteAdeleRing R K × finiteAdeleRing R K => x.1 * x.2) := sorry

theorem continuous_neg' :
    Continuous (λ x : finiteAdeleRing R K => - x) := sorry

instance topologicalRing : TopologicalRing (finiteAdeleRing R K) where
  continuous_add := continuous_add' R K
  continuous_mul := continuous_mul' R K
  continuous_neg := continuous_neg' R K

/-- [https://github.com/mariainesdff/ideles/blob/e6646cd462c86a8813ca04fb82e84cdc14a59ad4/src/adeles_R.lean#L685](https://github.com/mariainesdff/ideles/blob/e6646cd462c86a8813ca04fb82e84cdc14a59ad4/src/adeles_R.lean#L685)-/
theorem globalEmbedding_isFiniteAdele (x : K) :
    ProdAdicCompletions.IsFiniteAdele (ProdAdicCompletions.globalEmbedding R K x) := by
  set supp := setOf (fun (v : HeightOneSpectrum R) =>
    (ProdAdicCompletions.globalEmbedding R K) x v ∉ adicCompletionIntegers K v
  )
  obtain ⟨r, ⟨d, hd⟩, hx⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  have hd_ne_zero : Ideal.span {d} ≠ (0 : Ideal R) := by
    rw [Ideal.zero_eq_bot, Ne.def, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.ne_zero hd
  have hsubset : supp ⊆ { v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {d}} := by
    intro v hv
    simp only [supp, mem_adicCompletionIntegers, not_le, not_lt, Set.mem_setOf_eq] at hv
    rw [Set.mem_setOf_eq, ← int_valuation_lt_one_iff_dvd]
    by_contra! h_one_le
    simp only [IsFractionRing.mk'_eq_div] at hx
    have h_val : Valued.v ((ProdAdicCompletions.globalEmbedding R K x v)) =
      Valued.v (x : v.adicCompletion K) := by
      have h : Pi.ringHom (λ v => AdicCompletion.coeRingHom K v) x v = (x : v.adicCompletion K) := by
        simp only [Pi.ringHom_apply]; rfl
      rw [← h, Pi.ringHom_apply]
      rfl
    simp only [h_val, Valued.valuedCompletion_apply, adicValued_apply, HeightOneSpectrum.valuation_def] at hv
    simp only [← hx, map_div₀, Valuation.extendToLocalization_apply_map_apply] at hv
    have h_val_d : intValuation v d = 1 :=
      by rw [←le_antisymm (v.int_valuation_le_one d) h_one_le]; rfl
    rw [h_val_d, div_one] at hv
    exact not_lt.2 (v.int_valuation_le_one r) hv
  exact Set.Finite.subset (Ideal.finite_factors hd_ne_zero) hsubset

def globalEmbedding : K →+* finiteAdeleRing R K where
  toFun := λ x => ⟨ProdAdicCompletions.globalEmbedding R K x, globalEmbedding_isFiniteAdele R K x⟩
  map_one' := rfl
  map_zero' := rfl
  map_mul' x y := by simp only [map_mul]; rfl
  map_add' x y := by simp only [map_add]; rfl

theorem nontrivial_of_nonEmpty [i : Nonempty (HeightOneSpectrum R)] :
    Nontrivial (finiteAdeleRing R K) := by
  obtain v := (Classical.inhabited_of_nonempty i).default
  use 0, ι v 1
  simp only [ne_eq, ← Subtype.val_inj, ZeroMemClass.coe_zero, localInclusion]
  unfold ProdAdicCompletions.localInclusion
  intro h
  have h := congrFun h v
  simp only [dif_pos] at h
  exact zero_ne_one h

theorem globalEmbedding_injective [i : Nonempty (HeightOneSpectrum R)] :
    Function.Injective (globalEmbedding R K) := by
  haveI := nontrivial_of_nonEmpty
  exact (globalEmbedding R K).injective

end FiniteAdeleRing

end DedekindDomain
