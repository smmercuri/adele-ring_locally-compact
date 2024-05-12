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
  have h : setOf (fun w => localInclusion K v x w ∉ w.adicCompletionIntegers K) ⊆ {v} := by
    intro w hw
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hw ⊢
    contrapose! hw
    simp only [localInclusion, hw, ↓reduceDite]
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
def projection (v : HeightOneSpectrum R) : finiteAdeleRing R K →+* v.adicCompletion K :=
  RingHom.comp (Pi.evalRingHom _ v) (Subring.subtype _)

/-- Sends a local element to a finite adele filled with `1`s elsewhere. -/
def localInclusion (v : HeightOneSpectrum R) : v.adicCompletion K → finiteAdeleRing R K :=
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

variable (R K)

/-- The generating set of the finite adele ring are all sets of the form `Πᵥ Vᵥ`, where
each `Vᵥ` is open in `Kᵥ` and for all but finitely many `v` we have that `Vᵥ` is the `v`-adic
ring of integers. -/
def generatingSet : Set (Set (finiteAdeleRing R K)) :=
  Set.preimage (Subtype.val) '' (Set.pi Set.univ '' (
    setOf (
      fun V =>
        (∀ v, IsOpen (V v)) ∧
        (∀ᶠ v in Filter.cofinite, V v = v.adicCompletionIntegers K)
    )
  ))

instance topologicalSpace : TopologicalSpace (finiteAdeleRing R K) :=
  TopologicalSpace.generateFrom (generatingSet R K)

variable {R K}

/-- Consider two finite adeles `x`, `y`, a generating open set `U` of the finite adele ring and a function
`f : finiteAdeleRing R K × finiteAdeleRing R K → finiteAdeleRing K` such that `(x, y)` is in the preimage of
`U` under `f`. If `f` factors through a collection of continuous maps `g v` defined at each place, which
each preserve the respective ring of integers, then we can obtain two open sets `X` and `Y` of the finite
adele ring, which contain `x` and `y` respectively, such that their product `X ×ˢ Y` is contained in the
preimage of `U` under `f`.

Abstracted version of
[https://github.com/mariainesdff/ideles/blob/e6646cd462c86a8813ca04fb82e84cdc14a59ad4/src/adeles_R.lean#L469](https://github.com/mariainesdff/ideles/blob/e6646cd462c86a8813ca04fb82e84cdc14a59ad4/src/adeles_R.lean#L469)-/
theorem comap_of_generateFrom_nhd₂
    {x y : finiteAdeleRing R K}
    {U : Set (finiteAdeleRing R K)}
    (f : finiteAdeleRing R K × finiteAdeleRing R K → finiteAdeleRing R K)
    (hf : ∃ g : (v : HeightOneSpectrum R) → v.adicCompletion K × v.adicCompletion K → v.adicCompletion K,
        ∀ v,
          (g v ∘ (RingHom.prodMap (π v) (π v)) = (π v) ∘ f
          ∧ Continuous (g v)
          ∧ ∀ (x y : v.adicCompletion K),
            x ∈ v.adicCompletionIntegers K
              → y ∈ v.adicCompletionIntegers K
              → g v (x, y) ∈ v.adicCompletionIntegers K
      )
    )
    (hU : U ∈ generatingSet R K)
    (hxy : (x, y) ∈ f⁻¹' U) :
      ∃ X Y : Set (finiteAdeleRing R K), IsOpen X ∧ IsOpen Y ∧ x ∈ X ∧ y ∈ Y ∧ X ×ˢ Y ⊆ f ⁻¹' U := by
  obtain ⟨V, ⟨W, hW, hWV⟩, hVU⟩ := hU
  obtain ⟨g, hg⟩ := hf
  rw [← hVU, ← hWV] at hxy
  have hxy_g : ∀ v, (x.val v, y.val v) ∈ (g v) ⁻¹' W v := by
    intro v
    have hxy_f : (x, y) ∈ (π v ∘ f)⁻¹' W v := by
      refine Set.mem_of_mem_of_subset hxy (λ z hz => ?_)
      simp only [Set.mem_preimage] at hz ⊢
      exact Set.mem_of_mem_of_subset (Set.mem_image_of_mem (Function.eval v) hz) Set.eval_image_univ_pi_subset
    rw [← (hg v).1] at hxy_f
    exact hxy_f
  have hW' := λ v => Continuous.isOpen_preimage (hg v).2.1 (W v) (hW.1 v)
  have h := λ v =>
    (Classical.choose_spec (Classical.choose_spec (isOpen_prod_iff.1 (hW' v) (x.1 v) (y.1 v) (hxy_g v))))
  set Sx := (mem_finiteAdeleRing_iff _).1 x.property
  set Sy := (mem_finiteAdeleRing_iff _).1 y.property
  set Sxy := Sx.toFinset ∪ Sy.toFinset
  set SW := hW.2.toFinset
  set S := Sxy ∪ SW
  set Vx := fun v => ite (v ∈ S)
    (Classical.choose (isOpen_prod_iff.1 (hW' v) _ _ (hxy_g v)))
    (v.adicCompletionIntegers K)
  set Vy := fun v => ite (v ∈ S)
    (Classical.choose (Classical.choose_spec (isOpen_prod_iff.1 (hW' v) _ _ (hxy_g v))))
    (v.adicCompletionIntegers K)
  use Subtype.val ⁻¹' Set.pi Set.univ Vx, Subtype.val ⁻¹' Set.pi Set.univ Vy
  refine ⟨?_, ?_, fun v _ => ?_, fun v _ => ?_, fun p ⟨hp₁, hp₂⟩ => ?_⟩ <;>
    try apply TopologicalSpace.isOpen_generateFrom_of_mem <;>
    simp only [generatingSet, Set.mem_image, exists_exists_and_eq_and]
  · refine ⟨Vx, ⟨fun v => ?_, ?_⟩, rfl⟩
    · simp only [Vx]
      split_ifs
      · exact (h v).1
      · exact Valued.valuationSubring_isOpen (v.adicCompletion K)
    · apply Set.Finite.subset S.finite_toSet
      rw [Set.compl_subset_comm]; simp only [Vx, ite_eq_right_iff]
      exact fun _ hv_compl hv => (hv_compl hv).elim
  · refine ⟨Vy, ⟨fun v => ?_, ?_⟩, rfl⟩
    · simp only [Vy]
      split_ifs
      · exact (h v).2.1
      · exact Valued.valuationSubring_isOpen (v.adicCompletion K)
    · apply Set.Finite.subset S.finite_toSet
      rw [Set.compl_subset_comm]; simp only [Vy, ite_eq_right_iff]
      exact λ _ hv_compl hv => (hv_compl hv).elim
  · simp only [Vx, S, Sxy]
    split_ifs with hv <;> simp only [Finset.not_mem_union, Set.Finite.mem_toFinset, Set.mem_compl_iff, not_not] at hv
    · exact (h v).2.2.1
    · exact hv.1.1
  · simp only [Vy, S, Sxy]
    split_ifs with hv <;> simp only [Finset.not_mem_union, Set.Finite.mem_toFinset, Set.mem_compl_iff, not_not] at hv
    · exact (h v).2.2.2.1
    · exact hv.1.2
  · rw [Set.mem_preimage, Set.mem_univ_pi] at hp₁ hp₂
    simp only [Vx, Vy] at hp₁ hp₂
    rw [← hVU, ← hWV];
    intro v _
    by_cases hv : v ∈ S <;> specialize hp₁ v <;> specialize hp₂ v <;> simp only [hv, if_true, if_false] at hp₁ hp₂
    · apply Set.image_subset_iff.2 (h v).2.2.2.2
      simp only [Set.mem_image, Set.mem_prod, Prod.exists]
      exact ⟨_, _, ⟨hp₁, hp₂⟩, congrFun ((hg v).1) p⟩
    · simp only [S, SW, Finset.not_mem_union, Set.Finite.mem_toFinset, Set.mem_compl_iff, not_not] at hv
      rw [hv.2, SetLike.mem_coe]
      have h_comm := congrFun ((hg v).1) p
      convert (hg v).2.2 _ _ hp₁ hp₂
      convert h_comm
      rw [h_comm]
      rfl

/-- If `f : finiteAdeleRing R K × finiteAdeleRing R K → finiteAdeleRing R K` factors through a collection
of continuous maps `g v` defined at each place, which each preserve the respective ring of integers, then
`f` is continuous. -/
theorem continuous_if_factors₂
    (f : finiteAdeleRing R K × finiteAdeleRing R K → finiteAdeleRing R K)
    (hf : ∃ g : (v : HeightOneSpectrum R) → v.adicCompletion K × v.adicCompletion K → v.adicCompletion K,
      ∀ v,
        (g v ∘ (RingHom.prodMap (π v) (π v)) = (π v) ∘ f
        ∧ Continuous (g v)
        ∧ ∀ (x y : v.adicCompletion K),
          x ∈ v.adicCompletionIntegers K
            → y ∈ v.adicCompletionIntegers K
            → g v (x, y) ∈ v.adicCompletionIntegers K
      )
    ) :
    Continuous f := by
  rw [continuous_generateFrom_iff]
  exact λ _ hU => isOpen_prod_iff.2 (λ _ _ hxy => comap_of_generateFrom_nhd₂ f hf hU hxy)

variable (R K)

/-- Addition on the finite adele ring factors through continuous maps `g v` defined at each place,
which preserve the ring of integers. -/
theorem add_factors :
    ∃ g : (v : HeightOneSpectrum R) → v.adicCompletion K × v.adicCompletion K → v.adicCompletion K,
      ∀ v,
        (g v ∘ (RingHom.prodMap (π v) (π v))
          = (π v) ∘ ((λ x : finiteAdeleRing R K × finiteAdeleRing R K => x.1 + x.2))
        ∧ Continuous (g v)
        ∧ ∀ (x y : v.adicCompletion K),
          x ∈ v.adicCompletionIntegers K
            → y ∈ v.adicCompletionIntegers K
            → g v (x, y) ∈ v.adicCompletionIntegers K
        ) :=
  ⟨λ v => (λ p : v.adicCompletion K × v.adicCompletion K => p.1 + p.2),
    λ v => ⟨rfl, continuous_add, (v.adicCompletionIntegers K).add_mem⟩⟩

/-- Multiplication on the finite adele ring factors through continuous maps `g v` defined at each place,
which preserve the ring of integers. -/
theorem mul_factors :
    ∃ g : (v : HeightOneSpectrum R) → v.adicCompletion K × v.adicCompletion K → v.adicCompletion K,
      ∀ v,
        (g v ∘ (RingHom.prodMap (π v) (π v))
          = (π v) ∘ ((λ x : finiteAdeleRing R K × finiteAdeleRing R K => x.1 * x.2))
        ∧ Continuous (g v)
        ∧ ∀ (x y : v.adicCompletion K),
          x ∈ v.adicCompletionIntegers K
            → y ∈ v.adicCompletionIntegers K
            → g v (x, y) ∈ v.adicCompletionIntegers K
        ) :=
  ⟨λ v => (λ p : v.adicCompletion K × v.adicCompletion K => p.1 * p.2),
    λ v => ⟨rfl, continuous_mul, (v.adicCompletionIntegers K).mul_mem⟩⟩

/-- Addition on the finite adele ring is continuous. -/
theorem continuous_add' :
    Continuous (λ x : finiteAdeleRing R K × finiteAdeleRing R K => x.1 + x.2) :=
  continuous_if_factors₂ _ (add_factors R K)

/-- Multiplication on the finite adele ring is continuous. -/
theorem continuous_mul' :
    Continuous (λ x : finiteAdeleRing R K × finiteAdeleRing R K => x.1 * x.2) :=
  continuous_if_factors₂ _ (mul_factors R K)

instance : ContinuousAdd (finiteAdeleRing R K) := ⟨continuous_add' R K⟩
instance : ContinuousMul (finiteAdeleRing R K) := ⟨continuous_mul' R K⟩
instance : ContinuousNeg (finiteAdeleRing R K) := TopologicalSemiring.continuousNeg_of_mul

/-- The topological ring structure on the finite adele ring. -/
instance topologicalRing : TopologicalRing (finiteAdeleRing R K) where
  continuous_add := continuous_add' R K
  continuous_mul := continuous_mul' R K

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
      by rw [← le_antisymm (v.int_valuation_le_one d) h_one_le]; rfl
    rw [h_val_d, div_one] at hv
    exact not_lt.2 (v.int_valuation_le_one r) hv
  exact Set.Finite.subset (Ideal.finite_factors hd_ne_zero) hsubset

/-- The global embedding sending an element `x ∈ K` to `(x)ᵥ` in the finite adele ring. -/
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
