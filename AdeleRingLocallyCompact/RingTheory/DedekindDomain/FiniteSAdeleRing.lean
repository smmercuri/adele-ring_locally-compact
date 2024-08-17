/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteAdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.AdicValuation

/-!
# Finite S-adele ring

Let `R` be a Dedekind domain of Krull dimension 1, `K` its field of fractions and `S` a
finite set of finite places `v` of `K`. In this file we define the finite S-adele ring, whose
carrier is the set of all elements in `ProdAdicCompletions R K` which are in the `v`-adic ring
of integers outside of `S`, and we show that this is locally compact. The finite S-adele ring
affords an open embedding into the regular finite adele ring and, moreover, cover the finite
adele ring. This allows us to show that the finite adele ring is also locally compact.

## Main definitions
 - `DedekindDomain.SProdAdicCompletions R K S` is the `DedekindDomain.ProdAdicCompletions R K`
   split into a product along the predicate `v ∈ S`.
 - `DedekindDomain.SProdAdicCompletionIntegers` is the direct product whose left type
   is the product of the `v`-adic completions of `K` over all `v ∈ S` and whose right type is
   the product of the `v`-adic ring of integers over all `v ∉ S`.
 - `DedekindDomain.SProdAdicCompletionIntegers_subtype` is the subtype of
   `DedekindDomain.SProdAdicCompletions R K S` analogous to `DedekindDomain.SProdAdicCompletionIntegers`.
 - `DedekindDomain.finiteSAdeleRing` is the subring of `ProdAdicCompletions R K` of all finite
   S-adeles.
 - `DedekindDomain.FiniteSAdeleRing.toFiniteAdeleRing` is the map embedding the finite S-adele
   ring into the finite adele ring.
 - `DedekindDomain.FiniteSAdeleRing.topologicalSpace` is the topological space of the finite
   S-adele ring, viewed as a subspace of the finite adele ring; this is shown to be equivalent
   to the topology when viewed as a subspace of `ProdAdicCompletions R K` (that these topologies
   coincide is an important part of what allows us to show that the finite S-adele ring is
   locally compact).

## Main results
 - `DedekindDomain.FiniteSAdeleRing.toFiniteAdeleRing_openEmbedding` : the map sending finite
   S-adeles to finite adeles is an open embedding; this is crucial so that when we can push
   the S-adeles to an open covering of the finite adele ring.
 - `DedekindDomain.FiniteSAdeleRing.generatingSet_eq` : the generating set of the subspace
   topology of the finite S-adele ring when viewed as a subspace of the finite adele ring is
   equal to the generating set of the subspace topology when viewed as a subspace of
   `ProdAdicCompletions R K` and so these two topologies coincide.
 - `DedekindDomain.FiniteSAdeleRing.homeomorph_piSubtypeProd` : the finite S-adele ring is
   homeomorphic to `DedekindDomain.SProdAdicCompletionIntegers_subtype`.
 - `DedekindDomain.FiniteSAdeleRing.locallyCompactSpace` : the finite S-adele ring is locally
   compact.
 - `DedekindDomain.FiniteAdeleRing.locallyCompactSpace` : the finite adele ring is locally compact.

## Implementation notes
 - There are two formalisations of the object `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ`. These are
   `DedekindDomain.SProdAdicCompletionIntegers` and
   `DedekindDomain.SProdAdicCompletionIntegers_subtype`, where the former is viewed as a type
   and the latter as a subtype of `Π (v ∈ S), Kᵥ × Π (v ∉ S), Kᵥ`. The reason for this is that
   the former is easily shown to be locally compact (its `fst` is a finite product of locally
   compact spaces and its `snd` is an infinite product of compact spaces), but it is much easier
   to show that the latter is homeomorphic to the finite S-adele ring, because we can just
   descend the natural homeomorphism on parent types. Thus we need to show that these two
   formalisations are also homeomorphic, which is found in
   `DedekindDomain.SProdAdicCompletionIntegers.homeomorph`.

## Tags
finite s-adele ring, dedekind domain
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Classical

namespace DedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] (K : Type*)
  [Field K] [Algebra R K] [IsFractionRing R K] (S : Finset (HeightOneSpectrum R))

/-- The type `DedekindDomain.ProdAdicCompletions` split as a product along the predicate `v ∈ S`. -/
def SProdAdicCompletions :=
  ((v : S) → v.val.adicCompletion K) × ((v : {v // v ∉ S}) → v.val.adicCompletion K)

/-- Binary product split along the predicate `v ∈ S`, whose first element ranges over `v`-adic
completions of `K` and whose second element ranges over `v`-adic rings of integers. -/
def SProdAdicCompletionIntegers :=
  ((v : S) → v.val.adicCompletion K) × ((v : {v // v ∉ S}) → v.val.adicCompletionIntegers K)

/-- The subtype of `DedekindDomain.SProdAdicCompletions` whose second product ranges over
`v`-adic rings of integers. -/
def SProdAdicCompletionIntegers_subtype :=
  {x : SProdAdicCompletions R K S // ∀ v : {v // v ∉ S}, x.2 v ∈ v.val.adicCompletionIntegers K}

namespace SProdAdicCompletions

instance : Coe (SProdAdicCompletionIntegers R K S) (SProdAdicCompletions R K S) where
  coe := fun x => (λ (v : S) => x.1 v, λ (v : {v // v ∉ S}) => (x.2 v : v.val.adicCompletion K))

theorem coe_injective :
    (Coe.coe : SProdAdicCompletionIntegers R K S → SProdAdicCompletions R K S).Injective := by
  intro x y hxy
  refine Prod.ext (Prod.ext_iff.1 hxy).1 ?_
  funext v
  have h : (x.2 v : v.val.adicCompletion K) = y.2 v :=
   Function.funext_iff.1 ((Prod.ext_iff.1 hxy).2) v
  exact (SetLike.coe_eq_coe.1 h)

section DerivedInstances

instance : TopologicalSpace (SProdAdicCompletions R K S) := instTopologicalSpaceProd

instance : TopologicalSpace (SProdAdicCompletionIntegers_subtype R K S) :=
 instTopologicalSpaceSubtype

instance : CommRing (SProdAdicCompletions R K S) := Prod.instCommRing

instance : Inhabited (SProdAdicCompletions R K S) := instInhabitedProd

end DerivedInstances

end SProdAdicCompletions

namespace SProdAdicCompletionIntegers

section DerivedInstances

instance topologicalSpace : TopologicalSpace (SProdAdicCompletionIntegers R K S) :=
  instTopologicalSpaceProd

instance : CommRing (SProdAdicCompletionIntegers R K S) := Prod.instCommRing

instance : Inhabited (SProdAdicCompletionIntegers R K S) := instInhabitedProd

end DerivedInstances

/-- The type equivalence between the two formalisations of `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ`. -/
def subtypeEquiv :
    SProdAdicCompletionIntegers_subtype R K S ≃ SProdAdicCompletionIntegers R K S where
  toFun x := (x.val.1 , fun v => ⟨x.val.2 v, x.property v⟩)
  invFun x := ⟨x, fun v => SetLike.coe_mem (x.2 v)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The homeomorphism between the two formalisations of `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ`. -/
def homeomorph :
    SProdAdicCompletionIntegers_subtype R K S ≃ₜ SProdAdicCompletionIntegers R K S where
  toEquiv := subtypeEquiv R K S
  continuous_toFun := by
    refine Continuous.prod_mk (Continuous.fst (Continuous.subtype_val
      ({ isOpen_preimage := fun s a => a }) )) ?_
    refine continuous_pi (fun v => Continuous.subtype_mk ?_ _)
    refine Continuous.comp (ContinuousMap.eval v).continuous_toFun ?_
    exact (Continuous.snd (Continuous.subtype_val ({ isOpen_preimage := fun s a => a }) ))
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.prod_mk
      (Continuous.fst { isOpen_preimage := fun s a => a }) ?_) _
    refine continuous_pi (fun v => Continuous.subtype_val ?_)
    refine Continuous.comp (ContinuousMap.eval v).continuous_toFun ?_
    exact Continuous.snd  ({ isOpen_preimage := fun s a => a })

/-- `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ` is locally compact. -/
instance : LocallyCompactSpace (SProdAdicCompletionIntegers R K S) :=
  @Prod.locallyCompactSpace _ _ _ _ Pi.locallyCompactSpace_of_finite Pi.locallyCompactSpace

/-- `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ` is locally compact. -/
instance : LocallyCompactSpace (SProdAdicCompletionIntegers_subtype R K S) :=
  (Homeomorph.locallyCompactSpace_iff (SProdAdicCompletionIntegers.homeomorph R K S)).2
    inferInstance

end SProdAdicCompletionIntegers

local notation "π" => FiniteAdeleRing.projection K
local notation "ι" => FiniteAdeleRing.localInclusion K

variable {R K}

def IsFiniteSAdele (x : ProdAdicCompletions R K) :=
  ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers K

variable {S}

namespace IsFiniteSAdele

theorem mul {x y : ProdAdicCompletions R K} (hx : IsFiniteSAdele S x) (hy : IsFiniteSAdele S y) :
    IsFiniteSAdele S (x * y) := by
  intros v hv
  rw [mem_adicCompletionIntegers, Pi.mul_apply, Valued.v.map_mul]
  exact mul_le_one' (hx v hv) (hy v hv)

theorem one : IsFiniteSAdele S (1 : ProdAdicCompletions R K) :=
  fun v _ => by rw [mem_adicCompletionIntegers]; exact le_of_eq (Valued.v.map_one')

theorem add {x y : ProdAdicCompletions R K} (hx : IsFiniteSAdele S x) (hy : IsFiniteSAdele S y) :
    IsFiniteSAdele S (x + y) := by
  intro v hv
  rw [mem_adicCompletionIntegers, Pi.add_apply]
  exact le_trans (Valued.v.map_add_le_max' (x v) (y v)) (max_le (hx v hv) (hy v hv))

theorem zero : IsFiniteSAdele S (0 : ProdAdicCompletions R K) := by
  intro v _
  rw [mem_adicCompletionIntegers]
  convert zero_le_one' (WithZero (Multiplicative ℤ))
  exact Valued.v.map_zero'

theorem neg {x : ProdAdicCompletions R K} (hx : IsFiniteSAdele S x) :
    IsFiniteSAdele S (-x) := by
  intro v hv
  rw [mem_adicCompletionIntegers, Pi.neg_apply, Valuation.map_neg]
  exact hx v hv

end IsFiniteSAdele

variable (R K S)

/-- The finite S-adele ring. -/
def FiniteSAdeleRing := {x : ProdAdicCompletions R K // IsFiniteSAdele S x}

namespace FiniteSAdeleRing

/-- The finite S-adele ring regarded as a subring of the product of local completions of K.

Note that the finite S-adele ring is not a subalegrba of the product of local completions of K,
but it is of `∏ K × ∏ O_K`, where the first product is over `v ∈ S` and the second is over `v ∉ S`.
-/
def subring : Subring (ProdAdicCompletions R K) where
  carrier := {x | IsFiniteSAdele S x}
  mul_mem' hx hy := hx.mul hy
  one_mem' := IsFiniteSAdele.one
  add_mem' hx hy := hx.add hy
  zero_mem' := IsFiniteSAdele.zero
  neg_mem' hx := hx.neg

instance : CommRing (FiniteSAdeleRing R K S) := (subring R K S).toCommRing

instance : TopologicalSpace (FiniteSAdeleRing R K S) :=
  inferInstanceAs (TopologicalSpace (subring R K S))

instance : TopologicalRing (FiniteSAdeleRing R K S) :=
  inferInstanceAs (TopologicalRing (subring R K S))

@[ext]
lemma ext {x y : FiniteSAdeleRing R K S} (h : x.val = y.val) : x = y :=
  Subtype.ext h

/-- the finite S-adele ring is homeomorphic to `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ`. -/
def homeomorph_piSubtypeProd :
    FiniteSAdeleRing R K S ≃ₜ SProdAdicCompletionIntegers_subtype R K S :=
  Homeomorph.subtype (Homeomorph.piEquivPiSubtypeProd _ _) <| fun _ =>
    ⟨fun hx v => hx v.1 v.2, fun hx v hv => hx ⟨v, hv⟩⟩

/-- The finite S-adele ring is locally compact. -/
theorem locallyCompactSpace : LocallyCompactSpace (FiniteSAdeleRing R K S) :=
  (Homeomorph.locallyCompactSpace_iff (homeomorph_piSubtypeProd R K S)).2 inferInstance

variable {R K S}

/-- A finite S-adele is a finite adele. -/
theorem isFiniteAdele (x : FiniteSAdeleRing R K S) :
    x.1.IsFiniteAdele := by
  rw [ProdAdicCompletions.IsFiniteAdele, Filter.eventually_cofinite]
  refine Set.Finite.subset S.finite_toSet (fun v hv => ?_)
  contrapose hv
  rw [Set.mem_setOf_eq, not_not]
  exact x.2 v hv

/-- If `x` is a `v`-adic integer, then the local inclusion of `x` at any place `v` is a
finite S-adele. -/
theorem isFiniteSAdele_localInclusion (v : HeightOneSpectrum R) {x : v.adicCompletion K}
    (hx : x ∈ v.adicCompletionIntegers K) :
    IsFiniteSAdele S (ι v x).val := by
  intros w _
  simp only [FiniteAdeleRing.localInclusion, ProdAdicCompletions.localInclusion]
  by_cases hw : w = v
  · rw [hw, dif_pos]
    simp only [hx]
    rfl
  · simp only [hw, ↓reduceDIte]
    exact (w.adicCompletionIntegers K).one_mem'

/-- If `v ∈ S` then the local inclusion of any `x` in the `v`-adic completion of `K` is a
finite S-adele. -/
theorem isFiniteSAdele_localInclusion_of_S {v : HeightOneSpectrum R}
    (x : v.adicCompletion K) (h : v ∈ S) :
    IsFiniteSAdele S (ι v x).val := by
  intros w hw
  simp only [FiniteAdeleRing.localInclusion, ProdAdicCompletions.localInclusion,
    Ne.symm (ne_of_mem_of_not_mem h hw), ↓reduceDIte]
  exact (w.adicCompletionIntegers K).one_mem

variable (R K S)

/-- Ring homomorphism sending finite S-adeles to finite adeles. -/
def toFiniteAdeleRing : FiniteSAdeleRing R K S →+* FiniteAdeleRing R K where
  toFun x := ⟨x.1, isFiniteAdele x⟩
  map_add' _ _ := rfl
  map_one' := rfl
  map_zero' := rfl
  map_mul' _ _ := rfl

local notation "e" => toFiniteAdeleRing R K

theorem toFiniteAdeleRing_injective : Function.Injective (e S) := by
  intro x y hxy
  rwa [toFiniteAdeleRing, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, Subtype.mk.injEq, Subtype.val_inj] at hxy

theorem toFiniteAdeleRing_range :
    Set.range (e S) = {x : FiniteAdeleRing R K | IsFiniteSAdele S x.val} :=
  (Set.range_eq_iff _ _).2 ⟨λ x => x.2, λ x hx => by {use ⟨x, hx⟩; rfl}⟩

theorem toFiniteAdeleRing_range_eq_pi : Subtype.val '' Set.range (e S) =
    Set.pi Set.univ (λ v => if (v ∈ S) then Set.univ else (v.adicCompletionIntegers K)) := by
  ext x
  rw [toFiniteAdeleRing_range R K]
  refine ⟨fun ⟨y, hy₀, hy₁⟩ v _ => ?_, fun hx => ?_⟩
  · by_cases hv : v ∈ S <;> simp only [hv, ↓reduceIte, Set.mem_univ]; rw [← hy₁]; exact hy₀ v hv
  · simp only [Set.mem_pi, Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_left,
      exists_prop, exists_eq_right_right]
    refine ⟨x, Set.Finite.subset (Finset.finite_toSet S) (fun v hv => ?_), fun v hv => ?_, rfl⟩
    · simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hv
      contrapose! hv
      simp only [Finset.mem_coe] at hv
      specialize hx v (Set.mem_univ v)
      simp only [hv, dif_neg, if_false] at hx
      exact hx
    · have h := hx v (Set.mem_univ v)
      simp only [dif_neg, hv] at h
      exact h

/-- The finite S-adele ring embedded into the finite adele ring is in the generating set of
the topology of the finite adele ring -/
theorem toFiniteAdeleRing_range_mem_generatingSet :
    Set.range (e S) ∈ FiniteAdeleRing.generatingSet R K := by
  simp only [FiniteAdeleRing.generatingSet, Filter.eventually_cofinite, Set.mem_image,
    Set.mem_setOf_eq, exists_exists_and_eq_and]
  use (fun v => ite (v ∈ S) Set.univ (v.adicCompletionIntegers K))
  refine ⟨⟨λ v => ?_, Set.Finite.subset (Finset.finite_toSet S) (λ v hv => ?_)⟩,
    by rw [← toFiniteAdeleRing_range_eq_pi, Set.preimage_image_eq _ Subtype.val_injective]⟩
  · by_cases hv : v ∈ S <;> simp only [hv, if_true, if_false, isOpen_univ];
      exact Valued.valuationSubring_isOpen (v.adicCompletion K)
  · simp only [Set.mem_setOf_eq, ite_eq_right_iff, not_forall, exists_prop] at hv
    exact hv.1


/-- Subtype val of the finite S-adele ring factors through the embedding into the
finite adele ring. -/
theorem subtype_val_embedding :
    (Subtype.val : FiniteSAdeleRing R K S → ProdAdicCompletions R K) = Subtype.val ∘ e S := rfl

theorem subtype_val_range_eq_pi :
    Set.range (Subtype.val : FiniteSAdeleRing R K S → ProdAdicCompletions R K)
      = Set.pi Set.univ (λ v => ite (v ∈ S) Set.univ (v.adicCompletionIntegers K)) := by
  rw [subtype_val_embedding, Set.range_comp, toFiniteAdeleRing_range_eq_pi]

/-- Neighbourhoods of the finite S-adele ring. -/
theorem nhds_iff (x : FiniteSAdeleRing R K S) : U ∈ nhds x ↔
    ∃ (V : (v: HeightOneSpectrum R) → Set (v.adicCompletion K)) (I : Finset (HeightOneSpectrum R)),
      (∀ v, V v ∈ nhds (x.val v)) ∧
        Subtype.val ⁻¹' Set.pi (I.toSet) V ⊆ U := by
  rw [nhds_induced (Subtype.val : FiniteSAdeleRing R K S → _), Filter.mem_comap, nhds_pi]
  refine ⟨fun ⟨t, ht, h⟩ => ?_, fun ⟨V, I, hV, hVU⟩ => ?_⟩
  · obtain ⟨I, V, hV⟩ := Filter.mem_pi'.1 ht
    exact ⟨V, I, ⟨hV.1, Set.Subset.trans (fun _ hx => hV.2 hx) h⟩⟩
  · exact ⟨I.toSet.pi V, Filter.mem_pi'.2 ⟨I, V, ⟨fun v => hV v, subset_rfl⟩⟩, hVU⟩

local notation "μᵥ" => @WithZero.unitsWithZeroEquiv (Multiplicative ℤ)

open AdicCompletion in
theorem AdicCompletion.exists_nmem_of_open_ball (v : HeightOneSpectrum R)
    (γ : (WithZero (Multiplicative ℤ))ˣ) (y : v.adicCompletion K) :
    ∃ x : v.adicCompletion K, Valued.v (x - y) > γ := by
  choose p hp using @valuation_exists_uniformizer R _ _ K _ _ _ v
  use p ^ (- Multiplicative.toAdd (μᵥ γ) - 1) + y
  have h_val : γ.val = (μᵥ γ : WithZero (Multiplicative ℤ)) := by
    simp only [WithZero.unitsWithZeroEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk, WithZero.coe_unzero]
  simp only [add_sub_cancel_right, h_val, map_zpow₀, Valued.valuedCompletion_apply,
    v.adicValued_apply, hp, gt_iff_lt, ← WithZero.coe_zpow, WithZero.coe_lt_coe,
    ← Multiplicative.toAdd_lt, ofAdd_neg, inv_zpow', neg_sub, sub_neg_eq_add, toAdd_zpow,
    toAdd_ofAdd, smul_eq_mul, mul_one, lt_add_iff_pos_left, zero_lt_one]

open AdicCompletion in
theorem FiniteAdeleRing.exists_nmem_of_finite_open_balls
    (γ : (v : HeightOneSpectrum R) → (WithZero (Multiplicative ℤ))ˣ)
    (y : FiniteAdeleRing R K) :
    ∃ (x : FiniteAdeleRing R K), ∀ v ∈ S, Valued.v (x v - y v) > γ v := by
  choose x hx using fun v => AdicCompletion.exists_nmem_of_open_ball R K v (γ v) (y v)
  let y : ProdAdicCompletions R K := fun v => if v ∈ S then x v else 1
  have hy : y.IsFiniteAdele := by
    refine y.isFiniteAdele_iff.2 <| Set.Finite.subset S.finite_toSet (fun v hv => ?_)
    contrapose! hv
    simp only [Finset.mem_coe] at hv
    simp only [Set.mem_setOf_eq, y, hv, if_false, one_mem, not_not]
  refine ⟨⟨y, hy⟩, fun v hv => ?_⟩
  simp only [y, hv, if_true]
  exact hx _

theorem FiniteAdeleRing.smul_apply (x : FiniteIntegralAdeles R K) (y : FiniteAdeleRing R K) :
    (x • y) v = x v * y v := rfl

theorem FiniteAdeleRing.add_apply (x : FiniteAdeleRing R K) (y : FiniteAdeleRing R K) :
    (x + y) v = x v + y v := rfl

theorem image_toFiniteAdeleRing_mem_nhds_zero {U : Set (FiniteSAdeleRing R K S)} (h : U ∈ nhds 0) :
    (e S) '' U ∈ nhds 0 := by
  rw [Filter.HasBasis.mem_iff (RingSubgroupsBasis.hasBasis_nhds_zero _)]
  simp_rw [true_and]
  rw [nhds_iff] at h
  obtain ⟨V, I, hV, hVU⟩ := h
  have (v : HeightOneSpectrum R) : (0 : FiniteSAdeleRing R K S).val v = 0 := rfl
  simp_rw [this] at hV
  simp only [Valued.mem_nhds_zero] at hV
  simp only [Submodule.coe_toAddSubgroup, Subtype.exists, exists_prop]
  choose γ hγ using hV
  choose x hx using FiniteAdeleRing.exists_nmem_of_finite_open_balls R K I (fun v => (γ v)⁻¹) 0
  choose r s hrs using FiniteAdeleRing.mul_nonZeroDivisor_mem_finiteIntegralAdeles x
  use r
  use r.2
  intro z hz
  simp only [SetLike.mem_coe, Submodule.mem_span_singleton] at hz
  rw [Set.mem_image]
  rw [subtype_val_embedding, Set.preimage_comp] at hVU
  rw [← Set.image_subset_image_iff (toFiniteAdeleRing_injective R K S)] at hVU
  apply hVU
  rw [Set.image_preimage_eq_inter_range]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Finset.mem_coe]
  obtain ⟨b, rfl⟩ := hz
  refine ⟨fun v hv => ?_, ?_⟩
  · apply hγ
    simp only [Set.mem_setOf_eq, FiniteAdeleRing.smul_apply, Valued.v.map_mul]
    apply lt_of_le_of_lt <| mul_le_mul_right' ((v.mem_adicCompletionIntegers R K).1 (b v).2)
      (Valued.v (Algebra.cast r.val : v.adicCompletion K))
    rw [one_mul]
    specialize hx v hv
    --simp at hx
    have : ((γ v))⁻¹ * Valued.v (algebraMap R (v.adicCompletion K) r) < 1 := by
      have h_ne_zero : Valued.v ((algebraMap R (adicCompletion K v)) ↑r) ≠ 0 := by
        rw [v.valuedAdicCompletion_eq_valuation]
        simp only [ne_eq, map_eq_zero]
        rw [IsFractionRing.to_map_eq_zero_iff]
        exact nonZeroDivisors.coe_ne_zero r
      have := mul_lt_right₀ _ hx h_ne_zero
      --simp at this
      apply lt_of_lt_of_le this
      rw [← Valued.v.map_mul]
      have : x v * algebraMap _ _ r.val = (algebraMap _ (FiniteAdeleRing R K) s) v := by
        simp
        have := congrArg (fun x => x v) hrs
        simp at this
        rw [← this]
        rfl
      simp at this
      have this' : x.val v - (0 : FiniteAdeleRing R K).val v = (x - 0).val v := rfl
      rw [this']
      simp only [sub_zero]
      rw [this]
      have : ((algebraMap (FiniteIntegralAdeles R K) (FiniteAdeleRing R K)) s).val v = s v := rfl
      rw [this]
      rw [← mem_adicCompletionIntegers R K v]
      simp only [SetLike.coe_mem]
    have := mul_lt_mul_of_lt_of_le₀ le_rfl (Units.ne_zero (γ v)) this
    simp at this
    exact this
  · rw [toFiniteAdeleRing_range]
    exact fun v _ => mul_mem (SetLike.coe_mem _) (v.coe_mem_adicCompletionIntegers r)

theorem image_toFiniteAdeleRing_mem_nhds (x : FiniteSAdeleRing R K S) {U : Set (FiniteSAdeleRing R K S)} (h : U ∈ nhds x) :
    (e S) '' U ∈ nhds (e S x) := by
  rw [Filter.HasBasis.mem_iff (RingSubgroupsBasis.hasBasis_nhds _ _)]
  simp_rw [true_and]
  rw [nhds_iff] at h
  obtain ⟨V, I, hV, hVU⟩ := h
  have (v : HeightOneSpectrum R) : (0 : FiniteSAdeleRing R K S).val v = 0 := rfl
  simp only [Valued.mem_nhds] at hV
  simp only [Submodule.coe_toAddSubgroup, Subtype.exists, exists_prop]
  choose γ hγ using hV
  choose y hy using FiniteAdeleRing.exists_nmem_of_finite_open_balls R K I (fun v => (γ v)⁻¹) (e S x)
  choose r₁ s₁ hrs₁ using FiniteAdeleRing.mul_nonZeroDivisor_mem_finiteIntegralAdeles y
  choose r₂ s₂ hrs₂ using FiniteAdeleRing.mul_nonZeroDivisor_mem_finiteIntegralAdeles (e S x)
  use r₁ * r₂
  use mul_mem_nonZeroDivisors.2 ⟨r₁.2, r₂.2⟩
  intro z hz
  simp only [Submodule.mem_toAddSubgroup, Set.mem_setOf_eq] at hz
  simp only [SetLike.mem_coe, Submodule.mem_span_singleton] at hz
  rw [Set.mem_image]
  rw [subtype_val_embedding, Set.preimage_comp] at hVU
  rw [← Set.image_subset_image_iff (toFiniteAdeleRing_injective R K S)] at hVU
  apply hVU
  rw [Set.image_preimage_eq_inter_range]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Finset.mem_coe]
  obtain ⟨b, hb⟩ := hz
  have := add_eq_of_eq_sub hb
  rw [← this]
  refine ⟨fun v hv => ?_, ?_⟩
  · apply hγ
    simp only [Set.mem_setOf_eq, FiniteAdeleRing.smul_apply, Valued.v.map_mul]
    rw [subtype_val_embedding, Function.comp_apply]
    simp only [FiniteAdeleRing.add_apply]
    simp only [FiniteAdeleRing.smul_apply, Valued.v.map_mul, add_sub_cancel_right]
    apply lt_of_le_of_lt <| mul_le_mul_right' ((v.mem_adicCompletionIntegers R K).1 (b v).2)
      (Valued.v (Algebra.cast (r₁ * r₂).val : v.adicCompletion K))
    rw [one_mul]
    specialize hy v hv
    simp only at hy
    --simp at hy
    have : ((γ v))⁻¹ * Valued.v (algebraMap R (v.adicCompletion K) (r₁ * r₂)) < 1 := by
      have h_ne_zero : Valued.v ((algebraMap R (adicCompletion K v)) ↑(r₁ * r₂)) ≠ 0 := by
        rw [v.valuedAdicCompletion_eq_valuation]
        simp only [ne_eq, map_eq_zero]
        rw [IsFractionRing.to_map_eq_zero_iff]
        exact nonZeroDivisors.coe_ne_zero _
      have := mul_lt_right₀ _ hy h_ne_zero
      simp only at this
      apply lt_of_lt_of_le this
      rw [← Valued.v.map_mul]
      have : (y v) * algebraMap _ _ (r₁ * r₂).val = (algebraMap _ (FiniteAdeleRing R K) (s₁) * algebraMap _ _ r₂.val) v := by
        simp
        have := congrArg (fun x => x v) hrs₁
        simp [Algebra.cast] at this
        have this' : (y * algebraMap _ _ r₁.val) v = y v * algebraMap _ _ r₁.val := rfl
        rw [← mul_assoc, ← this']
        simp only [this]
        rfl
      --simp at this
      rw [sub_mul, this]

      have : (((algebraMap (FiniteIntegralAdeles R K) (FiniteAdeleRing R K)) s₁) * (algebraMap _ _ r₂.val)) v = s₁ v * (algebraMap _ _ r₂.val):= rfl
      simp only
      simp_rw [this]
      rw [← mem_adicCompletionIntegers R K v]
      simp
      apply Subring.sub_mem
      · exact mul_mem (SetLike.coe_mem _) (v.coe_mem_adicCompletionIntegers r₂)
      · nth_rewrite 2 [mul_comm]
        rw [← mul_assoc]
        have := congrArg (fun x => x v) hrs₂
        simp [Algebra.cast] at this

        have this' : ((e S) x * algebraMap _ _ r₂.val) v = (e S x) v * algebraMap _ _ r₂.val := rfl
        rw [← this']
        simp only [this]
        exact mul_mem (SetLike.coe_mem _) (v.coe_mem_adicCompletionIntegers r₁)
    have := mul_lt_mul_of_lt_of_le₀ le_rfl (Units.ne_zero (γ v)) this
    rw [Units.mul_inv_cancel_left, mul_one] at this
    exact this
  · simp only [toFiniteAdeleRing_range, map_mul]
    exact fun v hv => add_mem (mul_mem (SetLike.coe_mem _) (mul_mem (v.coe_mem_adicCompletionIntegers r₁) (v.coe_mem_adicCompletionIntegers r₂)))
      (x.2 v hv)

theorem AdicCompletion.dvd_of_valued_le {v : HeightOneSpectrum R}
    {x y : v.adicCompletion K} (h : Valued.v x ≤ Valued.v y) (hy : y ≠ 0):
    ∃ r : v.adicCompletionIntegers K, r * y = x := by
  have : Valued.v (x * y⁻¹) ≤ 1 := by
    rw [Valued.v.map_mul]
    simp
    rw [mul_inv_le_iff₀ ((map_ne_zero _).2 hy), one_mul]
    exact h
  use ⟨x * y⁻¹, this⟩
  rw [inv_mul_cancel_right₀ hy]

theorem AdicCompletion.dvd_of_valued_lt {v : HeightOneSpectrum R}
    {x y : v.adicCompletion K} (h : Valued.v x < Valued.v y) (hy : y ≠ 0) :
    ∃ r : v.adicCompletionIntegers K, r * y = x :=
  AdicCompletion.dvd_of_valued_le _ _ (le_of_lt h) hy

theorem FiniteAdeleRing.dvd_of_valued_lt {x : FiniteAdeleRing R K} {r : nonZeroDivisors R}
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
  choose a ha using fun v => AdicCompletion.dvd_of_valued_le R K (this v) ((map_ne_zero _).1 (hr v))
  use a
  ext
  funext v
  exact ha v

theorem mem_nhds_zero_comap_toFiniteAdeleRing {U : Set (FiniteSAdeleRing R K S)}
    (h : U ∈ Filter.comap (e S) (nhds 0)) : U ∈ nhds 0 := by
  rw [nhds_iff]
  rw [Filter.mem_comap] at h
  simp_rw [Filter.HasBasis.mem_iff (RingSubgroupsBasis.hasBasis_nhds_zero _ ), true_and] at h
  obtain ⟨t, ⟨r, hrt⟩, htU⟩ := h
  rw [subtype_val_embedding]
  simp at hrt
  simp only [Valued.mem_nhds]
  simp only [Function.comp_apply]
  simp only [map_zero]
  have : (0 : FiniteAdeleRing R K).val = 0 := rfl
  simp only [this]
  clear this
  have (v : HeightOneSpectrum R) : (0 : ProdAdicCompletions R K) v = 0 := rfl
  simp only [this, sub_zero]
  clear this
  -- I should be S ∪ (divisors of r)
  -- V should just be balls of radius p^(v r)
  use fun (v : HeightOneSpectrum R) => { y | Valued.v y < Valued.v (algebraMap _ (v.adicCompletion K) r.val) }
  let I := S ∪ ((Ideal.span {r.val}).finite_factors (nonZeroDivisors.ne_zero <| (Ideal.span_singleton_nonZeroDivisors.2 r.2))).toFinset
  use I
  constructor
  · intro v
    let r := Valued.v (algebraMap _ (v.adicCompletion K) r.val)
    have h_ne_zero : r ≠ 0 := by
      simp only [r, v.valuedAdicCompletion_eq_valuation]
      simp only [ne_eq, map_eq_zero]
      rw [IsFractionRing.to_map_eq_zero_iff]
      exact nonZeroDivisors.coe_ne_zero _
    use (isUnit_iff_ne_zero.2 h_ne_zero).unit
    exact subset_rfl
  · apply Set.Subset.trans _ htU
    rw [Set.preimage_comp]
    intro x hx
    simp
    apply hrt
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_setOf_eq] at hx
    simp
    rw [Submodule.mem_span_singleton]
    have : ∀ v, v.asIdeal ∣ Ideal.span {r.val} → v ∈ I := by
      intro v hv
      simp only [I, Finset.mem_union]
      right
      simp at hv ⊢
      exact hv
    apply FiniteAdeleRing.dvd_of_valued_lt R K this hx
    intro v hv
    simp [toFiniteAdeleRing]
    simp [I] at hv
    exact x.2 v hv.1

theorem mem_nhds_comap_toFiniteAdeleRing (x : FiniteSAdeleRing R K S) {U : Set (FiniteSAdeleRing R K S)}
    (h : U ∈ Filter.comap (e S) (nhds (e S x))) : U ∈ nhds x := by
  rw [nhds_iff]
  rw [Filter.mem_comap] at h
  simp_rw [Filter.HasBasis.mem_iff (RingSubgroupsBasis.hasBasis_nhds _ _), true_and] at h
  obtain ⟨t, ⟨r, hrt⟩, htU⟩ := h
  rw [subtype_val_embedding]
  simp at hrt
  simp only [Valued.mem_nhds]
  simp only [Function.comp_apply]
  use fun (v : HeightOneSpectrum R) => { y | Valued.v (y - (e S x) v) < Valued.v (algebraMap _ (v.adicCompletion K) r.val) }
  let I := S ∪ ((Ideal.span {r.val}).finite_factors (nonZeroDivisors.ne_zero <| (Ideal.span_singleton_nonZeroDivisors.2 r.2))).toFinset
  use I
  constructor
  · intro v
    let r := Valued.v (algebraMap _ (v.adicCompletion K) r.val)
    have h_ne_zero : r ≠ 0 := by
      simp only [r, v.valuedAdicCompletion_eq_valuation]
      simp only [ne_eq, map_eq_zero]
      rw [IsFractionRing.to_map_eq_zero_iff]
      exact nonZeroDivisors.coe_ne_zero _
    use (isUnit_iff_ne_zero.2 h_ne_zero).unit
    exact subset_rfl
  · apply Set.Subset.trans _ htU
    rw [Set.preimage_comp]
    intro y hy
    simp
    apply hrt
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_setOf_eq] at hy
    have (v : HeightOneSpectrum R) : ((e S y) v - (e S x) v) = (e S y - e S x) v := rfl
    simp only [this] at hy
    simp
    rw [Submodule.mem_span_singleton]
    have : ∀ v, v.asIdeal ∣ Ideal.span {r.val} → v ∈ I := by
      intro v hv
      simp only [I, Finset.mem_union]
      right
      simp at hv ⊢
      exact hv
    apply FiniteAdeleRing.dvd_of_valued_lt R K this hy
    intro v hv
    simp [toFiniteAdeleRing]
    simp [I] at hv
    exact sub_mem (y.2 v hv.1) (x.2 v hv.1)

theorem inducing_toFiniteAdeleRing : Inducing (e S) := by
  refine inducing_iff_nhds.2 (fun x => Filter.ext (fun U => ⟨fun hU => ⟨e S '' U,  ?_⟩, mem_nhds_comap_toFiniteAdeleRing R K S x⟩))
  exact ⟨image_toFiniteAdeleRing_mem_nhds R K S x hU, by rw [(toFiniteAdeleRing_injective R K S).preimage_image]⟩

/-- The map sending finite S-adeles to finite adeles is open and injective. -/
theorem toFiniteAdeleRing_openEmbedding : OpenEmbedding (e S) := by
  use ⟨inducing_toFiniteAdeleRing R K S, toFiniteAdeleRing_injective R K S⟩
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [Filter.HasBasis.mem_iff (RingSubgroupsBasis.hasBasis_nhds _ _)]
  simp_rw [true_and]
  choose a b hab using FiniteAdeleRing.mul_nonZeroDivisor_mem_finiteIntegralAdeles x
  use a
  rw [toFiniteAdeleRing_range] at hx ⊢
  intro y hy
  simp at hy ⊢
  intro v hv
  rw [Submodule.mem_span_singleton] at hy
  obtain ⟨c, hc⟩ := hy
  have := add_eq_of_eq_sub hc
  rw [← this]
  apply (v.adicCompletionIntegers K).add_mem'
  · apply (v.adicCompletionIntegers K).mul_mem'
    · simp only [Subsemiring.coe_carrier_toSubmonoid, Subring.coe_toSubsemiring, SetLike.mem_coe,
      ValuationSubring.mem_toSubring, SetLike.coe_mem]
    · exact v.coe_mem_adicCompletionIntegers _
  · exact hx v hv

end FiniteSAdeleRing

namespace FiniteAdeleRing

open FiniteSAdeleRing

local notation "e" => toFiniteAdeleRing R K

/-- The finite adele ring is locally compact. -/
theorem locallyCompactSpace : LocallyCompactSpace (FiniteAdeleRing R K) := by
  refine LocallyCompactSpace.mk (fun x N hN => ?_)
  set S := (Filter.eventually_cofinite.1 x.2).toFinset
  have hx : IsFiniteSAdele S x.1 :=
    fun v hv => by rwa [Set.Finite.mem_toFinset, Set.nmem_setOf_iff, not_not] at hv
  obtain ⟨U, hU₀, hU₁, hU₂⟩ := mem_nhds_iff.1 hN
  have hU_S : (e S) ⁻¹' U ∈ nhds ⟨x, hx⟩ :=
    mem_nhds_iff.2 ⟨_, subset_rfl,
      (toFiniteAdeleRing_openEmbedding R K S).continuous.isOpen_preimage _ hU₁, hU₂⟩
  obtain ⟨N_S, hN_S₀, hN_S₁, hN_S₂⟩ :=
    (FiniteSAdeleRing.locallyCompactSpace R K S).local_compact_nhds ⟨x, hx⟩ _ hU_S
  refine ⟨(e S) '' N_S, ?_, subset_trans (Set.image_subset_iff.2 hN_S₁) hU₀,
    ((openEmbedding_iff _).1 (toFiniteAdeleRing_openEmbedding R K S)).1.isCompact_iff.1 hN_S₂⟩
  · obtain ⟨V, hV, hVOpen, hxV⟩ := mem_nhds_iff.1 hN_S₀
    exact mem_nhds_iff.2 <| ⟨(e S) '' V,
      (Set.image_subset_image_iff (toFiniteAdeleRing_openEmbedding R K S).inj).2 hV,
      (toFiniteAdeleRing_openEmbedding R K S).isOpenMap _ hVOpen, ⟨_, hxV, rfl⟩⟩


end FiniteAdeleRing

end DedekindDomain
