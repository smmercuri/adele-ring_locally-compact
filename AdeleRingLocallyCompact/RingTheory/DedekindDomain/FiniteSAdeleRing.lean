/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteAdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.AdicValuation
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.Factorization
import AdeleRingLocallyCompact.Algebra.Order.GroupWithZero.Canonical

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

Note that the finite S-adele ring is not a subalgerba of the product of local completions of K,
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

theorem injective_toFiniteAdeleRing : Function.Injective (e S) := by
  intro x y hxy
  rwa [toFiniteAdeleRing, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, Subtype.mk.injEq, Subtype.val_inj] at hxy

theorem range_toFiniteAdeleRing :
    Set.range (e S) = {x : FiniteAdeleRing R K | IsFiniteSAdele S x.val} :=
  (Set.range_eq_iff _ _).2 ⟨λ x => x.2, λ x hx => by {use ⟨x, hx⟩; rfl}⟩

theorem isOpen_range_toFiniteAdeleRing : IsOpen (Set.range (e S)) := by
  refine isOpen_iff_mem_nhds.2 (fun x hx => ?_)
  simp only [Filter.HasBasis.mem_iff (RingSubgroupsBasis.hasBasis_nhds _ _), true_and]
  choose a b hab using FiniteAdeleRing.mul_nonZeroDivisor_mem_finiteIntegralAdeles x
  refine ⟨a, fun y hy => ?_⟩
  rw [range_toFiniteAdeleRing] at hx ⊢
  intro v hv
  rw [Set.mem_setOf_eq, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton] at hy
  obtain ⟨c, hc⟩ := hy
  rw [← add_eq_of_eq_sub hc]
  exact add_mem (mul_mem (SetLike.coe_mem _) (v.coe_mem_adicCompletionIntegers _)) (hx v hv)

/-- Subtype val of the finite S-adele ring factors through the embedding into the
finite adele ring. -/
theorem subtype_val_embedding :
    (Subtype.val : FiniteSAdeleRing R K S → ProdAdicCompletions R K) = Subtype.val ∘ e S := rfl

variable {R K S}

/-- Neighbourhoods of the finite S-adele ring. -/
theorem nhds_iff {x : FiniteSAdeleRing R K S} {U : Set (FiniteSAdeleRing R K S)} : U ∈ nhds x ↔
    ∃ (V : (v: HeightOneSpectrum R) → Set (v.adicCompletion K)) (I : Finset (HeightOneSpectrum R)),
      (∀ v, V v ∈ nhds (x.val v)) ∧
        Subtype.val ⁻¹' Set.pi (I.toSet) V ⊆ U := by
  rw [nhds_induced (Subtype.val : FiniteSAdeleRing R K S → _), Filter.mem_comap, nhds_pi]
  refine ⟨fun ⟨t, ht, h⟩ => ?_, fun ⟨V, I, hV, hVU⟩ => ?_⟩
  · obtain ⟨I, V, hV⟩ := Filter.mem_pi'.1 ht
    exact ⟨V, I, ⟨hV.1, Set.Subset.trans (fun _ hx => hV.2 hx) h⟩⟩
  · exact ⟨I.toSet.pi V, Filter.mem_pi'.2 ⟨I, V, ⟨fun v => hV v, subset_rfl⟩⟩, hVU⟩

open FiniteAdeleRing in
theorem image_toFiniteAdeleRing_mem_nhds (x : FiniteSAdeleRing R K S)
    {U : Set (FiniteSAdeleRing R K S)} (h : U ∈ nhds x) :
    (e S) '' U ∈ nhds (e S x) := by
  simp only [Filter.HasBasis.mem_iff (RingSubgroupsBasis.hasBasis_nhds _ _), true_and,
    Submodule.coe_toAddSubgroup, Subtype.exists, exists_prop]
  obtain ⟨V, I, hV, hVU⟩ := nhds_iff.1 h
  simp only [Valued.mem_nhds] at hV
  choose γ hγ using hV
  choose y hy using exists_nmem_of_finite_open_balls I (fun v => (γ v)⁻¹) (e S x)
  choose r₁ s₁ hrs₁ using mul_nonZeroDivisor_mem_finiteIntegralAdeles y
  choose r₂ s₂ hrs₂ using mul_nonZeroDivisor_mem_finiteIntegralAdeles (e S x)
  refine ⟨r₁ * r₂, mul_mem_nonZeroDivisors.2 ⟨r₁.2, r₂.2⟩, fun z hz => ?_⟩
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton] at hz
  rw [subtype_val_embedding, Set.preimage_comp,
    ← Set.image_subset_image_iff (injective_toFiniteAdeleRing R K S)] at hVU
  apply hVU
  simp only [Set.image_preimage_eq_inter_range]
  obtain ⟨b, hb⟩ := hz
  rw [← add_eq_of_eq_sub hb, range_toFiniteAdeleRing]
  refine ⟨fun v hv => hγ v ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, smul_apply, Valued.v.map_mul]
    rw [subtype_val_embedding, Function.comp_apply]
    simp only [add_apply, smul_apply, Valued.v.map_mul, add_sub_cancel_right]
    apply lt_of_le_of_lt <| mul_le_mul_right' ((v.mem_adicCompletionIntegers R K).1 (b v).2)
      (Valued.v (algebraMap _ _ (r₁ * r₂).val))
    rw [one_mul, ← inv_mul_lt_one_iff₀ (Units.ne_zero _), ← Units.val_inv_eq_inv_val]
    apply lt_of_lt_of_le (mul_lt_right₀ _ (hy v hv) (v.algebraMap_valuation_ne_zero K (r₁ * r₂)))
    rw [← Valued.v.map_mul, sub_mul, Submonoid.coe_mul, map_mul, ← mul_assoc, ← mul_integer_apply,
      congrArg (fun x => x v) hrs₁, ← mem_adicCompletionIntegers R K v]
    nth_rewrite 3 [mul_comm]
    refine sub_mem (mul_mem (SetLike.coe_mem _) (v.coe_mem_adicCompletionIntegers r₂)) ?_
    rw [← mul_assoc, ← mul_integer_apply, congrArg (fun x => x v) hrs₂]
    exact mul_mem (SetLike.coe_mem _) (v.coe_mem_adicCompletionIntegers r₁)
  · simp only [map_mul]
    exact fun v hv => add_mem (mul_mem (SetLike.coe_mem _) (mul_mem
      (v.coe_mem_adicCompletionIntegers r₁) (v.coe_mem_adicCompletionIntegers r₂))) (x.2 v hv)

theorem mem_nhds_comap_toFiniteAdeleRing (x : FiniteSAdeleRing R K S)
    {U : Set (FiniteSAdeleRing R K S)} (h : U ∈ Filter.comap (e S) (nhds (e S x))) :
    U ∈ nhds x := by
  simp only [nhds_iff, subtype_val_embedding, Valued.mem_nhds]
  simp only [Filter.mem_comap, Filter.HasBasis.mem_iff (RingSubgroupsBasis.hasBasis_nhds _ _),
    true_and] at h
  obtain ⟨t, ⟨r, hrt⟩, htU⟩ := h
  simp only [Submodule.mem_toAddSubgroup] at hrt
  use fun (v : HeightOneSpectrum R) =>
    { y | Valued.v (y - (e S x) v) < Valued.v (algebraMap _ (v.adicCompletion K) r.val) }
  let I := S ∪ Ideal.factorsFinset_of_nonZeroDivisor r
  refine ⟨I,
    ⟨fun v => ⟨(isUnit_iff_ne_zero.2 (v.algebraMap_valuation_ne_zero K r)).unit, subset_rfl⟩, ?_⟩⟩
  refine Set.Subset.trans (fun y hy => ?_) htU
  apply hrt
  rw [Set.mem_setOf_eq, Submodule.mem_span_singleton]
  have : ∀ v, v.asIdeal ∣ Ideal.span {r.val} → v ∈ I :=
    fun v hv => Finset.mem_union.2 (Or.inr <| (Set.Finite.mem_toFinset _).2 hv)
  refine FiniteAdeleRing.dvd_of_valued_lt this hy (fun v hv => ?_)
  exact sub_mem (y.2 v (Finset.not_mem_union.1 hv).1) (x.2 v (Finset.not_mem_union.1 hv).1)

variable (R K S)

theorem inducing_toFiniteAdeleRing : Inducing (e S) := by
  refine inducing_iff_nhds.2 (fun x => Filter.ext (fun U => ⟨fun hU => ⟨e S '' U,  ?_⟩,
    mem_nhds_comap_toFiniteAdeleRing x⟩))
  exact ⟨image_toFiniteAdeleRing_mem_nhds x hU,
    by rw [(injective_toFiniteAdeleRing R K S).preimage_image]⟩

/-- The map sending finite S-adeles to finite adeles is open and injective. -/
theorem toFiniteAdeleRing_openEmbedding : OpenEmbedding (e S) :=
  ⟨⟨inducing_toFiniteAdeleRing R K S, injective_toFiniteAdeleRing R K S⟩,
    isOpen_range_toFiniteAdeleRing R K S⟩

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
