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
of integers outside of `S`, as `FinsetAdeleRing R K S` and we show that this is locally compact.
The finite S-adele ring affords an open embedding into the regular finite adele ring and,
moreover, cover the finite adele ring. This allows us to show that the finite adele ring is also
locally compact.

## Main definitions
 - `DedekindDomain.FinsetProd R K S` is the `DedekindDomain.ProdAdicCompletions R K`
   split into a product along the predicate `v ∈ S`.
 - `DedekindDomain.FinsetIntegralAdeles R K S` is the direct product whose left type
   is the product of the `v`-adic completions of `K` over all `v ∈ S` and whose right type is
   the product of the `v`-adic ring of integers over all `v ∉ S`.
 - `DedekindDomain.FinsetIntegralAdeles.Subtype R K S` is
   `DedekindDomain.FinsetIntegralAdeles R K S` as a subtype of `DedekindDomain.FinsetProd R K S`.
 - `DedekindDomain.FinsetAdeleRing R K S` is the subring of `ProdAdicCompletions R K` of all finite
   S-adeles.
 - `DedekindDomain.FinsetAdeleRing.toFiniteAdeleRing` is the map embedding the finite S-adele
   ring into the finite adele ring.

## Main results
 - `DedekindDomain.FinsetAdeleRing.homeomorph_subtype` : the finite S-adele ring is
   homeomorphic to `DedekindDomain.FiniteIntegralAdeles.Subtype`.
 - `DedekindDomain.FinsetAdeleRing.algebraMap_inducing` : the map sending finite S-adeles to
   finite adeles is inducing; equivalently, the topology of the finite S-adele ring when viewed as
   a subspace of the finite adele ring is equal to the topology when viewed as a subspace of
   `ProdAdicCompletions R K`.
 - `DedekindDomain.FinsetAdeleRing.algebraMap_openEmbedding` : the map sending finite
   S-adeles to finite adeles is an open embedding.
 - `DedekindDomain.FinsetAdeleRing.locallyCompactSpace` : the finite S-adele ring is locally
   compact.
 - `DedekindDomain.FiniteAdeleRing.locallyCompactSpace` : the finite adele ring is locally compact.

## Implementation notes
 - There are two formalisations of the object `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ`. These are
   `DedekindDomain.FinsetIntegralAdeles` and `DedekindDomain.FinsetIntegralAdeles.Subtype`,
   where the former is viewed as a type and the latter as a subtype of
   `Π (v ∈ S), Kᵥ × Π (v ∉ S), Kᵥ`. The reason for this is that the former is easily shown to be
   locally compact (its `fst` is a finite product of locally compact spaces and its `snd` is an
   infinite product of compact spaces), but it is much easier to show that the latter is
   homeomorphic to the finite S-adele ring, because we can just descend the natural homeomorphism
   on parent types. Thus we need to show that these two formalisations are also homeomorphic, which
   is found in `DedekindDomain.FinsetIntegralAdeles.homeomorph`.

## Tags
finite s-adele ring, dedekind domain
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Classical

namespace DedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] (K : Type*)
  [Field K] [Algebra R K] [IsFractionRing R K] (S : Finset (HeightOneSpectrum R))

namespace ProdAdicCompletions

/-- The type `DedekindDomain.ProdAdicCompletions` split as a product along the predicate `v ∈ S`. -/
def FinsetProd :=
  ((v : S) → v.val.adicCompletion K) × ((v : {v // v ∉ S}) → v.val.adicCompletion K)

section DerivedInstances

instance : TopologicalSpace (FinsetProd R K S) := instTopologicalSpaceProd

instance : CommRing (FinsetProd R K S) := Prod.instCommRing

instance : Inhabited (FinsetProd R K S) := instInhabitedProd

end DerivedInstances

end ProdAdicCompletions

/-- Binary product split along the predicate `v ∈ S`, whose first element ranges over `v`-adic
completions of `K` and whose second element ranges over `v`-adic rings of integers. -/
def FinsetIntegralAdeles :=
  ((v : S) → v.val.adicCompletion K) × ((v : {v // v ∉ S}) → v.val.adicCompletionIntegers K)

namespace FinsetIntegralAdeles

open ProdAdicCompletions

/-- The subtype of `DedekindDomain.FinsetProd` whose second product ranges over
`v`-adic rings of integers. -/
def Subtype := {x : FinsetProd R K S // ∀ v : {v // v ∉ S}, x.2 v ∈ v.val.adicCompletionIntegers K}

instance : Coe (FinsetIntegralAdeles R K S) (FinsetProd R K S) where
  coe := fun x => (λ (v : S) => x.1 v, λ (v : {v // v ∉ S}) => (x.2 v : v.val.adicCompletion K))

theorem coe_injective :
    (Coe.coe : FinsetIntegralAdeles R K S → FinsetProd R K S).Injective := by
  refine fun x y hxy => Prod.ext (Prod.ext_iff.1 hxy).1 (funext <| fun v => SetLike.coe_eq_coe.1 ?_)
  exact congrArg (fun x => x.2 v) hxy

instance : TopologicalSpace (FinsetIntegralAdeles R K S) :=
  instTopologicalSpaceProd

instance topologicalSpaceSubtype : TopologicalSpace (Subtype R K S) :=
 instTopologicalSpaceSubtype

instance : CommRing (FinsetIntegralAdeles R K S) := Prod.instCommRing

instance : Inhabited (FinsetIntegralAdeles R K S) := instInhabitedProd

/-- The type equivalence between the two formalisations of `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ`. -/
def subtype_equiv :
    Subtype R K S ≃ FinsetIntegralAdeles R K S where
  toFun x := (x.val.1 , fun v => ⟨x.val.2 v, x.property v⟩)
  invFun x := ⟨x, fun v => SetLike.coe_mem (x.2 v)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The homeomorphism between the two formalisations of `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ`. -/
def subtype_homeomorph :
    Subtype R K S ≃ₜ FinsetIntegralAdeles R K S where
  toEquiv := subtype_equiv R K S
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
instance : LocallyCompactSpace (FinsetIntegralAdeles R K S) := Prod.locallyCompactSpace _ _

/-- `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ` as a subtype is locally compact. -/
instance : LocallyCompactSpace (Subtype R K S) :=
  (subtype_homeomorph R K S).locallyCompactSpace_iff.2 inferInstance

end FinsetIntegralAdeles

variable {R K}

def IsFinsetAdele (x : ProdAdicCompletions R K) :=
  ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers K

variable {S}

namespace IsFinsetAdele

theorem mul {x y : ProdAdicCompletions R K} (hx : IsFinsetAdele S x) (hy : IsFinsetAdele S y) :
    IsFinsetAdele S (x * y) := by
  intros v hv
  rw [mem_adicCompletionIntegers, Pi.mul_apply, Valued.v.map_mul]
  exact mul_le_one' (hx v hv) (hy v hv)

theorem one : IsFinsetAdele S (1 : ProdAdicCompletions R K) :=
  fun v _ => by rw [mem_adicCompletionIntegers]; exact le_of_eq (Valued.v.map_one')

theorem add {x y : ProdAdicCompletions R K} (hx : IsFinsetAdele S x) (hy : IsFinsetAdele S y) :
    IsFinsetAdele S (x + y) := by
  intro v hv
  rw [mem_adicCompletionIntegers, Pi.add_apply]
  exact le_trans (Valued.v.map_add_le_max' (x v) (y v)) (max_le (hx v hv) (hy v hv))

theorem zero : IsFinsetAdele S (0 : ProdAdicCompletions R K) := by
  intro v _
  rw [mem_adicCompletionIntegers, Pi.zero_apply, Valued.v.map_zero]
  exact zero_le_one

theorem neg {x : ProdAdicCompletions R K} (hx : IsFinsetAdele S x) :
    IsFinsetAdele S (-x) := by
  intro v hv
  rw [mem_adicCompletionIntegers, Pi.neg_apply, Valuation.map_neg]
  exact hx v hv

end IsFinsetAdele

variable (R K S)

/-- The finite S-adele ring. -/
def FinsetAdeleRing := {x : ProdAdicCompletions R K // IsFinsetAdele S x}

namespace FinsetAdeleRing

open FiniteAdeleRing

/-- The finite S-adele ring regarded as a subring of the product of local completions of K.

Note that the finite S-adele ring is not a subalgebra of the product of `∏ Kᵥ`, but it is a
subalgebra of `∏ (v ∈ S), Kᵥ × ∏ (v ∉ S), Oᵥ`.
-/
def subring : Subring (ProdAdicCompletions R K) where
  carrier := {x | IsFinsetAdele S x}
  mul_mem' hx hy := hx.mul hy
  one_mem' := IsFinsetAdele.one
  add_mem' hx hy := hx.add hy
  zero_mem' := IsFinsetAdele.zero
  neg_mem' hx := hx.neg

instance : CommRing (FinsetAdeleRing R K S) := (subring R K S).toCommRing

instance : TopologicalSpace (FinsetAdeleRing R K S) :=
  inferInstanceAs (TopologicalSpace (subring R K S))

instance : TopologicalRing (FinsetAdeleRing R K S) :=
  inferInstanceAs (TopologicalRing (subring R K S))

@[ext]
lemma ext {x y : FinsetAdeleRing R K S} (h : x.val = y.val) : x = y :=
  Subtype.ext h

/-- The finite S-adele ring is homeomorphic to `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ`. -/
def homeomorph_subtype :
    FinsetAdeleRing R K S ≃ₜ FinsetIntegralAdeles.Subtype R K S :=
  Homeomorph.subtype (Homeomorph.piEquivPiSubtypeProd _ _) <| fun _ =>
    ⟨fun hx v => hx v.1 v.2, fun hx v hv => hx ⟨v, hv⟩⟩

/-- The finite S-adele ring is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (FinsetAdeleRing R K S) :=
  (Homeomorph.locallyCompactSpace_iff (homeomorph_subtype R K S)).2 inferInstance

variable {R K S}

/-- A finite S-adele is a finite adele. -/
theorem isFiniteAdele (x : FinsetAdeleRing R K S) :
    x.1.IsFiniteAdele := by
  rw [ProdAdicCompletions.IsFiniteAdele, Filter.eventually_cofinite]
  refine Set.Finite.subset S.finite_toSet (fun v hv => ?_)
  contrapose hv
  rw [Set.mem_setOf_eq, not_not]
  exact x.2 v hv

/-- If `x` is a `v`-adic integer, then the local inclusion of `x` at any place `v` is a
finite S-adele. -/
theorem isFinsetAdele_localInclusion (v : HeightOneSpectrum R) {x : v.adicCompletion K}
    (hx : x ∈ v.adicCompletionIntegers K) :
    IsFinsetAdele S (localInclusion K v x).val := by
  intros w _
  simp only [localInclusion, ProdAdicCompletions.localInclusion]
  by_cases hw : w = v
  · rw [hw, dif_pos]
    simp only [hx]
    rfl
  · simp only [hw, ↓reduceDIte]
    exact (w.adicCompletionIntegers K).one_mem'

/-- If `v ∈ S` then the local inclusion of any `x` in the `v`-adic completion of `K` is a
finite S-adele. -/
theorem isFinsetAdele_localInclusion_of_mem {v : HeightOneSpectrum R}
    (x : v.adicCompletion K) (h : v ∈ S) :
    IsFinsetAdele S (localInclusion K v x).val := by
  intros w hw
  simp only [localInclusion, ProdAdicCompletions.localInclusion,
    Ne.symm (ne_of_mem_of_not_mem h hw), ↓reduceDIte]
  exact (w.adicCompletionIntegers K).one_mem

theorem isFinsetAdele_support (x : FiniteAdeleRing R K) :
    IsFinsetAdele (support x) x.1 :=
  fun v hv => by rwa [support, Set.Finite.mem_toFinset, Set.nmem_setOf_iff, not_not] at hv

def ofFiniteAdele_support (x : FiniteAdeleRing R K) : FinsetAdeleRing R K (support x) :=
  ⟨x, isFinsetAdele_support x⟩

variable (R K S)

/-- Ring homomorphism sending finite S-adeles to finite adeles.-/
def toFiniteAdeleRing : FinsetAdeleRing R K S →+* FiniteAdeleRing R K where
  toFun x := ⟨x.1, isFiniteAdele x⟩
  map_add' _ _ := rfl
  map_one' := rfl
  map_zero' := rfl
  map_mul' _ _ := rfl

instance : Algebra (FinsetAdeleRing R K S) (FiniteAdeleRing R K) where
  toRingHom := toFiniteAdeleRing R K S
  smul x y := toFiniteAdeleRing R K S x * y
  smul_def' _ _ := rfl
  commutes' _ _ := by rw [mul_comm]

local notation "e" => fun S => algebraMap (FinsetAdeleRing R K S) (FiniteAdeleRing R K)

/-- The map sending finite S-adeles to finite adeles is injective. -/
theorem algebraMap_injective : Function.Injective (e S) := by
  intro x y hxy
  simp only [algebraMap, Algebra.toRingHom, toFiniteAdeleRing, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk] at hxy
  rwa [Subtype.mk.injEq, Subtype.val_inj] at hxy

theorem algebraMap_range :
    Set.range (e S) = {x : FiniteAdeleRing R K | IsFinsetAdele S x.val} :=
  (Set.range_eq_iff _ _).2 ⟨λ x => x.2, fun x hx => by {use ⟨x, hx⟩; rfl}⟩

variable {R K S}

theorem isFinsetAdele_mem_range {x : FiniteAdeleRing R K} (hx : x ∈ Set.range (e S)) :
    IsFinsetAdele S x.val := by
  convert Set.mem_setOf.1 (algebraMap_range R K S ▸ hx)

def ofFiniteAdele_mem_range {x : FiniteAdeleRing R K} (hx : x ∈ Set.range (e S)) :
    FinsetAdeleRing R K S :=
  ⟨x, isFinsetAdele_mem_range hx⟩

theorem algebraMap_range_mem_nhds (x : FinsetAdeleRing R K S) :
    Set.range (e S) ∈ nhds (e S x) := by
  simp only [Filter.HasBasis.mem_iff (RingSubgroupsBasis.hasBasis_nhds _ _), true_and]
  choose a b _ using FiniteAdeleRing.mul_nonZeroDivisor_mem_finiteIntegralAdeles (e S x)
  refine ⟨a, fun y hy => ?_⟩
  rw [algebraMap_range]
  intro v hv
  rw [Set.mem_setOf_eq, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton] at hy
  obtain ⟨c, hc⟩ := hy
  rw [← add_eq_of_eq_sub hc]
  exact add_mem (mul_mem (SetLike.coe_mem _) (v.coe_mem_adicCompletionIntegers _)) (x.2 v hv)

variable (R K S)

/-- The finite S-adele ring is open in the finite adele ring. -/
theorem isOpen_algebraMap_range : IsOpen (Set.range (e S)) :=
  isOpen_iff_mem_nhds.2 <| fun _ hx => algebraMap_range_mem_nhds <| ofFiniteAdele_mem_range hx

/-- `Subtype.val` of the finite S-adele ring factors through the embedding into the
finite adele ring. -/
theorem subtype_val_algebraMap :
    (Subtype.val : FinsetAdeleRing R K S → ProdAdicCompletions R K) = Subtype.val ∘ e S := rfl

variable {R K S}

theorem algebraMap_mk {x : FiniteAdeleRing R K} (hx : IsFinsetAdele S x.1) :
    e S ⟨x, hx⟩ = x := rfl

/-- Neighbourhoods of the finite S-adele ring. -/
theorem nhds_iff {x : FinsetAdeleRing R K S} {U : Set (FinsetAdeleRing R K S)} : U ∈ nhds x ↔
    ∃ (V : (v: HeightOneSpectrum R) → Set (v.adicCompletion K)) (I : Finset (HeightOneSpectrum R)),
      (∀ v, V v ∈ nhds (x.val v)) ∧
        Subtype.val ⁻¹' Set.pi (I.toSet) V ⊆ U := by
  rw [nhds_induced, Filter.mem_comap, nhds_pi]
  refine ⟨fun ⟨t, ht, h⟩ => ?_, fun ⟨V, I, hV, hVU⟩ => ?_⟩
  · obtain ⟨I, V, hV⟩ := Filter.mem_pi'.1 ht
    exact ⟨V, I, ⟨hV.1, Set.Subset.trans (fun _ hx => hV.2 hx) h⟩⟩
  · exact ⟨I.toSet.pi V, Filter.mem_pi'.2 ⟨I, V, ⟨fun v => hV v, subset_rfl⟩⟩, hVU⟩

open Set Submodule in
/-- The embedding of the finite S-adele ring into the finite adele ring preserves neighbourhoods. -/
theorem algebraMap_image_mem_nhds (x : FinsetAdeleRing R K S)
    {U : Set (FinsetAdeleRing R K S)} (h : U ∈ nhds x) :
    (e S) '' U ∈ nhds (e S x) := by
  simp only [Filter.HasBasis.mem_iff (RingSubgroupsBasis.hasBasis_nhds _ _), true_and,
    coe_toAddSubgroup, Subtype.exists, exists_prop]
  obtain ⟨V, I, hV, hVU⟩ := nhds_iff.1 h
  choose γ hγ using fun v => Valued.mem_nhds.1 <| hV v
  choose y hy using exists_not_mem_of_finite_nhds I (fun v => (γ v)⁻¹) (e S x)
  choose r s hrs using sub_mul_nonZeroDivisor_mem_finiteIntegralAdeles (e S x) y
  refine ⟨r, r.2, fun z hz => ?_⟩
  simp only [mem_toAddSubgroup, mem_span_singleton] at hz
  rw [subtype_val_algebraMap, preimage_comp,
    ← image_subset_image_iff (algebraMap_injective R K S)] at hVU
  apply hVU
  simp only [image_preimage_eq_inter_range]
  obtain ⟨b, hb⟩ := hz
  rw [← add_eq_of_eq_sub hb, algebraMap_range]
  refine ⟨fun v hv => hγ v ?_, ?_⟩
  · simp only [mem_setOf_eq, smul_apply, Valued.v.map_mul, add_apply]
    rw [subtype_val_algebraMap, Function.comp_apply, add_sub_cancel_right, Valued.v.map_mul]
    apply lt_of_le_of_lt <| mul_le_mul_right' ((v.mem_adicCompletionIntegers R K).1 (b v).2) _
    rw [one_mul, ← inv_mul_lt_one_iff₀ (Units.ne_zero _), ← Units.val_inv_eq_inv_val]
    apply lt_of_lt_of_le <| mul_lt_right₀ _ (hy v hv) (v.algebraMap_valuation_ne_zero K r)
    have := congrArg (fun x => x v) hrs
    simp only [mul_integer_apply, sub_apply, ← Valued.v.map_mul] at this ⊢
    exact this ▸ (s v).2
  · exact fun v hv => add_mem (mul_mem (SetLike.coe_mem _) (v.coe_mem_adicCompletionIntegers r))
      (x.2 v hv)

open Set Submodule Finset in
/-- The pullback of a neighbourhood in the finite adele ring is a neighbourhood in the
finite S-adele ring. -/
theorem mem_nhds_comap_algebraMap (x : FinsetAdeleRing R K S)
    {U : Set (FinsetAdeleRing R K S)} (h : U ∈ Filter.comap (e S) (nhds (e S x))) :
    U ∈ nhds x := by
  simp only [nhds_iff, Valued.mem_nhds]
  simp only [Filter.mem_comap, Filter.HasBasis.mem_iff (RingSubgroupsBasis.hasBasis_nhds _ _)] at h
  obtain ⟨t, ⟨r, _, hrt⟩, htU⟩ := h
  use fun (v : HeightOneSpectrum R) =>
    { y | Valued.v (y - (e S x) v) < Valued.v (algebraMap _ (v.adicCompletion K) r.val) }
  let I := S ∪ Ideal.factorsFinset_of_nonZeroDivisor r
  let γr (v : HeightOneSpectrum R) := (isUnit_iff_ne_zero.2 (v.algebraMap_valuation_ne_zero K r))
  refine ⟨I, ⟨fun v => ⟨(γr v).unit, subset_rfl⟩, subset_trans (fun y hy => ?_) htU⟩⟩
  apply hrt
  rw [mem_setOf_eq, mem_toAddSubgroup, mem_span_singleton]
  exact dvd_of_valued_lt (fun v hv => mem_union.2 (Or.inr <| (Finite.mem_toFinset _).2 hv)) hy
    (fun v hv => sub_mem (y.2 v (not_mem_union.1 hv).1) (x.2 v (not_mem_union.1 hv).1))

variable (R K S)

/-- The topologies of the finite S-adele ring when viewed as a subspace of
`ProdAdicCompletions R K` and as a subspace of the finite adele ring coincide. -/
theorem algebraMap_inducing : Inducing (e S) := by
  refine inducing_iff_nhds.2 (fun x => Filter.ext (fun U => ⟨fun hU => ⟨e S '' U,  ?_⟩,
    mem_nhds_comap_algebraMap x⟩))
  exact ⟨algebraMap_image_mem_nhds x hU, by rw [(algebraMap_injective R K S).preimage_image]⟩

/-- The map sending finite S-adeles to finite adeles is open and injective. -/
theorem algebraMap_openEmbedding : OpenEmbedding (e S) :=
  ⟨⟨algebraMap_inducing R K S, algebraMap_injective R K S⟩, isOpen_algebraMap_range R K S⟩

end FinsetAdeleRing

namespace FiniteAdeleRing

open FinsetAdeleRing

local notation "e" => fun S => algebraMap (FinsetAdeleRing R K S) (FiniteAdeleRing R K)

/-- The finite adele ring is locally compact. -/
theorem locallyCompactSpace : LocallyCompactSpace (FiniteAdeleRing R K) := by
  refine LocallyCompactSpace.mk <| fun x N hN => let S := support x; ?_
  have h := (algebraMap_inducing R K S).nhds_eq_comap (ofFiniteAdele_support x)
  let ⟨M, hM⟩ := (FinsetAdeleRing.locallyCompactSpace R K S).local_compact_nhds
    (ofFiniteAdele_support x) _ (h ▸ Filter.preimage_mem_comap hN)
  refine ⟨(e S) '' M, ?_, Set.image_subset_iff.2 hM.2.1,
    (algebraMap_inducing R K S).isCompact_iff.1 hM.2.2⟩
  have := algebraMap_range_mem_nhds (ofFiniteAdele_support x)
  exact (algebraMap_inducing R K S).map_nhds_of_mem _ this ▸ Filter.image_mem_map hM.1

end FiniteAdeleRing

end DedekindDomain
