/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib
import AdeleRingLocallyCompact.Algebra.Order.GroupWithZero.Canonical
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteAdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.AdicValuation
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.Factorization
import AdeleRingLocallyCompact.Topology.Homeomorph

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

private def IsIntegralAt : (v : {v // v ∉ S}) → v.val.adicCompletion K → Prop :=
  fun v x => x ∈ v.val.adicCompletionIntegers K

private def IsFinsetIntegralProd : ((v : {v // v ∉ S}) → v.val.adicCompletion K) → Prop :=
  fun x => ∀ v, x v ∈ v.val.adicCompletionIntegers K

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
def Subtype :=
  {x : FinsetProd R K S // ∀ v : {v // v ∉ S}, x.2 v ∈ v.val.adicCompletionIntegers K}

instance : Coe (FinsetIntegralAdeles R K S) (FinsetProd R K S) where
  coe := fun x => (fun (v : S) => x.1 v, fun (v : {v // v ∉ S}) => (x.2 v : v.val.adicCompletion K))

theorem coe_injective :
    (Coe.coe : FinsetIntegralAdeles R K S → FinsetProd R K S).Injective := by
  refine fun x y hxy => Prod.ext (Prod.ext_iff.1 hxy).1 (funext <| fun v => SetLike.coe_eq_coe.1 ?_)
  exact congrArg (fun x => x.2 v) hxy

section DerivedInstances

instance : TopologicalSpace (FinsetIntegralAdeles R K S) :=
  instTopologicalSpaceProd

instance topologicalSpaceSubtype : TopologicalSpace (Subtype R K S) :=
 instTopologicalSpaceSubtype

instance : CommRing (FinsetIntegralAdeles R K S) := Prod.instCommRing

instance : Inhabited (FinsetIntegralAdeles R K S) := instInhabitedProd

end DerivedInstances

/-- The homeomorphism between the two formalisations of `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ`. -/
def subtype_homeomorph : Subtype R K S ≃ₜ FinsetIntegralAdeles R K S :=
  Homeomorph.trans (Homeomorph.prodSubtypeSndEquivSubtypeProd <| IsFinsetIntegralProd R K S)
    (Homeomorph.prodCongr (Homeomorph.refl _)
      (@Homeomorph.subtypePiEquivPi _ _ _ (IsIntegralAt R K S)))

def empty_homeomorph :
    FinsetIntegralAdeles R K ∅ ≃ₜ FiniteIntegralAdeles R K :=
  Homeomorph.trans
    (Homeomorph.prodCongr (Homeomorph.homeomorphOfUnique _ _) (Homeomorph.refl _))
    (Homeomorph.piEquivPiSubtypeProd _
      (fun v : HeightOneSpectrum R => v.adicCompletionIntegers K)).symm

/-- `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ` is locally compact. -/
instance : LocallyCompactSpace (FinsetIntegralAdeles R K S) :=
  @Prod.locallyCompactSpace _ _ _ _ Pi.locallyCompactSpace_of_finite Pi.locallyCompactSpace

/-- `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ` is locally compact. -/
instance : LocallyCompactSpace (Subtype R K S) :=
  (Homeomorph.locallyCompactSpace_iff (subtype_homeomorph R K S)).2 inferInstance

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
  rw [mem_adicCompletionIntegers]
  convert zero_le_one' (WithZero (Multiplicative ℤ))
  exact Valued.v.map_zero'

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

/-- The finite S-adele ring regarded as a subring of the product of local completions of K.

Note that the finite S-adele ring is not a `K`-subalgebra of the product of `∏ Kᵥ`, but it is a
`K_S`-subalgebra, where `K_S` denotes the `S`-integers.
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

def empty_homeomorph :
    FinsetAdeleRing R K ∅ ≃ₜ FiniteIntegralAdeles R K :=
  Homeomorph.trans
    (Homeomorph.trans (homeomorph_subtype R K _) (FinsetIntegralAdeles.subtype_homeomorph R K _))
    (FinsetIntegralAdeles.empty_homeomorph R K)

/-- The finite S-adele ring is locally compact. -/
theorem locallyCompactSpace : LocallyCompactSpace (FinsetAdeleRing R K S) :=
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

open FiniteAdeleRing in
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

open FiniteAdeleRing in
/-- If `v ∈ S` then the local inclusion of any `x` in the `v`-adic completion of `K` is a
finite S-adele. -/
theorem isFinsetAdele_localInclusion_of_mem {v : HeightOneSpectrum R}
    (x : v.adicCompletion K) (h : v ∈ S) :
    IsFinsetAdele S (localInclusion K v x).val := by
  intros w hw
  simp only [localInclusion, ProdAdicCompletions.localInclusion,
    Ne.symm (ne_of_mem_of_not_mem h hw), ↓reduceDIte]
  exact (w.adicCompletionIntegers K).one_mem

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

/-- The finite S-adele ring is open in the finite adele ring. -/
theorem isOpen_algebraMap_range : IsOpen (Set.range (e S)) := by
  refine isOpen_iff_mem_nhds.2 (fun x hx => ?_)
  simp only [Filter.HasBasis.mem_iff (RingSubgroupsBasis.hasBasis_nhds _ _), true_and]
  choose a b hab using FiniteAdeleRing.mul_nonZeroDivisor_mem_finiteIntegralAdeles x
  refine ⟨a, fun y hy => ?_⟩
  rw [algebraMap_range] at hx ⊢
  intro v hv
  rw [Set.mem_setOf_eq, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton] at hy
  obtain ⟨c, hc⟩ := hy
  rw [← add_eq_of_eq_sub hc]
  exact add_mem (mul_mem (SetLike.coe_mem _) (v.coe_mem_adicCompletionIntegers _)) (hx v hv)

/-- `Subtype.val` of the finite S-adele ring factors through the embedding into the
finite adele ring. -/
theorem subtype_val_embedding :
    (Subtype.val : FinsetAdeleRing R K S → ProdAdicCompletions R K) = Subtype.val ∘ e S := rfl

variable {R K S}

/-- Neighbourhoods of the finite S-adele ring. -/
theorem nhds_iff {x : FinsetAdeleRing R K S} {U : Set (FinsetAdeleRing R K S)} : U ∈ nhds x ↔
    ∃ (V : (v: HeightOneSpectrum R) → Set (v.adicCompletion K)) (I : Finset (HeightOneSpectrum R)),
      (∀ v, V v ∈ nhds (x.val v)) ∧
        Subtype.val ⁻¹' Set.pi (I.toSet) V ⊆ U := by
  rw [nhds_induced (Subtype.val : FinsetAdeleRing R K S → _), Filter.mem_comap, nhds_pi]
  refine ⟨fun ⟨t, ht, h⟩ => ?_, fun ⟨V, I, hV, hVU⟩ => ?_⟩
  · obtain ⟨I, V, hV⟩ := Filter.mem_pi'.1 ht
    exact ⟨V, I, ⟨hV.1, Set.Subset.trans (fun _ hx => hV.2 hx) h⟩⟩
  · exact ⟨I.toSet.pi V, Filter.mem_pi'.2 ⟨I, V, ⟨fun v => hV v, subset_rfl⟩⟩, hVU⟩

open FiniteAdeleRing in
/-- The embedding of the finite S-adele ring into the finite adele ring preserves neighbourhoods. -/
theorem algebraMap_image_mem_nhds (x : FinsetAdeleRing R K S)
    {U : Set (FinsetAdeleRing R K S)} (h : U ∈ nhds x) :
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
    ← Set.image_subset_image_iff (algebraMap_injective R K S)] at hVU
  apply hVU
  simp only [Set.image_preimage_eq_inter_range]
  obtain ⟨b, hb⟩ := hz
  rw [← add_eq_of_eq_sub hb, algebraMap_range]
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

/-- The pullback of a neighbourhood in the finite adele ring is a neighbourhood in the
finite S-adele ring. -/
theorem mem_nhds_comap_algebraMap (x : FinsetAdeleRing R K S)
    {U : Set (FinsetAdeleRing R K S)} (h : U ∈ Filter.comap (e S) (nhds (e S x))) :
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

namespace FiniteIntegralAdeles

theorem algebraMap_factors : (algebraMap (FiniteIntegralAdeles R K) (FiniteAdeleRing R K)) =
  (algebraMap (FinsetAdeleRing R K ∅) (FiniteAdeleRing R K)) ∘
    (FinsetAdeleRing.empty_homeomorph R K).symm :=
  funext (fun _ => rfl)

theorem algebraMap_inducing :
    Inducing <| algebraMap (FiniteIntegralAdeles R K) (FiniteAdeleRing R K) :=
  algebraMap_factors R K ▸ Inducing.comp (FinsetAdeleRing.algebraMap_inducing _ _ _)
    (Homeomorph.inducing _)

instance : ContinuousSMul (FiniteIntegralAdeles R K) (FiniteAdeleRing R K) := by
  apply inducing_id.continuousSMul (algebraMap_inducing _ _).continuous
  intro _ _
  rfl

instance : CompactSpace (FiniteIntegralAdeles R K) := Pi.compactSpace

end FiniteIntegralAdeles

namespace FiniteAdeleRing

open FinsetAdeleRing

local notation "e" => toFiniteAdeleRing R K

/-- The finite adele ring is locally compact. -/
theorem locallyCompactSpace : LocallyCompactSpace (FiniteAdeleRing R K) := by
  refine LocallyCompactSpace.mk (fun x N hN => ?_)
  let S := (Filter.eventually_cofinite.1 x.2).toFinset
  have hx : IsFinsetAdele S x.1 :=
    fun v hv => by rwa [Set.Finite.mem_toFinset, Set.nmem_setOf_iff, not_not] at hv
  obtain ⟨U, hU₀, hU₁, hU₂⟩ := mem_nhds_iff.1 hN
  have hU_S : (e S) ⁻¹' U ∈ nhds ⟨x, hx⟩ :=
    mem_nhds_iff.2 ⟨_, subset_rfl,
      (algebraMap_openEmbedding R K S).continuous.isOpen_preimage _ hU₁, hU₂⟩
  obtain ⟨N_S, hN_S₀, hN_S₁, hN_S₂⟩ :=
    (FinsetAdeleRing.locallyCompactSpace R K S).local_compact_nhds ⟨x, hx⟩ _ hU_S
  refine ⟨(e S) '' N_S, ?_, subset_trans (Set.image_subset_iff.2 hN_S₁) hU₀,
    ((openEmbedding_iff _).1 (algebraMap_openEmbedding R K S)).1.isCompact_iff.1 hN_S₂⟩
  · obtain ⟨V, hV, hVOpen, hxV⟩ := mem_nhds_iff.1 hN_S₀
    exact mem_nhds_iff.2 <| ⟨(e S) '' V,
      (Set.image_subset_image_iff (algebraMap_openEmbedding R K S).inj).2 hV,
      (algebraMap_openEmbedding R K S).isOpenMap _ hVOpen, ⟨_, hxV, rfl⟩⟩

end FiniteAdeleRing

end DedekindDomain
