/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteAdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.AdicValuation
import AdeleRingLocallyCompact.Topology.Homeomorph

/-!
# Finite S-adele ring

Let `R` be a Dedekind domain of Krull dimension 1, `K` its field of fractions and `S` a finite set of
finite places `v` of `R`. In this file we define the finite S-adele ring, whose carrier is the set of all elements in
`ProdAdicCompletions R K` which are in the `v`-adic ring of integers outside of `S`, and we show that this is
locally compact. The finite S-adele ring affords an open embedding into the regular finite adele ring and, moreover,
cover the finite adele ring. This allows us to show that the finite adele ring is also locally compact.

## Main definitions
 - `DedekindDomain.SProdAdicCompletionIntegers_subtype` is the direct product whose left type is the product of the
   `v`-adic completions of `K` over all `v ∈ S` and whose right type is the product of the `v`-adic ring of
   integers over all `v ∉ S`.
 - `DedekindDomain.finiteSAdeleRing` is the subring of `ProdAdicCompletions R K` of all finite S-adeles.
 - `DedekindDomain.FiniteSAdeleRing.toFiniteAdeleRing` is the map embedding the finite S-adele ring into the
   finite adele ring.
 - `DedekindDomain.FiniteSAdeleRing.topologicalSpace` is the topological space of the finite S-adele ring, viewed
   as a subspace of the finite adele ring; this is shown to be equivalent to the topology when viewed as a
   subspace of `ProdAdicCompletions R K` (that these topologies coincide is an important part of what allows us
   to show that the finite S-adele ring is locally compact).

## Main results
 - `DedekindDomain.FiniteSAdeleRing.toFiniteAdeleRing_openEmbedding` : the map sending finite S-adeles to
   finite adeles is an open embedding; this is crucial so that when we can push the S-adeles to an open covering
   of the finite adele ring.
 - `DedekindDomain.FiniteSAdeleRing.generatingSet_eq` : the generating set of the subspace topology of the finite
   S-adele ring when viewed as a subspace of the finite adele ring is equal to the generating set of the subspace
   topology when viewed as a subspace of `ProdAdicCompletions R K` and so these two topologies coincide.
 - `DedekindDomain.FiniteSAdeleRing.homeomorph_piSubtypeProd` : the finite S-adele ring is homeomorphic to
   `DedekindDomain.SProdAdicCompletionIntegers_subtype`.
 - `DedekindDomain.FiniteSAdeleRing.locallyCompactSpace` : the finite S-adele ring is locally compact.
 - `DedekindDomain.FiniteAdeleRing.locallyCompactSpace` : the finite adele ring is locally compact.

## Implementation notes
 - There are two formalisations of the object `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ`. These are
   `DedekindDomain.SProdAdicCompletionIntegers` and `DedekindDomain.SProdAdicCompletionIntegers_subtype`,
   where the former is viewed as a type and the latter as a subtype of `Π (v ∈ S), Kᵥ × Π (v ∉ S), Kᵥ`.
   The reason for this is that the former is easily shown to be locally compact
   (its `fst` is a finite product of locally compact spaces and its `snd` is an infinite product of compact spaces),
   but it is much easier to show that the latter is homeomorphic to the finite S-adele ring, because we can just
   descend the natural homeomorphism on parent types. Thus we need to show that these two formalisations are
   also homeomorphic, which is found in `DedekindDomain.SProdAdicCompletionIntegers.homeomorph`.

## Tags
finite s-adele ring, dedekind domain

## TODO
 - Move the local compactness of the finite adele ring to `FiniteAdeleRing.lean`, currently this
   results in circular imports.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Classical

namespace DedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] (K : Type*)
  [Field K] [Algebra R K] [IsFractionRing R K] (S : Finset (HeightOneSpectrum R))

/-- The type `DedekindDomain.ProdAdicCompletions` split as a product along the predicate `v ∈ S`. -/
def SProdAdicCompletions :=
  (((v : S) → v.val.adicCompletion K) × ((v : {v // v ∉ S}) → v.val.adicCompletion K))

/-- Binary product split along the predicate `v ∈ S`, whose first element ranges over `v`-adic completions
of `K` and whose second element ranges over `v`-adic rings of integers. -/
def SProdAdicCompletionIntegers :=
  (((v : S) → v.val.adicCompletion K) × ((v : {v // v ∉ S}) → v.val.adicCompletionIntegers K))

/-- The subtype of `DedekindDomain.SProdAdicCompletions` whose second product ranges over `v`-adic rings of
integers. -/
def SProdAdicCompletionIntegers_subtype :=
  {x : SProdAdicCompletions R K S // ∀ v : {v // v ∉ S}, x.2 v ∈ v.val.adicCompletionIntegers K}

namespace SProdAdicCompletions

instance : Coe (SProdAdicCompletionIntegers R K S) (SProdAdicCompletions R K S) where
  coe := λ x => (λ (v : S) => x.1 v, λ (v : {v // v ∉ S}) => (x.2 v : v.val.adicCompletion K))

theorem coe_injective : (Coe.coe : SProdAdicCompletionIntegers R K S → SProdAdicCompletions R K S).Injective := by
  intro x y hxy
  refine Prod.ext (Prod.ext_iff.1 hxy).1 ?_
  funext v
  have h : (x.2 v : v.val.adicCompletion K) = y.2 v := Function.funext_iff.1 ((Prod.ext_iff.1 hxy).2) v
  exact (SetLike.coe_eq_coe.1 h)

section DerivedInstances

instance : TopologicalSpace (SProdAdicCompletions R K S) := instTopologicalSpaceProd

instance : TopologicalSpace (SProdAdicCompletionIntegers_subtype R K S) := instTopologicalSpaceSubtype

instance : CommRing (SProdAdicCompletions R K S) := Prod.instCommRing

instance : Inhabited (SProdAdicCompletions R K S) := instInhabitedProd

end DerivedInstances

/-- The homeomorphism between `Π v, Kᵥ` and `Π (v ∈ S), Kᵥ × Π (v ∉ S), Kᵥ`. -/
theorem homeomorph_piSubtypeProd : ProdAdicCompletions R K ≃ₜ SProdAdicCompletions R K S :=
  Homeomorph.piEquivPiSubtypeProd _ _

end SProdAdicCompletions

namespace SProdAdicCompletionIntegers

section DerivedInstances

instance topologicalSpace : TopologicalSpace (SProdAdicCompletionIntegers R K S) := instTopologicalSpaceProd

instance : CommRing (SProdAdicCompletionIntegers R K S) := Prod.instCommRing

instance : Inhabited (SProdAdicCompletionIntegers R K S) := instInhabitedProd

end DerivedInstances

/-- The type equivalence between the two formalisations of `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ`. -/
theorem subtypeEquiv : SProdAdicCompletionIntegers_subtype R K S ≃ SProdAdicCompletionIntegers R K S where
  toFun := λ x => (x.val.1 , λ v => ⟨x.val.2 v, x.property v⟩)
  invFun := λ x => ⟨x, λ v => SetLike.coe_mem (x.2 v)⟩
  left_inv := λ _ => rfl
  right_inv := λ _ => rfl

/-- The homeomorphism between the two formalisations of `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ`. -/
theorem homeomorph : SProdAdicCompletionIntegers_subtype R K S ≃ₜ SProdAdicCompletionIntegers R K S where
  toEquiv := subtypeEquiv R K S
  continuous_toFun := by
    unfold subtypeEquiv
    refine Continuous.prod_mk (Continuous.fst (Continuous.subtype_val ({ isOpen_preimage := fun s a => a }) )) ?_
    refine continuous_pi (λ v => Continuous.subtype_mk ?_ _)
    refine Continuous.comp (ContinuousMap.eval v).continuous_toFun ?_
    exact (Continuous.snd (Continuous.subtype_val ({ isOpen_preimage := fun s a => a }) ))
  continuous_invFun := by
    unfold subtypeEquiv
    refine Continuous.subtype_mk (Continuous.prod_mk (Continuous.fst { isOpen_preimage := fun s a => a }) ?_) _
    refine continuous_pi (λ v => Continuous.subtype_val ?_)
    refine Continuous.comp (ContinuousMap.eval v).continuous_toFun ?_
    exact Continuous.snd  ({ isOpen_preimage := fun s a => a })

instance : LocallyCompactSpace ((v : S) → v.val.adicCompletion K) := Pi.locallyCompactSpace_of_finite

instance : LocallyCompactSpace ((v : {v // v ∉ S}) → v.val.adicCompletionIntegers K) := Pi.locallyCompactSpace

/-- `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ` is locally compact. -/
instance : LocallyCompactSpace (SProdAdicCompletionIntegers R K S) :=
  Prod.locallyCompactSpace
    ((v : S) → v.val.adicCompletion K)
    ((v : {v // v ∉ S}) → v.val.adicCompletionIntegers K)

/-- `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ` is locally compact. -/
instance : LocallyCompactSpace (SProdAdicCompletionIntegers_subtype R K S) :=
  (Homeomorph.locallyCompactSpace_iff (SProdAdicCompletionIntegers.homeomorph R K S)).2 inferInstance

end SProdAdicCompletionIntegers

local notation "π" => FiniteAdeleRing.projection K
local notation "ι" => FiniteAdeleRing.localInclusion K

variable {R K}

def IsFiniteSAdele (x : ProdAdicCompletions R K) :=
  ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers K

variable {S}

theorem mul {x y : ProdAdicCompletions R K} (hx : IsFiniteSAdele S x) (hy : IsFiniteSAdele S y) :
  IsFiniteSAdele S (x * y) := by
  intros v hv
  rw [mem_adicCompletionIntegers, Pi.mul_apply, Valued.v.map_mul]
  exact mul_le_one' (hx v hv) (hy v hv)

theorem one : IsFiniteSAdele S (1 : ProdAdicCompletions R K) :=
  λ v _ => by rw [mem_adicCompletionIntegers]; exact le_of_eq (Valued.v.map_one')

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

variable (R K S)

/-- The finite S-adele ring. -/
def finiteSAdeleRing : Subring (ProdAdicCompletions R K) where
  carrier := (setOf (IsFiniteSAdele S))
  mul_mem' hx hy := mul hx hy
  one_mem' := one
  add_mem' hx hy := add hx hy
  zero_mem' := zero
  neg_mem' hx := neg hx

namespace FiniteSAdeleRing

variable {R K S}

/-- A finite S-adele is a finite adele. -/
theorem mem_isFiniteAdele {x : ProdAdicCompletions R K} (hx : x ∈ finiteSAdeleRing R K S) :
  x ∈ finiteAdeleRing R K := by
  rw [mem_finiteAdeleRing_iff, ProdAdicCompletions.IsFiniteAdele, Filter.eventually_cofinite]
  refine Set.Finite.subset S.finite_toSet (λ v hv => ?_)
  contrapose hv
  rw [Set.mem_setOf_eq, not_not]
  exact hx v hv

/-- If `x` is a `v`-adic integer, then the local inclusion of `x` at any place `v` is a finite S-adele. -/
theorem isFiniteSAdele_localInclusion (v : HeightOneSpectrum R) {x : v.adicCompletion K}
  (hx : x ∈ v.adicCompletionIntegers K) :
  IsFiniteSAdele S (ι v x).val := by
  intros w _
  simp only [FiniteAdeleRing.localInclusion, ProdAdicCompletions.localInclusion]
  by_cases hw : w = v
  · rw [hw, dif_pos]
    simp only [hx]
    rfl
  · simp only [↓reduceDite, hw]
    exact (w.adicCompletionIntegers K).one_mem'

/-- If `v ∈ S` then the local inclusion of any `x` in the `v`-adic completion of `K` is a finite S-adele. -/
theorem isFiniteSAdele_localInclusion_of_S {v : HeightOneSpectrum R} (x : v.adicCompletion K) (h : v ∈ S) :
  IsFiniteSAdele S (ι v x).val := by
  intros w hw
  simp only [FiniteAdeleRing.localInclusion, ProdAdicCompletions.localInclusion]
  simp only [Ne.symm (ne_of_mem_of_not_mem h hw), ↓reduceDite]
  exact (w.adicCompletionIntegers K).one_mem'

variable (R K S)

/-- Ring homomorphism sending finite S-adeles to finite adeles. -/
def toFiniteAdeleRing : finiteSAdeleRing R K S →+* finiteAdeleRing R K where
  toFun := λ x => ⟨x.1, mem_isFiniteAdele x.2⟩
  map_add' _ _ := rfl
  map_one' := rfl
  map_zero' := rfl
  map_mul' _ _ := rfl

local notation "e" => toFiniteAdeleRing R K

/-- The S-adeles are given the subspace topology viewed as a subspace of the finite adele ring. -/
instance topologicalSpace : TopologicalSpace (finiteSAdeleRing R K S)
  := TopologicalSpace.induced (e S) (TopologicalSpace.generateFrom (FiniteAdeleRing.generatingSet R K))

theorem toFiniteAdeleRing_inducing : Inducing (e S) := by rw [inducing_iff]; rfl

theorem toFiniteAdeleRing_injective : Function.Injective (e S) := by
  intro x y hxy
  simp only [toFiniteAdeleRing, Subtype.mk.injEq, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, Subtype.mk.injEq, SetLike.coe_eq_coe] at hxy
  exact hxy

theorem toFiniteAdeleRing_range : Set.range (e S) = setOf (λ x : finiteAdeleRing R K => IsFiniteSAdele S x.val) :=
  (Set.range_eq_iff _ _).2 ⟨λ x => x.2, λ x hx => by {use ⟨x, hx⟩; rfl}⟩

theorem toFiniteAdeleRing_range_eq_pi : Subtype.val '' Set.range (e S) =
  Set.pi Set.univ (λ v => if (v ∈ S) then Set.univ else (v.adicCompletionIntegers K)) := by
  ext x
  rw [toFiniteAdeleRing_range R K]
  refine ⟨λ ⟨y, hy₀, hy₁⟩ v _ => ?_, ?_⟩
  · by_cases hv : v ∈ S <;> simp only [hv, ↓reduceIte, Set.mem_univ]; rw [← hy₁]; exact hy₀ v hv
  · simp only [Set.mem_pi, Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_left, exists_prop,
      exists_eq_right_right, mem_finiteAdeleRing_iff]
    intro hx
    refine ⟨λ v hv => ?_, Set.Finite.subset (Finset.finite_toSet S) (λ v hv => ?_)⟩
    · have h := hx v (Set.mem_univ v)
      simp only [dif_neg, hv] at h
      exact h
    · simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hv
      contrapose! hv
      simp only [Finset.mem_coe] at hv
      specialize hx v (Set.mem_univ v)
      simp only [hv, dif_neg, if_false] at hx
      exact hx

/-- The finite S-adele ring embedded into the finite adele ring is in the generating set of the topology of the
finite adele ring -/
theorem toFiniteAdeleRing_range_mem_generatingSet : Set.range (e S) ∈ FiniteAdeleRing.generatingSet R K := by
  simp only [FiniteAdeleRing.generatingSet, Filter.eventually_cofinite, Set.mem_image, Set.mem_setOf_eq,
    exists_exists_and_eq_and]
  use (λ v => ite (v ∈ S) Set.univ (v.adicCompletionIntegers K))
  refine ⟨⟨λ v => ?_, Set.Finite.subset (Finset.finite_toSet S) (λ v hv => ?_)⟩,
    by rw [← toFiniteAdeleRing_range_eq_pi, Set.preimage_image_eq _ Subtype.val_injective]⟩
  · by_cases hv : v ∈ S <;> simp only [hv, if_true, if_false, isOpen_univ];
      exact Valued.valuationSubring_isOpen (v.adicCompletion K)
  · simp only [Set.mem_setOf_eq, ite_eq_right_iff, not_forall, exists_prop] at hv
    exact hv.1

/-- The map sending finite S-adeles to finite adeles is open and injective. -/
theorem toFiniteAdeleRing_openEmbedding : OpenEmbedding (e S) := by
  use ⟨toFiniteAdeleRing_inducing R K S, toFiniteAdeleRing_injective R K S⟩
  exact TopologicalSpace.isOpen_generateFrom_of_mem (toFiniteAdeleRing_range_mem_generatingSet R K S)

/-- The generating set of the topology of the finite S-adele ring. -/
def generatingSet : Set (Set (finiteSAdeleRing R K S))
  := Set.preimage (e S) '' (FiniteAdeleRing.generatingSet R K)

theorem generateFrom :
  topologicalSpace R K S = TopologicalSpace.generateFrom (FiniteSAdeleRing.generatingSet R K S) := by
  rw [generatingSet, ← induced_generateFrom_eq]; rfl

theorem set_univ_mem_generatingSet : Set.univ ∈ generatingSet R K S := by
  simp only [generatingSet, Set.mem_image, Set.preimage_eq_univ_iff]
  use (Set.range (e S)), toFiniteAdeleRing_range_mem_generatingSet R K S

/-- Subtype val of the finite S-adele ring factors through the embedding into the finite adele ring. -/
theorem subtype_val_embedding :
  (Subtype.val : finiteSAdeleRing R K S → ProdAdicCompletions R K) = Subtype.val ∘ e S := rfl

theorem subtype_val_range_eq_pi :
  Set.range (Subtype.val : finiteSAdeleRing R K S → ProdAdicCompletions R K)
    = Set.pi Set.univ (λ v => ite (v ∈ S) Set.univ (v.adicCompletionIntegers K)) := by
  rw [subtype_val_embedding, Set.range_comp, toFiniteAdeleRing_range_eq_pi]

/-- The generating set of the subspace topology of the finite S-adele ring viewed as a subspace of the finite
adele ring coincides with the generating set of the subspace topology obtained as a subspace of
`ProdAdicCompletions`. -/
theorem generatingSet_eq : generatingSet R K S =
  Set.preimage Subtype.val '' (
    setOf (
      λ U =>
        ∃ (V : (v: HeightOneSpectrum R) → Set (v.adicCompletion K)) (I : Finset (HeightOneSpectrum R)),
          (∀ v ∈ I, IsOpen (V v)) ∧ U = Set.pi (I.toSet) V
    )
  ) := by
  ext x
  simp only [generatingSet, FiniteAdeleRing.generatingSet, Filter.eventually_cofinite, Set.mem_image,
      Set.mem_setOf_eq, exists_exists_and_eq_and]
  refine ⟨λ ⟨V, ⟨hV_open, hV_fin⟩, hV_pi⟩ => ?_, λ ⟨y, ⟨V, I, hV_open, hV_pi⟩, hy⟩ => ?_⟩
  · set I := Set.Finite.toFinset hV_fin with IDef
    rw [← Set.preimage_comp, ← subtype_val_embedding] at hV_pi
    rw [← hV_pi]
    use Set.pi Set.univ
      (λ (v : HeightOneSpectrum R) =>
        if (v ∈ (I ∪ S).toSet) then
          (if (v ∈ I.toSet)
            then (V v) else (v.adicCompletionIntegers K)
          ) else
        Set.univ
      )
    refine ⟨?_, ?_⟩
    · use (λ v => ite (v ∈ I) (V v) (v.adicCompletionIntegers K)), I ∪ S
      refine ⟨λ v _ => ?_, by rw [Set.univ_pi_ite]; rfl⟩
      · by_cases hv : v ∈ I <;> simp only [dif_pos, dif_neg, hv, if_true, if_false, hV_open v];
          exact Valued.valuationSubring_isOpen (v.adicCompletion K)
    · simp only [← Set.image_eq_image Subtype.val_injective, Set.image_preimage_eq_inter_range]
      rw [subtype_val_range_eq_pi, ← Set.pi_inter_distrib, ← Set.pi_inter_distrib]
      refine Set.pi_congr rfl (λ v _ => ?_)
      by_cases hv₀ : v ∈ I ∪ S <;> by_cases hv₁ : v ∈ I <;> by_cases hv₂ : v ∈ S <;> simp [hv₀, hv₁, hv₂] <;>
        rw [Set.Finite.mem_toFinset, Set.nmem_setOf_iff, not_not] at hv₁ <;> rw [← hv₁]
  · use (λ v =>
      if (v ∈ I) then
        (V v) else
          (if (v ∈ S) then
            Set.univ else
            (v.adicCompletionIntegers K)
          )
        )
    refine ⟨⟨λ v => ?_, ?_⟩, ?_⟩
    · by_cases hv₀ : v ∈ I <;> by_cases hv₁ : v ∈ S <;> simp [hv₀, hv₁]; exact hV_open v hv₀; exact hV_open v hv₀;
        exact Valued.valuationSubring_isOpen (v.adicCompletion K)
    · refine Set.Finite.subset (Set.Finite.union (Finset.finite_toSet S) (Finset.finite_toSet I)) (λ v hv => ?_)
      contrapose! hv
      simp only [Set.mem_union, Finset.mem_coe, not_or] at hv
      simp only [Set.mem_setOf_eq, hv, if_false, not_not]
    · simp only [← Set.preimage_comp, ← subtype_val_embedding, ← hy, ← Set.image_eq_image Subtype.val_injective,
        Set.image_preimage_eq_inter_range, hV_pi, subtype_val_range_eq_pi]
      rw [← Set.pi_inter_distrib]
      nth_rewrite 2 [← Set.pi_univ_ite]
      rw [← Set.pi_inter_distrib]
      refine Set.pi_congr rfl (λ v _ => ?_)
      by_cases hv₀ : v ∈ I <;> by_cases hv₁ : v ∈ S <;> simp [hv₀, hv₁]

/-- The subspace topology of the finite S-adele ring viewed as a subspace of the finite adele ring coincides
with the subspace topology when viewed as a subspace of `ProdAdicCompletions`. -/
theorem topologicalSpace_eq_piTopologicalSpace : topologicalSpace R K S = instTopologicalSpaceSubtype := by
  rw [generateFrom, instTopologicalSpaceSubtype, instTopologicalSpaceProdAdicCompletions, pi_eq_generateFrom,
    induced_generateFrom_eq, generatingSet_eq]

/-- the finite S-adele ring is homeomorphic to `Π (v ∈ S), Kᵥ × Π (v ∉ S), Oᵥ`. -/
theorem homeomorph_piSubtypeProd : finiteSAdeleRing R K S ≃ₜ SProdAdicCompletionIntegers_subtype R K S := by
  rw [topologicalSpace_eq_piTopologicalSpace]
  refine Homeomorph.subtype (SProdAdicCompletions.homeomorph_piSubtypeProd R K S) (λ x => ?_)
  unfold SProdAdicCompletions.homeomorph_piSubtypeProd
  exact ⟨λ hx v => hx v.1 v.2, λ hx v hv => hx ⟨v, hv⟩⟩

/-- The finite S-adele ring is locally compact. -/
theorem locallyCompactSpace : LocallyCompactSpace (finiteSAdeleRing R K S) :=
  (Homeomorph.locallyCompactSpace_iff (homeomorph_piSubtypeProd R K S)).2 inferInstance

end FiniteSAdeleRing

-- TODO: move to FiniteAdeleRing.lean?
namespace FiniteAdeleRing

open FiniteSAdeleRing

local notation "e" => toFiniteAdeleRing R K

/-- The finite adele ring is locally compact. -/
theorem locallyCompactSpace : LocallyCompactSpace (finiteAdeleRing R K) := by
  refine LocallyCompactSpace.mk (λ x N hN => ?_)
  set S_set := setOf (λ (v : HeightOneSpectrum R) => x.val v ∉ v.adicCompletionIntegers K)
  have hS : S_set.Finite := Filter.eventually_cofinite.1 ((mem_finiteAdeleRing_iff x.val).1 x.property)
  set S := hS.toFinset
  set A_K_S := finiteSAdeleRing R K S
  have hx : x.val ∈ A_K_S := λ v hv => by rwa [hS.mem_toFinset, Set.nmem_setOf_iff, not_not] at hv
  obtain ⟨U, hU, hUOpen, hxU⟩ := mem_nhds_iff.1 hN
  set U_S := (e S) ⁻¹' U
  have he : e S ⟨x, hx⟩ = x := rfl
  have hU_S : U_S ∈ nhds ⟨x, hx⟩ := by
    rw [mem_nhds_iff]
    use U_S
    exact ⟨subset_rfl,
      (OpenEmbedding.continuous (toFiniteAdeleRing_openEmbedding R K S)).isOpen_preimage U hUOpen, hxU⟩
  obtain ⟨N_S, hN_S, hNU_S, hN_S_compact⟩ :=
    (FiniteSAdeleRing.locallyCompactSpace R K S).local_compact_nhds ⟨x, hx⟩ U_S hU_S
  obtain ⟨V, hV, hVOpen, hxV⟩ := mem_nhds_iff.1 hN_S
  use (e S) '' N_S
  refine ⟨?_, subset_trans (Set.image_subset_iff.2 hNU_S) hU,
    by rwa [← Embedding.isCompact_iff ((openEmbedding_iff _).1 (toFiniteAdeleRing_openEmbedding R K S)).1]⟩
  · rw [mem_nhds_iff]
    use (e S) '' V
    rw [Set.image_subset_image_iff (toFiniteAdeleRing_openEmbedding R K S).inj]
    use hV, OpenEmbedding.isOpenMap (toFiniteAdeleRing_openEmbedding R K S) V hVOpen, ⟨x, hx⟩

end FiniteAdeleRing

end DedekindDomain
