import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteAdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.AdicValuation
import AdeleRingLocallyCompact.Topology.Homeomorph

noncomputable section

open DedekindDomain IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Classical

namespace DedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] (K : Type*)
  [Field K] [Algebra R K] [IsFractionRing R K] (S : Finset (HeightOneSpectrum R))

def SProdAdicCompletions :=
  (((v : S) → v.val.adicCompletion K) × ((v : {v // v ∉ S}) → v.val.adicCompletion K))

def SProdAdicCompletionIntegers :=
  (((v : S) → v.val.adicCompletion K) × ((v : {v // v ∉ S}) → v.val.adicCompletionIntegers K))

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

-- TOP level
-- Πᵥ Kᵥ is homeomorphic to Πₛ Kᵥ × Π Kᵥ
theorem homeomorph_piSubtypeProd : ProdAdicCompletions R K ≃ₜ SProdAdicCompletions R K S :=
  Homeomorph.piEquivPiSubtypeProd _ _

end SProdAdicCompletions

namespace SProdAdicCompletionIntegers

def piSubtypeProd : SProdAdicCompletionIntegers R K S → ProdAdicCompletions R K :=
  λ x v => if hv : v ∈ S then x.1 ⟨v, hv⟩ else x.2 ⟨v, hv⟩

section DerivedInstances

instance topologicalSpace : TopologicalSpace (SProdAdicCompletionIntegers R K S) := instTopologicalSpaceProd

instance : CommRing (SProdAdicCompletionIntegers R K S) := Prod.instCommRing

instance : Inhabited (SProdAdicCompletionIntegers R K S) := instInhabitedProd

end DerivedInstances

theorem subtypeEquiv : SProdAdicCompletionIntegers_subtype R K S ≃ SProdAdicCompletionIntegers R K S where
  toFun := λ x => (x.val.1 , λ v => ⟨x.val.2 v, x.property v⟩)
  invFun := λ x => ⟨x, λ v => SetLike.coe_mem (x.2 v)⟩
  left_inv := λ _ => rfl
  right_inv := λ _ => rfl

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

instance : LocallyCompactSpace ((w : S) → w.val.adicCompletion K) := Pi.locallyCompactSpace_of_finite

instance : LocallyCompactSpace ((w : {v // v ∉ S}) → w.val.adicCompletionIntegers K) := Pi.locallyCompactSpace

instance : LocallyCompactSpace (SProdAdicCompletionIntegers R K S) :=
  Prod.locallyCompactSpace
    ((w : S) → w.val.adicCompletion K)
    ((w : {v // v ∉ S}) → w.val.adicCompletionIntegers K)

instance : LocallyCompactSpace (SProdAdicCompletionIntegers_subtype R K S) :=
  Homeomorph.locallyCompactSpace (SProdAdicCompletionIntegers.homeomorph R K S)

end SProdAdicCompletionIntegers

local notation "π" => FiniteAdeleRing.projection
local notation "ι" => FiniteAdeleRing.localInclusion

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

def finiteSAdeleRing : Subring (ProdAdicCompletions R K) where
  carrier := (setOf (IsFiniteSAdele S))
  mul_mem' hx hy := mul hx hy
  one_mem' := one
  add_mem' hx hy := add hx hy
  zero_mem' := zero
  neg_mem' hx := neg hx

namespace FiniteSAdeleRing

variable {R K S}

theorem mem_isFiniteAdele {x : ProdAdicCompletions R K} (hx : x ∈ finiteSAdeleRing R K S) :
  x ∈ finiteAdeleRing R K := by
  rw [mem_finiteAdeleRing_iff, ProdAdicCompletions.IsFiniteAdele, Filter.eventually_cofinite]
  refine Set.Finite.subset S.finite_toSet (λ v hv => ?_)
  contrapose hv
  rw [Set.mem_setOf_eq, not_not]
  exact hx v hv

theorem isFiniteSAdele_localInclusion (v : HeightOneSpectrum R) (x : v.adicCompletion K)
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

theorem isFiniteSAdele_localInclusion_of_S (v : HeightOneSpectrum R) (x : v.adicCompletion K) (h : v ∈ S) :
  IsFiniteSAdele S (ι v x).val := by
  intros w hw
  simp only [FiniteAdeleRing.localInclusion, ProdAdicCompletions.localInclusion]
  simp only [Ne.symm (ne_of_mem_of_not_mem h hw), ↓reduceDite]
  exact (w.adicCompletionIntegers K).one_mem'

variable (K S)

theorem projection_range (v : HeightOneSpectrum R) :
  π v '' (setOf (λ (x : finiteAdeleRing R K) => IsFiniteSAdele S x.val)) =
     if (v ∈ S) then Set.univ else (v.adicCompletionIntegers K) := by
  by_cases hv : v ∈ S <;> simp only [hv, ↓reduceIte, Set.eq_univ_iff_forall]
  · intro x
    use ι v x
    exact ⟨isFiniteSAdele_localInclusion_of_S v x hv, FiniteAdeleRing.projection_localInclusion_eq v x⟩
  · refine Set.ext (λ x => ⟨λ ⟨y, hy, hyx⟩ => by rw [← hyx]; exact hy v hv, λ hx => ?_⟩)
    use ι v x
    exact ⟨isFiniteSAdele_localInclusion v x hx, FiniteAdeleRing.projection_localInclusion_eq v x⟩


variable (R)

def toFiniteAdeleRing : finiteSAdeleRing R K S → finiteAdeleRing R K
  := λ x => ⟨x.1, mem_isFiniteAdele x.2⟩

local notation "e" => toFiniteAdeleRing R K

instance topologicalSpace: TopologicalSpace (finiteSAdeleRing R K S)
  := TopologicalSpace.induced (e S) (TopologicalSpace.generateFrom (FiniteAdeleRing.generatingSet R K))

theorem toFiniteAdeleRing_inducing : Inducing (e S) := by rw [inducing_iff]; rfl

theorem toFiniteAdeleRing_injective : (e S).Injective := by
  intro x y hxy
  simp only [toFiniteAdeleRing, Subtype.mk.injEq] at  hxy
  rw [Subtype.mk.injEq]
  exact hxy

theorem toFiniteAdeleRing_range : Set.range (e S) = setOf (λ x : finiteAdeleRing R K => IsFiniteSAdele S x.val) := by
  exact (Set.range_eq_iff _ _).2 ⟨λ x => x.2, λ x hx => by {use ⟨x, hx⟩; rfl}⟩

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

theorem toFiniteAdeleRing_openEmbedding : OpenEmbedding (e S) := by
  use ⟨toFiniteAdeleRing_inducing R K S, toFiniteAdeleRing_injective R K S⟩
  exact TopologicalSpace.isOpen_generateFrom_of_mem (toFiniteAdeleRing_range_mem_generatingSet R K S)

variable {R K S}

theorem isFiniteSAdele_piSubtypeProd (x : SProdAdicCompletionIntegers R K S) :
  IsFiniteSAdele S (SProdAdicCompletionIntegers.piSubtypeProd R K S x) :=
  λ v hv => by simp only [SProdAdicCompletionIntegers.piSubtypeProd, hv, ↓reduceDite, SetLike.coe_mem]

variable (R K S)

theorem finiteSAdeleEquiv : finiteSAdeleRing R K S ≃ SProdAdicCompletionIntegers R K S where
  toFun := λ ⟨x, hx⟩ => (λ (v : S) => x v, λ (v : {v // v ∉ S}) => ⟨x v, hx v.1 v.2⟩)
  invFun x := ⟨SProdAdicCompletionIntegers.piSubtypeProd R K S x, isFiniteSAdele_piSubtypeProd x⟩
  right_inv _ := by
    apply Prod.ext <;>
      · ext y; rcases y with ⟨val, property⟩; simp only [property, SProdAdicCompletionIntegers.piSubtypeProd]; rfl
  left_inv := λ ⟨x, hx⟩ => by
    simp only [Subtype.mk.injEq]
    funext v
    by_cases h : v ∈ S <;>
      · simp only [h, SProdAdicCompletionIntegers.piSubtypeProd, dif_pos, dif_neg, not_false_iff]

def generatingSet : Set (Set (finiteSAdeleRing R K S))
  := Set.preimage (e S) '' (FiniteAdeleRing.generatingSet R K)

theorem generateFrom :
  topologicalSpace R K S = TopologicalSpace.generateFrom (FiniteSAdeleRing.generatingSet R K S) := by
  rw [generatingSet, ← induced_generateFrom_eq]; rfl

theorem set_univ_mem_generatingSet : Set.univ ∈ generatingSet R K S := by
  simp only [generatingSet, Set.mem_image, Set.preimage_eq_univ_iff]
  use (Set.range (e S)), toFiniteAdeleRing_range_mem_generatingSet R K S

theorem subtype_val_embedding :
  (Subtype.val : finiteSAdeleRing R K S → ProdAdicCompletions R K) = Subtype.val ∘ e S := rfl

theorem subtype_val_range_eq_pi :
  Set.range (Subtype.val : finiteSAdeleRing R K S → ProdAdicCompletions R K)
    = Set.pi Set.univ (λ v => ite (v ∈ S) Set.univ (v.adicCompletionIntegers K)) := by
  rw [subtype_val_embedding, Set.range_comp, toFiniteAdeleRing_range_eq_pi]

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

-- BOTTOM-LEFT : finite S-adeles, are given the subspace topology of the finite Adeles
-- we show that this is the _same_ as giving it the subspace topology of Πᵥ Kᵥ (most of this is already above, see generatingSet_eq)
theorem topologicalSpace_eq_piTopologicalSpace : topologicalSpace R K S = instTopologicalSpaceSubtype := by
  rw [generateFrom, instTopologicalSpaceSubtype, instTopologicalSpaceProdAdicCompletions, pi_eq_generateFrom,
    induced_generateFrom_eq, generatingSet_eq]

theorem homeomorph_piSubtypeProd : finiteSAdeleRing R K S ≃ₜ SProdAdicCompletionIntegers_subtype R K S := by
  rw [topologicalSpace_eq_piTopologicalSpace]
  refine Homeomorph.subtype (SProdAdicCompletions.homeomorph_piSubtypeProd R K S) (λ x => ?_)
  unfold SProdAdicCompletions.homeomorph_piSubtypeProd
  exact ⟨λ hx v => hx v.1 v.2, λ hx v hv => hx ⟨v, hv⟩⟩

theorem locallyCompactSpace : LocallyCompactSpace (finiteSAdeleRing R K S) := by
  exact Homeomorph.locallyCompactSpace (homeomorph_piSubtypeProd R K S)

end FiniteSAdeleRing

-- TODO: move to FiniteAdeleRing.lean?
namespace FiniteAdeleRing

open FiniteSAdeleRing

local notation "e" => toFiniteAdeleRing R K

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
