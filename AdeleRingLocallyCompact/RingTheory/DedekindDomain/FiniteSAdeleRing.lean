import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteAdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.AdicValuation
import AdeleRingLocallyCompact.Topology.Homeomorph

noncomputable section

open DedekindDomain IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Classical

namespace DedekindDomain

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (S : Finset (HeightOneSpectrum R))

def SProdAdicCompletions :=
  (((v : S) → v.val.adicCompletion K) × ((v : {v // v ∉ S}) → v.val.adicCompletion K))

def SProdAdicCompletionIntegers :=
  (((v : S) → v.val.adicCompletion K) × ((v : {v // v ∉ S}) → v.val.adicCompletionIntegers K))

def SProdAdicCompletionIntegers' :=
  {x : SProdAdicCompletions R K S // ∀ v : {v // v ∉ S}, x.2 v ∈ v.val.adicCompletionIntegers K}

namespace SProdAdicCompletions

instance : Coe (SProdAdicCompletionIntegers R K S) (SProdAdicCompletions R K S) where
  coe := λ x => (λ (v : S) => x.1 v, λ (v : {v // v ∉ S}) => (x.2 v : v.val.adicCompletion K))

theorem coe_injective : (Coe.coe : SProdAdicCompletionIntegers R K S → SProdAdicCompletions R K S).Injective := by
  intro x y hxy
  apply Prod.ext
  {
    exact (Prod.ext_iff.1 hxy).1
  }
  {
    have h := Function.funext_iff.1 ((Prod.ext_iff.1 hxy).2)
    funext v
    have h' : (x.2 v : v.val.adicCompletion K) = y.2 v := h v
    contrapose h'
    simp [h']
  }

section DerivedInstances

instance : TopologicalSpace (SProdAdicCompletions R K S) := instTopologicalSpaceProd

instance : TopologicalSpace (SProdAdicCompletionIntegers' R K S) := instTopologicalSpaceSubtype

instance : CommRing (SProdAdicCompletions R K S) := Prod.instCommRing

instance : Inhabited (SProdAdicCompletions R K S) := instInhabitedProd

end DerivedInstances

-- TOP level
-- Πᵥ Kᵥ is homeomorphic to Πₛ Kᵥ × Π Kᵥ
theorem homeomorph_piSubtypeProd : ProdAdicCompletions R K ≃ₜ SProdAdicCompletions R K S := Homeomorph.piEquivPiSubtypeProd _ _

end SProdAdicCompletions

namespace SProdAdicCompletionIntegers

def piSubtypeProd : SProdAdicCompletionIntegers R K S → ProdAdicCompletions R K :=
  λ x v => if hv : v ∈ S then x.1 ⟨v, hv⟩ else x.2 ⟨v, hv⟩

section DerivedInstances

instance topologicalSpace : TopologicalSpace (SProdAdicCompletionIntegers R K S) := instTopologicalSpaceProd

instance : CommRing (SProdAdicCompletionIntegers R K S) := Prod.instCommRing

instance : Inhabited (SProdAdicCompletionIntegers R K S) := instInhabitedProd

end DerivedInstances

theorem equiv_invProp : ∀ x : SProdAdicCompletionIntegers R K S, (∀ v : {v // v ∉ S}, (x.2 v).val ∈ v.val.adicCompletionIntegers K) := by
  intro x v
  simp

theorem equiv : SProdAdicCompletionIntegers' R K S ≃ SProdAdicCompletionIntegers R K S where
  toFun := λ x => (x.val.1 , λ v => ⟨x.val.2 v, x.property v⟩)
  invFun := λ x => ⟨x, equiv_invProp R K S x⟩
  left_inv := by
    rintro ⟨x, hx⟩
    rfl
  right_inv := by
    rintro ⟨x, hx⟩
    rfl

theorem homeomorph : SProdAdicCompletionIntegers' R K S ≃ₜ SProdAdicCompletionIntegers R K S where
  toEquiv := equiv R K S
  continuous_toFun := by
    unfold equiv
    simp
    apply Continuous.prod_mk
    exact (Continuous.fst (Continuous.subtype_val ({ isOpen_preimage := fun s a => a }) ))
    apply continuous_pi
    intro v
    apply Continuous.subtype_mk
    set g := Function.eval v ∘ (λ x : SProdAdicCompletionIntegers' R K S => x.val.2)
    have h : g = λ x => x.val.2 v := by
      funext x
      rfl
    rw [← h]
    apply Continuous.comp
    continuity
    exact (Continuous.snd (Continuous.subtype_val ({ isOpen_preimage := fun s a => a }) ))

  continuous_invFun := by
    unfold equiv
    simp
    apply Continuous.subtype_mk
    apply Continuous.prod_mk
    exact Continuous.fst { isOpen_preimage := fun s a => a }
    apply continuous_pi
    intro v
    apply Continuous.subtype_val
    have h : (λ x : SProdAdicCompletionIntegers R K S => x.2 v) = Function.eval v ∘ (λ x : SProdAdicCompletionIntegers R K S => x.2) := by
      funext x
      rfl
    rw [h]
    apply Continuous.comp
    continuity
    exact Continuous.snd  ({ isOpen_preimage := fun s a => a })

instance : LocallyCompactSpace ((w : S) → w.val.adicCompletion K)
  := Pi.locallyCompactSpace_of_finite

instance : LocallyCompactSpace ((w : {v // v ∉ S}) → w.val.adicCompletionIntegers K)
  := Pi.locallyCompactSpace

instance : LocallyCompactSpace (SProdAdicCompletionIntegers R K S)
  := Prod.locallyCompactSpace
    ((w : S) → w.val.adicCompletion K)
    ((w : {v // v ∉ S}) → w.val.adicCompletionIntegers K)

instance : LocallyCompactSpace (SProdAdicCompletionIntegers' R K S)
  := Homeomorph.locallyCompactSpace (SProdAdicCompletionIntegers.homeomorph R K S)

end SProdAdicCompletionIntegers

local notation "π" => FiniteAdeleRing.projection R K
local notation "ι" => FiniteAdeleRing.inclusion R K

def IsFiniteSAdele (x : ProdAdicCompletions R K) :=
  ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers K

theorem mul {x y : ProdAdicCompletions R K} (hx : IsFiniteSAdele R K S x) (hy : IsFiniteSAdele R K S y) :
    IsFiniteSAdele R K S (x * y) := by
{
  intros v hv
  rw [mem_adicCompletionIntegers]
  rw [Pi.mul_apply, Valued.v.map_mul]
  exact mul_le_one' (hx v hv) (hy v hv)
}

theorem one : IsFiniteSAdele R K S (1 : ProdAdicCompletions R K) := by
{
  intros v _
  rw [mem_adicCompletionIntegers]
  exact le_of_eq (Valued.v.map_one')
}

theorem add {x y : ProdAdicCompletions R K} (hx : IsFiniteSAdele R K S x) (hy : IsFiniteSAdele R K S y) :
  IsFiniteSAdele R K S (x + y) := by
{
  intros v hv
  rw [mem_adicCompletionIntegers]
  rw [Pi.add_apply]
  exact le_trans (Valued.v.map_add_le_max' (x v) (y v)) (max_le (hx v hv) (hy v hv))
}

theorem zero : IsFiniteSAdele R K S (0 : ProdAdicCompletions R K) := by
{
  intros v _
  rw [mem_adicCompletionIntegers]
  convert zero_le_one' (WithZero (Multiplicative ℤ))
  exact Valued.v.map_zero'
}

theorem neg {x : ProdAdicCompletions R K} (hx : IsFiniteSAdele R K S x) :
  IsFiniteSAdele R K S (-x) := by
{
  intros v hv
  rw [mem_adicCompletionIntegers]
  rw [Pi.neg_apply, Valuation.map_neg]
  exact hx v hv
}

def finiteSAdeleRing : Subring (ProdAdicCompletions R K) where
  carrier := (setOf (IsFiniteSAdele R K S))
  mul_mem' hx hy := mul R K S hx hy
  one_mem' := one R K S
  add_mem' hx hy := add R K S hx hy
  zero_mem' := zero R K S
  neg_mem' hx := neg R K S hx

namespace FiniteSAdeleRing

theorem mem_isFiniteAdele : x ∈ finiteSAdeleRing R K S → x ∈ finiteAdeleRing R K := by
{
  intro hx
  simp
  rw [ProdAdicCompletions.IsFiniteAdele]
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset S.finite_toSet
  intros v hv
  rw [Set.mem_setOf_eq] at hv
  contrapose hv
  simp
  exact hx v hv
}

theorem isFiniteSAdele_inclusion (v : HeightOneSpectrum R) (x : v.adicCompletion K) (h : v ∈ S)
  : IsFiniteSAdele R K S (ι v x) := by
  intros w hw
  simp [FiniteAdeleRing.inclusion, ProdAdicCompletions.inclusion]
  simp [Ne.symm (ne_of_mem_of_not_mem h hw)]
  exact (w.adicCompletionIntegers K).one_mem'

theorem isFiniteSAdele_inclusion' (v : HeightOneSpectrum R) (x : v.adicCompletion K) (h : x ∈ v.adicCompletionIntegers K)
  : IsFiniteSAdele R K S (ι v x) := by
  intros w _
  simp [FiniteAdeleRing.inclusion, ProdAdicCompletions.inclusion]
  by_cases hw : w = v
  {
    rw [hw]
    simp [h]
  }
  {
    simp [hw]
    exact (w.adicCompletionIntegers K).one_mem'
  }

theorem projection_range (v : HeightOneSpectrum R) :
  π v '' (setOf (λ x : finiteAdeleRing R K => IsFiniteSAdele R K S x)) = ite (v ∈ S) Set.univ (v.adicCompletionIntegers K) := by
  by_cases hv : v ∈ S
  {
    simp [hv]
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_image]
    use ι v x
    exact ⟨isFiniteSAdele_inclusion R K S v x hv, FiniteAdeleRing.projection_inclusion_eq R K v x⟩
  }
  {
    simp [hv]
    ext x
    refine' ⟨λ ⟨y, hy, hyx⟩ => _, λ hx => _⟩
    {
      specialize hy v hv
      rw [←hyx]
      exact hy
    }
    {
      use ι v x
      exact ⟨isFiniteSAdele_inclusion' R K S v x hx, FiniteAdeleRing.projection_inclusion_eq R K v x⟩
    }
  }

def embedding : finiteSAdeleRing R K S → finiteAdeleRing R K
  := λ x => ⟨x.1, mem_isFiniteAdele R K S x.2⟩

local notation "e" => embedding R K

def projection (v : HeightOneSpectrum R) : finiteSAdeleRing R K S → v.adicCompletion K
  := (π v) ∘ (e S)

local notation "π_S" => projection R K S

instance topologicalSpace: TopologicalSpace (finiteSAdeleRing R K S)
  := TopologicalSpace.induced (e S) (TopologicalSpace.generateFrom (FiniteAdeleRing.generatingSet R K))

theorem embeddingInducing : Inducing (e S) := by
  rw [inducing_iff]
  rfl

theorem embeddingInjective : (e S).Injective := by
  intros x y hxy
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  rw [embedding, embedding] at hxy
  simp at hxy
  simpa

theorem embeddingRange : Set.range (e S) = setOf (λ x : finiteAdeleRing R K => IsFiniteSAdele R K S x) := by
  rw [Set.range_eq_iff]
  use (by exact λ ⟨_, hx⟩ v hv => hx v hv)
  exact λ x hx => by
      use ⟨x, hx⟩
      rw [embedding]


theorem embedding_range : Set.range (e S) = setOf (λ x : finiteAdeleRing R K => IsFiniteSAdele R K S x) := by
  exact (Set.range_eq_iff _ _).2 ⟨λ x => x.2, λ x hx => by {use ⟨x, hx⟩; rfl}⟩

theorem embeddingRange_eq_pi : Subtype.val '' Set.range (e S) = Set.pi Set.univ (λ v => ite (v ∈ S) Set.univ (v.adicCompletionIntegers K)) := by
  ext x
  rw [embeddingRange R K]
  refine' ⟨_, _⟩
  {
    rintro ⟨y, hy₀, hy₁⟩ v _
    by_cases hv : v ∈ S
    {
      simp [hv]
    }
    {
      simp [hv]
      convert hy₀ v hv
      rw [← hy₁]
    }
  }
  {
    intro hx
    rw [Set.mem_pi] at hx
    simp
    refine' ⟨_, _⟩
    {
      intro v hv
      have h := hx v (Set.mem_univ v)
      simp only [dif_neg, hv] at h
      exact h
    }
    {
      rw [ProdAdicCompletions.IsFiniteAdele, Filter.eventually_cofinite]
      apply Set.Finite.subset (Finset.finite_toSet S)
      intro v hv
      rw [Set.mem_setOf_eq] at hv
      specialize hx v (Set.mem_univ v)
      contrapose hv
      simp [hv] at hx
      simp
      exact hx hv
    }
  }

theorem embeddingOpen : @OpenEmbedding _ _ _ (TopologicalSpace.generateFrom (FiniteAdeleRing.generatingSet R K)) (e S)
  := by
  use ⟨embeddingInducing R K S, embeddingInjective R K S⟩
  {
    rw [embeddingRange R K S]
    apply TopologicalSpace.isOpen_generateFrom_of_mem
    rw [FiniteAdeleRing.generatingSet]
    rw [Set.mem_image]
    simp
    use (λ v => ite (v ∈ S) Set.univ (v.adicCompletionIntegers K))

    refine' ⟨⟨_, _⟩, _⟩
    {
      intro v
      by_cases hv : v ∈ S
      {
        simp [projection_range R K S v, hv]
      }
      {
        simp [projection_range R K S v, hv]
        exact ProdAdicCompletions.isOpen_adicCompletionIntegers R K v
      }
    }
    {
      simp [projection_range R K S]
      rw [Set.setOf_and]
      apply Set.Finite.inter_of_left
      simp
    }
    {
      rw [← embeddingRange R K]
      rw [← embeddingRange_eq_pi]
      rw [Set.preimage_image_eq _ Subtype.val_injective]
    }
  }

theorem isFiniteSAdele_piSubtypeProd : ∀ x, IsFiniteSAdele R K S (SProdAdicCompletionIntegers.piSubtypeProd R K S x) := by
  intros x v hv
  rw [SProdAdicCompletionIntegers.piSubtypeProd]
  simp [hv]

theorem finiteSAdeleEquiv : finiteSAdeleRing R K S ≃ SProdAdicCompletionIntegers R K S where
  toFun := λ ⟨x, hx⟩ => (λ (v : S) => x v, λ (v : {v // v ∉ S}) => ⟨x v, hx v.1 v.2⟩)
  invFun x := ⟨SProdAdicCompletionIntegers.piSubtypeProd R K S x, isFiniteSAdele_piSubtypeProd R K S x⟩
  right_inv := by
    rintro ⟨f, g⟩
    simp
    apply Prod.ext
    {
      ext y
      rcases y with ⟨val, property⟩
      simp only [property, SProdAdicCompletionIntegers.piSubtypeProd, dif_pos, dif_neg, Subtype.coe_mk]
    }
    {
      ext y
      rcases y with ⟨val, property⟩
      simp only [property, SProdAdicCompletionIntegers.piSubtypeProd]
      simp
    }
  left_inv := by
    rintro ⟨x, hx⟩
    simp
    funext v
    by_cases h : v ∈ S <;>
      · simp only [h, SProdAdicCompletionIntegers.piSubtypeProd, dif_pos, dif_neg, not_false_iff]

def generatingSet : Set (Set (finiteSAdeleRing R K S))
  := Set.preimage (e S) '' (FiniteAdeleRing.generatingSet R K)

theorem generateFrom : topologicalSpace R K S = TopologicalSpace.generateFrom (FiniteSAdeleRing.generatingSet R K S) := by
  have h := @induced_generateFrom_eq _ _ (FiniteAdeleRing.generatingSet R K) (e S)
  rw [generatingSet, ← h]
  rfl

theorem embeddingRange_mem_generatingSet : Set.range (e S) ∈ FiniteAdeleRing.generatingSet R K := by
  rw [FiniteAdeleRing.generatingSet]
  simp
  use (λ v => ite (v ∈ S) Set.univ (v.adicCompletionIntegers K))
  refine' ⟨⟨_, _⟩, _⟩
  {
    intro v
    by_cases hv : v ∈ S
    {
      simp [hv]
    }
    {
      simp [hv]
      exact ProdAdicCompletions.isOpen_adicCompletionIntegers R K v
    }
  }
  {
    apply Set.Finite.subset (Finset.finite_toSet S)
    intro v hv
    simp at hv
    exact hv.1
  }
  {
    ext x
    refine' ⟨_, _⟩
    {
      intro hx
      simp at hx
      rw [Set.mem_pi] at hx
      rw [embeddingRange]
      intro v hv
      simp [hv] at hx
      exact hx v hv
    }
    {
      intro hx
      rw [embeddingRange] at hx
      simp
      rw [Set.mem_pi]
      intro v _
      simp
      intro hv
      exact hx v hv
    }
  }

theorem set_univ_mem_generatingSet : Set.univ ∈ generatingSet R K S := by
  rw [generatingSet]
  simp
  use (Set.range (e S)), embeddingRange_mem_generatingSet R K S

theorem subtype_val_embedding : (Subtype.val : finiteSAdeleRing R K S → ProdAdicCompletions R K) = Subtype.val ∘ e S := by
  funext x
  rfl

theorem subtype_val_range_eq_pi
  : Set.range (Subtype.val : finiteSAdeleRing R K S → ProdAdicCompletions R K)
  = Set.pi Set.univ (λ v => ite (v ∈ S) Set.univ (v.adicCompletionIntegers K)) := by
  rw [subtype_val_embedding, Set.range_comp, embeddingRange_eq_pi]

theorem generatingSet_eq : generatingSet R K S =
  Set.preimage Subtype.val '' (
    setOf (
      λ U =>
        ∃ (V : (v: HeightOneSpectrum R) → Set (v.adicCompletion K)) (I : Finset (HeightOneSpectrum R)),
          (∀ v ∈ I, IsOpen (V v)) ∧ U = Set.pi (I.toSet) V
    )
  ) := by
  ext x
  refine' ⟨_, _⟩
  {
    intro hx
    rw [generatingSet] at hx
    rw [FiniteAdeleRing.generatingSet] at hx
    simp at hx
    obtain ⟨V, hV, hV'⟩ := hx
    simp
    set I := Set.Finite.toFinset hV.2 with IDef
    rw [← Set.preimage_comp] at hV'
    rw [← subtype_val_embedding] at hV'
    rw [← hV']
    use Set.pi Set.univ (λ (v : HeightOneSpectrum R) => ite (v ∈ (I ∪ S).toSet) (ite (v ∈ I.toSet) (V v) (v.adicCompletionIntegers K)) Set.univ)
    refine' ⟨_, _⟩
    {
      use (λ v => ite (v ∈ I) (V v) (v.adicCompletionIntegers K))
      use (I ∪ S)
      refine' ⟨λ v _ => _, _⟩
      {
        by_cases hv' : v ∈ I
        {
          simp only [dif_pos, hv', if_true, hV.1 v]
        }
        {
          simp only [dif_neg, hv', if_false]
          exact ProdAdicCompletions.isOpen_adicCompletionIntegers R K v
        }
      }
      {
        rw [Set.univ_pi_ite]
        rfl
      }
    }
    {
      rw [← Set.image_eq_image Subtype.val_injective]
      rw [Set.image_preimage_eq_inter_range]
      rw [Set.image_preimage_eq_inter_range]
      rw [subtype_val_range_eq_pi]
      rw [← Set.pi_inter_distrib]
      rw [← Set.pi_inter_distrib]
      apply Set.pi_congr rfl
      intro v _
      by_cases hv' : v ∈ I ∪ S
      {
        by_cases hv'' : v ∈ I
        {
          by_cases hv''' : v ∈ S
          {
            simp [hv', hv'', hv''']
          }
          {
            simp [hv', hv'', hv''']
          }
        }
        {
          by_cases hv''' : v ∈ S
          {
            simp [hv', hv'', hv''']
            rw [Set.Finite.mem_toFinset] at hv''
            rw [Set.nmem_setOf_iff] at hv''
            simp at hv''
            rw [← hv'']
          }
          {
            simp [hv', hv'', hv''']
            simp at hv''
            rw [Set.Finite.mem_toFinset] at hv''
            rw [Set.nmem_setOf_iff] at hv''
            simp at hv''
            rw [← hv'']
          }
        }
      }
      {
        by_cases hv'' : v ∈ I
        {
          by_cases hv''' : v ∈ S
          {
            simp [hv', hv'', hv''']
          }
          {
            simp [hv', hv'', hv''']
          }
        }
        {
          by_cases hv''' : v ∈ S
          {
            simp [hv', hv'', hv''']
            rw [Set.Finite.mem_toFinset] at hv''
            rw [Set.nmem_setOf_iff] at hv''
            push_neg at hv''
            rw [← hv'']
          }
          {
            simp [hv', hv'', hv''']
            rw [Set.Finite.mem_toFinset] at hv''
            rw [Set.nmem_setOf_iff] at hv''
            simp at hv''
            rw [← hv'']
          }
        }
      }
    }
  }
  {
    intro hx
    simp at hx
    obtain ⟨y, ⟨V, I, hV⟩, hy⟩ := hx
    rw [generatingSet]
    rw [FiniteAdeleRing.generatingSet]
    simp
    use (λ v => ite (v ∈ I) (V v) (ite (v ∈ S) Set.univ (v.adicCompletionIntegers K)))
    refine' ⟨_, _⟩
    {
      refine' ⟨_, _⟩
      {
        intro v
        by_cases hv : v ∈ I
        {
          by_cases hv' : v ∈ S
          {
            simp [hv, hv']
            exact hV.1 v hv
          }
          {
            simp [hv, hv']
            exact hV.1 v hv
          }
        }
        {
          by_cases hv' : v ∈ S
          {
            simp [hv, hv']
          }
          {
            simp [hv, hv']
            exact ProdAdicCompletions.isOpen_adicCompletionIntegers R K v
          }
        }
      }
      {
        apply Set.Finite.subset (Set.Finite.union (Finset.finite_toSet S) (Finset.finite_toSet I))
        intro v hv
        simp at hv
        contrapose hv
        simp
        simp at hv
        push_neg at hv
        simp [hv]
      }
    }
    {
      rw [← Set.preimage_comp]
      rw [← subtype_val_embedding]
      rw [← hy]
      rw [← Set.image_eq_image Subtype.val_injective]
      rw [Set.image_preimage_eq_inter_range]
      rw [Set.image_preimage_eq_inter_range]
      rw [hV.2]
      rw [subtype_val_range_eq_pi]
      rw [← Set.pi_inter_distrib]
      nth_rewrite 2 [← Set.pi_univ_ite]
      rw [← Set.pi_inter_distrib]
      apply Set.pi_congr rfl
      intro v _
      by_cases hv : v ∈ I
      {
        by_cases hv' : v ∈ S
        {
          simp [hv, hv']
        }
        {
          simp [hv, hv']
        }
      }
      {
        by_cases hv' : v ∈ S
        {
          simp [hv, hv']
        }
        {
          simp [hv, hv']
        }
      }
    }
  }

-- BOTTOM-LEFT : finite S-adeles, are given the subspace topology of the finite Adeles
-- we show that this is the _same_ as giving it the subspace topology of Πᵥ Kᵥ (most of this is already above, see generatingSet_eq)
theorem topologicalSpace_eq_piTopologicalSpace : topologicalSpace R K S = instTopologicalSpaceSubtype := by
  rw [generateFrom]
  rw [instTopologicalSpaceSubtype]
  rw [instTopologicalSpaceProdAdicCompletions]
  rw [pi_eq_generateFrom]
  rw [induced_generateFrom_eq]
  rw [generatingSet_eq]

theorem homeomorph_piSubtypeProd : finiteSAdeleRing R K S ≃ₜ SProdAdicCompletionIntegers' R K S := by
  rw [topologicalSpace_eq_piTopologicalSpace]
  apply Homeomorph.subtype (SProdAdicCompletions.homeomorph_piSubtypeProd R K S)
  intro x
  unfold SProdAdicCompletions.homeomorph_piSubtypeProd
  refine' ⟨_, _⟩
  {
    intro hx v
    exact hx v.val v.property
  }
  {
    intro h v hv
    exact h ⟨v, hv⟩
  }

theorem locallyCompactSpace (S : Finset (HeightOneSpectrum R)) : LocallyCompactSpace (finiteSAdeleRing R K S) := by
  exact Homeomorph.locallyCompactSpace (homeomorph_piSubtypeProd R K S)

end FiniteSAdeleRing

namespace FiniteAdeleRing

local notation "e" => FiniteSAdeleRing.embedding R K

theorem locallyCompactSpace : LocallyCompactSpace (finiteAdeleRing R K) := by
    have local_compact_nhds : ∀ (x : finiteAdeleRing R K), ∀ n ∈ nhds x, ∃ s ∈ nhds x, s ⊆ n ∧ IsCompact s := by
      {
        intros x N hN
        set setS := setOf (λ (v : HeightOneSpectrum R) => x.val v ∉ v.adicCompletionIntegers K)
        have hS : setS.Finite := Filter.eventually_cofinite.1 ((mem_finiteAdeleRing_iff x.val).1 x.property)
        set S := hS.toFinset
        set A_K_S := finiteSAdeleRing R K S

        have hx : x.val ∈ A_K_S := by
          {
            intros v hv
            rwa [hS.mem_toFinset, Set.nmem_setOf_iff, not_not] at hv
          }

        obtain ⟨U, hU, hUOpen, hxU⟩ := mem_nhds_iff.1 hN
        set U_S := (e S) ⁻¹' U
        have he : e S ⟨x, hx⟩ = x := rfl
        have hU_S : U_S ∈ nhds ⟨x, hx⟩ := by
        {
          rw [mem_nhds_iff]
          use U_S
          use subset_rfl
          use (OpenEmbedding.continuous (FiniteSAdeleRing.embeddingOpen R K S)).isOpen_preimage U hUOpen
          exact hxU
        }
        obtain ⟨N', hN', hNU', hNC'⟩ := (FiniteSAdeleRing.locallyCompactSpace R K S).local_compact_nhds ⟨x, hx⟩ U_S hU_S
        obtain ⟨V, hV, hVOpen, hxV⟩ := mem_nhds_iff.1 hN'
        use (e S) '' N'
        apply And.intro
        {
          rw [mem_nhds_iff]
          use (e S) '' V
          rw [Set.image_subset_image_iff (FiniteSAdeleRing.embeddingOpen R K S).inj]
          use hV
          use OpenEmbedding.isOpenMap (FiniteSAdeleRing.embeddingOpen R K S) V hVOpen
          use ⟨x, hx⟩
        }
        apply And.intro
        {
          apply subset_trans _ hU
          simp
          exact hNU'
        }
        {
          rwa [← Embedding.isCompact_iff ((openEmbedding_iff _).1 (FiniteSAdeleRing.embeddingOpen R K S)).1]
        }
      }
    exact ⟨local_compact_nhds⟩

end FiniteAdeleRing

end DedekindDomain
