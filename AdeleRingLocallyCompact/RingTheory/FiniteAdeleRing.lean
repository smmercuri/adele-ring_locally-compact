import Mathlib

open DedekindDomain
open NumberField
open IsDedekindDomain

open scoped Classical

namespace DedekindDomain

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K] [NumberField K] [Algebra R K]
  [IsFractionRing R K] (S : Finset (HeightOneSpectrum R))

def SProdAdicCompletions := (((v : S) → v.val.adicCompletion K) × ((v : {v // v ∉ S}) → v.val.adicCompletion K))
def SProdAdicCompletionIntegers := (((v : S) → v.val.adicCompletion K) × ((v : {v // v ∉ S}) → v.val.adicCompletionIntegers K))

--local notation "K_hat" => ProdAdicCompletions R K
local notation "K_hat_S" => SProdAdicCompletions R K S
local notation "R_hat_S" => SProdAdicCompletionIntegers R K S

namespace ProdAdicCompletions

def projection (v : HeightOneSpectrum R) : ProdAdicCompletions R K → v.adicCompletion K
  := Pi.evalRingHom _ v

theorem adicCompletions.congr (w v : HeightOneSpectrum R) (h : w = v)
  : w.adicCompletion K = v.adicCompletion K := congrArg _ h

noncomputable def inclusion (v : HeightOneSpectrum R) : v.adicCompletion K → ProdAdicCompletions R K
  := λ x => (λ w => dite (w = v) (λ h => adicCompletions.congr R K w v h ▸ x) (λ _ => (1 : w.adicCompletion K)))

theorem isFiniteAdele_inclusion (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : (inclusion R K v x).IsFiniteAdele := by
  rw [ProdAdicCompletions.IsFiniteAdele]
  rw [Filter.eventually_cofinite]
  have h : setOf (λ w => inclusion R K v x w ∉ w.adicCompletionIntegers K) ⊆ {v} := by
    intro w hw
    simp [Set.mem_setOf_eq] at hw ⊢
    contrapose hw
    push_neg
    rw [inclusion]
    simp [hw]
    exact (w.adicCompletionIntegers K).one_mem'
  apply Set.Finite.subset _ h
  simp

theorem projection_inclusion_eq' (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : inclusion R K v x v = x := by simp [inclusion]

theorem projection_inclusion_eq (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : projection R K v (inclusion R K v x) = x := by convert projection_inclusion_eq' R K v x

-- TODO : update and use 'Valued.valuationSubring_isOpen
def isOpen_adicCompletionIntegers (v : HeightOneSpectrum R): IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  rw [isOpen_iff_mem_nhds]
  intros x hx
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hx
  rw [Valued.mem_nhds]
  use 1
  intros y hy
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, ← sub_add_cancel y x]
  rw [Set.mem_setOf_eq] at hy
  exact le_trans (Valued.v.map_add (y - x) x) (max_le (le_of_lt hy) hx)

end ProdAdicCompletions

namespace SProdAdicCompletions

noncomputable instance : Coe (R_hat_S) (K_hat_S) where
  coe := λ x => (λ (v : S) => x.1 v, λ (v : {v // v ∉ S}) => (x.2 v : v.val.adicCompletion K))

theorem coe_injective : (Coe.coe : R_hat_S → K_hat_S).Injective := by
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

instance : TopologicalSpace (K_hat_S) := instTopologicalSpaceProd

private noncomputable instance : CommRing ((v : S) → v.val.adicCompletion K) :=
  inferInstanceAs (CommRing (∀ v : S, v.val.adicCompletion K))
private noncomputable instance : CommRing ((v : {v // v ∉ S}) → v.val.adicCompletion K) :=
  inferInstanceAs (CommRing (∀ v : {v // v ∉ S}, v.val.adicCompletion K))
noncomputable instance : CommRing (K_hat_S) := Prod.instCommRing

private noncomputable instance : Inhabited ((v : S) → v.val.adicCompletion K) :=
  inferInstanceAs (Inhabited (∀ v : S, v.val.adicCompletion K))
private noncomputable instance : Inhabited ((v : {v // v ∉ S}) → v.val.adicCompletion K) :=
  inferInstanceAs (Inhabited ((v : {v // v ∉ S}) → v.val.adicCompletion K))
noncomputable instance : Inhabited (K_hat_S) := instInhabitedProd

end DerivedInstances

end SProdAdicCompletions

namespace SProdAdicCompletionIntegers

noncomputable def piSubtypeProd : SProdAdicCompletionIntegers R K S → ProdAdicCompletions R K :=
  λ x v => if hv : v ∈ S then x.1 ⟨v, hv⟩ else x.2 ⟨v, hv⟩

section DerivedInstances

-- TODO : do we need to specify the Pi.topologicalSpace ?
instance topologicalSpace_fst : TopologicalSpace ((v : S) → v.val.adicCompletion K) := Pi.topologicalSpace
instance topologicalSpace_snd : TopologicalSpace ((v : {v // v ∉ S}) → v.val.adicCompletionIntegers K) := Pi.topologicalSpace
instance topologicalSpace : TopologicalSpace (R_hat_S)
  := @instTopologicalSpaceProd _ _ (topologicalSpace_fst R K S) (topologicalSpace_snd R K S)

private noncomputable instance : CommRing ((v : {v // v ∉ S}) → v.val.adicCompletionIntegers K) :=
  inferInstanceAs (CommRing (∀ v : {v // v ∉ S}, v.val.adicCompletionIntegers K))
noncomputable instance : CommRing (R_hat_S) := Prod.instCommRing

private noncomputable instance : Inhabited ((v : {v // v ∉ S}) → v.val.adicCompletionIntegers K) :=
  inferInstanceAs (Inhabited ((v : {v // v ∉ S}) → v.val.adicCompletionIntegers K))
noncomputable instance : Inhabited (R_hat_S) := instInhabitedProd

end DerivedInstances

end SProdAdicCompletionIntegers

namespace FiniteAdeleRing

def projection (v : HeightOneSpectrum R) : finiteAdeleRing R K → v.adicCompletion K
  :=  (Pi.evalRingHom _ v) ∘ Subtype.val

noncomputable def inclusion (v : HeightOneSpectrum R) : v.adicCompletion K → finiteAdeleRing R K
  := λ x => ⟨ProdAdicCompletions.inclusion R K v x, ProdAdicCompletions.isFiniteAdele_inclusion R K v x⟩

local notation "π" => projection R K
local notation "ι" => inclusion R K

theorem projection_inclusion_eq' (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : (ι v x).val v = x := by simp [inclusion, ProdAdicCompletions.projection_inclusion_eq']

theorem projection_inclusion_eq (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : π v (ι v x) = x := by convert projection_inclusion_eq' R K v x

def generatingSet : Set (Set (finiteAdeleRing R K)) :=
  Set.preimage (Subtype.val) '' (Set.pi Set.univ '' (
    setOf (
      λ V =>
        (∀ v, IsOpen (V v)) ∧
        (∀ᶠ v in Filter.cofinite, V v = v.adicCompletionIntegers K)
    )
  ))

noncomputable instance : TopologicalSpace (finiteAdeleRing R K)
  := TopologicalSpace.generateFrom (generatingSet R K)

end FiniteAdeleRing

namespace FiniteSAdeleRing

local notation "π" => FiniteAdeleRing.projection R K
local notation "ι" => FiniteAdeleRing.inclusion R K

def IsFiniteSAdele (x : ProdAdicCompletions R K) :=
  ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers K

theorem mul {x y : ProdAdicCompletions R K} (hx : IsFiniteSAdele R K S x) (hy : IsFiniteSAdele R K S y) :
    IsFiniteSAdele R K S (x * y) := by
{
  intros v hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [Pi.mul_apply, Valued.v.map_mul]
  exact mul_le_one' (hx v hv) (hy v hv)
}

theorem one : IsFiniteSAdele R K S (1 : ProdAdicCompletions R K) := by
{
  intros v _
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact le_of_eq (Valued.v.map_one')
}

theorem add {x y : ProdAdicCompletions R K} (hx : IsFiniteSAdele R K S x) (hy : IsFiniteSAdele R K S y) :
  IsFiniteSAdele R K S (x + y) := by
{
  intros v hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [Pi.add_apply]
  exact le_trans (Valued.v.map_add_le_max' (x v) (y v)) (max_le (hx v hv) (hy v hv))
}

theorem zero : IsFiniteSAdele R K S (0 : ProdAdicCompletions R K) := by
{
  intros v _
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  convert zero_le_one' (WithZero (Multiplicative ℤ))
  exact Valued.v.map_zero'
}

theorem neg {x : ProdAdicCompletions R K} (hx : IsFiniteSAdele R K S x) :
  IsFiniteSAdele R K S (-x) := by
{
  intros v hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [Pi.neg_apply, Valuation.map_neg]
  exact hx v hv
}

noncomputable def finiteSAdeleRing : Subring (ProdAdicCompletions R K) where
  carrier := (setOf (IsFiniteSAdele R K S))
  mul_mem' hx hy := mul R K S hx hy
  one_mem' := one R K S
  add_mem' hx hy := add R K S hx hy
  zero_mem' := zero R K S
  neg_mem' hx := neg R K S hx

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

noncomputable def embedding : finiteSAdeleRing R K S → finiteAdeleRing R K
  := λ x => ⟨x.1, mem_isFiniteAdele R K S x.2⟩

local notation "e" => embedding R K

noncomputable def projection (v : HeightOneSpectrum R) : finiteSAdeleRing R K S → v.adicCompletion K
  := (π v) ∘ (e S)

local notation "π_S" => projection R K S

noncomputable instance topologicalSpace: TopologicalSpace (finiteSAdeleRing R K S)
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

-- this is saying that e S '' (e S ⁻¹' V) is in the generating set, we have e S ⁻¹' V is in generating set by defn
-- TODO : make this more general? i.e., generatingSet is closed under intersection
theorem mem_finiteAdeleRingGeneratingSet_range_inter : ∀ V : Set (finiteAdeleRing R K),
  V ∈ FiniteAdeleRing.generatingSet R K
  → Set.range (e S) ∩ V ∈ FiniteAdeleRing.generatingSet R K := by
  intros V hV
  rw [FiniteAdeleRing.generatingSet]
  simp
  have h' := embeddingRange_mem_generatingSet R K S
  rw [FiniteAdeleRing.generatingSet] at hV h'
  simp at hV h'
  obtain ⟨W', hW'⟩ := h'
  obtain ⟨W, hW⟩ := hV
  use (λ v => W' v ∩ W v)

  refine' ⟨⟨λ v => IsOpen.inter (hW'.1.1 v) (hW.1.1 v), _⟩, _⟩
  {
    push_neg
    apply Set.Finite.subset (Set.Finite.union hW.1.2 hW'.1.2)
    intros v hv
    contrapose hv
    rw [Set.nmem_setOf_iff]
    push_neg
    simp at hv
    push_neg at hv
    simp [hv]
  }
  {
    rw [Set.pi_inter_distrib]
    rw [Set.preimage_inter]
    rw [hW.2]
    rw [hW'.2]
  }

theorem mem_generatingSet_iff : ∀ U, U ∈ FiniteSAdeleRing.generatingSet R K S ↔
  U ∈ Set.preimage (Subtype.val) '' (Set.pi Set.univ '' (
    setOf (
      λ V =>
        (∀ v, IsOpen (V v)) ∧
        (∀ v, v ∉ S → V v ⊆ v.adicCompletionIntegers K) ∧
        (∀ᶠ v in Filter.cofinite, V v = v.adicCompletionIntegers K)
    )
  ))
  /-(∀ x, x ∈ Subtype.val '' U ↔ x ∈ Set.pi Set.univ (λ v => π_S v '' U)) ∧
  (∀ v, IsOpen (π_S v '' U)) ∧
  (∀ᶠ v in Filter.cofinite, π_S v '' U = v.adicCompletionIntegers K)-/:= by
  intro U
  --simp only [projection, Set.image_comp]
  refine' ⟨_, _⟩
  {
    intros hU
    rw [FiniteSAdeleRing.generatingSet] at hU

    obtain ⟨V, hV, hVU⟩ := hU
    rw [FiniteAdeleRing.generatingSet] at hV
    simp at hV
    simp only [← hVU]
    obtain ⟨W, hW⟩ := hV
    have h' := embeddingRange_mem_generatingSet R K S
    rw [FiniteAdeleRing.generatingSet] at h'
    simp at h'
    obtain ⟨W', hW'⟩ := h'
    simp
    use (λ v => W v ∩ W' v)
    refine' ⟨⟨_, _, _⟩, _⟩
    {
      intro v
      exact IsOpen.inter (hW.1.1 v) (hW'.1.1 v)
    }
    {
      intros v hv
      apply subset_trans (Set.inter_subset_right (W v) (W' v))
      intro xv hxv
      have h := hW'.2
      rw [← Set.image_eq_image Subtype.val_injective] at h
      have h₁ : Set.pi Set.univ W' ⊆ Set.range (Subtype.val : finiteAdeleRing R K → ProdAdicCompletions R K) := by
        have h : ∀ x, x ∈ Set.pi Set.univ W' → ProdAdicCompletions.IsFiniteAdele x := by
          intro x hx
          rw [ProdAdicCompletions.IsFiniteAdele]
          simp
          apply Set.Finite.subset hW'.1.2
          intro v hv
          rw [Set.mem_setOf_eq] at hv ⊢
          contrapose hv
          simp at hv ⊢
          specialize hx v (Set.mem_univ v)
          rw [hv] at hx
          exact hx

        intro x hx
        rw [Set.mem_range]
        use ⟨x, h x hx⟩
      rw [Set.image_preimage_eq_of_subset h₁] at h
      have h₂ := @Set.eval_image_univ_pi _ _ W' v
      rw [← h₂] at hxv
      rw [h] at hxv
      rw [Set.mem_image] at hxv
      obtain ⟨x, hx⟩ := hxv
      rw [embeddingRange] at hx
      rw [← hx.2]
      obtain ⟨y, hy⟩ := hx.1
      rw [← hy.2]
      exact hy.1 v hv
      {
        have h : Set.Nonempty (Set.range (e S)) := by
          use 1
          use 1
          rfl
        contrapose h
        push_neg at h ⊢
        obtain h' := hW'.2
        simp [h] at h'
        rw [← h']
      }
    }
    {
      push_neg
      apply Set.Finite.subset (Set.Finite.union hW.1.2 hW'.1.2)
      intros v hv
      contrapose hv
      rw [Set.nmem_setOf_iff]
      push_neg
      simp at hv
      push_neg at hv
      simp [hv]
    }
    {
      rw [Set.pi_inter_distrib]
      rw [Set.preimage_inter]
      have h' : (Subtype.val : finiteSAdeleRing R K S → ProdAdicCompletions R K) = Subtype.val ∘ (e S) := by
        funext x v
        rfl
      rw [h']
      rw [Set.preimage_comp]
      rw [Set.preimage_comp]
      rw [← Set.preimage_inter]
      rw [hW.2]
      rw [hW'.2]
      exact Set.preimage_inter_range
    }
  }
  {
    intro hU
    use (e S '' U)
    rw [FiniteAdeleRing.generatingSet]
    refine' ⟨_, Set.preimage_image_eq _ (embeddingInjective R K S)⟩
    {
      simp at hU ⊢
      obtain ⟨V, hV⟩ := hU
      use V
      refine' ⟨⟨hV.1.1, hV.1.2.2⟩, _⟩
      {
        have h' : (Subtype.val : finiteSAdeleRing R K S → ProdAdicCompletions R K) = Subtype.val ∘ (e S) := by
          funext x v
          rfl
        obtain hV' := hV.2
        rw [h'] at hV'
        rw [Set.preimage_comp] at hV'
        rw [← hV']
        rw [Set.image_preimage_eq_of_subset]
        rw [embeddingRange]
        intro x hx
        rw [Set.mem_preimage] at hx
        rw [Set.mem_pi] at hx
        intro v hv
        exact hV.1.2.1 v hv (hx v (Set.mem_univ v))
      }
    }
  }

theorem subtype_val_embedding : (Subtype.val : finiteSAdeleRing R K S → ProdAdicCompletions R K) = Subtype.val ∘ e S := by
  funext x
  rfl

theorem subtype_val_range_eq_pi
  : Set.range (Subtype.val : finiteSAdeleRing R K S → ProdAdicCompletions R K)
  = Set.pi Set.univ (λ v => ite (v ∈ S) Set.univ (v.adicCompletionIntegers K)) := by
  simp
  ext x
  rw [Set.mem_pi]
  refine' ⟨_, _⟩
  {
    intro hx v _
    by_cases hv : v ∈ S
    {
      simp [hv]
    }
    {
      simp [hv]
      exact hx v hv
    }
  }
  {
    intro hx v hv
    specialize hx v (Set.mem_univ v)
    simp [hv] at hx
    exact hx
  }

theorem generatingSet_eq : generatingSet R K S =
  Set.preimage (Subtype.val) '' (Set.pi Set.univ '' (
    setOf (
      λ V =>
        (∀ v, IsOpen (V v)) ∧
        (∀ v, v ∉ S → V v ⊆ v.adicCompletionIntegers K) ∧
        (∀ᶠ v in Filter.cofinite, V v = v.adicCompletionIntegers K)
    )
  ))
  := Set.ext (mem_generatingSet_iff R K S)

theorem generatingSet_eq' : generatingSet R K S =
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

    --set W := (λ (v : HeightOneSpectrum R) => ite (v ∈ I.toSet) (V v) Set.univ)
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
            --exact λ h => by rw [← h]
          }
          {
            simp [hv', hv'', hv''']
            --simp at hv''
            --simp [hv'']
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
            --simp [hv'']
          }
        }
      }
      {
        by_cases hv'' : v ∈ I
        {
          by_cases hv''' : v ∈ S
          {
            simp [hv', hv'', hv''']
            --exact λ h => by rw [← h]
          }
          {
            simp [hv', hv'', hv''']
            --simp at hv''
            --simp [hv'']
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
def SProdAdicCompletionIntegers_generatingSet : Set (Set (SProdAdicCompletionIntegers R K S))
  := Set.image (finiteSAdeleEquiv R K S).toFun '' (generatingSet R K S)

def W₁ : Set (Set ((v : S) → v.val.adicCompletion K)) := Set.image (Prod.fst) '' (SProdAdicCompletionIntegers_generatingSet R K S)

def W₂ : Set (Set ((v : {v // v ∉ S}) → v.val.adicCompletionIntegers K)) := Set.image (Prod.snd) '' (SProdAdicCompletionIntegers_generatingSet R K S)
-- TODO : change this to use prod_generateFrom_generateFrom_eq instead (i.e., instead of IsOpen s, use s ∈ G, where G generates Pi.topologicalSpace)
def T := setOf (
    λ g =>
      ∃ (s : Set ((w : S) → w.val.adicCompletion K)) (t : Set ((w : {v // v ∉ S}) → w.val.adicCompletionIntegers K)),
      IsOpen s ∧ IsOpen t ∧ g = s ×ˢ t
  )

theorem equivPiSubtypeProd_image_pi  {α : Type u_1}  (p : α → Prop) (β : α → Type u_2) (t : (i : α) → Set (β i)) (U : Set ((i : α) → β i)) (hU : U = Set.pi Set.univ t)
  : Equiv.piEquivPiSubtypeProd p β '' U = (Prod.fst '' (Equiv.piEquivPiSubtypeProd p β '' U)) ×ˢ (Prod.snd '' (Equiv.piEquivPiSubtypeProd p β '' U)) := by
  simp
  rw [hU]
  apply subset_antisymm
  {
     exact λ _ hx => Set.mem_prod.2 ⟨Set.mem_image_of_mem _ hx, Set.mem_image_of_mem _ hx⟩
  }
  {
    rw [Set.prod_subset_iff]
    intro x hx y hy
    simp at hx hy ⊢
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    use (λ i => ite (p i) (x' i) (y' i))
    rw [← hx'.2, ← hy'.2]
    refine' ⟨_, ⟨by {funext v; simp [v.property]}, by {funext v; simp [v.property]}⟩⟩
    {
      intro i
      by_cases h : p i
      {
        simp [h]
        exact hx'.1 i
      }
      {
        simp [h]
        exact hy'.1 i
      }
    }
  }

theorem equivPiSubtypeProd_symm_image_pi {α : Type u_1}  (p : α → Prop) (β : α → Type u_2) (s : (i : {x // p x}) → Set (β i)) (t : (i : {x // ¬p x}) → Set (β i)) (U : Set ((i : α) → β i))
  (h : (Equiv.piEquivPiSubtypeProd p β).symm '' (Set.pi Set.univ s ×ˢ Set.pi Set.univ t) = U)
  : ∃ r, U = Set.pi Set.univ r := by
  use λ i => dite (p i) (λ h => s ⟨i, h⟩) (λ h => t ⟨i, h⟩)
  rw [← h]
  unfold Equiv.piEquivPiSubtypeProd
  simp
  apply subset_antisymm
  {
    intro x hx
    rw [Set.mem_pi]
    obtain ⟨x', hx', hxx'⟩ := hx
    intro i _
    rw [← hxx']
    rw [Set.mem_prod] at hx'
    rw [Set.mem_pi, Set.mem_pi] at hx'
    by_cases hi : p i
    {
      simp [hi]
      exact hx'.1 ⟨i, hi⟩ (Set.mem_univ i)
    }
    {
      simp [hi]
      exact hx'.2 ⟨i, hi⟩ (Set.mem_univ _)
    }
  }
  {
    intro x hx
    rw [Set.mem_pi] at hx
    rw [Set.mem_image]
    use (λ v => x v.val, λ v => x v.val)
    simp
    refine' ⟨_, _⟩
    {
      intro i hi
      specialize hx i
      simp [hi] at hx
      exact hx
    }
    {
      intro i hi
      specialize hx i
      simp [hi] at hx
      exact hx
    }
  }

theorem h'' : ∀ x : finiteSAdeleRing R K S, Equiv.piEquivPiSubtypeProd (λ v => v ∈ S) (λ v => v.adicCompletion K) x.val = (Coe.coe : R_hat_S → K_hat_S) (finiteSAdeleEquiv R K S x) := by
  intro x
  unfold finiteSAdeleEquiv
  rfl

-- TODO : can we use this result to simplify the proof of the equivalence?
theorem h''' : Equiv.piEquivPiSubtypeProd (λ v => v ∈ S) (λ v => v.adicCompletion K) ∘ Subtype.val = (Coe.coe : R_hat_S → K_hat_S) ∘ (finiteSAdeleEquiv R K S) := funext (h'' R K S)
def p_R_1 := @Prod.fst ((v : S) → v.val.adicCompletion K) ((v : {v // v ∉ S}) → v.val.adicCompletionIntegers K)
def p_R_2 := @Prod.snd ((v : S) → v.val.adicCompletion K) ((v : {v // v ∉ S}) → v.val.adicCompletionIntegers K)
def p_K_1 := @Prod.fst ((v : S) → v.val.adicCompletion K) ((v : {v // v ∉ S}) → v.val.adicCompletion K)
def p_K_2 := @Prod.snd ((v : S) → v.val.adicCompletion K) ((v : {v // v ∉ S}) → v.val.adicCompletion K)

theorem t₁ : p_K_1 R K S ∘ (Coe.coe : R_hat_S → K_hat_S) = p_R_1 R K S := by
  funext x
  rfl

theorem t₂ : p_K_2 R K S ∘ (Coe.coe : R_hat_S → K_hat_S) = λ y : R_hat_S => (λ v : {v // v ∉ S} => (y.2 v : v.val.adicCompletion K)) := by
  funext x
  rfl

theorem t₃ : ∀ x y, (Coe.coe : R_hat_S → K_hat_S) (x, y) = (x, (λ v : {v // v ∉ S} => (y v : v.val.adicCompletion K))) := by
  intro x y
  rfl

-- TODO: can we abstract this?
theorem h'''' (U : Set R_hat_S)
  : (Coe.coe : R_hat_S → K_hat_S) '' ((p_R_1 R K S '' U) ×ˢ (p_R_2 R K S '' U))
  = (p_K_1 R K S '' ((Coe.coe : R_hat_S → K_hat_S) '' U)) ×ˢ (p_K_2 R K S '' ((Coe.coe : R_hat_S → K_hat_S) '' U)) := by
  ext x
  refine' ⟨_, _⟩
  {
    intro hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← hyx]
    have h : ((Coe.coe : R_hat_S → K_hat_S) y).1 = y.1 := rfl
    have h' : ((Coe.coe : R_hat_S → K_hat_S) y).2 = (λ (v : {v // v ∉ S}) => (y.2 v : v.val.adicCompletion K)) := rfl
    rw [Set.mem_prod] at hy ⊢
    rw [h]
    refine' ⟨_, _⟩
    {
      convert hy.1
      rw [← Set.image_comp]
      rfl
    }
    {
      rw [h']
      rw [← Set.image_comp]
      rw [t₂ R K S]
      simp
      obtain ⟨y', hy', hyy'⟩ := hy.2
      use y', hy'
      rw [← hyy']
      rfl
    }
  }
  {
    intro hx

    rw [← Set.image_comp, ← Set.image_comp, t₁, t₂] at hx
    simp
    rw [Set.mem_prod] at hx
    obtain ⟨x', hx', hxx'⟩ := hx.1
    obtain ⟨y', hy', hyy'⟩ := hx.2
    use (x'.1, y'.2)
    simp [t₃, hxx', hyy']
    have h : x'.1 = x.1 := by {rw [← hxx']; rfl}
    rw [h]
    simp
    rw [Set.mem_prod]
    apply And.intro
    {
      rw [Set.mem_image]
      use x'
    }
    {
      rw [Set.mem_image]
      use y', hy'
      rfl
    }
  }

theorem finiteSAdeleEquiv_image_pi {t : (v : HeightOneSpectrum R) → Set (v.adicCompletion K)} (U : Set (finiteSAdeleRing R K S)) (hU : Subtype.val '' U = (Set.pi Set.univ t))
  : (finiteSAdeleEquiv R K S) '' U = (p_R_1 R K S '' ((finiteSAdeleEquiv R K S) '' U)) ×ˢ (p_R_2 R K S '' ((finiteSAdeleEquiv R K S) '' U)) := by
  rw [← Set.image_eq_image (SProdAdicCompletions.coe_injective R K S)]
  rw [← Set.image_comp]
  rw [← h''']
  rw [Set.image_comp]
  have h' := equivPiSubtypeProd_image_pi (λ v => v ∈ S) (λ v => v.adicCompletion K) t (Subtype.val '' U) hU
  convert h'
  rw [h'''']
  nth_rewrite 2 [← Set.image_comp]
  nth_rewrite 3 [← Set.image_comp]
  rw [← h''']
  nth_rewrite 4 [← Set.image_comp]
  nth_rewrite 5 [← Set.image_comp]
  rfl

theorem SProdAdicCompletionsIntegers_generateFrom_mem_univ :
  Set.univ ∈ SProdAdicCompletionIntegers_generatingSet R K S := by
  rw [SProdAdicCompletionIntegers_generatingSet]
  use Set.univ, set_univ_mem_generatingSet R K S
  simp

theorem generatingSet_equiv_image_fst_sUnion
  : ⋃₀ W₁ R K S = Set.univ := by
  rw [Set.sUnion_eq_univ_iff]
  intro x
  use Set.univ
  refine' ⟨_, Set.mem_univ x⟩
  rw [W₁]
  simp
  use Set.univ, SProdAdicCompletionsIntegers_generateFrom_mem_univ R K S
  simp

theorem generatingSet_equiv_image_snd_sUnion
  : ⋃₀ W₂ R K S = Set.univ := by
  rw [Set.sUnion_eq_univ_iff]
  intro x
  use Set.univ
  refine' ⟨_, Set.mem_univ x⟩
  rw [W₂]
  simp
  use Set.univ, SProdAdicCompletionsIntegers_generateFrom_mem_univ R K S
  simp

theorem generateFrom_congr {α : Type u} (g g' : Set (Set α)) (h : g = g') :
  TopologicalSpace.generateFrom g = TopologicalSpace.generateFrom g' := by rw [h]

theorem generatingSet_image_embedding (U : Set (finiteSAdeleRing R K S)) (hU : U ∈ (generatingSet R K S))
  : e S '' U ∈ FiniteAdeleRing.generatingSet R K := by
  rw [generatingSet] at hU
  obtain ⟨V, hV⟩ := hU
  rw [← hV.2]
  rw [Set.image_preimage_eq_inter_range]
  rw [Set.inter_comm]
  exact mem_finiteAdeleRingGeneratingSet_range_inter R K S V hV.1

-- TOP level
-- Πᵥ Kᵥ is homeomorphic to Πₛ Kᵥ × Π Kᵥ
theorem h₀ : ProdAdicCompletions R K ≃ₜ SProdAdicCompletions R K S := Homeomorph.piEquivPiSubtypeProd _ _


-- BOTTOM-RIGHT: Π Kᵥ × Π Kᵥ subtype that is essentially Π Kᵥ × Πᵥ Oᵥ
def SProdAdicCompletionIntegers' := {x : SProdAdicCompletions R K S // ∀ v : {v // v ∉ S}, x.2 v ∈ v.val.adicCompletionIntegers K}
-- give it the subtype topology
instance : TopologicalSpace (SProdAdicCompletionIntegers' R K S) := instTopologicalSpaceSubtype

-- BOTTOM-LEFT : finite S-adeles, are given the subspace topology of the finite Adeles
-- we show that this is the _same_ as giving it the subspace topology of Πᵥ Kᵥ (most of this is already above, see generatingSet_eq)
instance h₁ : topologicalSpace R K S = instTopologicalSpaceSubtype := by
  rw [generateFrom]
  rw [instTopologicalSpaceSubtype]
  rw [instTopologicalSpaceProdAdicCompletions]
  rw [pi_eq_generateFrom]
  rw [induced_generateFrom_eq]
  apply generateFrom_congr
  rw [generatingSet_eq']

theorem homeomorph : finiteSAdeleRing R K S ≃ₜ SProdAdicCompletionIntegers' R K S := by
  rw [h₁]
  apply Homeomorph.subtype (h₀ R K S)
  intro x
  unfold h₀
  refine' ⟨_, _⟩
  {
    intro hx v
    exact hx v.val v.property
  }
  {
    intro h v hv
    exact h ⟨v, hv⟩
  }

theorem t' : ∀ x : SProdAdicCompletionIntegers' R K S, (∀ v : {v // v ∉ S}, x.val.2 v ∈ v.val.adicCompletionIntegers K) := by exact λ x => x.2
theorem t : ∀ x : SProdAdicCompletionIntegers R K S, (∀ v : {v // v ∉ S}, (x.2 v).val ∈ v.val.adicCompletionIntegers K) := by
  intro x v
  simp

def g : SProdAdicCompletionIntegers' R K S → (v : {v // v ∉ S}) → v.val.adicCompletionIntegers K := λ x v => ⟨x.val.2 v, x.property v⟩
theorem h₄ : SProdAdicCompletionIntegers' R K S ≃ SProdAdicCompletionIntegers R K S where
  toFun := λ x => (x.val.1 , g R K S x)
  invFun := λ x => ⟨x, t R K S x⟩
  left_inv := by
    rintro ⟨x, hx⟩
    rfl
  right_inv := by
    rintro ⟨x, hx⟩
    rfl

theorem h₃ : SProdAdicCompletionIntegers' R K S ≃ₜ SProdAdicCompletionIntegers R K S where
  toEquiv := h₄ R K S
  continuous_toFun := by
    unfold h₄
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
    unfold h₄
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

end FiniteSAdeleRing

end DedekindDomain
