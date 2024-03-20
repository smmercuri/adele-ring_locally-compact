import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteAdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.InfiniteAdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.AdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.Uniformizers
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.ResidueField
import AdeleRingLocallyCompact.Topology.Homeomorph

open DedekindDomain IsDedekindDomain

open scoped Classical

namespace LocallyCompact

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K] [NumberField K] [Algebra R K]
  [IsFractionRing R K] (S : Finset (HeightOneSpectrum R)) (v : HeightOneSpectrum R)
  (B : (n : ℕ) → Basis (Fin n) ℚ (Fin n → ℚ)) (C : (n : ℕ) → Basis (Fin n) ℝ (Fin n → ℝ))

local notation "e" => FiniteSAdeleRing.embedding R K

theorem isClosed_adicCompletionIntegers : IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  rw [isClosed_iff_nhds]
  intro x hx
  contrapose hx
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hx
  push_neg at hx ⊢
  use {y | Valued.v y = Valued.v x}, (Valued.loc_const (ne_zero_of_lt hx))
  rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_iff]
  intro y ⟨hy, hy'⟩
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hy'
  rw [← hy] at hx
  rw [Set.mem_empty_iff_false]
  exact (not_lt_of_le hy') hx

def openBall (γ : (WithZero (Multiplicative ℤ))ˣ) : Set (v.adicCompletion K) := setOf (λ y => Valued.v y < γ)

theorem isOpen_openBall (γ : (WithZero (Multiplicative ℤ))ˣ) : IsOpen (openBall R K v γ) := by
  rw [isOpen_iff_mem_nhds]
  intros x hx
  rw [openBall, Set.mem_setOf_eq] at hx
  rw [Valued.mem_nhds, openBall]
  use γ
  intros y hy
  rw [← sub_add_cancel y x]
  rw [Set.mem_setOf_eq] at hy
  exact lt_of_le_of_lt (Valued.v.map_add (y - x) x) (max_lt hy hx)

theorem isClosed_openBall (γ : (WithZero (Multiplicative ℤ))ˣ) : IsClosed (openBall R K v γ) := by
  rw [isClosed_iff_nhds]
  intro x hx
  contrapose hx
  rw [openBall, Set.mem_setOf_eq] at hx
  push_neg at hx ⊢
  have h : Valued.v x ≠ 0 := by
    contrapose hx
    push_neg at hx
    rw [hx]
    simp
  use {y | Valued.v y = Valued.v x}, (Valued.loc_const h)
  rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_iff]
  intro y ⟨hy, hy'⟩
  rw [openBall, Set.mem_setOf_eq] at hy'
  rw [← hy] at hx
  rw [Set.mem_empty_iff_false]
  exact (not_le_of_lt hy') hx

theorem openBall_of_le_one_subset_adicCompletionIntegers (γ : (WithZero (Multiplicative ℤ))ˣ) (hγ : γ ≤ 1) :
  openBall R K v γ ⊆ v.adicCompletionIntegers K := by
  intro x hx
  rw [openBall, Set.mem_setOf_eq] at hx
  exact le_of_lt (lt_of_lt_of_le hx hγ)

/-
theorem adicValuation_eq_one_iff (x : v.adicCompletionIntegers K) :
  IsUnit x ↔ Valued.v (x : v.adicCompletion K) = 1 := by
  refine' ⟨_, _⟩
  {
    intro hx

    have h := Valuation.mem_unitGroup_iff (v.adicCompletion K) (Valued.v)
    obtain ⟨y, hy⟩ := hx
    obtain ⟨z, _, _, _⟩ := y
    have hz : IsUnit z.val := sorry
    obtain ⟨w, hw⟩ := hz
    specialize h w

    sorry
    /-
    rw [← h]
    --have h' : x ∈ (v.adicCompletion K)ˣ
    rw [← @Valuation.mem_unitGroup_iff _ (Valued.v) _]
    rw [ValuationSubring.valuation_eq_one_iff] at hx
    rw [← hx]
    -/
  }
  {
    sorry
  }
-/





theorem adicValuation_lt_one_of_maximalIdeal (x : v.adicCompletionIntegers K) :
  x ∈ adicCompletionIntegers.maximalIdeal R K v → Valued.v (x : v.adicCompletion K) < 1 := by
  intro hx
  rw [adicCompletionIntegers.maximalIdeal] at hx
  rw [LocalRing.mem_maximalIdeal] at hx
  rw [mem_nonunits_iff] at hx
  contrapose hx
  push_neg at hx ⊢
  apply adicValuationIntegers_isUnit_of_one R K v
  exact (le_antisymm x.property hx)

-- TODO : can give an easier proof of this now with Maria's work above, max ideal is generated by π
theorem adicValuation_le_of_maximalIdeal (x : v.adicCompletionIntegers K) :
  x ∈ adicCompletionIntegers.maximalIdeal R K v → Valued.v (x : v.adicCompletion K) ≤ Multiplicative.ofAdd (-1 : ℤ) := by
  intro hx
  have h := adicValuation_lt_one_of_maximalIdeal R K v x hx
  rw [← WithZero.coe_one] at h
  rw [← ofAdd_zero] at h
  have h' : ∀ x, x < Multiplicative.ofAdd (0 : ℤ) → x ≤ Multiplicative.ofAdd (-1 : ℤ) := by
    intro x hx

    rw [← Multiplicative.toAdd_le]
    rw [← Multiplicative.toAdd_lt] at hx

    simp_rw [toAdd_ofAdd] at hx ⊢
    have h'' : (-1 : ℤ) = Order.pred (0 : ℤ) := by rfl
    rw [h'']
    apply Order.le_pred_of_lt
    exact hx
  by_cases hx : Valued.v (x : v.adicCompletion K) ≠ 0
  {
    rw [← WithZero.coe_unzero hx] at h ⊢
    rw [WithZero.coe_lt_coe] at h
    rw [WithZero.coe_le_coe]
    exact h' _ h
  }
  {
    simp at hx
    rw [hx]
    simp
  }
/-
theorem Ideal.pow_carrier {R : Type u} [CommSemiring R] {I : Ideal R}  {a : R} {n : ℕ} :
  (I^n).carrier = (I.carrier) ^ n := rfl

theorem Ideal.mem_pow {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R] [LocalRing R] {I : Ideal R}  {a : R} {n : ℕ} (hI : Submodule.IsPrincipal I):
  a ∈ I^n ↔ ∃ (f : Fin n → I),
    List.prod (List.ofFn fun (i : Fin n) => ↑(f i)) = a := by
    --rw [Submodule.pow_eq_span_pow_set]
   -- simp
    --rw [Ideal.mem_span]
    have h := maximalIdeal_isPrincipal_of_isDedekindDomain R
    obtain ⟨π, hπ⟩ := hI
    rw [hπ]
    simp
    rw [Ideal.span_singleton_pow]
-/
/-
theorem MonoidWithZeroHom.map_list_prod {α : Type u_6}  {β : Type u_7}  [MulZeroOneClass α] [MulZeroOneClass β]
  (f : α →*₀ β) (l : List α) :
  f (List.prod l) = List.prod (List.map f l) := sorry
-/
/-
theorem map_adicValuation_list_maximalIdeal {n : ℕ} (f : Fin n → (adicCompletionIntegers.maximalIdeal R K v)) :
  List.prod (List.map (⇑Valued.v) (List.ofFn ((Subtype.val : v.adicCompletionIntegers K → v.adicCompletion K) ∘ fun i => ↑(f i)))) ≤ Multiplicative.ofAdd (-1 : ℤ)^n := by
  set l := (List.map (⇑Valued.v) (List.ofFn ((Subtype.val : v.adicCompletionIntegers K → v.adicCompletion K) ∘ fun i => ↑(f i))))
  have h : n = l.length := by
    rw [← List.length_ofFn f]
    rw [List.length_map]
    simp

  rw [h]
  apply List.prod_le_pow_card
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨a, ha, hax⟩ := hx
  rw [← hax]
  rw [List.mem_ofFn] at ha
  rw [Set.mem_range] at ha
  obtain ⟨b, hb⟩ := ha
  rw [← hb]
  apply adicValuation_le_of_maximalIdeal R K v _
  simp

-/
theorem adicValuation_le_pow_of_maximalIdeal (x : v.adicCompletionIntegers K) (n : ℕ) :
  x ∈ (adicCompletionIntegers.maximalIdeal R K v)^n → Valued.v (x : v.adicCompletion K) ≤ Multiplicative.ofAdd (-n : ℤ) := by
  by_cases hn : n = 0
  {
    simp [hn]
    exact x.property
  }
  intro hx
  obtain ⟨π, hπ⟩ := adicCompletionIntegers_exists_uniformizer R K v
  -- TODO :refactor this
  have hπ_ne_zero : π ≠ 0 := by
    contrapose hπ
    push_neg at hπ
    rw [hπ]
    simp
  rw [isUniformizer_is_generator R K v hπ] at hx
  rw [Ideal.span_singleton_pow] at hx
  rw [Ideal.mem_span_singleton] at hx
  obtain ⟨y, hxy⟩ := hx
  rw [hxy]
  rw [Subring.coe_mul, Valued.v.map_mul, Subring.coe_pow, Valued.v.map_pow]
  have h : Valued.v (π : v.adicCompletion K) ^ n * Valued.v (y : v.adicCompletion K) ≤ Valued.v (π : v.adicCompletion K) ^ n * 1 := by
    rw [mul_le_mul_left₀]
    exact y.property
    simp
    intro h'
    exfalso
    exact hπ_ne_zero h'

  apply le_trans h
  rw [mul_one]
  rw [hπ]
  rw [← WithZero.coe_pow]
  rw [WithZero.coe_le_coe]
  simp
  rw [← one_mul (n : ℤ), Int.ofAdd_mul]
  simp


local notation "μ_v" => @WithZero.unitsWithZeroEquiv (Multiplicative ℤ)

theorem isTotallyBounded_adicCompletionIntegers : TotallyBounded (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  rw [Filter.HasBasis.totallyBounded_iff (Valued.hasBasis_uniformity _ _)]
  intro γ
  simp
  obtain ⟨π, hπ⟩ := adicCompletionIntegers_exists_uniformizer R K v
  by_cases hγ : (γ : WithZero (Multiplicative ℤ)) > 1
  {
    use {0}
    simp
    intro x hx
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hx
    rw [Set.mem_setOf_eq]
    exact lt_of_le_of_lt hx hγ
  }
  by_cases hγ' : γ = 1
  {
    /-
    Idea here is that the residue field of a Dedekind Domain is finite. We may need to do quite a bit of work here. What's needed:
      -- (v.adicCompletionIntegers K).localRing.residueField exists, it is not a set. How do we get a set out of it?
        -- we are going to need to work with powers of the max ideal later anyway, so instead maybe work with own versions using the uniformizer
          (v.adicCompletionIntegers K).localRing / (Ideal.span ({(⟨π, hπ⟩ : v.adicCompletionIntegers K)})
        -- this is still a ring, so show how to express finiteness of it, does it have a carrier?
      -- Then we need to show that this is isomorphic to R / P, which I think has been shown to be finite in Lean (see Ideal.Norm)

    -/
    --obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    --have hπ' : Valued.v (π : v.adicCompletion K) ≤ 1 := by
    --  rw [← Valued.extension_extends]

    set M := (v.adicCompletionIntegers K).localRing.maximalIdeal
    set S := (v.adicCompletionIntegers K) ⧸ M
    set quotientMap : v.adicCompletionIntegers K → S := Submodule.Quotient.mk

    have h := residueRing_order_fintype R K v 1 hπ
    rw [pow_one] at h

    set T := Quotient.out' '' (h.elems.toSet)
    use T, (Set.Finite.image Subtype.val (Set.Finite.image Quotient.out' (Finset.finite_toSet h.elems)))
    intro x hx
    rw [Set.mem_iUnion]
    set y := (Quotient.out' (quotientMap ⟨x, hx⟩))
    use y
    rw [Set.mem_iUnion]

    have h' : Subtype.val (Quotient.out' (quotientMap ⟨x, hx⟩)) ∈ Subtype.val '' T := by
      rw [Set.mem_image]
      use y
      refine' ⟨_, rfl⟩
      apply Set.mem_image_of_mem
      simp
      apply h.complete

    use h'
    rw [Set.mem_setOf_eq]
    have h'' : y - ⟨x, hx⟩ ∈ M := by
      rw [← Submodule.Quotient.eq]
      rw [← Submodule.Quotient.mk''_eq_mk]
      rw [Quotient.out_eq']

    rw [hγ']
    have h''' := adicValuation_lt_one_of_maximalIdeal R K v (y - ⟨x, hx⟩) h''
    exact h'''
  }
  {
    --have h : (γ : WithZero (Multiplicative ℤ)) ≠ 0 := Units.ne_zero γ
    --set n := Multiplicative.toAdd γ.val
    --have ho : Option.isSome γ.val = true := sorry
    have ho' : ∃ μ : Multiplicative ℤ, γ.val = (μ : WithZero (Multiplicative ℤ)) := by
      use μ_v γ
      unfold WithZero.unitsWithZeroEquiv
      simp

    obtain ⟨μ, hμ⟩ := ho'
    --set n := Option.get! μ
    --have h : ∃ (n : ℕ), -(n : ℤ) = Option.some (γ.1) := sorry
    --obtain ⟨a, b⟩ := γ
    set M := (v.adicCompletionIntegers K).localRing.maximalIdeal^((-Multiplicative.toAdd μ + 1).toNat)

    set S := (v.adicCompletionIntegers K) ⧸ M
    set quotientMap : v.adicCompletionIntegers K → S := Submodule.Quotient.mk

    have h : Fintype S := residueRing_order_fintype R K v (-Multiplicative.toAdd μ + 1).toNat hπ

    set T := Quotient.out' '' (h.elems.toSet)
    use T, (Set.Finite.image Subtype.val (Set.Finite.image Quotient.out' (Finset.finite_toSet h.elems)))
    intro x hx
    rw [Set.mem_iUnion]
    set y := (Quotient.out' (quotientMap ⟨x, hx⟩))
    use y
    rw [Set.mem_iUnion]

    have h' : Subtype.val (Quotient.out' (quotientMap ⟨x, hx⟩)) ∈ Subtype.val '' T := by
      rw [Set.mem_image]
      use y
      refine' ⟨_, rfl⟩
      apply Set.mem_image_of_mem
      simp
      apply h.complete

    use h'
    rw [Set.mem_setOf_eq]
    have h'' : y - ⟨x, hx⟩ ∈ M := by
      rw [← Submodule.Quotient.eq]
      rw [← Submodule.Quotient.mk''_eq_mk]
      rw [Quotient.out_eq']

    --have h''' : ∀ z, z ∈ M → Valued.v (z : v.adicCompletion K) < γ := sorry
    have h'''' := adicValuation_le_pow_of_maximalIdeal R K v (y - ⟨x, hx⟩) ((-Multiplicative.toAdd μ + 1).toNat) h''
    apply lt_of_le_of_lt h''''
    rw [hμ]
    rw [← ofAdd_toAdd μ]
    rw [WithZero.coe_lt_coe]
    rw [Multiplicative.ofAdd_lt]
    simp
    have h_nonneg : 0 ≤ - (Multiplicative.toAdd μ) + 1 := by
      simp
      rw [← Multiplicative.ofAdd_le]
      rw [ofAdd_toAdd]
      rw [← WithZero.coe_le_coe]
      rw [← hμ]
      simp at hγ
      apply le_trans hγ
      rw [← WithZero.coe_one]
      rw [WithZero.coe_le_coe]
      rw [← ofAdd_zero]
      rw [Multiplicative.ofAdd_le]
      exact zero_le_one

    rw [Int.toNat_of_nonneg h_nonneg]
    rw [neg_add]
    rw [neg_neg]
    linarith
  }

instance piReal_locallyCompact : LocallyCompactSpace (Fin n → ℝ) := Pi.locallyCompactSpace_of_finite

instance : CompleteSpace (v.adicCompletionIntegers K) := IsClosed.completeSpace_coe (isClosed_adicCompletionIntegers R K v)
theorem isCompact_adicCompletionIntegers : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  exact ⟨isTotallyBounded_adicCompletionIntegers R K v, IsClosed.isComplete (isClosed_adicCompletionIntegers R K v)⟩

instance instCompactSpace_adicCompletionIntegers :  CompactSpace (v.adicCompletionIntegers K) := by
  apply CompactSpace.mk
  convert isCompact_adicCompletionIntegers R K v
  rw [← isCompact_iff_isCompact_univ]



theorem mem_openBall_mul_uniformizer_pow (x π : v.adicCompletion K) (hx : x ∈ openBall R K v γ) (hπ : IsUniformizer R K v π)
  : Valued.v (π^(Multiplicative.toAdd (μ_v γ)) * x) < 1 := by
  rw [Valued.v.map_mul]
  simp_all only [map_zpow₀]
  rw [openBall, Set.mem_setOf_eq] at hx
  rw [hπ]
  have h₀ : γ.val⁻¹ ≠ 0 := by
    simp_all only [ne_eq, inv_eq_zero, Units.ne_zero, not_false_eq_true]
  rw [(Units.inv_mul' γ).symm]
  apply mul_lt_mul_of_lt_of_le₀ _ h₀ hx
  simp

  have h₁ : γ.val = (μ_v γ : WithZero (Multiplicative ℤ)) := by
    unfold WithZero.unitsWithZeroEquiv
    simp
  rw [h₁]
  rw [← WithZero.coe_inv]
  rw [← WithZero.coe_zpow]
  rw [← WithZero.coe_inv]
  rw [WithZero.coe_le_coe]
  rw [← ofAdd_zsmul]
  simp



/--/
theorem mem_openBall_eq_uniformizer_pow (γ : (WithZero (Multiplicative ℤ))ˣ) (x : v.adicCompletion K) (hx : x ∈ openBall R K v γ) :
  ∃ (μ : Multiplicative ℤ) (π : v.adicCompletion K),
    γ.val = (μ : WithZero (Multiplicative ℤ)) ∧
    Valued.v π = Multiplicative.ofAdd ((-1 : ℤ)) ∧
    x = π^(Multiplicative.toAdd μ) * x := sorry
    -/

theorem isCompact_openBall (γ : (WithZero (Multiplicative ℤ))ˣ) : IsCompact (openBall R K v γ) := by
  by_cases hγ : γ ≤ 1
  {
    apply IsCompact.of_isClosed_subset (isCompact_adicCompletionIntegers R K v) (isClosed_openBall R K v γ)
    exact openBall_of_le_one_subset_adicCompletionIntegers R K v γ hγ
  }
  {
    simp at hγ
    obtain ⟨π, hπ⟩ := adicCompletion_exists_uniformizer R K v

    set f := λ x => π^(-Multiplicative.toAdd (μ_v γ)) * x with f_def
    have hπ_ne_zero : π ≠ 0 := by
      contrapose hπ
      push_neg at hπ
      rw [hπ]
      simp

    have h_range : openBall R K v γ ⊆ Set.range f := by
      intro x hx
      rw [openBall] at hx
      rw [Set.mem_range]
      use π ^ (Multiplicative.toAdd (μ_v γ)) * x
      rw [f_def]
      dsimp
      rw [← mul_assoc]
      rw [← zpow_add₀ hπ_ne_zero]
      simp

    have h : f⁻¹' (openBall R K v γ) ⊆ (v.adicCompletionIntegers K) := by
      intro x hx
      rw [Set.mem_preimage] at hx
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
      apply le_of_lt
      have h' := mem_openBall_mul_uniformizer_pow R K v (f x) π hx hπ
      --dsimp at h'
      rw [← mul_assoc, ← zpow_add₀ hπ_ne_zero] at h'
      simp at h'
      simp_all only [ofAdd_neg, WithZero.coe_inv, ne_eq, add_left_neg, zpow_zero, one_mul]

    have h' := continuous_iff_isClosed.1 (continuous_mul_left (π^(-Multiplicative.toAdd (μ_v γ)))) _ (isClosed_openBall R K v γ)
    have h'' : IsCompact (f⁻¹' (openBall R K v γ)) := IsCompact.of_isClosed_subset (isCompact_adicCompletionIntegers R K v) h' h
    have h''' := IsCompact.image h'' (continuous_mul_left (π^(-Multiplicative.toAdd (μ_v γ))))
    rw [Set.image_preimage_eq_of_subset h_range] at h'''
    exact h'''
  }

instance : LocallyCompactSpace (v.adicCompletionIntegers K) := inferInstance
instance : LocallyCompactSpace (v.adicCompletion K) := by
  set Γ₀ := WithZero (Multiplicative ℤ)ˣ
  apply LocallyCompactSpace.mk
  intro x N hN
  rw [Valued.mem_nhds] at hN
  obtain ⟨γ, hN⟩ := hN
  have h : ∃ f, Continuous f ∧ f '' (openBall R K v γ) = setOf (λ y => Valued.v (y - x) < γ) := by
    use (λ y => y + x)
    refine' ⟨(continuous_add_right x) , _⟩
    ext y
    apply Iff.intro
    {
      intro hy
      rw [Set.image] at hy
      obtain ⟨a, ha, hay⟩ := hy
      rw [← hay]
      rw [Set.mem_setOf_eq]
      rw [add_sub_cancel]
      exact ha
    }
    {
      intro hy
      rw [Set.mem_image]
      use (y - x)
      exact ⟨hy, by rw [sub_add_cancel]⟩
    }
  obtain ⟨f, hf, hf'⟩ := h
  have h' : IsCompact (f '' (openBall R K v γ)) := IsCompact.image (isCompact_openBall R K v γ) hf
  use (f '' (openBall R K v γ))
  rw [Valued.mem_nhds]
  refine' ⟨_, _, h'⟩
  {
    use γ; exact subset_of_eq (Eq.symm hf')
  }
  {
    rw [hf']; exact hN
  }

instance : LocallyCompactSpace ((w : S) → w.val.adicCompletion K)
  := Pi.locallyCompactSpace_of_finite
instance : LocallyCompactSpace ((w : {v // v ∉ S}) → w.val.adicCompletionIntegers K)
  := Pi.locallyCompactSpace
instance : LocallyCompactSpace (SProdAdicCompletionIntegers R K S)
  := Prod.locallyCompactSpace
    ((w : S) → w.val.adicCompletion K)
    ((w : {v // v ∉ S}) → w.val.adicCompletionIntegers K)

instance : LocallyCompactSpace (SProdAdicCompletionIntegers' R K S) := Homeomorph.locallyCompactSpace (SProdAdicCompletionIntegers.homeomorph R K S)
/-
theorem RingTopology.preimage_nhds_coinduced [TopologicalSpace α] [Ring α] [Ring β] {π : α → β} {s : Set β} {a : α}
    (hs : s ∈ @nhds β ((RingTopology.coinduced π).toTopologicalSpace) (π a)) : π ⁻¹' s ∈ nhds a := sorry

theorem RingTopology.coinduced_toTopologicalSpace [t : TopologicalSpace α] [Ring α] [Ring β] {π : α → β} :
  (RingTopology.coinduced π).toTopologicalSpace = TopologicalSpace.coinduced π t := by
  unfold RingTopology.coinduced
  sorry
-/
theorem locallyCompact_finiteSAdeleRing (S : Finset (HeightOneSpectrum R)) : LocallyCompactSpace (FiniteSAdeleRing.finiteSAdeleRing R K S) := by
  exact Homeomorph.locallyCompactSpace (FiniteSAdeleRing.homeomorph_piSubtypeProd R K S)

theorem locallyCompact_adeleRing
  : @LocallyCompactSpace (adeleRing R K) (DedekindDomain.AdeleRing.topologicalSpace R K B C) := by
  have locallyCompact_finiteAdeleRing : LocallyCompactSpace (finiteAdeleRing R K) := by
    have local_compact_nhds : ∀ (x : finiteAdeleRing R K), ∀ n ∈ nhds x, ∃ s ∈ nhds x, s ⊆ n ∧ IsCompact s := by
      {
        intros x N hN
        set setS := setOf (λ (v : HeightOneSpectrum R) => x.val v ∉ v.adicCompletionIntegers K)
        have hS : setS.Finite := Filter.eventually_cofinite.1 ((mem_finiteAdeleRing_iff x.val).1 x.property)
        set S := hS.toFinset
        set A_K_S := FiniteSAdeleRing.finiteSAdeleRing R K S

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
        obtain ⟨N', hN', hNU', hNC'⟩ := (locallyCompact_finiteSAdeleRing R K S).local_compact_nhds ⟨x, hx⟩ U_S hU_S
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

  have locallyCompact_infiniteAdeleRing : @LocallyCompactSpace (infiniteAdeleRing K) (InfiniteAdeleRing.topologicalSpace K B C) := by
    have h := (@piReal_locallyCompact (FiniteDimensional.finrank ℚ K)).local_compact_nhds
    apply @LocallyCompactSpace.mk _ (InfiniteAdeleRing.topologicalSpace K B C)
    intro x N hN
    rw [nhds_induced] at hN
    simp at hN
    obtain ⟨M, hM, hMN⟩ := hN
    obtain ⟨T, hT, hTM, hTC⟩ := h ((LinearMap.piReal_to_realTensor_numberField.equiv K B C) x) M hM
    use (LinearMap.piReal_to_realTensor_numberField.equiv K B C) ⁻¹' T
    refine' ⟨_, _, _⟩
    {
      rw [nhds_induced]
      simp
      use T
    }
    {
      apply subset_trans _ hMN
      rw [← LinearEquiv.coe_toEquiv]
      exact (Equiv.preimage_subset (LinearEquiv.toEquiv (LinearMap.piReal_to_realTensor_numberField.equiv K B C)) _ _).2 hTM
    }
    {
      rw [← LinearEquiv.image_symm_eq_preimage (LinearMap.piReal_to_realTensor_numberField.equiv K B C) T]
      apply @IsCompact.image _ _ _ (InfiniteAdeleRing.topologicalSpace K B C) _ _ hTC
      have h' : InfiniteAdeleRing.topologicalSpace K B C = TopologicalSpace.induced (LinearMap.piReal_to_realTensor_numberField.equiv K B C).toEquiv (InfiniteAdeleRing.piReal_topologicalSpace (FiniteDimensional.finrank ℚ K)) := rfl
      rw [← Equiv.coinduced_symm (LinearMap.piReal_to_realTensor_numberField.equiv K B C).toEquiv] at h'
      rw [h']
      exact continuous_coinduced_rng
    }

  exact @Prod.locallyCompactSpace (infiniteAdeleRing K) (finiteAdeleRing R K) (InfiniteAdeleRing.topologicalSpace K B C) _ _ _
end LocallyCompact
