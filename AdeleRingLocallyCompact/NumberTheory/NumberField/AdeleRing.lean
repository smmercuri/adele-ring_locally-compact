/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FinsetAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.InfiniteAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.Completion

open scoped TensorProduct
open scoped Classical

set_option linter.longLine false
/-!
# Adele Ring

We define the adele ring of a number field `K` as the direct product of the infinite adele ring
of `K` and the finite adele ring of `K`. We show that the adele ring of `K` is a
locally compact space.

## Main definitions
 - `NumberField.adeleRing K` is the adele ring of a number field `K`.
 - `NumberField.AdeleRing.globalEmbedding K` is the map sending `x ∈ K` to `(x)ᵥ`.
 - `NumberField.AdeleRing.principalSubgroup K` is the subgroup of principal adeles `(x)ᵥ`.

## Main results
 - `AdeleRing.locallyCompactSpace` : the adele ring of a number field is a locally compact space.

## References
 * [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
 * [M.I. de Frutos-Fernàndez, *Formalizing the Ring of Adèles of a Global Field*][defrutosfernandez2022]

## Tags
adele ring, dedekind domain
-/

noncomputable section

open DedekindDomain

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The adele ring of a number field. -/
def AdeleRing := InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K

namespace AdeleRing

section DerivedInstances

instance : CommRing (AdeleRing K) := Prod.instCommRing

instance : Inhabited (AdeleRing K) := ⟨0⟩

instance : TopologicalSpace (AdeleRing K) :=
  instTopologicalSpaceProd

instance : TopologicalRing (AdeleRing K) :=
  instTopologicalRingProd

instance : Algebra K (AdeleRing K) := Prod.algebra _ _ _

end DerivedInstances

/-- The global embedding sending `x ∈ K` to `(x)ᵥ`. -/
def globalEmbedding : K →+* AdeleRing K := algebraMap K (AdeleRing K)

@[simp]
theorem globalEmbedding_fst_apply (x : K) : (globalEmbedding K x).1 v = x := rfl

@[simp]
theorem globalEmbedding_snd_apply (x : K) : (globalEmbedding K x).2 v = x := rfl

theorem globalEmbedding_injective : Function.Injective (globalEmbedding K) :=
  fun _ _ hxy => (InfiniteAdeleRing.globalEmbedding K).injective (Prod.ext_iff.1 hxy).1

/-- The adele ring of a number field is a locally compact space. -/
theorem locallyCompactSpace : LocallyCompactSpace (AdeleRing K) := by
  haveI := InfiniteAdeleRing.locallyCompactSpace K
  haveI := FiniteAdeleRing.locallyCompactSpace (RingOfIntegers K) K
  exact Prod.locallyCompactSpace _ _

/-- The subgroup of principal adeles `(x)ᵥ` where `x ∈ K`. -/
def principalSubgroup : AddSubgroup (AdeleRing K) := (globalEmbedding K).range.toAddSubgroup

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

--def tensorProduct_equiv_pi : AdeleRing K ⊗[K] L ≃ₗ[K] (Fin (FiniteDimensional.finrank K L) → AdeleRing K) :=
--  LinearEquiv.trans
--    (TensorProduct.congr (LinearEquiv.refl _ _) (FiniteDimensional.finBasis K L).equivFun)
--    (TensorProduct.piScalarRight _ K _ _)

--instance : TopologicalSpace (AdeleRing K ⊗[K] L) :=
--  TopologicalSpace.induced (tensorProduct_equiv_pi K L) inferInstance

variable (G H : Type*) [AddGroup G] [AddGroup H] [TopologicalSpace G] [TopologicalSpace H]
def Homeomorph.quotientCongr (G' : AddSubgroup G) (H' : AddSubgroup H) [G'.Normal] [H'.Normal]
    (e : G ≃ₜ H) (h : e '' G' = H') : G ⧸ G' ≃ₜ H ⧸ H' := sorry

variable {ι : Type*} {G : ι → Type*} [(i : ι) → AddGroup (G i)] [(i : ι) → TopologicalSpace (G i)]
  [Fintype ι] (p : (i : ι) → AddSubgroup (G i))
def Homeomorph.quotientPi : ((i : ι) → G i) ⧸ AddSubgroup.pi Set.univ p ≃ₜ ((i : ι) → G i ⧸ p i) :=
  sorry

def baseChange [NumberField L] :
    (Fin (FiniteDimensional.finrank K L) → AdeleRing K) ≃ₜ AdeleRing L :=
  sorry

def baseChange_quotient [NumberField L] :
    (Fin (FiniteDimensional.finrank K L) → AdeleRing K ⧸ principalSubgroup K) ≃ₜ AdeleRing L ⧸ principalSubgroup L := by
  apply Homeomorph.trans (Homeomorph.quotientPi _).symm
  apply Homeomorph.quotientCongr _ _ _ _ (baseChange K L)
  sorry

open NumberField in
instance (v : InfinitePlace K) : NontriviallyNormedField (v.completion) where
  toNormedField := InfinitePlace.Completion.instNormedFieldCompletion v
  non_trivial := by
    simp only [← dist_zero_right]
    have h := InfinitePlace.Completion.isometry_extensionEmbedding v |>.dist_eq
    use 2
    rw [← h 2 0]
    simp only [map_ofNat, map_zero, dist_zero_right, RCLike.norm_ofNat, Nat.one_lt_ofNat]

instance (v : InfinitePlace K) : ProperSpace (v.completion) :=
  ProperSpace.of_locallyCompactSpace v.completion

open IsDedekindDomain in
theorem FiniteAdeleRing.sub_mem_finiteIntegralAdeles (a : FiniteAdeleRing (𝓞 K) K) :
  ∃ (x : K) (y : FiniteIntegralAdeles (𝓞 K) K),
    a - algebraMap K (FiniteAdeleRing (𝓞 K) K) x = algebraMap _ _ y := sorry

variable {K}
theorem InfinitePlace.card_eq_one_of_finrank_eq_one (h : FiniteDimensional.finrank ℚ K = 1) :
    Fintype.card (NumberField.InfinitePlace K) = 1 := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one h,
    InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one h]

theorem InfinitePlace.isReal_of_nrComplexPlaces_eq_zero (h : InfinitePlace.NrComplexPlaces K = 0)
    (v : InfinitePlace K) : v.IsReal := by
  simp only [Fintype.card_eq_zero_iff, isEmpty_subtype, InfinitePlace.not_isComplex_iff_isReal] at h
  exact h v

theorem InfinitePlace.isComplex_of_nrRealPlaces_eq_zero (h : InfinitePlace.NrRealPlaces K = 0)
    (v : InfinitePlace K) : v.IsComplex := by
  simp only [Fintype.card_eq_zero_iff, isEmpty_subtype, InfinitePlace.not_isReal_iff_isComplex] at h
  exact h v

open Metric NumberField.InfinitePlace in
theorem InfiniteAdeleRing.sub_mem_closedBalls (a : InfiniteAdeleRing ℚ) :
    ∃ (x : 𝓞 ℚ), ∀ v, norm ((a - algebraMap ℚ _ x) v) ≤ 1 := by
  have hr := InfinitePlace.isReal_of_nrComplexPlaces_eq_zero <|
    nrComplexPlaces_eq_zero_of_finrank_eq_one <| FiniteDimensional.finrank_self _
  obtain ⟨inf, h_inf⟩ := Fintype.card_eq_one_iff.1 <|
    InfinitePlace.card_eq_one_of_finrank_eq_one (FiniteDimensional.finrank_self _)
  let f := Completion.extensionEmbedding_of_isReal <| hr inf
  let x := ⌊f (a inf)⌋
  have h := (Completion.isometry_extensionEmbedding_of_isReal <| hr inf).dist_eq
  specialize h (a inf) x
  simp only [map_intCast, MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom] at h
  use x
  intro v
  rw [h_inf v]
  rw [dist_eq_norm] at h
  rw [dist_eq_norm] at h
  simp only [map_intCast]
  have : (a - x) inf = a inf - x := rfl
  rw [this]
  rw [← h]
  simp only [Int.self_sub_floor, Real.norm_eq_abs, ge_iff_le, x]
  rw [Int.abs_fract]
  exact le_of_lt (Int.fract_lt_one _)

variable (K)

open DedekindDomain IsDedekindDomain Metric in
theorem isCompact_quotient_principal :
    IsCompact (Set.univ : Set <| AdeleRing K ⧸ principalSubgroup K) := by
  suffices h : IsCompact (Set.univ : Set <| AdeleRing ℚ ⧸ principalSubgroup ℚ) by
    let n := FiniteDimensional.finrank ℚ K
    haveI : CompactSpace (Fin n → AdeleRing ℚ ⧸ principalSubgroup ℚ) :=
      haveI : CompactSpace (AdeleRing ℚ ⧸ principalSubgroup ℚ) := isCompact_univ_iff.1 h
      Pi.compactSpace
    exact isCompact_univ_iff.2 <| Homeomorph.compactSpace (baseChange_quotient ℚ K)
  let W_inf : Set (InfiniteAdeleRing ℚ) := Set.pi Set.univ <|
    fun (v : InfinitePlace ℚ) => closedBall 0 1
  let W_fin : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    algebraMap _ _ '' (Set.univ : Set (FiniteIntegralAdeles (𝓞 ℚ) ℚ))
  let W : Set (AdeleRing ℚ) := W_inf.prod W_fin
  let f : AdeleRing ℚ → AdeleRing ℚ ⧸ principalSubgroup ℚ := QuotientAddGroup.mk' _
  have h_W_compact : IsCompact W := by
    refine IsCompact.prod (isCompact_univ_pi (fun v => ?_))
      (IsCompact.image CompactSpace.isCompact_univ <| continuous_algebraMap _ _)
    exact isCompact_iff_isClosed_bounded.2 <| ⟨isClosed_ball, isBounded_closedBall⟩
  have h_W_image : f '' W = Set.univ := by
    simp only [f, Set.eq_univ_iff_forall]
    intro x
    let a := Quotient.out' x
    rw [Set.mem_image]
    choose xf yf hf using FiniteAdeleRing.sub_mem_finiteIntegralAdeles ℚ a.2
    choose xi hi using InfiniteAdeleRing.sub_mem_closedBalls (a.1 - algebraMap _ _ xf)
    let c := globalEmbedding ℚ <| xi + xf
    let b := a - c
    have hb : b ∈ W := by
      simp only [W, Set.prod, W_inf, W_fin]
      refine ⟨Set.mem_univ_pi.2 fun v => ?_, ?_⟩
      · simp only [b, map_add, mem_closedBall, dist_zero_right, c,
          add_comm, Prod.fst_sub, Prod.fst_add, ← sub_sub]
        exact hi v
      · simp only [Set.image_univ, Set.mem_range, Eq.comm,
          FiniteAdeleRing.exists_finiteIntegralAdele_iff]
        intro v
        simp only [b, c, map_add, add_comm, ← sub_sub]
        exact (v.adicCompletionIntegers _).sub_mem
          ((FiniteAdeleRing.exists_finiteIntegralAdele_iff _).1 ⟨_, hf⟩ v)
            (v.coe_mem_adicCompletionIntegers _)
    refine ⟨b, hb, ?_⟩
    rw [← QuotientAddGroup.out_eq' x, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem]
    simp only [b, sub_sub_cancel_left, neg_mem_iff, principalSubgroup, AddSubgroup.mem_mk,
      Subsemiring.coe_carrier_toSubmonoid, Subring.coe_toSubsemiring, RingHom.coe_range,
      Set.mem_range, exists_apply_eq_apply]
  exact h_W_image ▸ IsCompact.image h_W_compact continuous_quot_mk

instance compactSpace_quotient_principal : CompactSpace (AdeleRing K ⧸ principalSubgroup K) :=
  ⟨isCompact_quotient_principal _⟩

end AdeleRing

end NumberField
