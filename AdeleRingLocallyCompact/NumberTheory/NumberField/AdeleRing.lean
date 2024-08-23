/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FinsetAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.InfiniteAdeleRing

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

instance : ContinuousSMul (FiniteIntegralAdeles (𝓞 K) K) (FiniteAdeleRing (𝓞 K) K) := sorry

instance : CompactSpace (FiniteIntegralAdeles (𝓞 K) K) := sorry

instance (v : InfinitePlace K) : ProperSpace (v.completion) := sorry

open IsDedekindDomain in
theorem FiniteAdeleRing.sub_mem_finiteIntegralAdeles (a : FiniteAdeleRing (𝓞 K) K) :
  ∃ (x : K) (y : FiniteIntegralAdeles (𝓞 K) K),
    a - algebraMap K (FiniteAdeleRing (𝓞 K) K) x = algebraMap _ _ y := sorry

open Metric in
theorem InfiniteAdeleRing.sub_mem_closedBalls (a : InfiniteAdeleRing K) :
  ∃ (x : 𝓞 K), ∀ v, norm ((a - algebraMap K _ x) v) ≤ 1 := sorry

open DedekindDomain IsDedekindDomain Metric in
theorem isCompact_quotient_principal :
    IsCompact (Set.univ : Set <| AdeleRing K ⧸ principalSubgroup K) := by
  let W_inf : Set (InfiniteAdeleRing K) := Set.pi Set.univ <|
    fun (v : InfinitePlace K) => closedBall 0 1
  let W_fin : Set (FiniteAdeleRing (RingOfIntegers K) K) :=
    algebraMap _ _ '' (Set.univ : Set (FiniteIntegralAdeles (RingOfIntegers K) K))
  let W : Set (AdeleRing K) := W_inf.prod W_fin
  let f : AdeleRing K → AdeleRing K ⧸ principalSubgroup K := QuotientAddGroup.mk' _
  have h_W_compact : IsCompact W := by
    refine IsCompact.prod (isCompact_univ_pi (fun v => ?_))
      (IsCompact.image CompactSpace.isCompact_univ <| continuous_algebraMap _ _)
    exact isCompact_iff_isClosed_bounded.2 <| ⟨isClosed_ball, isBounded_closedBall⟩
  have h_W_image : f '' W = Set.univ := by
    simp only [f, Set.eq_univ_iff_forall]
    intro x
    let a := Quotient.out' x
    rw [Set.mem_image]
    choose xf yf hf using FiniteAdeleRing.sub_mem_finiteIntegralAdeles K a.2
    choose xi hi using InfiniteAdeleRing.sub_mem_closedBalls K (a.1 - algebraMap _ _ xf)
    let c := globalEmbedding K <| xi + xf
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
        exact (v.adicCompletionIntegers K).sub_mem
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
