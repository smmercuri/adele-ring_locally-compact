/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib
import AdeleRingLocallyCompact.NumberTheory.NumberField.Basic
import AdeleRingLocallyCompact.RingTheory.TensorProduct.Basic

/-!
# Infinite adele ring

This file ports and develops further the Lean 3 formalization of the infinite adele ring found in
[https://github.com/mariainesdff/ideles/blob/e6646cd462c86a8813ca04fb82e84cdc14a59ad4/src/adeles_K.lean#L45](https://github.com/mariainesdff/ideles/blob/e6646cd462c86a8813ca04fb82e84cdc14a59ad4/src/adeles_K.lean#L45).
While the infinite adele ring there is given the coinduced _ring topology_ by the linear map `ℝⁿ →ₗ[ℝ] ℝ ⊗[ℚ] K`, where
`n` is the degree of the field extension `K/ℚ`, in this file we show that this is actually a linear equivalence
`ℝ ⊗[ℚ] K ≃ₗ[ℝ] ℝⁿ` and instead we give the infinite adele ring the induced topology under the forward
direction of this equivalence, which is equivalent to the coinduced topology on the reverse direction but not
necessarily to the coinduced _ring topology_ of prior work
(because `TopologicalSpace.coinduced ≤ RingTopology.coinduced.toTopologicalSpace`).
It is a TODO to show that we can build a topological ring structure from the topology defined here. The reason
for this change is that both directions under the equivalence is used in the proof of local compactness, which
is possible on the level of topological spaces, but not in the ring topology unless we show the above `≤` is
actually an equivalence.

## Main definitions
 - `DedekindDomain.infiniteAdeleRing` of a number field `K` is defined as the tensor product `ℝ ⊗[ℚ] K`.
 - `DedekindDomain.InfiniteAdeleRing.piReal_equiv` is the linear equivalence
   `infiniteAdeleRing K ≃ ℝⁿ`, where `K` is a number field and `n` is the degree of the field extension
   of `K` over `ℚ`.
 - `DedekindDomain.InfiniteAdeleRing.topologicalSpace` is the induced topology of the infinite adele ring along
   the linear equivalence `DedekindDomain.InfiniteAdeleRing.real_tensorProduct_numberField_equiv`.

## Main results
 - `DedekindDomain.InfiniteAdeleRing.locallyCompactSpace` : the infinite adele ring is a locally compact space
   since it's topology is induced from a finite product of locally compact spaces.

## References
 * [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
 * [M.I. de Frutos-Fernàndez, *Formalizing the Ring of Adèles of a Global Field*][defrutosfernandez2022]

## Tags
infinite adele ring, number field

## TODO
 - `DedekindDomain.InfiniteAdeleRing.locallyCompactSpace` could be abstracted to a general result since all it
   relies on is that the infinite adeles have a topology that is induced by a linear equivalence to a locally compact
   space.
 - Show that the infinite adele ring is a topological ring.
-/

noncomputable section

open DedekindDomain IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Algebra.TensorProduct
  LinearMap

open scoped TensorProduct

namespace DedekindDomain

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

def infiniteAdeleRing := (ℝ ⊗[ℚ] K)

namespace InfiniteAdeleRing

section DerivedInstances

instance : Ring (Fin n → ℝ) := Pi.ring
instance piReal_topologicalSpace : TopologicalSpace (Fin n → ℝ) := Pi.topologicalSpace
instance : CommRing (infiniteAdeleRing K) := Algebra.TensorProduct.instCommRing

end DerivedInstances

theorem piReal_equiv : (ℝ ⊗[ℚ] K) ≃ₗ[ℝ] (Fin (FiniteDimensional.finrank ℚ K) → ℝ) :=
  LinearEquiv.trans
    (baseChange_equiv ℝ (ratBasis_equiv K).symm)
    (rid_pi_linearEquiv ℚ ℝ (Fin (FiniteDimensional.finrank ℚ K)))

instance topologicalSpace : TopologicalSpace (infiniteAdeleRing K)
  := TopologicalSpace.induced
    (piReal_equiv K)
    (piReal_topologicalSpace (FiniteDimensional.finrank ℚ K))

/-- A finite product of ℝ is locally compact. -/
theorem piReal_locallyCompact : LocallyCompactSpace (Fin n → ℝ) := Pi.locallyCompactSpace_of_finite

/-- The infinite adele ring is locally compact. -/
theorem locallyCompactSpace : LocallyCompactSpace (infiniteAdeleRing K) := by
    refine LocallyCompactSpace.mk (λ x N hN => ?_)
    simp only [nhds_induced, Filter.mem_comap] at hN
    obtain ⟨M, hM, hMN⟩ := hN
    have h := (piReal_locallyCompact (FiniteDimensional.finrank ℚ K)).local_compact_nhds
    obtain ⟨T, hT, hTM, hT_compact⟩ := h ((InfiniteAdeleRing.piReal_equiv K) x) M hM
    use (InfiniteAdeleRing.piReal_equiv K) ⁻¹' T
    refine ⟨?_, subset_trans ?_ hMN, ?_⟩
    · rw [nhds_induced, Filter.mem_comap]
      use T
    · rw [← LinearEquiv.coe_toEquiv]
      exact (Equiv.preimage_subset
        (LinearEquiv.toEquiv (InfiniteAdeleRing.piReal_equiv K)) _ _).2 hTM
    · rw [← LinearEquiv.image_symm_eq_preimage (InfiniteAdeleRing.piReal_equiv K) T]
      apply IsCompact.image hT_compact
      have h_topology : InfiniteAdeleRing.topologicalSpace K =
        TopologicalSpace.induced
          (InfiniteAdeleRing.piReal_equiv K).toEquiv
          (InfiniteAdeleRing.piReal_topologicalSpace (FiniteDimensional.finrank ℚ K)) := rfl
      rw [← Equiv.coinduced_symm (InfiniteAdeleRing.piReal_equiv K).toEquiv] at h_topology
      rw [h_topology]
      exact continuous_coinduced_rng

end InfiniteAdeleRing

end DedekindDomain
