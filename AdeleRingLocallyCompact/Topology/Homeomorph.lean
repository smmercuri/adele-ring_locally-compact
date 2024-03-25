import Mathlib

namespace Homeomorph

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem locallyCompactSpace [i : LocallyCompactSpace Y] (h : X ≃ₜ Y) :
  LocallyCompactSpace X := by
  refine LocallyCompactSpace.mk (λ x N hN => ?_)
  rw [←h.symm_map_nhds_eq]
  rw [h.nhds_eq_comap, Filter.mem_comap] at hN
  obtain ⟨T, hT, hTN⟩ := hN
  obtain ⟨S, hS, hST, hS_compact⟩ := (i.1 (h x)) T hT
  use h.symm '' S
  rw [Filter.mem_map, preimage_image, Set.image_subset_iff, isCompact_image]
  refine ⟨hS, ?_, hS_compact⟩
  apply subset_trans hST
  rw [h.preimage_symm, ← h.preimage_subset, coe_toEquiv, preimage_image]
  exact hTN

  end Homeomorph
