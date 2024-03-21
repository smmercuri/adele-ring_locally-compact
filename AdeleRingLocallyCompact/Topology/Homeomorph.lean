import Mathlib

variable {X : Type*} {Y : Type*}

namespace Homeomorph

variable [TopologicalSpace X] [TopologicalSpace Y]

theorem locallyCompactSpace [i : LocallyCompactSpace Y] (h : X ≃ₜ Y) :
  LocallyCompactSpace X := by
  apply LocallyCompactSpace.mk
  intro x N hN
  rw [ ← h.symm_map_nhds_eq]
  have h' := (i.1 (h x))
  rw [h.nhds_eq_comap] at hN
  rw [Filter.mem_comap] at hN
  obtain ⟨T, hT⟩ := hN
  obtain ⟨S, hS, hS'⟩ := h' T hT.1
  use h.symm '' S
  rw [Filter.mem_map]
  simp
  refine' ⟨hS, _, hS'.2⟩
  apply subset_trans hS'.1
  rw [h.preimage_symm]
  rw [← h.preimage_subset]
  simp
  exact hT.2

  end Homeomorph
