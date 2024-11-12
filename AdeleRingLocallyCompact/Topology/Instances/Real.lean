/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# Topological properties of ℝ

We show that the only closed subfield of ℝ is ℝ.
-/

noncomputable section

theorem Real.subfield_eq_of_closed {K : Subfield ℝ} (hc : IsClosed (K : Set ℝ)) : K = ⊤ := by
  suffices : Set.univ ⊆ (K : Set ℝ)
  · exact eq_top_iff.2 fun _ _ => this (Set.mem_univ _)
  suffices : Set.univ ⊆ closure (Set.range ((↑) : ℚ → ℝ))
  · refine subset_trans this ?_
    rw [← IsClosed.closure_eq hc]
    apply closure_mono
    rintro _ ⟨_, rfl⟩
    simp only [SetLike.mem_coe, SubfieldClass.ratCast_mem]
  rw [DenseRange.closure_range Rat.denseRange_cast]
