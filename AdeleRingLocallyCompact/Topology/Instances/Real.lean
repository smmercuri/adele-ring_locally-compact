/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Instances.Real

/-!
# Topological properties of ℝ

We show that the only closed subfield of ℝ is ℝ.
-/

noncomputable section

theorem Real.subfield_eq_of_closed {K : Subfield ℝ} (hc : IsClosed (K : Set ℝ)) : K = ⊤ := by
  rw [SetLike.ext'_iff, Subfield.coe_top, ← hc.closure_eq]
  refine Rat.denseRange_cast.mono ?_ |>.closure_eq
  rintro - ⟨_, rfl⟩
  exact SubfieldClass.ratCast_mem K _
