/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
/-!
# Locally compact spaces

We add a `nhds_zero` version of `LocallyCompactSpace.of_hasBasis` that constructs a
`LocallyCompactSpace` instance from a compact basis of neighbourhoods of zero for
topological add groups.
-/

theorem LocallyCompactSpace.of_hasBasis_nhds_zero
    {X ι : Type*} [TopologicalSpace X] [AddGroup X] [TopologicalAddGroup X]
    {p : ι → Prop} {s : ι → Set X}
    (h : (nhds 0).HasBasis p s)
    (hx : ∀ (i : ι), p i → IsCompact (s i)) :
    LocallyCompactSpace X := by
  refine ⟨fun x _t ht =>
    let ⟨t, ht, ht'⟩ := nhds_translation_add_neg x ▸ ht
    let ⟨i, hp, ht⟩ := h.mem_iff.1 ht
    ⟨(fun y => y + - x) ⁻¹' (s i),
      ⟨nhds_translation_add_neg x ▸ ⟨s i, h.mem_of_mem hp, subset_refl _⟩,
        subset_trans ((add_right_surjective _).preimage_subset_preimage_iff.2 ht) ht',
          (Homeomorph.addRight (-x)).isCompact_preimage.2 (hx i hp)⟩⟩⟩
