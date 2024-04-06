/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# Homeomorphisms

In this file we prove that local compactness is preserved by homeomorphisms.

## Main results
 - `Homeomorph.locallyCompactSpace_iff` : if the codomain of a homeomorphism is a locally
   compact space, then the domain is also a locally compact space.
-/
namespace Homeomorph

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The codomain of a homeomorphism is a locally compact space if and only if
the domain is a locally compact space. -/
theorem locallyCompactSpace_iff (h : X ≃ₜ Y) :
    LocallyCompactSpace X ↔ LocallyCompactSpace Y := by
  exact ⟨fun _ => h.symm.openEmbedding.locallyCompactSpace,
    fun _ => h.closedEmbedding.locallyCompactSpace⟩

  end Homeomorph
