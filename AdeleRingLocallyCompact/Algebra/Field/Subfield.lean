/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Algebra.Field.Subfield

/-!
# Subfields

Some useful results on `fieldRange`.
-/

namespace RingHom

variable {K L : Type*} [DivisionRing K] [DivisionRing L] (f : K →+* L)

theorem mem_fieldRange_self (x : K) : f x ∈ f.fieldRange :=
  exists_apply_eq_apply _ _

theorem fieldRange_eq_top_iff {f : K →+* L} :
    f.fieldRange = ⊤ ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans Set.range_iff_surjective

end RingHom
