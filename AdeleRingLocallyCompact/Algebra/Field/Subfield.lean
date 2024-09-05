/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# Subfields

Some basic results about `fieldRange`.
-/

namespace RingHom

variable {K L : Type*} [Field K] [Field L]

@[simp]
theorem mem_fieldRange_self (f : K →+* L) (x : K) :
    f x ∈ f.fieldRange :=
  exists_apply_eq_apply _ _

theorem fieldRange_eq_top {f : K →+* L} :
    f.fieldRange = ⊤ ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans Set.range_iff_surjective

end RingHom
