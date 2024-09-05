/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib

namespace Equiv

variable {α β : Type*} (p : β → Prop)
def prodSubtypeSndEquivSubtypeProd : { s : α × β // p s.2 } ≃ α × { b : β // p b } where
  toFun s := ⟨s.1.1, ⟨s.1.2, s.2⟩⟩
  invFun s := ⟨⟨s.1, s.2.1⟩, s.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Equiv
