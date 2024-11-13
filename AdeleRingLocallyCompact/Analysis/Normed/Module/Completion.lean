/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.Algebra.UniformField

/-!
# Normed space structure on the completion of a normed space

We show that the completion of a normed and completable topological field is also a
normed field.
-/

namespace UniformSpace.Completion

variable (A : Type*) [NormedField A] [CompletableTopField A]

noncomputable instance instNormedFieldOfCompletableTopField :
    NormedField (UniformSpace.Completion A) where
  dist_eq x y := by
    refine induction_on₂ x y ?_ (by simp [← coe_sub, dist_eq_norm])
    exact isClosed_eq (uniformContinuous_extension₂ _).continuous (by fun_prop)
  norm_mul' x y := induction_on₂ x y (isClosed_eq (by fun_prop) (by fun_prop)) (by simp [← coe_mul])

end UniformSpace.Completion
