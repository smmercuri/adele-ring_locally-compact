/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# Normed space structure on the completion of a normed space

We show that the completion of a normed and completable topological field is also a
normed field.
-/

namespace UniformSpace.Completion

variable (A : Type*) [NormedField A] [CompletableTopField A]

noncomputable instance instNormedFieldOfCompletableTopField :
    NormedField (UniformSpace.Completion A) where
  toField := UniformSpace.Completion.instField
  dist_eq := fun x y => by
      refine Completion.induction_on₂ x y ?_ ?_ <;> clear x y
      · refine isClosed_eq (Completion.uniformContinuous_extension₂ _).continuous ?_
        exact Continuous.comp Completion.continuous_extension continuous_sub
      · intro x y
        rw [← Completion.coe_sub, norm_coe, Completion.dist_eq, dist_eq_norm]
  norm_mul' := fun x y => by
      refine Completion.induction_on₂ x y ?_ ?_ <;> clear x y
      · exact
          isClosed_eq (Continuous.comp continuous_norm continuous_mul)
            (Continuous.comp _root_.continuous_mul
              (Continuous.prod_map continuous_norm continuous_norm))
      · intro x y
        simp only [← coe_mul, norm_coe]
        exact norm_mul x y

end UniformSpace.Completion
