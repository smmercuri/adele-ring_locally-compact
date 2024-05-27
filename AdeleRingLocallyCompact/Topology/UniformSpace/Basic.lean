/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# Uniform spaces

In this file we prove that a `UniformSpace.comap f b` uniform structure defines a completable
topological field if the map `f` is a ring homomorphism between fields and if the codomain uniform
space `b` is a completable topological field.

## Main results
 - `UniformInducing.comap_completableTopField` : if the codomain of a ring homomorphism between
   fields is a completable topological field, then the domain is also a completable topological
   field.
-/
universe u v
variable {α : Type u} {β : Type v}

namespace UniformSpace

/-- The pullback of a completable topological field along a ring homomorphism
is a completable topological field. -/
theorem comap_completableTopField [Field β] [Field α] {f : α →+* β} [b : UniformSpace β]
    [@T0Space α (UniformSpace.comap f b).toTopologicalSpace] [CompletableTopField β] :
    @CompletableTopField _ _ (UniformSpace.comap f b) := by
  have h_ui : @UniformInducing _ _ (UniformSpace.comap f b) _ f := by
    rw [@uniformInducing_iff_uniformSpace]
  apply @CompletableTopField.mk _ _ (UniformSpace.comap f b)
  intro F F_cau inf_F
  have h_cau_i := @UniformInducing.cauchy_map_iff _ _ (UniformSpace.comap f b) _ _ h_ui
  rw [← h_cau_i] at F_cau ⊢
  have h_comm : (f ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ f := by
    ext; simp only [Function.comp_apply, map_inv₀, Subfield.coe_inv]
  rw [Filter.map_comm h_comm]
  apply CompletableTopField.nice _ F_cau
  rw [← Filter.push_pull', ← map_zero f]
  have h_inducing := (@UniformInducing.inducing _ _ (UniformSpace.comap f b) _ _ h_ui)
  have h_nhds :=
    @Inducing.nhds_eq_comap _ _ _ (UniformSpace.comap f b).toTopologicalSpace _ h_inducing
  rw [← h_nhds, inf_F, Filter.map_bot]

end UniformSpace
