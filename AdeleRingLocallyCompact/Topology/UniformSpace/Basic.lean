/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.Algebra.UniformField

/-!
# Uniform spaces

In this file we prove that a `UniformSpace.comap f b` uniform structure defines a completable
topological field if the map `f` is a ring homomorphism between fields and if the codomain uniform
space `b` is a completable topological field.

## Main results
 - `UniformInducing.completableTopField` : if the codomain of a uniform inducing ring
   homomorphism between fields is a completable topological field, then the domain is also a
   completable topological field.
-/
variable {α β : Type*} [Field β] [b : UniformSpace β] [CompletableTopField β]
  [Field α]

/-- The pullback of a completable topological field along a uniform inducing
ring homomorphism is a completable topological field. -/
theorem UniformInducing.completableTopField [UniformSpace α] [T0Space α] {f : α →+* β}
    (hf : UniformInducing f) : CompletableTopField α := by
  refine CompletableTopField.mk (fun F F_cau inf_F => ?_)
  rw [← UniformInducing.cauchy_map_iff hf] at F_cau ⊢
  have h_comm : (f ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ f := by
    ext; simp only [Function.comp_apply, map_inv₀, Subfield.coe_inv]
  rw [Filter.map_comm h_comm]
  apply CompletableTopField.nice _ F_cau
  rw [← Filter.push_pull', ← map_zero f, ← hf.inducing.nhds_eq_comap, inf_F, Filter.map_bot]

namespace UniformSpace

instance comap_completableTopField (f : α →+* β)
    [@T0Space α (UniformSpace.comap f b).toTopologicalSpace] :
    @CompletableTopField _ _ (UniformSpace.comap f b) :=
  letI := UniformSpace.comap f b; (uniformInducing_iff_uniformSpace.2 rfl).completableTopField

end UniformSpace
