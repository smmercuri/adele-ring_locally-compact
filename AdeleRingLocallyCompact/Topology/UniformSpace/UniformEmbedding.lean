import Mathlib

universe u v
variable {α : Type u} {β : Type v}

namespace UniformInducing

theorem comap_completableTopField [Field β] [Field α] {f : α →+* β} [b : UniformSpace β]
  [@T0Space α (UniformSpace.comap f b).toTopologicalSpace] [CompletableTopField β]
  (hf : @UniformInducing _ _ (UniformSpace.comap f b) _ f) :
    @CompletableTopField _ _ (UniformSpace.comap f b) := by
  apply @CompletableTopField.mk _ _ (UniformSpace.comap f b)
  intro F F_cau inf_F
  have h_cau_i := @UniformInducing.cauchy_map_iff _ _ (UniformSpace.comap f b) _ _ hf
  rw [← h_cau_i] at F_cau ⊢
  have h_comm : (f ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ f := by
    ext; simp only [Function.comp_apply, map_inv₀, Subfield.coe_inv]
  rw [Filter.map_comm h_comm]
  apply CompletableTopField.nice _ F_cau
  rw [← Filter.push_pull', ← map_zero f]
  have h_inducing := (@UniformInducing.inducing _ _ (UniformSpace.comap f b) _ _ hf)
  have h_nhds := @Inducing.nhds_eq_comap _ _ _ (UniformSpace.comap f b).toTopologicalSpace _ h_inducing
  rw [← h_nhds, inf_F, Filter.map_bot]

end UniformInducing
