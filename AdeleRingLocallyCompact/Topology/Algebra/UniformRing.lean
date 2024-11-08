/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# Completion of topological rings

This file contains a helper result for coercion within `UniformSpace.extensionHom` usage.
-/
namespace UniformSpace.Completion

variable {α : Type*} [Ring α] [UniformSpace α] [TopologicalRing α] [UniformAddGroup α]
  {β : Type u} [UniformSpace β] [Ring β] [UniformAddGroup β] [TopologicalRing β]
  (f : α →+* β) (hf : Continuous f)

theorem extensionHom_coe [CompleteSpace β] [T0Space β] (a : α):
    Completion.extensionHom f hf a = f a := by
  simp only [Completion.extensionHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    UniformSpace.Completion.extension_coe <| uniformContinuous_addMonoidHom_of_continuous hf]

end UniformSpace.Completion
