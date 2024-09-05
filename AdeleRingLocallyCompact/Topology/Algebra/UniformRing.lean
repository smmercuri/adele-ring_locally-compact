/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# Completions of topological rings

This file contains an `extensionHom` version of `UniformSpace.Completion.extension_coe`.
-/
namespace UniformSpace.Completion

variable {α : Type*} [Ring α] [UniformSpace α] [TopologicalRing α] [UniformAddGroup α]
variable {β : Type*} [UniformSpace β] [Ring β] [UniformAddGroup β] [TopologicalRing β]
  (g : α →+* β) (hg : Continuous g) (a : α)

def extensionHom_coe [CompleteSpace β] [T0Space β] :
    Completion.extensionHom g hg a = g a := by
  simp only [Completion.extensionHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    UniformSpace.Completion.extension_coe <| uniformContinuous_addMonoidHom_of_continuous hg]

end UniformSpace.Completion
