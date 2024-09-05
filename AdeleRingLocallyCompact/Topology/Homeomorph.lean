/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib
import AdeleRingLocallyCompact.Logic.Equiv.Basic

namespace Homeomorph

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] (p : α → Prop)
def prodSubtypeFstEquivSubtypeProd :
    { s : α × β // p s.1 } ≃ₜ { a : α // p a } × β where
  toEquiv := Equiv.prodSubtypeFstEquivSubtypeProd
  continuous_toFun := by
    simp only [Equiv.prodSubtypeFstEquivSubtypeProd]
    fun_prop
  continuous_invFun := by
    simp only [Equiv.prodSubtypeFstEquivSubtypeProd]
    fun_prop

variable (p : β → Prop)
def prodSubtypeSndEquivSubtypeProd :
    { s : α × β // p s.2 } ≃ₜ α × { b : β // p b } where
  toEquiv := Equiv.prodSubtypeSndEquivSubtypeProd p
  continuous_toFun := by
    simp only [Equiv.prodSubtypeSndEquivSubtypeProd]
    fun_prop
  continuous_invFun := by
    simp only [Equiv.prodSubtypeSndEquivSubtypeProd]
    fun_prop

variable {α : Type*} {β : α → Type*} [∀ a, TopologicalSpace (β a)] (p : (a : α) → β a → Prop)
def subtypePiEquivPi :
    { f : (a : α) → β a // ∀ a, p a (f a) } ≃ₜ ((a : α) → { b // p a b }) where
  toEquiv := Equiv.subtypePiEquivPi
  continuous_toFun := by
    refine continuous_pi (fun v => Continuous.subtype_mk ?_ _)
    exact Continuous.comp (ContinuousMap.eval v).continuous_toFun continuous_induced_dom
  continuous_invFun := by
    simp only [Equiv.subtypePiEquivPi]
    fun_prop

end Homeomorph
