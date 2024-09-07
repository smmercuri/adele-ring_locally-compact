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
  continuous_toFun :=
    Continuous.prod_mk (Continuous.subtype_mk (Continuous.fst continuous_subtype_val) _)
      (Continuous.snd continuous_subtype_val)
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.prod_mk (Continuous.comp continuous_subtype_val
      (Continuous.fst continuous_id)) (Continuous.snd continuous_id)) _

variable (p : β → Prop)
def prodSubtypeSndEquivSubtypeProd :
    { s : α × β // p s.2 } ≃ₜ α × { b : β // p b } where
  toEquiv := Equiv.prodSubtypeSndEquivSubtypeProd p
  continuous_toFun :=
    Continuous.prod_mk (Continuous.fst continuous_subtype_val)
      (Continuous.subtype_mk (Continuous.snd continuous_subtype_val) _)
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.prod_mk (Continuous.fst continuous_id)
      (Continuous.comp continuous_subtype_val (Continuous.snd continuous_id))) _


variable {α : Type*} {β : α → Type*} [∀ a, TopologicalSpace (β a)] (p : (a : α) → β a → Prop)
set_option trace.Meta.Tactic.fun_prop true in
def subtypePiEquivPi :
    { f : (a : α) → β a // ∀ a, p a (f a) } ≃ₜ ((a : α) → { b // p a b }) where
  toEquiv := Equiv.subtypePiEquivPi
  continuous_toFun := by
    refine continuous_pi (fun v => Continuous.subtype_mk ?_ _)
    exact Continuous.comp (ContinuousMap.eval v).continuous_toFun continuous_induced_dom
  continuous_invFun :=
    Continuous.subtype_mk (continuous_pi
      (fun x => Continuous.comp continuous_subtype_val (continuous_apply _))) _

end Homeomorph
