/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# Ring equivs

In this file we extend some standard results from `Equiv` to `RingEquiv`.
-/

namespace RingEquiv

variable {α β ι : Type*}

@[simps!]
def piEquivPiSubtypeProd (p : ι → Prop) [DecidablePred p] (Y : ι → Type*)
    [∀ i, Add (Y i)] [∀ i, Mul (Y i)] :
    ((i : ι) → Y i) ≃+* ((i : { x : ι // p x }) → Y i) × ((i : { x : ι // ¬p x }) → Y i) where
  toEquiv := Equiv.piEquivPiSubtypeProd p Y
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simps!]
def prodMap {R R' S S' : Type*} [Add R] [Add R'] [Mul R] [Mul R'] [Add S] [Add S'] [Mul S] [Mul S']
    (f : R ≃+* R') (g : S ≃+* S') :
    R × S ≃+* R' × S' where
  toEquiv := Equiv.prodCongr f g
  map_mul' _ _ := by
    simp only [Equiv.toFun_as_coe, Equiv.prodCongr_apply, EquivLike.coe_coe]
    rw [Prod.map_apply]
    simp only [Prod.fst_mul, map_mul, Prod.snd_mul, Prod.mk_mul_mk]
    rfl
  map_add' _ _ := by
    simp only [Equiv.toFun_as_coe, Equiv.prodCongr_apply, EquivLike.coe_coe]
    rw [Prod.map_apply]
    simp only [Prod.fst_add, map_add, Prod.snd_add, Prod.mk_add_mk]
    rfl

@[simp]
theorem coe_prodMap {R R' S S' : Type*} [Add R] [Add R'] [Mul R] [Mul R'] [Add S] [Add S'] [Mul S]
    [Mul S'] (f : R ≃+* R') (g : S ≃+* S') :
    ⇑(RingEquiv.prodMap f g) = Prod.map f g :=
  rfl

@[simps!]
def piCongrLeft' (A : α → Type*) (e : α ≃ β)
    [∀ a, Add (A a)] [∀ a, Mul (A a)] :
    ((a : α) → A a) ≃+* ((b : β) → A (e.symm b)) where
  toEquiv := Equiv.piCongrLeft' A e
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem piCongrLeft'_symm {R : Type*} [Add R] [Mul R] (e : α ≃ β) :
    (RingEquiv.piCongrLeft' (fun _ => R) e).symm = RingEquiv.piCongrLeft' _ e.symm := by
  simp only [piCongrLeft', RingEquiv.symm, MulEquiv.symm, Equiv.piCongrLeft'_symm]

@[simps!]
def piCongrLeft (B : β → Type*) (e : α ≃ β)
    [∀ b, Add (B b)] [∀ b, Mul (B b)] :
    ((a : α) → B (e a)) ≃+* ((b : β) → B b) :=
  (RingEquiv.piCongrLeft' B e.symm).symm

end RingEquiv
