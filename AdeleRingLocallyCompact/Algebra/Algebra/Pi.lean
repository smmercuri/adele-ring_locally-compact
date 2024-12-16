/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.TensorProduct.Basic
import AdeleRingLocallyCompact.FromMathlib.LinearAlgebra.TensorProduct.Pi

open scoped TensorProduct

noncomputable section

@[simps!]
def AlgEquiv.piCurry (S : Type*) [CommSemiring S] {Y : ι → Type*} (α : (i : ι) → Y i → Type*)
    [(i : ι) → (y : Y i) → Semiring (α i y)] [(i : ι) → (y : Y i) → Algebra S (α i y)] :
    ((i : Sigma Y) → α i.1 i.2) ≃ₐ[S] ((i : ι) → (y : Y i) → α i y) where
  toEquiv := Equiv.piCurry α
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simps!]
def AlgEquiv.piCongrLeft' (S : Type*) [CommSemiring S] (A : α → Type*) (e : α ≃ β)
    [∀ a, Semiring (A a)] [∀ a, Algebra S (A a)] :
    ((a : α) → A a) ≃ₐ[S] ((b : β) → A (e.symm b)) where
  toEquiv := Equiv.piCongrLeft' A e
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem AlgEquiv.piCongrLeft'_symm (S : Type*) {A : Type*} [CommSemiring S] [Semiring A]
    [Algebra S A] (e : α ≃ β) :
    (AlgEquiv.piCongrLeft' S (fun _ => A) e).symm = AlgEquiv.piCongrLeft' S _ e.symm := by
  simp [AlgEquiv.piCongrLeft', AlgEquiv.symm, RingEquiv.symm, MulEquiv.symm,
    Equiv.piCongrLeft'_symm]
  rfl

@[simp]
theorem AlgEquiv.piCongrLeft'_symm_apply_apply (S : Type*) (A : α → Type*) [CommSemiring S]
    [∀ a, Semiring (A a)] [∀ a, Algebra S (A a)] (e : α ≃ β) (g : (b : β) → A (e.symm b)) (b : β) :
    (piCongrLeft' S A e).symm g (e.symm b) = g b := by
  rw [← Equiv.piCongrLeft'_symm_apply_apply A e g b]
  rfl

@[simps! apply toEquiv]
def AlgEquiv.piCongrLeft (S : Type*) [CommSemiring S] (B : β → Type*) (e : α ≃ β)
    [∀ b, Semiring (B b)] [∀ b, Algebra S (B b)] :
    ((a : α) → B (e a)) ≃ₐ[S] ((b : β) → B b) :=
  (AlgEquiv.piCongrLeft' S B e.symm).symm
