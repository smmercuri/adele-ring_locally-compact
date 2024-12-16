/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Algebra.Algebra.Pi
import AdeleRingLocallyCompact.Topology.Algebra.Algebra

@[simps!]
def Pi.algHom {I R A : Type*} (f : I → Type*) [CommSemiring R] [s : (i : I) → Semiring (f i)]
    [(i : I) → Algebra R (f i)] [Semiring A] [Algebra R A] (g : (i : I) → A →ₐ[R] f i) :
    A →ₐ[R] (i : I) → f i where
  __ := Pi.ringHom fun i ↦ (g i).toRingHom
  commutes' r := by ext; simp

@[simps!]
def Pi.continuousAlgHom {I R A : Type*} (f : I → Type*) [CommSemiring R]
    [(i : I) → Semiring (f i)] [(i : I) → Algebra R (f i)] [(i : I) → TopologicalSpace (f i)]
    [Semiring A] [TopologicalSpace A] [Algebra R A] (g : (i : I) → A →A[R] f i) :
    A →A[R] (i : I) → f i where
  __ := Pi.algHom _ <| fun _ => (g _).toAlgHom
  cont := continuous_pi <| fun _ => (g _).cont
