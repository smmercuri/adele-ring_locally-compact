/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import AdeleRingLocallyCompact.Algebra.Algebra.Pi
import AdeleRingLocallyCompact.Algebra.Ring.Equiv
import AdeleRingLocallyCompact.FromMathlib.Algebra.Order.GroupWithZero.Unbundled
import AdeleRingLocallyCompact.FromMathlib.Analysis.SpecialFunctions.Pow.Real
import AdeleRingLocallyCompact.FromMathlib.Data.Fin.Lemmas
import AdeleRingLocallyCompact.FromMathlib.LinearAlgebra.TensorProduct.Pi
import AdeleRingLocallyCompact.NumberTheory.NumberField.Completion
import AdeleRingLocallyCompact.RingTheory.TensorProduct.Pi
import AdeleRingLocallyCompact.Topology.Algebra.Algebra
import AdeleRingLocallyCompact.Topology.Algebra.UniformRing
import AdeleRingLocallyCompact.Topology.Homeomorph

open scoped TensorProduct Classical Topology

/-!
# Infinite adele ring

This file formalises the definition of the infinite adele ring of a number field `K` as the
product of completions of `K` over its infinite places. The definition of the completions are
formalised in [AdeleRingLocallyCompact.NumberTheory.NumberField.Completion](Completion.lean).

We show that the infinite adele ring is locally compact and that it is isomorphic to the
space `ℝ ^ r₁ × ℂ ^ r₂` used in `Mathlib.NumberTheory.NumberField.mixedEmbedding`.

## Main definitions
 - `NumberField.InfiniteAdeleRing` of a number field `K` is defined as the product of
   the completions of `K` over its Archimedean places.
 - `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace` is the ring isomorphism between
   the infinite adele ring of `K` and `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature
   of `K`.

## Main results
 - `NumberField.InfiniteAdeleRing.locallyCompactSpace` : the infinite adele ring is a
   locally compact space.
 - `NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp` : applying the
   ring isomorphism of `equiv_mixedSpace` to a globally embedded `(x)ᵥ` in the infinite adele
   ring, where `x ∈ K`, is the same as applying the embedding `K → ℝ ^ r₁ × ℂ ^ r₂` given by
   `NumberField.mixedEmbedding` to `x`.


## References
 * [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
infinite adele ring, number field
-/

noncomputable section

namespace NumberField

open InfinitePlace InfinitePlace.Completion AbsoluteValue.Completion

open scoped Classical

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

/-- The infinite adele ring of a number field. -/
abbrev InfiniteAdeleRing := (v : InfinitePlace K) → v.completion

namespace InfiniteAdeleRing

instance : CommRing (InfiniteAdeleRing K) := Pi.commRing

instance : Inhabited (InfiniteAdeleRing K) := ⟨0⟩

instance : Nontrivial (InfiniteAdeleRing K) :=
  (inferInstanceAs <| Nonempty (InfinitePlace K)).elim fun w => Pi.nontrivial_at w

instance : TopologicalSpace (InfiniteAdeleRing K) := Pi.topologicalSpace

instance : TopologicalRing (InfiniteAdeleRing K) := Pi.instTopologicalRing

instance : Algebra K (InfiniteAdeleRing K) := Pi.algebra _ _

@[simp]
theorem algebraMap_apply (x : K) : algebraMap K (InfiniteAdeleRing K) x v = x := rfl

/-- The infinite adele ring is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (InfiniteAdeleRing K) :=
  Pi.locallyCompactSpace_of_finite

/-- The ring isomorphism between the infinite adele ring of a number field and the
space `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature of the number field. -/
def ringEquiv_mixedSpace :
    InfiniteAdeleRing K ≃+*
      ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ) :=
  RingEquiv.trans
    (RingEquiv.piEquivPiSubtypeProd (fun (v : InfinitePlace K) => IsReal v)
      (fun (v : InfinitePlace K) => v.completion))
    (RingEquiv.prodCongr
      (RingEquiv.piCongrRight (fun ⟨_, hv⟩ => Completion.ringEquiv_real_of_isReal hv))
      (RingEquiv.trans
        (RingEquiv.piCongrRight (fun v => Completion.ringEquiv_complex_of_isComplex
          ((not_isReal_iff_isComplex.1 v.2))))
        (RingEquiv.piCongrLeft (fun _ => ℂ) <|
          Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex))))

@[simp]
theorem ringEquiv_mixedSpace_apply (x : InfiniteAdeleRing K) :
    ringEquiv_mixedSpace K x =
      (fun (v : {w : InfinitePlace K // IsReal w}) =>
        ringEquiv_real_of_isReal v.2 (x v),
      fun (v : {w : InfinitePlace K // IsComplex w}) =>
        ringEquiv_complex_of_isComplex v.2 (x v)) :=
  rfl

/-- Transfers the embedding of `x ↦ (x)ᵥ` of the number field `K` into its infinite adele
ring to the mixed embedding `x ↦ (φᵢ(x))ᵢ` of `K` into the space `ℝ ^ r₁ × ℂ ^ r₂`, where
`(r₁, r₂)` is the signature of `K` and `φᵢ` are the complex embeddings of `K`. -/
theorem mixedEmbedding_eq_algebraMap_comp {x : K} :
    mixedEmbedding K x = ringEquiv_mixedSpace K (algebraMap K (InfiniteAdeleRing K) x) := by
  ext v <;> simp only [ringEquiv_mixedSpace_apply, algebraMap_apply, ringEquiv_real_of_isReal,
    ringEquiv_complex_of_isComplex, extensionEmbedding, extensionEmbedding_of_isReal,
    extensionEmbedding_of_comp, RingEquiv.coe_ofBijective, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, UniformSpace.Completion.extensionHom]
  · rw [UniformSpace.Completion.extension_coe
      (WithAbs.uniformInducing_of_comp <| v.1.norm_embedding_of_isReal v.2).uniformContinuous x]
    rfl
  · rw [UniformSpace.Completion.extension_coe
      (WithAbs.uniformInducing_of_comp <| v.1.norm_embedding_eq).uniformContinuous x]
    rfl

variable (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

/-
In other files we have established the following continuous algebra isomorphism:
(1) InfiniteAdeleRing K ⊗[K] L ≃A[K] Π (v : InfinitePlace K), (v.completion ⊗[K] L)
(2) (v.completion ⊗[K] L) ≃A[v.completion] Π (w : ExtensionPlace L v), w.1.completion.

We can piece these together and restrict scalars on (2), to give the K-algebra isomorphisms:
`InfiniteAdeleRing ⊗[K] L ≃A[K] Π v, (v.completion ⊗[K] L)
  ≃A[K] Π v, Π (w : ExtensionPlace L v), w.1.completion
    ≃A[K] Π (w : InfinitePlace L) w.completion
      = InfiniteAdeleRing L`
-/

instance : TopologicalSpace (InfiniteAdeleRing K ⊗[K] L) :=
  TopologicalSpace.induced
    (Algebra.TensorProduct.piLeft K L (fun v : InfinitePlace K => v.completion)) inferInstance

local instance : Algebra K (InfiniteAdeleRing L) := Pi.algebra _ _

open Algebra.TensorProduct in
def baseChange :
    InfiniteAdeleRing K ⊗[K] L ≃A[K] InfiniteAdeleRing L := by
  apply piLeftContinuousAlgEquiv K L _ |>.trans
  have (v : InfinitePlace K) := (InfinitePlace.Completion.baseChange L v).restrictScalars K
  apply ContinuousAlgEquiv.piCongrRight this |>.trans
  apply ContinuousAlgEquiv.piCurry K _ |>.symm |>.trans
  have := ContinuousAlgEquiv.piCongrLeft K (fun w => w.completion)
    (InfinitePlace.Completion.sigmaExtensionEquiv K L)
  exact (ContinuousAlgEquiv.refl _ _).trans this

end InfiniteAdeleRing

end NumberField
