/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib
import AdeleRingLocallyCompact.NumberTheory.NumberField.Embeddings

/-!
# Infinite adele ring

This file formalises the definition of the infinite adele ring of a number field `K` as the product of completions
of `K` over its infinite places and we show that it is locally compact. The definition of the completions
are formalised in `AdeleRingLocallyCompact.NumberTheory.NumberField.Embeddings`.

## Main definitions
 - `DedekindDomain.infiniteAdeleRing` of a number field `K` is defined as the product of the completions
   of `K` over its Archimedean places.

## Main results
 - `DedekindDomain.InfiniteAdeleRing.locallyCompactSpace` : the infinite adele ring is a locally compact space
   since it's topology is induced from a finite product of locally compact spaces.

## References
 * [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
infinite adele ring, number field
-/

noncomputable section

open DedekindDomain IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Algebra.TensorProduct
  LinearMap

open scoped TensorProduct

namespace DedekindDomain

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

def infiniteAdeleRing := (v : InfinitePlace K) → v.completion K

namespace InfiniteAdeleRing

section DerivedInstances

instance : CommRing (infiniteAdeleRing K) := Pi.commRing

instance : Inhabited (infiniteAdeleRing K) := ⟨0⟩

instance : Nontrivial (infiniteAdeleRing K) := Pi.nontrivial

end DerivedInstances

instance : TopologicalSpace (infiniteAdeleRing K)
  := Pi.topologicalSpace

instance : TopologicalRing (infiniteAdeleRing K) := Pi.instTopologicalRing

def globalEmbedding : K →+* infiniteAdeleRing K :=
  Pi.ringHom (fun (v : InfinitePlace K) => InfinitePlace.Completion.coeRingHom K v)

theorem globalEmbedding_injective : Function.Injective (globalEmbedding K) :=
  (globalEmbedding K).injective

/-- The infinite adele ring is locally compact. -/
theorem locallyCompactSpace : LocallyCompactSpace (infiniteAdeleRing K) :=
  Pi.locallyCompactSpace_of_finite

end InfiniteAdeleRing

end DedekindDomain
