/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib
import AdeleRingLocallyCompact.NumberTheory.NumberField.Embeddings

/-!
# Infinite adele ring

This file formalises the definition of the infinite adele ring of a number field `K` as the
product of completions of `K` over its infinite places and we show that it is locally compact.
The definition of the completions are formalised in
[AdeleRingLocallyCompact.NumberTheory.NumberField.Embeddings](Embeddings.lean).

## Main definitions
 - `DedekindDomain.infiniteAdeleRing` of a number field `K` is defined as the product of
   the completions of `K` over its Archimedean places.

## Main results
 - `DedekindDomain.InfiniteAdeleRing.locallyCompactSpace` : the infinite adele ring is a
  locally compact space since it's a finite product of locally compact spaces.

## Implementation notes
 - In the literature, the global embedding is usually defined by `x ↦ (x, x, ..., x)`, where
  the absolute value at each infinite place is extended from the embedding associated to `v`
  composed with the complex absolute value. Here the formalisation of `v.completion K` is
  obtained by injecting `K` to a `Subfield ℂ` type using the embedding associated to `v` and then
  completing this image with respect to the complex absolute value (see the implementation
  notes of `NumberTheory/NumberField/Embeddings.lean`). Thus, in our case
  the global embedding is defined by `x ↦ (e₁(x), ..., eₙ(x))`, where `eᵢ` are the embeddings
  and the absolute value at each infinite place is extended from the usual complex absolute value.
  These two definitions are clearly equivalent.

## References
 * [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
infinite adele ring, number field
-/

noncomputable section

namespace NumberField

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

def infiniteAdeleRing := (v : InfinitePlace K) → v.completion K

namespace InfiniteAdeleRing

section DerivedInstances

instance : CommRing (infiniteAdeleRing K) := Pi.commRing

instance : Inhabited (infiniteAdeleRing K) := ⟨0⟩

instance : Nontrivial (infiniteAdeleRing K) := Pi.nontrivial

end DerivedInstances

instance topologicalSpace : TopologicalSpace (infiniteAdeleRing K) := Pi.topologicalSpace

instance topologicalRing : TopologicalRing (infiniteAdeleRing K) := Pi.instTopologicalRing

def globalEmbedding : K →+* infiniteAdeleRing K :=
  Pi.ringHom (fun (v : InfinitePlace K) => InfinitePlace.Completion.coeRingHom K v)

theorem globalEmbedding_injective : Function.Injective (globalEmbedding K) :=
  (globalEmbedding K).injective

/-- The infinite adele ring is locally compact. -/
theorem locallyCompactSpace : LocallyCompactSpace (infiniteAdeleRing K) :=
  Pi.locallyCompactSpace_of_finite

end InfiniteAdeleRing

end NumberField
