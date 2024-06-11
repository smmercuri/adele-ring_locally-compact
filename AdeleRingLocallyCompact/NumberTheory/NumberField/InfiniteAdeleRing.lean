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
  locally compact space since it is a finite product of locally compact spaces.

## References
 * [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
infinite adele ring, number field
-/

noncomputable section

namespace NumberField

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

/-- The infinite adele ring of a number field. -/
def infiniteAdeleRing := (v : InfinitePlace K) → v.completion

namespace InfiniteAdeleRing

section DerivedInstances

instance : CommRing (infiniteAdeleRing K) := Pi.commRing

instance : Inhabited (infiniteAdeleRing K) := ⟨0⟩

instance : Nontrivial (infiniteAdeleRing K) :=
  (inferInstanceAs <| Nonempty (InfinitePlace K)).elim fun w => Pi.nontrivial_at w

end DerivedInstances

instance topologicalSpace : TopologicalSpace (infiniteAdeleRing K) := Pi.topologicalSpace

instance topologicalRing : TopologicalRing (infiniteAdeleRing K) := Pi.instTopologicalRing

instance : Algebra K (infiniteAdeleRing K) := Pi.algebra _ _

/-- The global embedding of a number field into its infinite adele ring,
sending `x ∈ K` to `(x)ᵥ`. -/
abbrev globalEmbedding : K →+* infiniteAdeleRing K := algebraMap K (infiniteAdeleRing K)

@[simp]
theorem globalEmbedding_apply (x : K) : globalEmbedding K x v = (x : v.completion) := rfl

/-- The infinite adele ring is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (infiniteAdeleRing K) :=
  Pi.locallyCompactSpace_of_finite

end InfiniteAdeleRing

end NumberField
