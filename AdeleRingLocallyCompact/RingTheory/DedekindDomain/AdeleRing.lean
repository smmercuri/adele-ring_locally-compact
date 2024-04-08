/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.InfiniteAdeleRing

/-!
# Adele Ring

We define the adele ring of a number field `K` as the direct product of the infinite adele ring
of `K` and the finite adele ring of `K`, whose product is restricted with respect to the ring
of integers in `K`. We show that the adele ring of `K` is a locally compact space.

## Main definitions
 - `adeleRing K` is the adele ring of a number field `K`.

## Main results
 - `AdeleRing.locallyCompactSpace` : the adele ring of a number field is a locally compact space.

## References
 * [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
 * [M.I. de Frutos-Fernàndez, *Formalizing the Ring of Adèles of a Global Field*][defrutosfernandez2022]

## Tags
adele ring, dedekind domain

## TODO
 - Show that the adele ring is a topological ring.
-/

noncomputable section

open DedekindDomain IsDedekindDomain NumberField

open scoped Classical

namespace DedekindDomain

variable (K : Type*) [Field K] [NumberField K]

/-- The adele ring of a number field. -/
def adeleRing := infiniteAdeleRing K × finiteAdeleRing (ringOfIntegers K) K

namespace AdeleRing

section DerivedInstances

instance : CommRing (adeleRing K) := Prod.instCommRing

instance : Inhabited (adeleRing K) := ⟨0⟩

instance topologicalSpace : TopologicalSpace (adeleRing K) :=
  instTopologicalSpaceProd

end DerivedInstances

def globalEmbedding : K →+* adeleRing K :=
  RingHom.prod (InfiniteAdeleRing.globalEmbedding K) (FiniteAdeleRing.globalEmbedding _ _)

theorem globalEmbedding_injective : Function.Injective (globalEmbedding K) :=
  λ _ _ hxy => InfiniteAdeleRing.globalEmbedding_injective K (Prod.ext_iff.1 hxy).1

/-- The adele ring of a number field is a locally compact space. -/
theorem locallyCompactSpace : LocallyCompactSpace (adeleRing K) := by
  haveI := InfiniteAdeleRing.locallyCompactSpace K
  haveI := FiniteAdeleRing.locallyCompactSpace (ringOfIntegers K) K
  exact Prod.locallyCompactSpace _ _

end AdeleRing

end DedekindDomain
