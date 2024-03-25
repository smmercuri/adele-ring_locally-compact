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

Let `R` be a Dedekind domain of Krull dimension 1, `K` its field of fractions and `v` a maximal ideal of `R`.
If `K` is a number field we define the adele ring and show that it is a locally compact space.

## Main definitions
  - `adeleRing R K` is the adele ring of a number field `K`.

## Main results
  - `AdeleRing.locallyCompactSpace` : the adele ring of a number field is a locally compact space.
-/
noncomputable section

open DedekindDomain IsDedekindDomain

open scoped Classical

namespace DedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] (K : Type*)
  [Field K] [NumberField K] [Algebra R K] [IsFractionRing R K]

/-- The adele ring of a number field. -/
def adeleRing := infiniteAdeleRing K × finiteAdeleRing R K

namespace AdeleRing

section DerivedInstances

instance topologicalSpace : TopologicalSpace (adeleRing R K) :=
  instTopologicalSpaceProd

end DerivedInstances

/-- The adele ring of a number field is a locally compact space. -/
theorem locallyCompactSpace : LocallyCompactSpace (adeleRing R K) := by
  haveI := InfiniteAdeleRing.locallyCompactSpace K
  haveI := FiniteAdeleRing.locallyCompactSpace R K
  exact Prod.locallyCompactSpace _ _

end AdeleRing

end DedekindDomain
