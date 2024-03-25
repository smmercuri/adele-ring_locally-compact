import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.InfiniteAdeleRing

noncomputable section

open DedekindDomain IsDedekindDomain

open scoped Classical

namespace DedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] (K : Type*)
  [Field K] [NumberField K] [Algebra R K] [IsFractionRing R K]

/-- The adele ring of a number field -/
def adeleRing := infiniteAdeleRing K × finiteAdeleRing R K

namespace AdeleRing

section DerivedInstances

instance topologicalSpace : TopologicalSpace (adeleRing R K) :=
  instTopologicalSpaceProd

end DerivedInstances

theorem locallyCompactSpace : LocallyCompactSpace (adeleRing R K) := by
  haveI := InfiniteAdeleRing.locallyCompactSpace K
  haveI := FiniteAdeleRing.locallyCompactSpace R K
  exact Prod.locallyCompactSpace _ _

end AdeleRing

end DedekindDomain
