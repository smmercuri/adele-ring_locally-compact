import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.InfiniteAdeleRing

open DedekindDomain IsDedekindDomain

open scoped Classical

namespace DedekindDomain

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K] [NumberField K] [Algebra R K]
  [IsFractionRing R K]
  (B : (n : ℕ) → Basis (Fin n) ℚ (Fin n → ℚ)) (C : (n : ℕ) → Basis (Fin n) ℝ (Fin n → ℝ))

def adeleRing := infiniteAdeleRing K × finiteAdeleRing R K

namespace AdeleRing

section DerivedInstances

noncomputable instance topologicalSpace : TopologicalSpace (adeleRing R K) := @instTopologicalSpaceProd _ _ (InfiniteAdeleRing.topologicalSpace K B C) _

end DerivedInstances

theorem locallyCompactSpace
  : @LocallyCompactSpace (adeleRing R K) (DedekindDomain.AdeleRing.topologicalSpace R K B C) := by
  haveI := InfiniteAdeleRing.locallyCompactSpace K
  haveI := FiniteAdeleRing.locallyCompactSpace R K
  exact @Prod.locallyCompactSpace (infiniteAdeleRing K) (finiteAdeleRing R K) (InfiniteAdeleRing.topologicalSpace K B C) _ _ _

end AdeleRing

end DedekindDomain
