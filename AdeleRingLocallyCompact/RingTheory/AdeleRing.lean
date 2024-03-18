import Mathlib
import AdeleRingLocallyCompact.RingTheory.FiniteAdeleRing
import AdeleRingLocallyCompact.RingTheory.InfiniteAdeleRing

open DedekindDomain
open NumberField
open IsDedekindDomain

open scoped TensorProduct
open scoped Classical

namespace DedekindDomain

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K] [NumberField K] [Algebra R K]
  [IsFractionRing R K] (S : Finset (HeightOneSpectrum R))
  (B : (n : ℕ) → Basis (Fin n) ℚ (Fin n → ℚ)) (C : (n : ℕ) → Basis (Fin n) ℝ (Fin n → ℝ))

def adeleRing := infiniteAdeleRing K × finiteAdeleRing R K

namespace AdeleRing

section DerivedInstances

noncomputable instance topologicalSpace : TopologicalSpace (adeleRing R K) := @instTopologicalSpaceProd _ _ (InfiniteAdeleRing.topologicalSpace K B C) _

end DerivedInstances

end AdeleRing

end DedekindDomain
