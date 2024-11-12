/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FinsetAdeleRing
import AdeleRingLocallyCompact.NumberTheory.NumberField.InfiniteAdeleRing

set_option linter.longLine false
/-!
# Adele Ring

We define the adele ring of a number field `K` as the direct product of the infinite adele ring
of `K` and the finite adele ring of `K`. We show that the adele ring of `K` is a
locally compact space.

## Main definitions
 - `NumberField.AdeleRing K` is the adele ring of a number field `K`.
 - `NumberField.AdeleRing.principalSubgroup K` is the subgroup of principal adeles `(x)ᵥ`.

## Main results
 - `AdeleRing.locallyCompactSpace` : the adele ring of a number field is a locally compact space.

## References
 * [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
 * [M.I. de Frutos-Fernàndez, *Formalizing the Ring of Adèles of a Global Field*][defrutosfernandez2022]

## Tags
adele ring, dedekind domain
-/

noncomputable section

open DedekindDomain

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The adele ring of a number field. -/
def AdeleRing := InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K

namespace AdeleRing

section DerivedInstances

instance : CommRing (AdeleRing K) := Prod.instCommRing

instance : Inhabited (AdeleRing K) := ⟨0⟩

instance : TopologicalSpace (AdeleRing K) := instTopologicalSpaceProd

instance : TopologicalRing (AdeleRing K) := instTopologicalRingProd

instance : Algebra K (AdeleRing K) := Prod.algebra _ _ _

end DerivedInstances

@[simp]
theorem algebraMap_fst_apply (x : K) : (algebraMap K (AdeleRing K) x).1 v = x := rfl

@[simp]
theorem algebraMap_snd_apply (x : K) : (algebraMap K (AdeleRing K) x).2 v = x := rfl

theorem algebraMap_injective : Function.Injective (algebraMap K (AdeleRing K)) :=
  fun _ _ hxy => (algebraMap K (InfiniteAdeleRing K)).injective (Prod.ext_iff.1 hxy).1

/-- The adele ring of a number field is a locally compact space. -/
instance locallyCompactSpace : LocallyCompactSpace (AdeleRing K) := by
  letI := FiniteAdeleRing.locallyCompactSpace (𝓞 K) K
  exact Prod.locallyCompactSpace _ _

/-- The subgroup of principal adeles `(x)ᵥ` where `x ∈ K`. -/
def principalSubgroup : AddSubgroup (AdeleRing K) :=
  (algebraMap K (AdeleRing K)).range.toAddSubgroup

end AdeleRing

end NumberField
