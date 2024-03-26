/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

/-!
# Finite adele ring

The finite adele ring is defined in `Mathlib.RingTheory.DedekindDomain`
[https://github.com/leanprover-community/mathlib4/blob/1c0ac885c9b8aa4daa1830acb56b755140a8059f/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean#L274-L280].
In this file we supplement the theory by defining some local maps and the topological space for the finite adele ring.

## Main definitions
- `DedekindDomain.FiniteAdeleRing.projection v` is the map sending a finite adele `x` to its `v`th place `x v` in
  the `v`-adic completion of `K`.
- `DedekindDomain.FiniteAdeleRing.localInclusion v` is the map sending an element `x` of the `v`-adic completion
  of `K` to the finite adele which has `x` in its `v`th place and `1`s everywhere else.
- `DedekindDomain.FiniteAdeleRing.generatingSet` is the generating set of the topology of the finite adele ring.

## Main results
- `DedekindDomain.FiniteAdeleRing.topologicalSpace` : the topological space on the finite adele ring.

## References
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
finite adèle ring, dedekind domain
-/

noncomputable section

open DedekindDomain IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Classical

namespace DedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] (K : Type*)
  [Field K] [Algebra R K] [IsFractionRing R K]

namespace ProdAdicCompletions

variable {R}

/-- Sends an element of the product of all `adicCompletions` to a local place. -/
def projection (v : HeightOneSpectrum R) :
  ProdAdicCompletions R K → v.adicCompletion K :=
  Pi.evalRingHom _ v

/-- Sends a local element to the product of all `adicCompletions` filled with `1`s elsewhere. -/
def localInclusion (v : HeightOneSpectrum R) :
  v.adicCompletion K → ProdAdicCompletions R K :=
  λ x =>
    (λ w =>
      if hw : w = v then
        congrArg (λ v => v.adicCompletion K) hw ▸ x else
        (1 : w.adicCompletion K)
    )

variable {K}

/-- The local inclusion of any element is a finite adele. -/
theorem isFiniteAdele_localInclusion (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
  (localInclusion K v x).IsFiniteAdele := by
  rw [ProdAdicCompletions.IsFiniteAdele, Filter.eventually_cofinite]
  have h : setOf (λ w => localInclusion K v x w ∉ w.adicCompletionIntegers K) ⊆ {v} := by
    intro w hw
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hw ⊢
    contrapose! hw
    rw [localInclusion]
    simp only [hw, ↓reduceDite]
    exact (w.adicCompletionIntegers K).one_mem'
  exact Set.Finite.subset (Set.finite_singleton _) h

/-- The `v`th place of the local inclusion is the original element. -/
theorem localInclusion_rfl (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
  localInclusion K v x v = x := by simp only [localInclusion, dif_pos]

/-- The projection and local inclusions are inverses on `ProdAdicCompletions`. -/
theorem projection_localInclusion_eq (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
  projection K v (localInclusion K v x) = x := by convert localInclusion_rfl v x

end ProdAdicCompletions

namespace FiniteAdeleRing

variable {R K}

/-- Sends a finite adele to a local place. -/
def projection (v : HeightOneSpectrum R) :
  finiteAdeleRing R K → v.adicCompletion K :=
  (Pi.evalRingHom _ v) ∘ Subtype.val

/-- Sends a local element to a finite adele filled with `1`s elsewhere. -/
def localInclusion (v : HeightOneSpectrum R) :
  v.adicCompletion K → finiteAdeleRing R K :=
  λ x => ⟨ProdAdicCompletions.localInclusion K v x,
          ProdAdicCompletions.isFiniteAdele_localInclusion v x⟩

local notation "π" => projection
local notation "ι" => localInclusion

/-- The `v`th place of the local inclusion is the original element. -/
theorem localInclusion_rfl (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : (ι v x).val v = x := by
  simp only [localInclusion, ProdAdicCompletions.localInclusion_rfl]

/-- The projection and local inclusions are inverses on the finite adele ring. -/
theorem projection_localInclusion_eq (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : π v (ι v x) = x := by
  convert localInclusion_rfl v x

variable (R K)

/-- The generating set of the finite adele ring are all sets of the form `Πᵥ Vᵥ`, where
each `Vᵥ` is open in `Kᵥ` and for all but finitely many `v` we have that `Vᵥ` is the `v`-adic
ring of integers. -/
def generatingSet : Set (Set (finiteAdeleRing R K)) :=
  Set.preimage (Subtype.val) '' (Set.pi Set.univ '' (
    setOf (
      λ V =>
        (∀ v, IsOpen (V v)) ∧
        (∀ᶠ v in Filter.cofinite, V v = v.adicCompletionIntegers K)
    )
  ))

instance topologicalSpace : TopologicalSpace (finiteAdeleRing R K)
  := TopologicalSpace.generateFrom (generatingSet R K)

end FiniteAdeleRing

end DedekindDomain
