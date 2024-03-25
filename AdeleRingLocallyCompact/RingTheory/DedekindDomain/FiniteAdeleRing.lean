/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib

noncomputable section

open DedekindDomain IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Classical

namespace DedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] (K : Type*)
  [Field K] [Algebra R K] [IsFractionRing R K]

namespace ProdAdicCompletions

variable {R}

def projection (v : HeightOneSpectrum R) :
  ProdAdicCompletions R K → v.adicCompletion K :=
  Pi.evalRingHom _ v

def localInclusion (v : HeightOneSpectrum R) :
  v.adicCompletion K → ProdAdicCompletions R K :=
  λ x =>
    (λ w =>
      if hw : w = v then
        congrArg (λ v => v.adicCompletion K) hw ▸ x else
        (1 : w.adicCompletion K)
    )

variable {K}

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

theorem localInclusion_rfl (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
  localInclusion K v x v = x := by simp only [localInclusion, dif_pos]

theorem projection_localInclusion_eq (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
  projection K v (localInclusion K v x) = x := by convert localInclusion_rfl v x

end ProdAdicCompletions

namespace FiniteAdeleRing

variable {R K}

def projection (v : HeightOneSpectrum R) :
  finiteAdeleRing R K → v.adicCompletion K :=
  (Pi.evalRingHom _ v) ∘ Subtype.val

def localInclusion (v : HeightOneSpectrum R) :
  v.adicCompletion K → finiteAdeleRing R K :=
  λ x => ⟨ProdAdicCompletions.localInclusion K v x,
          ProdAdicCompletions.isFiniteAdele_localInclusion v x⟩

local notation "π" => projection
local notation "ι" => localInclusion

theorem localInclusion_rfl (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : (ι v x).val v = x := by
  simp only [localInclusion, ProdAdicCompletions.localInclusion_rfl]

theorem projection_localInclusion_eq (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : π v (ι v x) = x := by
  convert localInclusion_rfl v x

variable (R K)

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
