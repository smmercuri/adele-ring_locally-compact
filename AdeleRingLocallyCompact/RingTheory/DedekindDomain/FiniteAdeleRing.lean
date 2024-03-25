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

def inclusion (v : HeightOneSpectrum R) :
  v.adicCompletion K → ProdAdicCompletions R K :=
  λ x =>
    (λ w =>
      if hw : w = v then
        congrArg (λ v => v.adicCompletion K) hw ▸ x else
        (1 : w.adicCompletion K)
    )

variable {K}

theorem isFiniteAdele_inclusion (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : (inclusion K v x).IsFiniteAdele := by
  rw [ProdAdicCompletions.IsFiniteAdele, Filter.eventually_cofinite]
  have h : setOf (λ w => inclusion K v x w ∉ w.adicCompletionIntegers K) ⊆ {v} := by
    intro w hw
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hw ⊢
    contrapose! hw
    rw [inclusion]
    simp only [hw, ↓reduceDite]
    exact (w.adicCompletionIntegers K).one_mem'
  exact Set.Finite.subset (Set.finite_singleton _) h

theorem projection_inclusion_eq' (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : inclusion K v x v = x := by simp only [inclusion, ↓reduceDite]

theorem projection_inclusion_eq (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : projection K v (inclusion K v x) = x := by
  convert projection_inclusion_eq' v x

end ProdAdicCompletions

namespace FiniteAdeleRing

variable {R K}

def projection (v : HeightOneSpectrum R) :
  finiteAdeleRing R K → v.adicCompletion K :=
  (Pi.evalRingHom _ v) ∘ Subtype.val

def inclusion (v : HeightOneSpectrum R) :
  v.adicCompletion K → finiteAdeleRing R K :=
  λ x => ⟨ProdAdicCompletions.inclusion K v x,
          ProdAdicCompletions.isFiniteAdele_inclusion v x⟩

local notation "π" => projection
local notation "ι" => inclusion

theorem projection_inclusion_eq' (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : (ι v x).val v = x := by
  simp only [inclusion, ProdAdicCompletions.projection_inclusion_eq']

theorem projection_inclusion_eq (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : π v (ι v x) = x := by
  convert projection_inclusion_eq' v x

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
