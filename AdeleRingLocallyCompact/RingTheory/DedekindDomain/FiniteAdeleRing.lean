import Mathlib

open DedekindDomain IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Classical

namespace DedekindDomain

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (S : Finset (HeightOneSpectrum R))

namespace ProdAdicCompletions

def projection (v : HeightOneSpectrum R) : ProdAdicCompletions R K → v.adicCompletion K
  := Pi.evalRingHom _ v

noncomputable def inclusion (v : HeightOneSpectrum R) : v.adicCompletion K → ProdAdicCompletions R K
  := λ x => (λ w => dite (w = v) (λ h => congrArg (λ v => v.adicCompletion K) h ▸ x) (λ _ => (1 : w.adicCompletion K)))

theorem isFiniteAdele_inclusion (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : (inclusion R K v x).IsFiniteAdele := by
  rw [ProdAdicCompletions.IsFiniteAdele]
  rw [Filter.eventually_cofinite]
  have h : setOf (λ w => inclusion R K v x w ∉ w.adicCompletionIntegers K) ⊆ {v} := by
    intro w hw
    simp [Set.mem_setOf_eq] at hw ⊢
    contrapose hw
    push_neg
    rw [inclusion]
    simp [hw]
    exact (w.adicCompletionIntegers K).one_mem'
  apply Set.Finite.subset _ h
  simp

theorem projection_inclusion_eq' (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : inclusion R K v x v = x := by simp [inclusion]

theorem projection_inclusion_eq (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : projection R K v (inclusion R K v x) = x := by convert projection_inclusion_eq' R K v x

-- TODO : remove this
theorem isOpen_adicCompletionIntegers (v : HeightOneSpectrum R) :
  IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  := Valued.valuationSubring_isOpen _

end ProdAdicCompletions

namespace FiniteAdeleRing

def projection (v : HeightOneSpectrum R) : finiteAdeleRing R K → v.adicCompletion K
  :=  (Pi.evalRingHom _ v) ∘ Subtype.val

noncomputable def inclusion (v : HeightOneSpectrum R) : v.adicCompletion K → finiteAdeleRing R K
  := λ x => ⟨ProdAdicCompletions.inclusion R K v x, ProdAdicCompletions.isFiniteAdele_inclusion R K v x⟩

local notation "π" => projection R K
local notation "ι" => inclusion R K

theorem projection_inclusion_eq' (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : (ι v x).val v = x := by simp [inclusion, ProdAdicCompletions.projection_inclusion_eq']

theorem projection_inclusion_eq (v : HeightOneSpectrum R) (x : v.adicCompletion K)
  : π v (ι v x) = x := by convert projection_inclusion_eq' R K v x

def generatingSet : Set (Set (finiteAdeleRing R K)) :=
  Set.preimage (Subtype.val) '' (Set.pi Set.univ '' (
    setOf (
      λ V =>
        (∀ v, IsOpen (V v)) ∧
        (∀ᶠ v in Filter.cofinite, V v = v.adicCompletionIntegers K)
    )
  ))

noncomputable instance : TopologicalSpace (finiteAdeleRing R K)
  := TopologicalSpace.generateFrom (generatingSet R K)

end FiniteAdeleRing

end DedekindDomain
