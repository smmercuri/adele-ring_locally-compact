import Mathlib
import AdeleRingLocallyCompact.RingTheory.FiniteAdeleRing
import AdeleRingLocallyCompact.RingTheory.InfiniteAdeleRing
import AdeleRingLocallyCompact.RingTheory.AdeleRing
import AdeleRingLocallyCompact.RingTheory.Uniformizers
import AdeleRingLocallyCompact.RingTheory.LocalRing
import AdeleRingLocallyCompact.Topology.Homeomorph

open DedekindDomain
open NumberField
open IsDedekindDomain

open scoped TensorProduct
open scoped Classical

namespace LocallyCompact

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K] [NumberField K] [Algebra R K]
  [IsFractionRing R K] (S : Finset (HeightOneSpectrum R)) (v : HeightOneSpectrum R)

instance : Fintype (LocalRing.ResidueField (v.adicCompletionIntegers K)) := sorry

noncomputable instance : CommRing (Fin n → LocalRing.ResidueField (v.adicCompletionIntegers K)) := inferInstance

noncomputable def adicCompletionIntegers_ofFiniteCoeffs (π : v.adicCompletionIntegers K) (n : ℕ)
  : (Fin n → v.adicCompletionIntegers K) → v.adicCompletionIntegers K
  := λ x => ((List.ofFn x).mapIdx (λ i j => j * π^i)).sum

theorem adicCompletionIntegers_finiteExpansion {π : v.adicCompletionIntegers K} (n : ℕ) (x : v.adicCompletionIntegers K) (hπ : IsUniformizer R K v π):
  ∃ (a : Fin n → LocalRing.ResidueField (v.adicCompletionIntegers K)),
    x - ((List.ofFn a).mapIdx (λ i j => (Quotient.out' j) * π^i)).sum ∈ (adicCompletionIntegers.maximalIdeal R K v)^n := by
    induction' n with d hd
    {
      simp
    }
    {
      obtain ⟨b, hbx⟩ := hd
      have h := isUniformizer_is_generator R K v hπ
      rw [h, Ideal.span_singleton_pow] at hbx ⊢
      rw [Ideal.mem_span_singleton'] at hbx
      obtain ⟨z, hz⟩ := hbx
      use Fin.snoc b (Ideal.Quotient.mk _ z)
      simp_rw [List.ofFn_succ']
      simp
      rw [List.mapIdx_append]
      simp
      rw [← sub_sub]
      rw [← hz]
      rw [← sub_mul]
      have h : π ∣ z - Quotient.out' (Ideal.Quotient.mk (adicCompletionIntegers.maximalIdeal R K v) z) := by
        rw [isUniformizer_is_generator R K v hπ]
        rw [← Ideal.mem_span_singleton]
        rw [← Submodule.Quotient.mk_eq_zero]
        rw [Submodule.Quotient.mk_sub]
        rw [Submodule.Quotient.mk]
        rw [Quotient.out_eq']
        simp

      rw [Ideal.mem_span_singleton]
      rw [pow_succ]
      exact mul_dvd_mul_right h (π^d)
    }

noncomputable def adicCompletionIntegers_toFiniteCoeffs {π : v.adicCompletionIntegers K} (n : ℕ) (hπ : IsUniformizer R K v π)
  : v.adicCompletionIntegers K ⧸ (adicCompletionIntegers.maximalIdeal R K v)^n → (Fin n → LocalRing.ResidueField (v.adicCompletionIntegers K))
  := λ x => (Classical.choose (adicCompletionIntegers_finiteExpansion R K v n (Quotient.out' x) hπ))

theorem adicCompletionIntegers_toPiResidueField_injective {π : v.adicCompletionIntegers K} (n : ℕ) (hπ : IsUniformizer R K v π)
  : (adicCompletionIntegers_toFiniteCoeffs R K v n hπ).Injective := by
  intro x y hxy
  unfold adicCompletionIntegers_toFiniteCoeffs at hxy
  set a := Classical.choose (adicCompletionIntegers_finiteExpansion R K v n (Quotient.out' x) hπ) with a_def
  set b := Classical.choose (adicCompletionIntegers_finiteExpansion R K v n (Quotient.out' y) hπ) with b_def
  have hx := Classical.choose_spec (adicCompletionIntegers_finiteExpansion R K v n (Quotient.out' x) hπ)
  have hy := Classical.choose_spec (adicCompletionIntegers_finiteExpansion R K v n (Quotient.out' y) hπ)
  rw [← a_def, hxy] at hx
  rw [← b_def] at hy
  rw [← Quotient.out_eq' x]
  rw [← Quotient.out_eq' y]
  rw [← Submodule.Quotient.mk]
  rw [← sub_eq_zero]
  rw [← Submodule.Quotient.mk_sub]
  rw [Submodule.Quotient.mk_eq_zero]
  rw [← sub_sub_sub_cancel_right _ _ (List.sum (List.mapIdx (fun i j => Quotient.out' j * π ^ i) (List.ofFn b)))]
  exact Ideal.sub_mem _ hx hy

theorem residueRing_order_fintype {π : v.adicCompletionIntegers K} (n : ℕ) (hπ : IsUniformizer R K v π)
  : Fintype (ResidueRing_order (v.adicCompletionIntegers K) n) := by
  haveI : Fintype (Fin n → LocalRing.ResidueField (v.adicCompletionIntegers K)) := Pi.fintype
  apply Fintype.ofInjective _ (adicCompletionIntegers_toPiResidueField_injective R K v n hπ)
