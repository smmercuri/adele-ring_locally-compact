import Mathlib
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteAdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.FiniteSAdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.InfiniteAdeleRing
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.AdeleRing
--import AdeleRingLocallyCompact.RingTheory.DedekindDomain.Uniformizers
--import AdeleRingLocallyCompact.RingTheory.DedekindDomain.ResidueField
import AdeleRingLocallyCompact.RingTheory.DedekindDomain.adicValuation
import AdeleRingLocallyCompact.Topology.Homeomorph

open DedekindDomain IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Classical

namespace LocallyCompact

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K] [NumberField K] [Algebra R K]
  [IsFractionRing R K] (S : Finset (HeightOneSpectrum R)) (v : HeightOneSpectrum R)
  (B : (n : ℕ) → Basis (Fin n) ℚ (Fin n → ℚ)) (C : (n : ℕ) → Basis (Fin n) ℝ (Fin n → ℝ))

local notation "e" => FiniteSAdeleRing.embedding R K

instance piReal_locallyCompact : LocallyCompactSpace (Fin n → ℝ) := Pi.locallyCompactSpace_of_finite

instance : LocallyCompactSpace ((w : S) → w.val.adicCompletion K)
  := Pi.locallyCompactSpace_of_finite

instance : LocallyCompactSpace ((w : {v // v ∉ S}) → w.val.adicCompletionIntegers K)
  := Pi.locallyCompactSpace

instance : LocallyCompactSpace (SProdAdicCompletionIntegers R K S)
  := Prod.locallyCompactSpace
    ((w : S) → w.val.adicCompletion K)
    ((w : {v // v ∉ S}) → w.val.adicCompletionIntegers K)

instance : LocallyCompactSpace (SProdAdicCompletionIntegers' R K S)
  := Homeomorph.locallyCompactSpace (SProdAdicCompletionIntegers.homeomorph R K S)

theorem locallyCompact_finiteSAdeleRing (S : Finset (HeightOneSpectrum R)) : LocallyCompactSpace (FiniteSAdeleRing.finiteSAdeleRing R K S) := by
  exact Homeomorph.locallyCompactSpace (FiniteSAdeleRing.homeomorph_piSubtypeProd R K S)

theorem locallyCompact_adeleRing
  : @LocallyCompactSpace (adeleRing R K) (DedekindDomain.AdeleRing.topologicalSpace R K B C) := by
  have locallyCompact_finiteAdeleRing : LocallyCompactSpace (finiteAdeleRing R K) := by
    have local_compact_nhds : ∀ (x : finiteAdeleRing R K), ∀ n ∈ nhds x, ∃ s ∈ nhds x, s ⊆ n ∧ IsCompact s := by
      {
        intros x N hN
        set setS := setOf (λ (v : HeightOneSpectrum R) => x.val v ∉ v.adicCompletionIntegers K)
        have hS : setS.Finite := Filter.eventually_cofinite.1 ((mem_finiteAdeleRing_iff x.val).1 x.property)
        set S := hS.toFinset
        set A_K_S := FiniteSAdeleRing.finiteSAdeleRing R K S

        have hx : x.val ∈ A_K_S := by
          {
            intros v hv
            rwa [hS.mem_toFinset, Set.nmem_setOf_iff, not_not] at hv
          }

        obtain ⟨U, hU, hUOpen, hxU⟩ := mem_nhds_iff.1 hN
        set U_S := (e S) ⁻¹' U
        have he : e S ⟨x, hx⟩ = x := rfl
        have hU_S : U_S ∈ nhds ⟨x, hx⟩ := by
        {
          rw [mem_nhds_iff]
          use U_S
          use subset_rfl
          use (OpenEmbedding.continuous (FiniteSAdeleRing.embeddingOpen R K S)).isOpen_preimage U hUOpen
          exact hxU
        }
        obtain ⟨N', hN', hNU', hNC'⟩ := (locallyCompact_finiteSAdeleRing R K S).local_compact_nhds ⟨x, hx⟩ U_S hU_S
        obtain ⟨V, hV, hVOpen, hxV⟩ := mem_nhds_iff.1 hN'
        use (e S) '' N'
        apply And.intro
        {
          rw [mem_nhds_iff]
          use (e S) '' V
          rw [Set.image_subset_image_iff (FiniteSAdeleRing.embeddingOpen R K S).inj]
          use hV
          use OpenEmbedding.isOpenMap (FiniteSAdeleRing.embeddingOpen R K S) V hVOpen
          use ⟨x, hx⟩
        }
        apply And.intro
        {
          apply subset_trans _ hU
          simp
          exact hNU'
        }
        {
          rwa [← Embedding.isCompact_iff ((openEmbedding_iff _).1 (FiniteSAdeleRing.embeddingOpen R K S)).1]
        }
      }
    exact ⟨local_compact_nhds⟩

  have locallyCompact_infiniteAdeleRing : @LocallyCompactSpace (infiniteAdeleRing K) (InfiniteAdeleRing.topologicalSpace K B C) := by
    have h := (@piReal_locallyCompact (FiniteDimensional.finrank ℚ K)).local_compact_nhds
    apply @LocallyCompactSpace.mk _ (InfiniteAdeleRing.topologicalSpace K B C)
    intro x N hN
    rw [nhds_induced] at hN
    simp at hN
    obtain ⟨M, hM, hMN⟩ := hN
    obtain ⟨T, hT, hTM, hTC⟩ := h ((InfiniteAdeleRing.real_tensorProduct_numberField_equiv K B C) x) M hM
    use (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K B C) ⁻¹' T
    refine' ⟨_, _, _⟩
    {
      rw [nhds_induced]
      simp
      use T
    }
    {
      apply subset_trans _ hMN
      rw [← LinearEquiv.coe_toEquiv]
      exact (Equiv.preimage_subset (LinearEquiv.toEquiv (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K B C)) _ _).2 hTM
    }
    {
      rw [← LinearEquiv.image_symm_eq_preimage (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K B C) T]
      apply @IsCompact.image _ _ _ (InfiniteAdeleRing.topologicalSpace K B C) _ _ hTC
      have h' : InfiniteAdeleRing.topologicalSpace K B C = TopologicalSpace.induced (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K B C).toEquiv (InfiniteAdeleRing.piReal_topologicalSpace (FiniteDimensional.finrank ℚ K)) := rfl
      rw [← Equiv.coinduced_symm (InfiniteAdeleRing.real_tensorProduct_numberField_equiv K B C).toEquiv] at h'
      rw [h']
      exact continuous_coinduced_rng
    }

  exact @Prod.locallyCompactSpace (infiniteAdeleRing K) (finiteAdeleRing R K) (InfiniteAdeleRing.topologicalSpace K B C) _ _ _
end LocallyCompact
