/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib
import AdeleRingLocallyCompact.NumberTheory.NumberField.Completion
import AdeleRingLocallyCompact.Algebra.Ring.Equiv
import AdeleRingLocallyCompact.Topology.Homeomorph

open scoped TensorProduct

/-!
# Infinite adele ring

This file formalises the definition of the infinite adele ring of a number field `K` as the
product of completions of `K` over its infinite places. The definition of the completions are
formalised in [AdeleRingLocallyCompact.NumberTheory.NumberField.Completion](Completion.lean).

We show that the infinite adele ring is locally compact and that it is isomorphic to the
space `ℝ ^ r₁ × ℂ ^ r₂` used in `Mathlib.NumberTheory.NumberField.mixedEmbedding`.

## Main definitions
 - `NumberField.InfiniteAdeleRing` of a number field `K` is defined as the product of
   the completions of `K` over its Archimedean places.
 - `NumberField.InfiniteAdeleRing.globalEmbedding` is the map sending `x ∈ K` to `(x)ᵥ`.
 - `NumberField.InfiniteAdeleRing.equiv_mixedSpace` is the ring isomorphism between
   the infinite adele ring of `K` and `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature
   of `K`.

## Main results
 - `NumberField.InfiniteAdeleRing.locallyCompactSpace` : the infinite adele ring is a
   locally compact space.
 - `NumberField.InfiniteAdeleRing.mixedEmbedding_eq_globalEmbedding_comp` : applying the
   ring isomorphism of `equiv_mixedSpace` to a globally embedded `(x)ᵥ` in the infinite adele
   ring, where `x ∈ K`, is the same as applying the embedding `K → ℝ ^ r₁ × ℂ ^ r₂` given by
   `NumberField.mixedEmbedding` to `x`.


## References
 * [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
infinite adele ring, number field
-/

noncomputable section

namespace NumberField

open InfinitePlace InfinitePlace.Completion AbsoluteValue.Completion

open scoped Classical

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

/-- The infinite adele ring of a number field. -/
def InfiniteAdeleRing := (v : InfinitePlace K) → v.completion

namespace InfiniteAdeleRing

section DerivedInstances

instance : CommRing (InfiniteAdeleRing K) := Pi.commRing

instance : Inhabited (InfiniteAdeleRing K) := ⟨0⟩

instance : Nontrivial (InfiniteAdeleRing K) :=
  (inferInstanceAs <| Nonempty (InfinitePlace K)).elim fun w => Pi.nontrivial_at w

end DerivedInstances

instance : TopologicalSpace (InfiniteAdeleRing K) := Pi.topologicalSpace

instance : TopologicalRing (InfiniteAdeleRing K) := Pi.instTopologicalRing

instance : Algebra K (InfiniteAdeleRing K) := Pi.algebra _ _

/-- The global embedding of a number field into its infinite adele ring,
sending `x ∈ K` to `(x)ᵥ`. -/
abbrev globalEmbedding : K →+* InfiniteAdeleRing K := algebraMap K (InfiniteAdeleRing K)

@[simp]
theorem globalEmbedding_apply (x : K) : globalEmbedding K x v = x := rfl

/-- The infinite adele ring is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (InfiniteAdeleRing K) :=
  Pi.locallyCompactSpace_of_finite

local notation "E" =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)
/-- The ring isomorphism between the infinite adele ring of a number field and the
space `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature of the number field. -/
abbrev equiv_mixedSpace :
    InfiniteAdeleRing K ≃+*
      ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ) :=
  RingEquiv.trans
    (RingEquiv.piEquivPiSubtypeProd (fun (v : InfinitePlace K) => IsReal v)
      (fun (v : InfinitePlace K) => v.completion))
    (RingEquiv.prodCongr
      (RingEquiv.piCongrRight (fun ⟨_, hv⟩ => Completion.equiv_real_of_isReal hv))
      (RingEquiv.trans
        (RingEquiv.piCongrRight (fun v => Completion.equiv_complex_of_isComplex
          ((not_isReal_iff_isComplex.1 v.2))))
        (RingEquiv.piCongrLeft (fun _ => ℂ) <|
          Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex))))

def homeomorph_mixedSpace : InfiniteAdeleRing K ≃ₜ
    ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ) := by
  apply Homeomorph.trans
    (Homeomorph.piEquivPiSubtypeProd (fun (v : InfinitePlace K) => IsReal v)
      (fun (v : InfinitePlace K) => v.completion))
    (Homeomorph.prodCongr
      (Homeomorph.piCongrRight
        (fun ⟨_, hv⟩ => (Completion.isometryEquiv_real_of_isReal hv).toHomeomorph))
      (Homeomorph.trans
        (Homeomorph.piCongrRight (fun v => Completion.isometryEquiv_complex_of_isComplex
          ((not_isReal_iff_isComplex.1 v.2)) |>.toHomeomorph))
          (@Homeomorph.piCongrLeft _ _ (fun _ => ℂ ) _ <|
            Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex))))

@[simp]
theorem equiv_mixedSpace_apply (x : InfiniteAdeleRing K) :
    equiv_mixedSpace K x =
      (fun (v : {w : InfinitePlace K // IsReal w}) => extensionEmbedding_of_isReal v.2 (x v),
       fun (v : {w : InfinitePlace K // IsComplex w}) => extensionEmbedding v.1 (x v)) := rfl

/-- Transfers the global embedding of `x ↦ (x)ᵥ` of the number field `K` into its infinite adele
ring to the mixed embedding `x ↦ (φᵢ(x))ᵢ` of `K` into the space `ℝ ^ r₁ × ℂ ^ r₂`, where
`(r₁, r₂)` is the signature of `K` and `φᵢ` are the complex embeddings of `K`. -/
theorem mixedEmbedding_eq_globalEmbedding_comp {x : K} :
    mixedEmbedding K x = equiv_mixedSpace K (globalEmbedding K x) := by
  ext ⟨v, hv⟩ <;> simp only [equiv_mixedSpace_apply, globalEmbedding_apply,
    equiv_real_of_isReal, equiv_complex_of_isComplex, extensionEmbedding,
    extensionEmbedding_of_isReal, extensionEmbedding_of_comp, RingEquiv.coe_ofBijective,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, UniformSpace.Completion.extensionHom]
  · rw [UniformSpace.Completion.extension_coe
      (WithAbs.uniformInducing_of_comp <| abs_of_isReal_eq_comp hv).uniformContinuous x]
    rfl
  · rw [UniformSpace.Completion.extension_coe
      (WithAbs.uniformInducing_of_comp <| abs_eq_comp v).uniformContinuous x]
    rfl

variable (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

/- We show that 𝔸_K ⊗[K] L is homeomorphic to (𝔸_K)^[L : K]. -/
def tensorProduct_equiv_pi : InfiniteAdeleRing K ⊗[K] L ≃ₗ[K]
    (Fin (FiniteDimensional.finrank K L) → InfiniteAdeleRing K) :=
  LinearEquiv.trans (TensorProduct.congr (LinearEquiv.refl K (InfiniteAdeleRing K))
      (Basis.equivFun (FiniteDimensional.finBasis K L)))
    (TensorProduct.piScalarRight _ _ _ _)

instance : TopologicalSpace (InfiniteAdeleRing K ⊗[K] L) :=
  TopologicalSpace.induced (tensorProduct_equiv_pi K L) inferInstance

def tensorProduct_continuousLinearEquiv_pi : InfiniteAdeleRing K ⊗[K] L ≃L[K]
    (Fin (FiniteDimensional.finrank K L) → InfiniteAdeleRing K) where
  toLinearEquiv := tensorProduct_equiv_pi K L
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    convert (tensorProduct_equiv_pi K L).toEquiv.coinduced_symm ▸ continuous_coinduced_rng

/- We show that ℝ^r₁ × ℂ^r₂ is homeomorphic to ℝ^[K : ℚ] -/

def mixedSpace_homeomorph_pi : E ≃ₜ (Fin (FiniteDimensional.finrank ℚ K) → ℝ) := by
  apply Homeomorph.trans (Homeomorph.prodCongr (Homeomorph.refl _) <|
    Homeomorph.piCongrRight (fun _ => Complex.equivRealProdCLM.toHomeomorph))
  have : ((v : {w : InfinitePlace K // w.IsComplex}) → ℝ × ℝ) ≃ₜ
      (((_ : {w : InfinitePlace K // w.IsComplex}) × Fin 2) → ℝ) := by
    apply Homeomorph.symm
    apply Homeomorph.trans
      (Homeomorph.piCurry <| fun (_ : {w : InfinitePlace K // w.IsComplex}) (_ : Fin 2) => ℝ)
    exact Homeomorph.piCongrRight (fun _ => Homeomorph.piFinTwo _)
  apply Homeomorph.trans (Homeomorph.prodCongr (Homeomorph.refl _) this)
  apply Homeomorph.trans (Homeomorph.sumArrowEquivProdArrow _ _ _).symm
  apply Homeomorph.piCongr _ (fun _ => Homeomorph.refl ℝ)
  apply Fintype.equivOfCardEq
  rw [← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank, NrRealPlaces, NrComplexPlaces]
  rw [Fintype.card_sum, Fintype.card_sigma, Finset.sum_const, mul_comm]
  simp only [Fintype.card_fin]
  rfl

/- Now put these together to show base change -/
/- TODO: this should be a continuous algebra equivalence -/
def baseChange : InfiniteAdeleRing K ⊗[K] L ≃ₜ InfiniteAdeleRing L := by
  apply Homeomorph.trans (tensorProduct_continuousLinearEquiv_pi K L).toHomeomorph
  apply Homeomorph.trans <| Homeomorph.piCongrRight (fun _ => (homeomorph_mixedSpace K))
  apply Homeomorph.trans <| Homeomorph.piCongrRight (fun _ => (mixedSpace_homeomorph_pi K))
  apply Homeomorph.trans (Homeomorph.piCurry _).symm
  apply Homeomorph.trans ?_ (homeomorph_mixedSpace L).symm
  apply Homeomorph.trans ?_ (mixedSpace_homeomorph_pi L).symm
  apply @Homeomorph.piCongrLeft _ _ (fun _ => ℝ) _
  apply Fintype.equivOfCardEq
  simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [mul_comm, FiniteDimensional.finrank_mul_finrank]

def baseChange' : InfiniteAdeleRing K ⊗[K] L ≃+* InfiniteAdeleRing L where
  toEquiv := baseChange K L
  map_mul' _ _ := sorry
  map_add' _ _ := sorry

/- New strategy! because I cannot get a ring equiv, or an algebra equiv out of above
(because ℂ is not ring equiv to ℝ × ℝ !). -/

/- 𝔸_K ⊗[K] L = (Πᵥ Kᵥ) ⊗[K] L ≃+* Πᵥ (Kᵥ ⊗[K] L).-/
-- This is the Pi version of TensorProduct.prodLeft
def piLeft : InfiniteAdeleRing K ⊗[K] L ≃+* ((v : InfinitePlace K) → v.completion ⊗[K] L) :=
  sorry

/- Now we need to show that each Kᵥ ⊗[K] L ≃+* Π_{w ∣ v} L_w, where w ∣ v means that
v = w.comap (algebraMap K L). -/
def NumberField.Completion.baseChange (v : InfinitePlace K) :
  v.completion ⊗[K] L ≃+*
    ((w : {w : InfinitePlace L // v = w.comap (algebraMap K L)}) → w.1.completion) := sorry

def NumberField.InfinitePlace.card_comap :
  Fintype.card { w : InfinitePlace L // v = w.comap (algebraMap K L) } =
    FiniteDimensional.finrank K L :=
  sorry

/- Then we show that
  InfinitePlace L ≃ (v : InfinitePlace K) → { w // v = w.comap (algebraMap K L)},
AS TYPES.

Can prove this by a cardinality argument with current results in mathlib. -/
def NumberField.Completion.equiv_comap :
    InfinitePlace L ≃
      ((v : InfinitePlace K) × { w : InfinitePlace L // v = w.comap (algebraMap K L)}) := by
  apply Fintype.equivOfCardEq
  norm_num
  haveI : IsUnramifiedAtInfinitePlaces K L := sorry
  haveI : IsGalois K L := sorry
  rw [IsUnramifiedAtInfinitePlaces.card_infinitePlace K L]
  simp_rw [InfinitePlace.card_comap]
  norm_num

theorem NumberField.Completion.equiv_comap_apply :
    (NumberField.Completion.equiv_comap K L).symm i = i.2.1 := sorry

/- Then piece together 𝔸_K ⊗[K] L ≃+* Πᵥ (Kᵥ ⊗[K] L) ≃+* Πᵥ Π_{w ∣ v} L_w ≃+* Π_w L_w = 𝔸_L. -/
def baseChange'' : InfiniteAdeleRing K ⊗[K] L ≃+* InfiniteAdeleRing L := by
  apply RingEquiv.trans (piLeft K L)
  have := RingEquiv.piCongrRight <| NumberField.Completion.baseChange K L
  apply RingEquiv.trans this
  let γ : (v : InfinitePlace K) → (w : {w : InfinitePlace L // v = w.comap (algebraMap K L)})
      → Type _ :=
    fun v w => w.1.completion
  apply RingEquiv.trans (RingEquiv.piCurry γ).symm
  have := RingEquiv.piCongrLeft (fun w => w.completion)
    (NumberField.Completion.equiv_comap K L).symm
  refine RingEquiv.trans ?_ this
  apply RingEquiv.piCongrRight
  intro i
  rw [NumberField.Completion.equiv_comap_apply]
  rfl


end InfiniteAdeleRing

end NumberField
