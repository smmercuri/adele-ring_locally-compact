/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib
import AdeleRingLocallyCompact.NumberTheory.NumberField.Completion
import AdeleRingLocallyCompact.Algebra.Ring.Equiv

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

theorem equiv_mixedSpace_symm_toFun :
    ⇑(equiv_mixedSpace K).symm = fun x : E => (fun v : InfinitePlace K => if hv : v.IsReal then
      (equiv_real_of_isReal hv).symm (x.1 ⟨v, hv⟩) else
        (equiv_complex_of_isComplex (not_isReal_iff_isComplex.1 hv)).symm <| x.2
          ⟨v, not_isReal_iff_isComplex.1 hv⟩) := rfl

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
def basis_equiv : (Fin (FiniteDimensional.finrank K L) → K) ≃ₗ[K] L :=
  LinearEquiv.symm (Basis.equivFun (FiniteDimensional.finBasis K L))

def tensorProduct_to_pi (n : ℕ) : (TensorProduct K (InfiniteAdeleRing K) (Fin n → K))
    →ₗ[InfiniteAdeleRing K] (Fin n → InfiniteAdeleRing K) :=
  (Algebra.TensorProduct.basis (InfiniteAdeleRing K) (Pi.basisFun K (Fin n))).constr
    (InfiniteAdeleRing K) (Pi.basisFun (InfiniteAdeleRing K) _)

def pi_to_tensorProduct (n : ℕ) : (Fin n → InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K]
    (TensorProduct K (InfiniteAdeleRing K) (Fin n → K)) :=
  (Pi.basisFun (InfiniteAdeleRing K) _).constr K
    (Algebra.TensorProduct.basis (InfiniteAdeleRing K) (Pi.basisFun K (Fin n)))

def tensorProduct_equiv_pi' (n : ℕ) : (TensorProduct K (InfiniteAdeleRing K) (Fin n → K))
    ≃ₗ[InfiniteAdeleRing K] (Fin n → InfiniteAdeleRing K) where
  toFun := tensorProduct_to_pi K n
  invFun := pi_to_tensorProduct K n
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LinearMap.coe_comp,
      ← @LinearMap.id_coe (InfiniteAdeleRing K)]
    have h : pi_to_tensorProduct K n ∘ₗ tensorProduct_to_pi K n = LinearMap.id := by
      apply Basis.ext (Algebra.TensorProduct.basis (InfiniteAdeleRing K) (Pi.basisFun K (Fin n)))
      intro i
      simp only [LinearMap.comp_apply, Algebra.TensorProduct.basis_apply, Pi.basisFun_apply,
        LinearMap.id_coe, id_eq, pi_to_tensorProduct, tensorProduct_to_pi,
        Basis.constr_apply_fintype, Basis.equivFun_apply,
        Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply, Pi.basisFun_repr,
        LinearMap.stdBasis_apply', RingHom.map_ite_one_zero, Pi.basisFun_apply, ite_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.basisFun_equivFun,
        LinearEquiv.refl_apply, Algebra.TensorProduct.basis_apply]
    rw [h]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LinearMap.coe_comp,
      ← @LinearMap.id_coe (InfiniteAdeleRing K)]
    have h : tensorProduct_to_pi K n ∘ₗ pi_to_tensorProduct K n = LinearMap.id := by
      apply Basis.ext (Pi.basisFun (InfiniteAdeleRing K) _)
      intro i
      simp only [LinearMap.comp_apply, Algebra.TensorProduct.basis_apply, Pi.basisFun_apply,
        LinearMap.id_coe, id_eq, pi_to_tensorProduct, tensorProduct_to_pi,
        Basis.constr_apply_fintype, Basis.equivFun_apply,
        Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply, Pi.basisFun_repr,
        LinearMap.stdBasis_apply', RingHom.map_ite_one_zero, Pi.basisFun_apply, ite_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.basisFun_equivFun,
        LinearEquiv.refl_apply, Algebra.TensorProduct.basis_apply]
    rw [h]
  map_add' _ _ := by simp only [map_add]
  map_smul' _ _ := by simp only [LinearMapClass.map_smul, RingHom.id_apply]

def tensorProduct_equiv_pi : (TensorProduct K (InfiniteAdeleRing K) L) ≃
    (Fin (FiniteDimensional.finrank K L) → InfiniteAdeleRing K) :=
  Equiv.trans (TensorProduct.congr
      (LinearEquiv.refl K (InfiniteAdeleRing K)) (basis_equiv _ _).symm).toEquiv
    (tensorProduct_equiv_pi' _ _).toEquiv

instance : TopologicalSpace (TensorProduct K (InfiniteAdeleRing K) L) :=
  TopologicalSpace.induced (tensorProduct_equiv_pi K L) inferInstance

def tensorProduct_homeomorph_pi : (TensorProduct K (InfiniteAdeleRing K) L) ≃ₜ
    (Fin (FiniteDimensional.finrank K L) → InfiniteAdeleRing K) where
  toEquiv := tensorProduct_equiv_pi K L
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    simp only [Equiv.invFun_as_coe]
    convert continuous_coinduced_rng
    rw [Equiv.coinduced_symm]
    rfl

/- We show that ℝ^r₁ × ℂ^r₂ is homeomorphic to ℝ^[K : ℚ] -/

def mixedSpace_equiv_pi : E ≃ (Fin (FiniteDimensional.finrank ℚ K) → ℝ) := by
  apply Equiv.trans (Equiv.prodCongr (Equiv.refl _) <|
    Equiv.piCongrRight (fun _ => Complex.equivRealProd))
  have : ((v : {w : InfinitePlace K // w.IsComplex}) → ℝ × ℝ) ≃
      (((_ : {w : InfinitePlace K // w.IsComplex}) × Fin 2) → ℝ) := by
    apply Equiv.symm
    apply Equiv.trans
      (Equiv.piCurry <| fun (_ : {w : InfinitePlace K // w.IsComplex}) (_ : Fin 2) => ℝ)
    exact Equiv.piCongrRight (fun _ => piFinTwoEquiv _)
  apply Equiv.trans (Equiv.prodCongr (Equiv.refl _) this)
  apply Equiv.trans (Equiv.sumArrowEquivProdArrow _ _ _).symm
  apply Equiv.piCongr _ (fun _ => Equiv.refl ℝ)
  apply Fintype.equivOfCardEq
  rw [← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank, NrRealPlaces, NrComplexPlaces]
  rw [Fintype.card_sum, Fintype.card_sigma, Finset.sum_const, mul_comm]
  simp only [Fintype.card_fin]
  rfl

def Homeomorph.piCurry {α : Type*} {β : α → Type*} (γ : (a : α) → β a → Type*)
    [t : (a : α) → (b : β a) → TopologicalSpace (γ a b)] :
    ((x : (i : α) × β i) → γ x.1 x.2) ≃ₜ ((a : α) → (b : β a) → γ a b) where
  toEquiv := Equiv.piCurry _
  continuous_toFun := by
    exact continuous_pi (fun _ => continuous_pi <| fun _ => continuous_apply _)
  continuous_invFun := by
    refine continuous_pi (fun ⟨x, y⟩ => ?_)
    simp [Equiv.piCurry, Sigma.uncurry]
    exact Continuous.comp' (continuous_apply _) (continuous_apply _)

variable (α β γ : Type*) [TopologicalSpace γ]
def Homeomorph.sumArrowEquivProdArrow : (α ⊕ β → γ) ≃ₜ (α → γ) × (β → γ) where
  toEquiv := Equiv.sumArrowEquivProdArrow _ _ _
  continuous_toFun := by
    simp [Equiv.sumArrowEquivProdArrow]
    apply And.intro
    · apply continuous_pi
      intro i
      apply continuous_apply
    · apply continuous_pi
      intro i
      apply continuous_apply
  continuous_invFun := by
    simp [Equiv.sumArrowEquivProdArrow]
    apply continuous_pi
    intro i
    cases i with
    | inl val =>
      simp_all only [Sum.elim_inl]
      fun_prop
    | inr val_1 =>
      simp_all only [Sum.elim_inr]
      fun_prop

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

def baseChange : (TensorProduct K (InfiniteAdeleRing K) L) ≃ InfiniteAdeleRing L := by
  apply Equiv.trans (tensorProduct_equiv_pi K L)
  apply Equiv.trans <| Equiv.piCongrRight (fun _ => (equiv_mixedSpace K).toEquiv)
  apply Equiv.trans <| Equiv.piCongrRight (fun _ => (mixedSpace_equiv_pi K))
  apply Equiv.trans (Equiv.piCurry _).symm
  apply Equiv.trans ?_ (equiv_mixedSpace L).symm.toEquiv
  apply Equiv.trans ?_ (mixedSpace_equiv_pi L).symm
  apply Equiv.piCongrLeft (fun _ => ℝ)
  apply Fintype.equivOfCardEq
  simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [mul_comm]
  rw [FiniteDimensional.finrank_mul_finrank ℚ K L]

def baseChange_homeomorph : (TensorProduct K (InfiniteAdeleRing K) L) ≃ₜ InfiniteAdeleRing L := by
  apply Homeomorph.trans (tensorProduct_homeomorph_pi K L)
  apply Homeomorph.trans <| Homeomorph.piCongrRight (fun _ => (homeomorph_mixedSpace K))
  apply Homeomorph.trans <| Homeomorph.piCongrRight (fun _ => (mixedSpace_homeomorph_pi K))
  apply Homeomorph.trans (Homeomorph.piCurry _).symm
  apply Homeomorph.trans ?_ (homeomorph_mixedSpace L).symm
  apply Homeomorph.trans ?_ (mixedSpace_homeomorph_pi L).symm
  apply @Homeomorph.piCongrLeft _ _ (fun _ => ℝ) _
  apply Fintype.equivOfCardEq
  simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [mul_comm]
  rw [FiniteDimensional.finrank_mul_finrank ℚ K L]

end InfiniteAdeleRing

end NumberField
