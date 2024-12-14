/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import AdeleRingLocallyCompact.NumberTheory.NumberField.Completion
import AdeleRingLocallyCompact.Algebra.Ring.Equiv
import AdeleRingLocallyCompact.FromMathlib.Algebra.Order.GroupWithZero.Unbundled
import AdeleRingLocallyCompact.FromMathlib.Analysis.SpecialFunctions.Pow.Real
import AdeleRingLocallyCompact.FromMathlib.Data.Fin.Lemmas
import AdeleRingLocallyCompact.FromMathlib.LinearAlgebra.TensorProduct.Pi
import AdeleRingLocallyCompact.Topology.Algebra.Algebra
import AdeleRingLocallyCompact.Topology.Algebra.UniformRing
import AdeleRingLocallyCompact.Topology.Homeomorph

open scoped TensorProduct Classical Topology

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
 - `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace` is the ring isomorphism between
   the infinite adele ring of `K` and `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature
   of `K`.

## Main results
 - `NumberField.InfiniteAdeleRing.locallyCompactSpace` : the infinite adele ring is a
   locally compact space.
 - `NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp` : applying the
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

instance : CommRing (InfiniteAdeleRing K) := Pi.commRing

instance : Inhabited (InfiniteAdeleRing K) := ⟨0⟩

instance : Nontrivial (InfiniteAdeleRing K) :=
  (inferInstanceAs <| Nonempty (InfinitePlace K)).elim fun w => Pi.nontrivial_at w

instance : TopologicalSpace (InfiniteAdeleRing K) := Pi.topologicalSpace

instance : TopologicalRing (InfiniteAdeleRing K) := Pi.instTopologicalRing

instance : Algebra K (InfiniteAdeleRing K) := Pi.algebra _ _

@[simp]
theorem algebraMap_apply (x : K) : algebraMap K (InfiniteAdeleRing K) x v = x := rfl

/-- The infinite adele ring is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (InfiniteAdeleRing K) :=
  Pi.locallyCompactSpace_of_finite

local notation "E" =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)
/-- The ring isomorphism between the infinite adele ring of a number field and the
space `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature of the number field. -/
def ringEquiv_mixedSpace :
    InfiniteAdeleRing K ≃+*
      ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ) :=
  RingEquiv.trans
    (RingEquiv.piEquivPiSubtypeProd (fun (v : InfinitePlace K) => IsReal v)
      (fun (v : InfinitePlace K) => v.completion))
    (RingEquiv.prodCongr
      (RingEquiv.piCongrRight (fun ⟨_, hv⟩ => Completion.ringEquiv_real_of_isReal hv))
      (RingEquiv.trans
        (RingEquiv.piCongrRight (fun v => Completion.ringEquiv_complex_of_isComplex
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
theorem ringEquiv_mixedSpace_apply (x : InfiniteAdeleRing K) :
    ringEquiv_mixedSpace K x =
      (fun (v : {w : InfinitePlace K // IsReal w}) =>
        ringEquiv_real_of_isReal v.2 (x v),
      fun (v : {w : InfinitePlace K // IsComplex w}) =>
        ringEquiv_complex_of_isComplex v.2 (x v)) :=
  rfl

/-- Transfers the embedding of `x ↦ (x)ᵥ` of the number field `K` into its infinite adele
ring to the mixed embedding `x ↦ (φᵢ(x))ᵢ` of `K` into the space `ℝ ^ r₁ × ℂ ^ r₂`, where
`(r₁, r₂)` is the signature of `K` and `φᵢ` are the complex embeddings of `K`. -/
theorem mixedEmbedding_eq_algebraMap_comp {x : K} :
    mixedEmbedding K x = ringEquiv_mixedSpace K (algebraMap K (InfiniteAdeleRing K) x) := by
  ext v <;> simp only [ringEquiv_mixedSpace_apply, algebraMap_apply, ringEquiv_real_of_isReal,
    ringEquiv_complex_of_isComplex, extensionEmbedding, extensionEmbedding_of_isReal,
    extensionEmbedding_of_comp, RingEquiv.coe_ofBijective, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, UniformSpace.Completion.extensionHom]
  · rw [UniformSpace.Completion.extension_coe
      (WithAbs.uniformInducing_of_comp <| v.1.norm_embedding_of_isReal v.2).uniformContinuous x]
    rfl
  · rw [UniformSpace.Completion.extension_coe
      (WithAbs.uniformInducing_of_comp <| v.1.norm_embedding_eq).uniformContinuous x]
    rfl

variable (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

/- We show that 𝔸_K ⊗[K] L is homeomorphic to (𝔸_K)^[L : K]. -/
def tensorProduct_equiv_pi : InfiniteAdeleRing K ⊗[K] L ≃ₗ[K]
    (Fin (FiniteDimensional.finrank K L) → InfiniteAdeleRing K) :=
  LinearEquiv.trans (TensorProduct.congr (LinearEquiv.refl K (InfiniteAdeleRing K))
      (Basis.equivFun (FiniteDimensional.finBasis K L)))
    (TensorProduct.piScalarRight _ _ _ _)

/-instance : TopologicalSpace (InfiniteAdeleRing K ⊗[K] L) :=
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
def baseChange_old : InfiniteAdeleRing K ⊗[K] L ≃ₜ InfiniteAdeleRing L := by
  apply Homeomorph.trans (tensorProduct_continuousLinearEquiv_pi K L).toHomeomorph
  apply Homeomorph.trans <| Homeomorph.piCongrRight (fun _ => (homeomorph_mixedSpace K))
  apply Homeomorph.trans <| Homeomorph.piCongrRight (fun _ => (mixedSpace_homeomorph_pi K))
  apply Homeomorph.trans (Homeomorph.piCurry _).symm
  apply Homeomorph.trans ?_ (homeomorph_mixedSpace L).symm
  apply Homeomorph.trans ?_ (mixedSpace_homeomorph_pi L).symm
  apply @Homeomorph.piCongrLeft _ _ (fun _ => ℝ) _
  apply Fintype.equivOfCardEq
  simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [mul_comm, FiniteDimensional.finrank_mul_finrank]-/

/- New strategy! because I cannot get a ring equiv, or an algebra equiv out of above
(because ℂ is not ring equiv to ℝ × ℝ !). -/

/- K-algebra isomorphisms: 𝔸_K ⊗[K] L =ₐ[K] (Πᵥ Kᵥ) ⊗[K] L ≃ₐ[K] Πᵥ (Kᵥ ⊗[K] L).-/

def AlgEquiv.piRight (R S A : Type*) {ι : Type*}  (B : ι → Type*) [CommSemiring R]
    [CommSemiring S] [Algebra R S] [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [(i : ι) → Semiring (B i)] [(i : ι) → Algebra R (B i)] [Fintype ι] [DecidableEq ι] :
    A ⊗[R] ((i : ι) → B i) ≃ₐ[S] (i : ι) → A ⊗[R] (B i) := by
  /-set f : @LinearEquiv S S _ _ _ _ _ _ _ ((i : ι) → A ⊗[R] B i) _
      NonUnitalNonAssocSemiring.toAddCommMonoid _ Algebra.toModule := TensorProduct.piRight R S A B
  apply Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct f
  · intro a₁ a₂ b₁ b₂
    simp only [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, f]
    simp_rw [Pi.mul_apply]
    rw [Pi.mul_def]
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul]
  · rfl-/
  apply AlgEquiv.ofLinearEquiv (TensorProduct.piRight R S A B)
  · rfl
  · have h := @LinearMap.map_mul_iff S (A ⊗[R] ((i : ι) → B i)) ((i : ι) → A ⊗[R] (B i)) _ _ _ _ _
      (TensorProduct.piRight R S A B)
    have (x : _) : (TensorProduct.piRight R S A B) x = (TensorProduct.piRightHom R S A B) x := rfl
    simp_rw [this]
    simp_rw [DFunLike.coe] at h
    have : (TensorProduct.piRight R S A B).toLinearMap.toFun = TensorProduct.piRightHom R S A B :=
      rfl
    rw [this] at h
    rw [h]
    ext
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.coe_comp,
      LinearMap.coe_single, Function.comp_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.compr₂_apply, LinearMap.mul_apply',
      Algebra.TensorProduct.tmul_mul_tmul, LinearEquiv.coe_coe, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul, Pi.mul_apply, LinearMap.compl₂_apply]

def piLeft_algEquiv : InfiniteAdeleRing K ⊗[K] L ≃ₐ[K]
    ((v : InfinitePlace K) → v.completion ⊗[K] L) := by
  apply AlgEquiv.trans (Algebra.TensorProduct.comm _ _ _)
  apply AlgEquiv.trans (AlgEquiv.piRight _ _ _ _)
  exact AlgEquiv.piCongrRight <| fun _ => Algebra.TensorProduct.comm _ _ _

  /-apply uniformContinuous_of_tendsto_zero
  rw [Metric.nhds_basis_closedBall.tendsto_iff Metric.nhds_basis_closedBall]
  refine fun ε _ => ⟨ε, ‹_›, fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, WithAbs.norm_eq _, ← h] at hx ⊢
  exact hx-/

variable (w : InfinitePlace L)

local notation "Σ_" v => {w : InfinitePlace L // w.comap (algebraMap K L) = v}

/- Now establish `Kᵥ`-algebra isomorphisms (Note completion as base field now)
Kᵥ ⊗[K] L ≃ₐ[v.completion] Π_{w ∣ v} L_w, where w ∣ v means that
v = w.comap (algebraMap K L). -/

def ContinuousAlgHom.extendScalars {A : Type*} (B : Type*) {C D : Type*}
    [CommSemiring A] [CommSemiring C] [CommSemiring D] [TopologicalSpace C]
    [TopologicalSpace D] [Algebra A C] [Algebra A D] [CommSemiring B] [Algebra A B]
    [Algebra B C] [IsScalarTower A B C] (f : C →A[A] D) :
    letI : Algebra B D := f.restrictDomain B |>.toRingHom.toAlgebra
    C →A[B] D :=
  letI : Algebra B D := f.restrictDomain B |>.toRingHom.toAlgebra
  {
    __ := f.toAlgHom.extendScalars B
    cont := f.cont
  }

def ContinuousAlgEquiv.restrictScalars (A : Type*) {B : Type*} {C D : Type*}
    [CommSemiring A] [CommSemiring C] [CommSemiring D] [TopologicalSpace C]
    [TopologicalSpace D] [CommSemiring B]  [Algebra B C] [Algebra B D] [Algebra A B]
    [Algebra A C] [Algebra A D] [IsScalarTower A B C] [IsScalarTower A B D] (f : C ≃A[B] D) :
    C ≃A[A] D where
  __ := f.toAlgEquiv.restrictScalars A
  continuous_toFun := f.continuous_toFun
  continuous_invFun := f.continuous_invFun

def NumberField.Completion.comap_extend {v : InfinitePlace K} (w : Σ_v) :
    v.completion →A[v.completion] w.1.completion :=
  ContinuousAlgHom.extendScalars v.completion (comap w)

def NumberField.Completion.comap_injective {v : InfinitePlace K} (w : Σ_v) :
    Function.Injective (Completion.comap w) :=
  (Completion.comap w).injective

def NumberField.Completion.comap_extend_injective {v : InfinitePlace K} (w : Σ_v) :
    Function.Injective (comap_extend K L w) :=
  (comap_extend K L w).injective

@[simps!]
def Pi.algHom {I R A : Type*} (f : I → Type*) [CommSemiring R] [s : (i : I) → Semiring (f i)]
    [(i : I) → Algebra R (f i)] [Semiring A] [Algebra R A] (g : (i : I) → A →ₐ[R] f i) :
    A →ₐ[R] (i : I) → f i where
  __ := Pi.ringHom fun i ↦ (g i).toRingHom
  commutes' r := by ext; simp

@[simps!]
def Pi.continuousAlgHom {I R A : Type*} (f : I → Type*) [CommSemiring R]
    [(i : I) → Semiring (f i)] [(i : I) → Algebra R (f i)] [(i : I) → TopologicalSpace (f i)]
    [Semiring A] [TopologicalSpace A] [Algebra R A] (g : (i : I) → A →A[R] f i) :
    A →A[R] (i : I) → f i where
  __ := Pi.algHom _ <| fun _ => (g _).toAlgHom
  cont := continuous_pi <| fun _ => (g _).cont

def NumberField.Completion.comap_pi (v : InfinitePlace K) :
    v.completion →A[K] ((w : Σ_v) → w.1.completion) :=
  Pi.continuousAlgHom _ <| (fun _ => comap _)

def NumberField.Completion.comap_pi_extend (v : InfinitePlace K) :
    v.completion →A[v.completion] ((w : Σ_v) → w.1.completion) :=
  ContinuousAlgHom.extendScalars v.completion (comap_pi K L v)

def NumberField.Completion.algebraMap_pi_ringHom :
    L →+* ((w : Σ_v) → w.1.completion) :=
  Pi.ringHom <| fun ⟨_, _⟩ => algebraMap _ _

def NumberField.Completion.algebraMap_pi :
    L →ₐ[K] ((w : Σ_v) → w.1.completion) where
  __ := algebraMap_pi_ringHom K v L
  commutes' _ := rfl

instance instNonemptyComap : Nonempty {w : InfinitePlace L // w.comap (algebraMap K L) = v} := by
  have : Function.Surjective fun (v : NumberField.InfinitePlace L) => v.comap (algebraMap K L) :=
    NumberField.InfinitePlace.comap_surjective
  let ⟨w, h⟩ := this v
  exact ⟨w, h⟩

instance : Nontrivial
    ((w : Σ_v) → w.1.completion) :=
  (instNonemptyComap K v L).elim fun w => Pi.nontrivial_at w

theorem NumberField.Completion.comap_pi_injective :
    Function.Injective (comap_pi K L v) :=
  (comap_pi K L v).injective

theorem NumberField.Completion.algebraMap_pi_injective :
    Function.Injective (algebraMap_pi K v L) :=
  (algebraMap_pi K v L).injective

def NumberField.Completion.baseChange_algHom (v : InfinitePlace K) :
    v.completion ⊗[K] L →ₐ[v.completion] ((w : Σ_v) → w.1.completion) :=
  Algebra.TensorProduct.lift (NumberField.Completion.comap_pi_extend K L v)
    (NumberField.Completion.algebraMap_pi K v L) (fun _ _ => mul_comm _ _)

instance : TopologicalSpace (v.completion ⊗[K] L) :=
  TopologicalSpace.induced (NumberField.Completion.baseChange_algHom K L v) inferInstance

def NumberField.Completion.baseChange_continuousAlgHom (v : InfinitePlace K) :
    v.completion ⊗[K] L →A[v.completion] ((w : Σ_v) → w.1.completion) where
  __ := baseChange_algHom K L v

theorem finrank_eq : FiniteDimensional.finrank v.completion ((w : Σ_v) → w.1.completion) =
    FiniteDimensional.finrank v.completion (v.completion ⊗[K] L) := by
  rw [FiniteDimensional.finrank_tensorProduct, FiniteDimensional.finrank_self,
    Completion.comap_prod_finrank, one_mul]

def AbsoluteValue.equivalent : AbsoluteValue K ℝ → AbsoluteValue K ℝ → Prop := fun v w =>
  ∃ (t : ℝ) (_: 0 < t), ∀ x, v x = (w x) ^ t

def AbsoluteValue.nontrivial : AbsoluteValue K ℝ → Prop := fun v => ∃ x ≠ 0, v x ≠ 1

theorem AbsoluteValue.exists_lt_one_of_nontrivial {v : AbsoluteValue K ℝ}
    (h : nontrivial K v) :
    ∃ x, 0 < v x ∧ v x < 1 := by
  by_contra! hc
  have : ∀ x, v x = 0 ∨ v x ≤ 1 := by
    intro x
    have := hc x⁻¹
    rw [map_inv₀] at this
    rw [one_le_inv_iff] at this
    by_cases hx : v x = 0
    · left; exact hx
    · right
      simp at hx
      simp at this
      exact (this hx).2
  rw [nontrivial] at h
  simp_rw [← not_or] at h
  rw [← not_forall] at h
  apply h
  intro x
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    simp_rw [map_eq_zero] at this
    simp at hc
    exact le_antisymm ((this x).resolve_left hx) (hc x hx)

theorem AbsoluteValue.exists_one_lt_of_nontrivial {v : AbsoluteValue K ℝ}
    (h : nontrivial K v) :
    ∃ x, 1 < v x := by
  let ⟨x, h⟩ := exists_lt_one_of_nontrivial K h
  use x⁻¹
  rwa [map_inv₀, one_lt_inv_iff]

theorem AbsoluteValue.one_lt_of_lt_one {v w : AbsoluteValue K ℝ}
    (h : ∀ x, v x < 1 → w x < 1) (x : K) (hv : 1 < v x) : 1 < w x := by
  have := inv_lt_one hv
  rw [← map_inv₀] at this
  have := h _ this
  rw [map_inv₀] at this
  have := inv_lt_one_iff.1 this
  cases this with
  | inl h =>
    have : x = 0 := by
      have := AbsoluteValue.nonneg w x
      have := le_antisymm h this
      simp at this
      exact this
    rw [this, map_zero] at hv
    linarith
  | inr h => exact h

theorem AbsoluteValue.one_lt_iff_of_lt_one_iff {v w : AbsoluteValue K ℝ}
    (h : ∀ x, v x < 1 ↔ w x < 1) (x : K) : 1 < v x ↔ 1 < w x := by
  constructor
  · exact fun hv => one_lt_of_lt_one _ (fun _ => (h _).1) x hv
  · exact fun hw => one_lt_of_lt_one _ (fun _ => (h _).2) x hw

theorem AbsoluteValue.eq_one_iff_of_lt_one_iff {v w : AbsoluteValue K ℝ}
    (h : ∀ x, v x < 1 ↔ w x < 1) (x : K) : v x = 1 ↔ w x = 1 := by
  have := (one_lt_iff_of_lt_one_iff K h x)
  constructor
  · intro hv
    have h' := (h x).not
    have h'' := hv.not_lt
    rw [h'] at h''
    simp at h''
    cases eq_or_lt_of_le h'' with
    | inl h =>
      rw [← h]
    | inr h =>
      rw [← this] at h
      linarith
  · intro hv
    have h' := (h x).not
    have h'' := hv.not_lt
    rw [← h'] at h''
    simp at h''
    cases eq_or_lt_of_le h'' with
    | inl h =>
      rw [← h]
    | inr h =>
      rw [this] at h
      linarith

theorem AbsoluteValue.equivalent_iff (v w : AbsoluteValue K ℝ) (hv : nontrivial K v) :
    equivalent K v w ↔ (∀ x, v x < 1 ↔ w x < 1) := by
  rw [equivalent]
  refine ⟨fun ⟨t, ht, h⟩ x => ?_, fun h => ?_⟩
  · exact h x ▸ Real.rpow_lt_one_iff' (AbsoluteValue.nonneg _ _) ht
  · have h' : ∀ (x : K), 1 < v x ↔ 1 < w x := one_lt_iff_of_lt_one_iff _ h
    have h'' : ∀ (x : K), v x = 1 ↔ w x = 1 := eq_one_iff_of_lt_one_iff _ h
    suffices : ∃ (t : ℝ) (_ : t > 0), ∀ x, 1 < v x → v x = w x ^ t
    · obtain ⟨t, ht, h'''⟩ := this
      use t, ht
      intro x
      by_cases h₀ : v x = 0
      · rw [AbsoluteValue.eq_zero] at h₀
        simp [h₀]
        rw [Real.zero_rpow (by linarith)]
      · by_cases h₁ : v x = 1
        · rw [h₁, (h'' x).1 h₁, Real.one_rpow]
        · by_cases h₂ : 0 < v x ∧ v x < 1
          · have : 1 < v x⁻¹ := by
              rw [map_inv₀]
              rw [one_lt_inv_iff]
              exact h₂
            have := h''' _ this
            simp at this
            rw [Real.inv_rpow (AbsoluteValue.nonneg _ _)] at this
            simp at this
            exact this
          · have h₄ : 1 < v x := by
              simp only [AbsoluteValue.pos_iff, ne_eq, not_and, not_lt] at h₂
              simp at h₀
              push_neg at h₁
              specialize h₂ h₀
              exact lt_of_le_of_ne h₂ h₁.symm
            exact h''' _ h₄
    have : ∃ (x : K), 1 < v x := exists_one_lt_of_nontrivial K hv
    obtain ⟨a, ha⟩ := this
    have : ∀ (b : K), 1 < v b →
        Real.log (v b) / Real.log (w b) = Real.log (v a) / Real.log (w a) := by
      by_contra hc
      simp at hc
      obtain ⟨b, hb₀, hb₂⟩ := hc
      push_neg at hb₂
      wlog hwlog : Real.log (v b) / Real.log (w b) < Real.log (v a) / Real.log (w a)
          generalizing a b
      · apply this b hb₀ a ha hb₂.symm
        simp at hwlog
        exact lt_of_le_of_ne hwlog hb₂.symm
      have : Real.log (v b) / Real.log (v a) < Real.log (w b) / Real.log (w a) := by
        have hwa := (h' _).1 ha
        have hwb := (h' _).1 hb₀
        rw [div_lt_div_iff (Real.log_pos ha) (Real.log_pos hwa)]
        nth_rw 2 [mul_comm]
        rwa [← div_lt_div_iff (Real.log_pos hwb) (Real.log_pos hwa)]
      let ⟨q, hq⟩ := exists_rat_btwn this
      rw [← Rat.num_div_den q] at hq
      push_cast at hq
      have h₀ : v (b ^ q.den / a ^ q.num) < 1 := by
        have := hq.1
        rw [div_lt_div_iff (Real.log_pos ha) (by simp only [Nat.cast_pos, q.den_pos])] at this
        rw [mul_comm] at this
        rw [← Real.log_pow, ← Real.log_zpow] at this
        rw [Real.log_lt_log_iff (pow_pos (by linarith) _) (zpow_pos_of_pos (by linarith) _)] at this
        rw [← div_lt_one (zpow_pos_of_pos (by linarith) _)] at this
        rwa [← map_pow, ← map_zpow₀, ← map_div₀] at this
      have h₁ : 1 < w (b ^ q.den / a ^ q.num) := by
        have hwa := (h' _).1 ha
        have hwb := (h' _).1 hb₀
        have := hq.2
        rw [div_lt_div_iff (by simp only [Nat.cast_pos, q.den_pos]) (Real.log_pos hwa)] at this
        nth_rw 2 [mul_comm] at this
        rw [← Real.log_pow, ← Real.log_zpow] at this
        rw [Real.log_lt_log_iff (zpow_pos_of_pos (by linarith) _) (pow_pos (by linarith) _)] at this
        rw [← one_lt_div (zpow_pos_of_pos (by linarith) _)] at this
        rwa [← map_pow, ← map_zpow₀, ← map_div₀] at this
      rw [h] at h₀
      exact not_lt_of_lt h₀ h₁
    use Real.log (v a) / Real.log (w a)
    use div_pos (Real.log_pos ha) (Real.log_pos ((h' a).1 ha))
    intro x hx
    rw [← this x hx]
    rw [div_eq_inv_mul, Real.rpow_mul (AbsoluteValue.nonneg _ _),
      Real.rpow_inv_log, Real.exp_one_rpow, Real.exp_log (by linarith)]
    · linarith [(h' x).1 hx]
    · linarith [(h' x).1 hx]

theorem NumberField.InfinitePlace.eq_of_equivalent {v w : InfinitePlace K}
    (h : AbsoluteValue.equivalent K v.1 w.1) :
    v = w := by
  rw [AbsoluteValue.equivalent] at h
  let ⟨t, ht, h⟩ := h
  have ht' : t = 1 := by
    specialize h ((2 : ℕ))
    let ⟨ψv, hψv⟩ := v.2
    let ⟨ψw, hψw⟩ := w.2
    rw [← hψv] at h
    rw [← hψw] at h
    simp at h
    apply Linarith.eq_of_not_lt_of_not_gt
    · intro h'
      have := Real.rpow_lt_self_of_one_lt (show 1 < 2 by linarith) h'
      linarith
    · intro h'
      have := Real.self_lt_rpow_of_one_lt (show 1 < 2 by linarith) h'
      linarith
  rw [ht'] at h
  simp at h
  apply Subtype.ext
  apply AbsoluteValue.ext
  exact h

theorem NumberField.InfinitePlace.abs_nontrivial : AbsoluteValue.nontrivial K v.1 := by
  rw [AbsoluteValue.nontrivial]
  use 2, by norm_num
  let ⟨φ, hφ⟩ := v.2
  rw [← hφ]
  simp only [place_apply, map_ofNat, RCLike.norm_ofNat, ne_eq, OfNat.ofNat_ne_one,
    not_false_eq_true]

theorem NumberField.InfinitePlace.exists_lt_one_one_le {v w : InfinitePlace K} (h : v ≠ w) :
    ∃ a : K, v a < 1 ∧ 1 ≤ w a := by
  by_contra! h'
  have : ∀ a : K, v a < 1 ↔ w a < 1 := by
    intro a
    refine ⟨h' a, ?_⟩
    intro hw
    by_contra h''
    simp at h''
    have hy : v (1 / 2) < 1 := by
      rw [← mk_embedding v]
      rw [apply]
      norm_num
    have (n : ℕ) (hn : n ≠ 0) : w (1 / 2) < w a ^ n ∧ w a ^ n < 1 := by
      refine ⟨?_, ?_⟩
      · have : v ((1 / 2) * (1 / a ^ n)) < 1 := by
          rw [map_mul]
          have : v (1 / a ^ n) ≤ 1 := by
            rw [one_div, map_inv₀, map_pow]
            apply inv_le_one
            apply one_le_pow₀ h''
          nth_rw 2 [one_div]
          rw [map_inv₀, map_pow]
          rw [mul_inv_lt_iff, mul_one]
          · apply lt_of_lt_of_le hy
            apply one_le_pow₀ h''
          · rw [← map_pow, pos_iff, pow_ne_zero_iff hn]
            intro ha
            rw [ha] at h''
            simp at h''
            linarith
        have := h' _ this
        rw [map_mul _ (1 / 2) (1 / a ^ n)] at this
        nth_rw 2 [one_div] at this
        rw [map_inv₀] at this
        rw [mul_inv_lt_iff, mul_one, map_pow] at this
        · exact this
        · rw [pos_iff, pow_ne_zero_iff hn]
          intro ha
          rw [ha] at h''
          simp at h''
          linarith
      · apply pow_lt_one (AbsoluteValue.nonneg _ _) hw hn
    have hwn : Filter.Tendsto (fun n => @norm (WithAbs w.1) _ a ^ n) Filter.atTop (𝓝 0) := by
      simp only [tendsto_pow_atTop_nhds_zero_iff, abs_norm]
      exact hw
    have hcontr : Filter.Tendsto (fun (n : ℕ) => w (1 / 2)) Filter.atTop (𝓝 0) := by
      have hf : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0) := tendsto_const_nhds
      have hwf : ∀ᶠ (_ : ℕ) in Filter.atTop, 0 ≤ w (1 / 2) := by
        simp only [one_div, map_inv₀, inv_nonneg, apply_nonneg, Filter.eventually_atTop, ge_iff_le,
          implies_true, exists_const]
      have hwn' : ∀ᶠ n in Filter.atTop, w (1 / 2) ≤ @norm (WithAbs w.1) _ a ^ n := by
        simp only [Filter.eventually_atTop, ge_iff_le]
        use 1
        intro n hn
        exact le_of_lt (this n (by linarith)).1
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := fun _ => w (1 / 2)) hf hwn hwf hwn'
    have hcontr := tendsto_nhds_unique hcontr tendsto_const_nhds |>.symm
    have : w (1 / 2) ≠ 0 := by norm_num
    exact this hcontr
  exact h <| eq_of_equivalent K ((AbsoluteValue.equivalent_iff K _ _ (abs_nontrivial _ _)).2 this)

theorem NumberField.InfinitePlace.exists_lt_one_one_lt {v w : InfinitePlace K} (h : v ≠ w) :
    ∃ a : K, 1 < v a ∧ w a < 1 := by
  obtain ⟨a, ha⟩ := exists_lt_one_one_le _ h
  obtain ⟨b, hb⟩ := exists_lt_one_one_le _ h.symm
  use b / a
  rw [map_div₀, map_div₀]
  constructor
  · rw [one_lt_div]
    · linarith
    · by_contra hv
      simp at hv
      have : v a = 0 :=
        le_antisymm hv (AbsoluteValue.nonneg _ _)
      simp at this
      rw [this] at ha
      simp at ha
      linarith
  · rw [div_lt_one]
    · linarith
    · linarith

variable {K}

theorem tendsto_pow_atTop {v : InfinitePlace K} {a : K} (ha : 1 < v a) :
    Filter.Tendsto (fun (n : ℕ) => v a ^ n) Filter.atTop Filter.atTop :=
  tendsto_pow_atTop_atTop_of_one_lt ha

theorem tendsto_pow_mul_atTop {v : InfinitePlace K} {a b : K} (ha : 1 < v a) (hb : 0 < v b) :
    Filter.Tendsto (fun (n : ℕ) => v (a ^ n * b)) Filter.atTop Filter.atTop := by
  simp_rw [map_mul v, map_pow]
  apply Filter.Tendsto.atTop_mul_const hb (tendsto_pow_atTop ha)

theorem tendsto_pow_zero {v : InfinitePlace K} {a : K} (ha : v a < 1) :
    Filter.Tendsto (fun (n : ℕ) => v a ^ n) Filter.atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (AbsoluteValue.nonneg _ _) ha

theorem tendsto_pow_mul_zero {v : InfinitePlace K} {a : K} (ha : v a < 1) (b : K) :
    Filter.Tendsto (fun (n : ℕ) => v (a ^ n * b)) Filter.atTop (𝓝 0) := by
  simp_rw [map_mul, map_pow]
  rw [← zero_mul (v b)]
  apply Filter.Tendsto.mul_const _ (tendsto_pow_zero ha)

def AbsoluteValue.toENNReal (v : AbsoluteValue K ℝ) := ENNReal.ofReal ∘ v

theorem AbsoluteValue.toENNReal_eq (v : AbsoluteValue K ℝ) (x : K) :
    (toENNReal v x).toReal = v x := by
  simp only [toENNReal, Function.comp_apply, apply_nonneg, ENNReal.toReal_ofReal]

def InfinitePlace.toENNReal (v : InfinitePlace K) := ENNReal.ofReal ∘ v

theorem InfinitePlace.toENNReal_eq (v : InfinitePlace K) (x : K) :
    (toENNReal v x).toReal = v x := by
  simp only [toENNReal, Function.comp_apply, apply_nonneg, ENNReal.toReal_ofReal]

theorem InfinitePlace.apply_eq_norm (v : InfinitePlace K) {a : K} :
    v a = @norm (WithAbs v.1) _ a :=
  rfl

def InfinitePlace.unitsEquiv (v : InfinitePlace K) :
    (WithAbs v.1)ˣ ≃ Kˣ := Equiv.refl _

def InfinitePlace.equiv (v : InfinitePlace K) : WithAbs v.1 ≃ K := Equiv.refl _

abbrev InfinitePlace.oneAddPow (v : InfinitePlace K) (n : ℕ) : K → WithAbs v.1 :=
  fun a => (equiv v).symm (1 + a ^ n)

abbrev InfinitePlace.oneSubPow (v : InfinitePlace K) (n : ℕ) : K → WithAbs v.1 :=
  fun a => (equiv v).symm (1 - a ^ n)

theorem InfinitePlace.one_add_pos {v : InfinitePlace K} {a : K} (ha : v a ≠ 1) :
    0 < v (1 + a) := by
  by_contra! h
  have : v (1 + a) = 0 := le_antisymm h <| AbsoluteValue.nonneg _ _
  simp [apply_eq_norm] at this
  have := eq_neg_add_of_add_eq this
  rw [add_zero] at this
  have := congrArg v this
  nth_rw 2 [apply_eq_norm] at this
  simp at this
  exact ha this

theorem InfinitePlace.one_add_pow_pos {v : InfinitePlace K} {a : K} (ha : v a ≠ 1) (n : ℕ) :
    0 < v (1 + a ^ n) := by
  by_cases h₀ : n = 0
  · simp [h₀]
    norm_num
    rw [← mk_embedding v]
    rw [InfinitePlace.apply]
    simp
  · have : v (a ^ n) ≠ 1 := by
      rwa [ne_eq, map_pow, pow_eq_one_iff_of_nonneg (AbsoluteValue.nonneg _ _) h₀]
    exact one_add_pos this

theorem InfinitePlace.one_add_ne_zero {v : InfinitePlace K} {a : K} (ha : v a ≠ 1) :
    1 + a ≠ 0 := by
  contrapose! ha
  rw [eq_neg_add_of_add_eq ha, add_zero, apply_eq_norm, norm_neg, norm_one]

theorem InfinitePlace.oneAddPow_ne_zero {v : InfinitePlace K} {a : K} (ha : v a ≠ 1) (n : ℕ) :
    oneAddPow v n a ≠ 0 := by
  by_cases h₀ : n = 0
  · rw [h₀, oneAddPow, equiv, Equiv.refl, pow_zero]
    norm_num
  · have : v (a ^ n) ≠ 1 := by
      rwa [ne_eq, map_pow, pow_eq_one_iff_of_nonneg (AbsoluteValue.nonneg _ _) h₀]
    contrapose! this
    rw [eq_neg_add_of_add_eq this, add_zero, apply_eq_norm, norm_neg, norm_one]

theorem InfinitePlace.ne_one_inv {v : InfinitePlace K} {a : K} (ha : v a ≠ 1) : v a⁻¹ ≠ 1 := by
  contrapose! ha
  simp at ha
  exact ha

theorem InfinitePlace.oneAddPow_isUnit {v : InfinitePlace K} {a : K} (ha : v a ≠ 1) (n : ℕ) :
    IsUnit (oneAddPow v n a) := by
  rw [isUnit_iff_ne_zero]
  exact oneAddPow_ne_zero ha n

abbrev InfinitePlace.oneAddPow_units (v : InfinitePlace K) (n : ℕ) :
    { a : K // v a ≠ 1 } → (WithAbs v.1)ˣ :=
  fun ⟨_, ha⟩ => (oneAddPow_isUnit ha n).unit

theorem InfinitePlace.apply_add_le (v : InfinitePlace K) (a b : K) : v (a + b) ≤ v a + v b := by
  simp only [apply_eq_norm]
  exact norm_add_le _ _

theorem InfinitePlace.abs_sub_apply_le (v : InfinitePlace K) (a b : K) :
    |v a - v b| ≤ v (a - b) := by
  simp only [apply_eq_norm]
  exact abs_norm_sub_norm_le _ _

theorem InfinitePlace.sub_apply_le_of_le {v : InfinitePlace K} (a b : K) (h : v b ≤ v a) :
    v a - v b ≤ v (a + b) := by
  simp only [apply_eq_norm]
  have := @abs_norm_sub_norm_le (WithAbs v.1) _ a (-b)
  simp at this
  rwa [abs_of_nonneg] at this
  exact sub_nonneg_of_le h

theorem tendsto_one_add_pow {v : InfinitePlace K} {a : K} (ha : v a < 1) :
    Filter.Tendsto (fun n => 1 + (v a ^ n)) Filter.atTop (𝓝 1) := by
  nth_rw 2 [← add_zero 1]
  apply Filter.Tendsto.const_add
  apply tendsto_pow_atTop_nhds_zero_of_lt_one (AbsoluteValue.nonneg _ _) ha

theorem tendsto_one_sub_pow {v : InfinitePlace K} {a : K} (ha : v a < 1) :
    Filter.Tendsto (fun n => 1 - (v a ^ n)) Filter.atTop (𝓝 1) := by
  nth_rw 2 [← sub_zero 1]
  apply Filter.Tendsto.const_sub
  apply tendsto_pow_atTop_nhds_zero_of_lt_one (AbsoluteValue.nonneg _ _) ha

theorem InfinitePlace.tendsto_oneAddPow_nhds_one {v : InfinitePlace K} {a : K} (ha : v a < 1) :
    Filter.Tendsto (fun n => oneAddPow v n a) Filter.atTop (𝓝 1) := by
  rw [← add_zero (1 : WithAbs v.1)]
  apply Filter.Tendsto.const_add
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_pow]
  apply tendsto_pow_atTop_nhds_zero_of_lt_one (AbsoluteValue.nonneg _ _) ha

theorem InfinitePlace.tendsto_oneSubPow {v : InfinitePlace K} {a : K} (ha : v a < 1) :
    Filter.Tendsto (fun n => oneSubPow v n a) Filter.atTop (𝓝 1) := by
  rw [← sub_zero 1]
  apply Filter.Tendsto.const_sub
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_pow]
  apply tendsto_pow_atTop_nhds_zero_of_lt_one (AbsoluteValue.nonneg _ _) ha

open InfinitePlace in
theorem  tendsto_div_oneAddPow_nhds_one {v : InfinitePlace K} {a : K} (ha : v a < 1) :
    Filter.Tendsto (fun n : ℕ => 1 / (oneAddPow v n a)) Filter.atTop (𝓝 1) := by
  nth_rw 2 [show (1 : WithAbs v.1) = 1 / 1 by norm_num]
  exact Filter.Tendsto.div tendsto_const_nhds (tendsto_oneAddPow_nhds_one ha) one_ne_zero

open InfinitePlace in
theorem tendsto_apply_div_oneAddPow_nhds_one {v : InfinitePlace K} {a : K} (ha : v a < 1) :
    Filter.Tendsto (fun (n : ℕ) => v (1 / (1 + a ^ n))) Filter.atTop (𝓝 1) := by
  have : Filter.Tendsto (fun (n : ℕ) => (InfinitePlace.toENNReal v) (1 / (1 + a ^ n)))
      Filter.atTop (𝓝 1) := by
    simp_rw [div_eq_mul_inv, one_mul, InfinitePlace.toENNReal, Function.comp_apply, map_inv₀]
    have := fun n : ℕ => ENNReal.ofReal_inv_of_pos (InfinitePlace.one_add_pow_pos (ne_of_lt ha) n)
    simp_rw [this]
    nth_rw 2 [← inv_one]
    apply Filter.Tendsto.inv
    simp_rw [← ENNReal.ofReal_one]
    apply ENNReal.tendsto_ofReal
    have hg := tendsto_one_sub_pow ha
    have hh := tendsto_one_add_pow ha
    have hfh (n : ℕ) : v (1 + a ^ n) ≤ 1 + v a ^ n := by
      apply le_trans (InfinitePlace.apply_add_le v _ _)
      rw [map_one, map_pow]
    have hgf (n : ℕ) : 1 - v a ^ n ≤ v (1 + a ^ n) := by
      apply le_trans _ (InfinitePlace.sub_apply_le_of_le _ _ _)
      · rw [map_one, map_pow]
      · rw [map_one, map_pow]
        exact pow_le_one _ (AbsoluteValue.nonneg _ _) (le_of_lt ha)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hg hh hgf hfh
  convert Filter.Tendsto.comp (ENNReal.tendsto_toReal (ENNReal.one_ne_top)) this
  rw [← InfinitePlace.toENNReal_eq v _]
  rw [InfinitePlace.toENNReal]
  simp only [zpow_neg, zpow_natCast, one_div, Function.comp_apply, map_inv₀, inv_nonneg,
    apply_nonneg, ENNReal.toReal_ofReal]

theorem tendsto_pow_mul_div_one_add_pow_one {v : InfinitePlace K} {a : K}
    (ha : v a < 1) (b : K) :
    Filter.Tendsto (fun (n : ℕ) => v (1 / (1 + a ^ n) * b)) Filter.atTop (𝓝 (v b)) := by
  simp_rw [map_mul]
  nth_rw 2 [← one_mul (v b)]
  apply Filter.Tendsto.mul_const _ (tendsto_apply_div_oneAddPow_nhds_one ha)

theorem tendsto_pow_div_one_add_pow_zero {v : InfinitePlace K} {a : K}
    (ha : 1 < v a) :
    Filter.Tendsto (fun (n : ℕ) => v (1 / (1 + a ^ n))) Filter.atTop (𝓝 0) := by
  simp_rw [div_eq_mul_inv, one_mul, map_inv₀]
  apply Filter.Tendsto.inv_tendsto_atTop
  have (n : ℕ) : v (a ^ n) - 1 ≤ v (1 + a ^ n) := by
    simp_rw [add_comm, ← map_one v, tsub_le_iff_right, InfinitePlace.apply_eq_norm]
    exact norm_le_add_norm_add _ _
  apply Filter.tendsto_atTop_mono this
  apply Filter.tendsto_atTop_add_right_of_le _ (-1) _ (fun _ => le_rfl)
  simp
  apply tendsto_atTop_of_geom_le (c := v (a))
  · simp only [pow_zero, inv_one, zero_lt_one]
  · exact ha
  · intro n
    rw [← map_pow, ← map_pow, ← map_mul]
    ring_nf
    exact le_rfl

open InfinitePlace in
theorem tendsto_div_oneAddPow_nhds_zero {v : InfinitePlace K} {a : K} (ha : 1 < v a) :
    Filter.Tendsto (fun n : ℕ => 1 / (oneAddPow v n a)) Filter.atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [← apply_eq_norm]
  exact tendsto_pow_div_one_add_pow_zero ha

theorem tendsto_pow_mul_div_one_add_pow_zero {v : InfinitePlace K} {a : K}
    (ha : 1 < v a) (b : K) :
    Filter.Tendsto (fun (n : ℕ) => v ((1 / (1 + a ^ n)) * b)) Filter.atTop (𝓝 0) := by
  simp_rw [map_mul]
  rw [← zero_mul (v b)]
  apply Filter.Tendsto.mul_const _ (tendsto_pow_div_one_add_pow_zero ha)

theorem exists_pow_mul_div_one_add_pow_lt_one {v : InfinitePlace K} {a b : K}
    (ha : v a < 1) (hb : 1 < v b) :
    ∃ N, ∀ r ≥ N, 1 < v (1 / (1 + a ^ r) * b) := by
  have := tendsto_pow_mul_div_one_add_pow_one ha b
  rw [Metric.tendsto_atTop] at this
  specialize this (dist 1 (v b) / 2) (div_pos (dist_pos.2 (by linarith)) (by norm_num))
  let ⟨N, hN⟩ := this
  use N
  intro r hr
  specialize hN r hr
  simp_rw [Real.dist_eq] at hN
  have : |1 - v b| = v b - 1 := by
    rw [show v b - 1 = - (1 - v b) by ring]
    rw [abs_eq_neg_self]
    linarith
  rw [this] at hN
  by_cases h : v b < v (1 / (1 + a ^ r) * b)
  · exact lt_trans hb h
  · rw [abs_eq_neg_self.2 (by linarith)] at hN
    have : (v b - 1) / 2 < v b - 1 := by
      linarith
    have := lt_trans hN this
    linarith

theorem exists_pow_mul_div_one_add_pow_one_lt {v : InfinitePlace K} {a b : K}
    (ha : v a < 1) (hb : v b < 1) :
    ∃ N, ∀ r ≥ N, v (1 / (1 + a ^ r) * b) < 1 := by
  have := tendsto_pow_mul_div_one_add_pow_one ha b
  rw [Metric.tendsto_atTop] at this
  specialize this (dist 1 (v b) / 2) (div_pos (dist_pos.2 (by linarith)) (by norm_num))
  let ⟨N, hN⟩ := this
  use N
  intro r hr
  specialize hN r hr
  simp_rw [Real.dist_eq] at hN
  have : |1 - v b| = 1 - v b := by
    rw [abs_eq_self]
    linarith
  rw [this] at hN
  by_cases h : v b < v (1 / (1 + a ^ r) * b)
  · rw [abs_eq_self.2 (by linarith)] at hN
    have : (1 - v b) / 2 < 1 - v b := by
      linarith
    have := lt_trans hN this
    linarith
  · push_neg at h
    exact lt_of_le_of_lt h hb

variable (K)

theorem Fin.castPred_val {n : ℕ} {j : Fin n.succ.succ} (hj : j ≠ Fin.last n.succ) :
    (j : Fin n.succ) = Fin.castPred j hj := by
  apply Fin.ext
  simp only [Nat.succ_eq_add_one, Fin.val_natCast, Fin.coe_castPred,
    Nat.mod_succ_eq_iff_lt]
  apply Fin.val_lt_last hj

theorem Fin.val_eq_zero_iff {n : ℕ} [NeZero n] {j : Fin n.succ} (hj : j ≠ Fin.last n)
    (hj' : j ≠ 0) : (j : Fin n) ≠ 0 := by
  rw [ne_eq, Fin.ext_iff] at hj' ⊢
  have : (0 : Fin (n.succ)).val = (0 : Fin n) := rfl
  contrapose! hj'
  rw [this, ← hj']
  rw [Fin.val_cast_of_lt]
  apply Fin.val_lt_last hj

theorem NumberField.InfinitePlace.exists_lt_one_one_lt_pi {n : ℕ}
    {v : Fin (n + 2) → InfinitePlace K} (h : v.Injective) :
    ∃ (a : K), 1 < v 0 a ∧ ∀ j ≠ 0, v j a < 1 := by
  induction n using Nat.case_strong_induction_on with
  | hz =>
    let ⟨a, ha⟩ := exists_lt_one_one_lt _ (h.ne zero_ne_one)
    use a, ha.1
    simp [Fin.forall_fin_two]
    exact ha.2
  | hi n ih =>
    let ⟨a, ha⟩ := ih n le_rfl <| h.comp (Fin.castSucc_injective _)
    let v'' : Fin 2 → InfinitePlace K := ![v 0, v (Fin.last _)]
    have : v''.Injective := by
      rw [Function.Injective]
      simp [Fin.forall_fin_two]
      simp [v'']
      refine ⟨?_, ?_⟩
      · apply h.ne
        rw [ne_eq, Fin.zero_eq_last_iff]
        norm_num
      · apply h.ne
        rw [ne_eq, Fin.last_eq_zero_iff]
        norm_num
    let ⟨b, hb⟩ := ih 0 (by linarith) <| this
    simp [Fin.forall_fin_two, v''] at hb
    by_cases ha₀ : v (Fin.last _) a < 1
    · use a
      use ha.1
      intro j hj
      by_cases hj' : j = Fin.last (n + 2)
      · rw [hj']
        convert ha₀
      · push_neg at hj'
        have := ha.2 (Fin.castPred _ hj')
        simp at this
        apply this
        contrapose! hj
        rwa [← Fin.castPred_zero, Fin.castPred_inj] at hj
    · by_cases ha₁ : v (Fin.last _) a = 1
      · have h₁ := tendsto_pow_mul_atTop ha.1 (show 0 < v 0 b by linarith)
        have hₙ (j : _) (hj : j ≠ 0) := tendsto_pow_mul_zero (ha.2 j hj) b
        simp_rw [Metric.tendsto_nhds] at hₙ
        rw [Filter.tendsto_atTop_atTop] at h₁
        let ⟨r₁, hr₁⟩ := h₁ 2
        simp only [Filter.eventually_atTop] at hₙ
        choose rₙ hrₙ using fun j hj => hₙ j hj 1 (by linarith)
        simp only [dist_zero_right] at hr₁ hrₙ
        let ri : Fin (n + 2) → ℕ :=
          fun j => if h : j = 0 then r₁ else
            rₙ j h
        let r := (Finset.univ.sup ri)
        have h₀ : ri 0 = r₁ := rfl
        have : r₁ ≤ r := by
          rw [← h₀]
          apply Finset.le_sup (Finset.mem_univ _)
        simp at this
        use a ^ r * b
        use lt_of_lt_of_le (by linarith) (hr₁ r this)
        intro j hj
        by_cases hj' : j ≠ Fin.last _
        · have h' : ri j = rₙ j (Fin.val_eq_zero_iff hj' hj) := by
            simp [ri, hj', hj, (Fin.val_eq_zero_iff hj' hj)]
          have : rₙ j (Fin.val_eq_zero_iff hj' hj) ≤ r := by
            rw [← h']
            apply Finset.le_sup (Finset.mem_univ _)
          convert hrₙ j (Fin.val_eq_zero_iff hj' hj) r this
          rw [Fin.castPred_val hj']
          simp
          rw [abs_of_nonneg (AbsoluteValue.nonneg _ _)]
          rw [abs_of_nonneg (AbsoluteValue.nonneg _ _)]
        · push_neg at hj'
          rw [hj']
          rw [map_mul, map_pow, ha₁, one_pow, one_mul]
          exact hb.2
      · push_neg at ha₁ ha₀
        have ha₂ : 1 < v (Fin.last _) a := by
          exact lt_of_le_of_ne ha₀ ha₁.symm
        have ha₃ := inv_lt_one ha.1
        simp only [← map_inv₀] at ha₃
        have h₁ := exists_pow_mul_div_one_add_pow_lt_one ha₃ hb.1
        have (j : _) (hj : j ≠ 0) : 0 < (v ∘ Fin.castSucc) j a := by
          by_contra h
          simp at h
          have := le_antisymm h (AbsoluteValue.nonneg _ _)
          simp at this
          rw [this, map_zero] at ha₂
          linarith
        have ha₅ (j : _) (hj : j ≠ 0) := one_lt_inv (this j hj) (ha.2 j hj)
        simp_rw [← map_inv₀] at ha₅
        have hₙ (j : _) (hj : j ≠ 0) := tendsto_pow_mul_div_one_add_pow_zero (ha₅ j hj) b
        have ha₄ := inv_lt_one ha₂
        rw [← map_inv₀] at ha₄
        have hN := exists_pow_mul_div_one_add_pow_one_lt ha₄ hb.2
        simp_rw [Metric.tendsto_nhds, Filter.eventually_atTop, dist_zero_right] at h₁ hₙ hN
        choose r₁ hr₁ using h₁
        choose rₙ hrₙ using fun j hj => hₙ j hj 1 (by linarith)
        choose rN hrN using hN
        let ri : Fin (n + 3) → ℕ :=
          fun j => if hN : j = Fin.last (n + 2) then rN else if h : j = 0 then r₁ else
            rₙ j (Fin.val_eq_zero_iff hN h)
        let r := (Finset.univ.sup ri)
        have h₀ : ri 0 = r₁ := rfl
        have : r₁ ≤ r := by
          rw [← h₀]
          apply Finset.le_sup (Finset.mem_univ _)
        simp at this
        use 1 / (1 + a⁻¹ ^ r)  * b
        simp only [Nat.succ_eq_add_one, Function.comp_apply, Fin.castSucc_zero] at hr₁ hrN
        use hr₁ r this
        intro j hj
        by_cases hj' : j ≠ Fin.last _
        · have h' : ri j = rₙ j (Fin.val_eq_zero_iff hj' hj) := by
            simp [ri, hj', hj]
          have : rₙ j (Fin.val_eq_zero_iff hj' hj) ≤ r := by
            rw [← h']
            apply Finset.le_sup (Finset.mem_univ _)
          convert hrₙ j (Fin.val_eq_zero_iff hj' hj) r this
          rw [Fin.castPred_val hj']
          simp
          rw [abs_of_nonneg (AbsoluteValue.nonneg _ _)]
          rw [abs_of_nonneg (AbsoluteValue.nonneg _ _)]
        · push_neg at hj'
          have h' : ri j = rN := by
            rw [hj']
            simp [ri]
          have : rN ≤ r := by
            rw [← h']
            apply Finset.le_sup (Finset.mem_univ _)
          exact hj' ▸ hrN r this

def Pi.map {ι : Sort*}  {α : ι → Sort*} {β : ι → Sort*} (f : (i : ι) → α i → β i) :
((i : ι) → α i) → (i : ι) → β i := fun a i ↦ f i (a i)

protected theorem Continuous.piMap {Y π : ι → Type*} [∀ i, TopologicalSpace (π i)]
    [∀ i, TopologicalSpace (Y i)]
    {f : ∀ i, π i → Y i} (hf : ∀ i, Continuous (f i)) : Continuous (Pi.map f) :=
  continuous_pi fun i ↦ (hf i).comp (continuous_apply i)

theorem DenseRange.piMap {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    {f : (i : ι) → (X i) → (Y i)} (hf : ∀ i, DenseRange (f i)):
    DenseRange (Pi.map f) := by
  simp [DenseRange]
  delta Pi.map
  simp_rw [Set.range_dcomp]
  simp [DenseRange] at hf
  exact dense_pi Set.univ (fun i _ => hf i)

theorem weak_approx {p : InfinitePlace K → Prop} [Nonempty {v // p v}] :
    DenseRange <| algebraMap K ((v : {v : InfinitePlace K // p v}) → WithAbs v.1.1) := by
  by_cases hcard : Fintype.card {v // p v} = 1
  · have huniq := Fintype.equivFinOfCardEq hcard |>.unique
    let v := huniq.default
    let f := Homeomorph.funUnique {v // p v} (WithAbs v.1.1)
    have hcomp : ⇑(algebraMap K ((v : { v // p v}) → WithAbs v.1.1)) =
        f.symm ∘ algebraMap K (WithAbs v.1.1) := by
      funext _
      simp [f]
      rfl
    have hcont : Continuous f.symm := f.continuous_invFun
    have hd1 : DenseRange (algebraMap K (WithAbs v.1.1)) := denseRange_id
    have hd2 : DenseRange f.symm := f.symm.surjective.denseRange
    have := DenseRange.comp hd2 hd1 hcont
    rw [hcomp]
    convert this <;> exact huniq.uniq _
  rw [Metric.denseRange_iff]
  intro z r hr
  have (v : {v // p v}) : ∃ (x : K), 1 < v.1 x ∧ ∀ w, w ≠ v → w.1 x < 1 := by
    let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin {v // p v}
    have : ∃ k, n = k + 2 := by
      use n - 2
      rw [n.sub_add_cancel]
      have : Fintype.card {v // p v} = n := Fintype.card_fin n ▸ Fintype.card_eq.2 ⟨e⟩
      have hpos : 0 < n := by
        rw [← this]
        exact Fintype.card_pos
      omega
    obtain ⟨k, rfl⟩ := this
    let ⟨m, hm⟩ := e.symm.surjective v
    let e' := e.trans (Equiv.swap 0 m)
    let ⟨x, hx⟩ := NumberField.InfinitePlace.exists_lt_one_one_lt_pi (v := Subtype.val ∘ e'.symm)
      ((e'.symm.injective_comp _).2 (Subtype.val_injective)) --(e v)
    use x
    simp [e', hm] at hx
    use hx.1
    intro w hw
    have he'v : e' v = 0 := by simp [e', e.symm_apply_eq.1 hm]
    have := e'.injective.ne hw
    rw [he'v] at this
    have := hx.2 (e' w) this
    simp [e'] at this
    exact this
  have (v : {v // p v}) : ∃ (x : ℕ → WithAbs v.1.1),
      Filter.Tendsto (fun n => x n) Filter.atTop (𝓝 1) ∧ ∀ w ≠ v,
        Filter.Tendsto (β := WithAbs w.1.1) (fun n => x n) Filter.atTop (𝓝 0) := by
    obtain ⟨x, hx⟩ := this v
    set f : ℕ → K := fun n => (1 + x⁻¹ ^ n)
    set z : ℕ → K := fun n => (f n)⁻¹
    use z
    refine ⟨?_, ?_⟩
    · have hx₁ := inv_lt_one hx.1
      rw [← map_inv₀] at hx₁
      have := tendsto_div_oneAddPow_nhds_one hx₁
      simp_rw [div_eq_mul_inv, one_mul] at this
      exact this
    · intro w hwv
      have : 0 < w.1 x := by
        by_contra! h
        have := le_antisymm h (AbsoluteValue.nonneg _ _)
        simp [InfinitePlace.apply_eq_norm] at h
        simp [h] at hx
        linarith
      have hx' := one_lt_inv this (hx.2 w hwv)
      rw [← map_inv₀] at hx'
      have := tendsto_div_oneAddPow_nhds_zero hx'
      simp_rw [div_eq_mul_inv, one_mul] at this
      exact this
  let x : (v : {v // p v}) → (ℕ → WithAbs v.1.1) := fun v => (this v).choose
  have h := fun v => (this v).choose_spec
  let y := fun n => ∑ v : {v // p v}, x v n * z v
  have : Filter.Tendsto
      (fun n v => (∑ v : {v // p v}, x v n * z v : WithAbs v.1.1)) Filter.atTop (𝓝 z) := by
    rw [tendsto_pi_nhds]
    intro v
    have : z v = ∑ w : {w // p w}, if w = v then z v else (0 : WithAbs w.1.1) := by
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [this]
    apply tendsto_finset_sum (Finset.univ : Finset {v // p v})
    intro w _
    by_cases hw : w = v
    · simp [hw]
      have : x w = x v := by rw [hw]
      rw [this]
      have : z w = z v := by rw [hw]
      rw [this, show 𝓝 (z v) = 𝓝 (1 * z v) by rw [one_mul]]
      apply Filter.Tendsto.mul_const
      exact (h v).1
    · simp [hw]
      rw [← zero_mul (z w)]
      apply Filter.Tendsto.mul_const
      apply (h w).2 v
      rw [← ne_eq] at hw
      exact hw.symm
  simp_rw [Metric.tendsto_atTop] at this
  specialize this r hr
  let ⟨N, h⟩ := this
  use y N
  rw [dist_comm]
  --sorry -- below works but is slow
  exact h N le_rfl

theorem weak_approx' {p : InfinitePlace K → Prop} [Nonempty {v // p v}]:
    DenseRange <| algebraMap K ((v : {v : InfinitePlace K // p v}) → v.1.completion) := by
  have hd : DenseRange (Pi.map (fun (v : {v  // p v}) (x : WithAbs v.1.1) =>
    (x : v.1.completion))) :=
    DenseRange.piMap (fun _ => UniformSpace.Completion.denseRange_coe)
  have : algebraMap K ((v : {v : InfinitePlace K // p v}) → v.1.completion) =
    (Pi.map (fun (v : {v  // p v}) (x : WithAbs v.1.1) => (x : v.1.completion))) ∘
      algebraMap K ((v : {v : InfinitePlace K // p v}) → WithAbs v.1.1) := rfl
  rw [this]
  apply DenseRange.comp hd (weak_approx K)
    <| Continuous.piMap (fun _ => UniformSpace.Completion.continuous_coe _)

theorem matrix_det_approx {n : ℕ}
    (B : Basis (Fin n) v.completion ((w : Σ_v) → w.1.completion))
    (h : ∀ r, r > 0 → ∃ α : Fin n → L, ∀ i,
      dist (B i) (algebraMap _ ((w : Σ_v) → w.1.completion) (α i)) < r)
    (ε : ℝ)
    (hε : ε > 0) :
    ∃ β : Fin n → L,
      dist (B.toMatrix B).det
        (B.toMatrix (fun i => algebraMap _ ((w : Σ_v) → w.1.completion) (β i))).det < ε := by
  let X := (Fin n) → (w : Σ_v) → w.1.completion
  let f : X → Matrix (Fin n) (Fin n) v.completion := fun α => B.toMatrix fun i => α i
  have hf : Continuous f :=
    B.toMatrixEquiv.toLinearMap.continuous_of_finiteDimensional
  have := Continuous.matrix_det hf
  rw [Metric.continuous_iff] at this
  have hc (b : X) := this b ε hε
  choose δ hδ using hc B
  specialize h δ hδ.1
  let ⟨α, hα⟩ := h
  use α
  rw [dist_comm]
  apply hδ.2
  rw [dist_comm, dist_eq_norm]
  simp_rw [dist_eq_norm] at hα
  rw [Pi.norm_def]
  have := Finset.sup_lt_iff
    (f := fun i => ‖B i - algebraMap L ((w : Σ_v) → w.1.completion) (α i)‖₊)
    (a := ⟨δ, le_of_lt hδ.1⟩) (s := Finset.univ) hδ.1
  exact this.2 fun i _ => hα i

theorem NumberField.Completion.matrix_approx {n : ℕ}
    (B : Basis (Fin n) v.completion ((w : Σ_v) → w.1.completion))
    (h : ∀ r, r > 0 → ∃ α : Fin n → L, ∀ i,
      dist (B i) (algebraMap _ ((w : Σ_v) → w.1.completion) (α i)) < r) :
    ∃ β : Fin n → L,
      IsUnit (B.det (fun (i : Fin n) => baseChange_algHom K L v (1 ⊗ₜ β i))) := by
  let M := ((w : Σ_v) → w.1.completion)
  obtain ⟨β, h⟩ := matrix_det_approx K v L B h (1 / 2) (by linarith)
  use β
  rw [isUnit_iff_ne_zero, Basis.det_apply]
  rw [← Basis.det_apply, B.det_self] at h
  intro hc
  simp_rw [baseChange_algHom, Algebra.TensorProduct.lift_tmul] at hc
  have : (comap_pi_extend K L v : v.completion →ₐ[v.completion] M) 1 = 1 :=
    map_one (comap_pi_extend K L v)
  simp_rw [this, one_mul] at hc
  have (x : _) : algebraMap_pi K v L x = algebraMap L M x := rfl
  simp [this] at hc
  rw [hc] at h
  rw [dist_zero_right, norm_one] at h
  linarith

set_option maxHeartbeats 0 in
theorem NumberField.Completion.baseChange_surjective (v : InfinitePlace K) :
    Function.Surjective (baseChange_algHom K L v) := by
  let n := (FiniteDimensional.finrank v.completion (v.completion ⊗[K] L))
  let Bw := FiniteDimensional.finBasisOfFinrankEq v.completion ((w : Σ_v) → w.1.completion)
        (finrank_eq K v L)
  have := weak_approx' (p := fun w : InfinitePlace L => w.comap (algebraMap K L) = v)
  have hr (r : _) (hr : r > 0) : ∃ (α : Fin n → L),
      ∀ i : Fin n, dist (Bw i) (algebraMap _ _ (α i)) < r := by
    exact ⟨fun i => Classical.choose (this.exists_dist_lt (Bw i) hr),
        fun i => Classical.choose_spec (this.exists_dist_lt (Bw i) hr)⟩
  have := matrix_approx K v L Bw hr
  let ⟨α, h⟩ := this
  have := is_basis_iff_det Bw
    (v := (fun (i : Fin n) => baseChange_algHom K L v (1 ⊗ₜ α i)))
  rw [← this] at h
  rw [← LinearMap.range_eq_top]
  rw [← top_le_iff]
  rw [← h.2]
  rw [Submodule.span_le]
  intro x hx
  rw [SetLike.mem_coe]
  rw [LinearMap.mem_range]
  obtain ⟨i, hi⟩ := hx
  rw [← hi]
  use 1 ⊗ₜ[K] α i

def NumberField.Completion.baseChange_linearEquiv (v : InfinitePlace K) :
    v.completion ⊗[K] L ≃ₗ[v.completion] ((w : Σ_v) → w.1.completion) :=
  LinearEquiv.ofBijective _ ⟨
    LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_eq K v L).symm |>.2 (baseChange_surjective K L v),
        baseChange_surjective K L v⟩

set_option synthInstance.maxHeartbeats 0 in
def NumberField.Completion.baseChange_algEquiv (v : InfinitePlace K) :
    v.completion ⊗[K] L ≃ₐ[v.completion] ((w : Σ_v) → w.1.completion) := by
  apply AlgEquiv.ofLinearEquiv (baseChange_linearEquiv K L v)
  · --rw [baseChange_linearEquiv]
    --rw [LinearEquiv.ofBijective_apply]
    exact map_one (baseChange_algHom K L v)
  · intro x y
    --rw [baseChange_linearEquiv, LinearEquiv.ofBijective_apply]
    exact map_mul (baseChange_algHom K L v) _ _

def NumberField.Completion.baseChange (v : InfinitePlace K) :
    v.completion ⊗[K] L ≃A[v.completion] ((w : Σ_v) → w.1.completion) where
  __ := baseChange_algEquiv K L v
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    convert (baseChange_algEquiv K L v).toEquiv.coinduced_symm ▸ continuous_coinduced_rng

/- Now have two algebra isomorphisms
(1) 𝔸_K ⊗[K] L ≃ₐ[K] Πᵥ (Kᵥ ⊗[K] L)
(2) (Kᵥ ⊗[K] L) ≃ₐ[v.completion] Π_{w ∣ v} L_w.

We can piece these together and restrict scalars on (2), to give the K-algebra isomorphisms:
𝔸_K ⊗[K] L ≃ₐ[K] Πᵥ (Kᵥ ⊗[K] L) ≃ₐ[K] Πᵥ Π_{w ∣ v} L_w ≃ₐ[K] Π_w L_w = 𝔸_L. -/

def NumberField.Completion.equiv_comap :
    InfinitePlace L ≃ ((v : InfinitePlace K) × Σ_v) :=
  (Equiv.sigmaFiberEquiv _).symm

theorem NumberField.Completion.equiv_comap_apply :
    (NumberField.Completion.equiv_comap K L).symm i = i.2.1 := rfl

@[simps!]
def AlgEquiv.piCurry (S : Type*) [CommSemiring S] {Y : ι → Type*} (α : (i : ι) → Y i → Type*)
    [(i : ι) → (y : Y i) → Semiring (α i y)] [(i : ι) → (y : Y i) → Algebra S (α i y)] :
    ((i : Sigma Y) → α i.1 i.2) ≃ₐ[S] ((i : ι) → (y : Y i) → α i y) where
  toEquiv := Equiv.piCurry α
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simps!]
def ContinuousAlgEquiv.piCurry (S : Type*) [CommSemiring S] {Y : ι → Type*}
    (α : (i : ι) → Y i → Type*) [(i : ι) → (y : Y i) → Semiring (α i y)]
    [(i : ι) → (y : Y i) → Algebra S (α i y)]  [(i : ι) → (y : Y i) → TopologicalSpace (α i y)] :
    ((i : Sigma Y) → α i.1 i.2) ≃A[S] ((i : ι) → (y : Y i) → α i y) where
  toAlgEquiv := AlgEquiv.piCurry S α
  continuous_toFun := continuous_pi (fun _ => continuous_pi <| fun _ => continuous_apply _)
  continuous_invFun := by
    refine continuous_pi (fun ⟨x, y⟩ => ?_)
    simp only [AlgEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AlgEquiv.symm_toEquiv_eq_symm,
      EquivLike.coe_coe, AlgEquiv.piCurry_symm_apply, Sigma.uncurry]
    exact Continuous.comp' (continuous_apply _) (continuous_apply _)

@[simps!]
def AlgEquiv.piCongrLeft' (S : Type*) [CommSemiring S] (A : α → Type*) (e : α ≃ β)
    [∀ a, Semiring (A a)] [∀ a, Algebra S (A a)] :
    ((a : α) → A a) ≃ₐ[S] ((b : β) → A (e.symm b)) where
  toEquiv := Equiv.piCongrLeft' A e
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem AlgEquiv.piCongrLeft'_symm (S : Type*) {A : Type*} [CommSemiring S] [Semiring A]
    [Algebra S A] (e : α ≃ β) :
    (AlgEquiv.piCongrLeft' S (fun _ => A) e).symm = AlgEquiv.piCongrLeft' S _ e.symm := by
  simp [AlgEquiv.piCongrLeft', AlgEquiv.symm, RingEquiv.symm, MulEquiv.symm,
    Equiv.piCongrLeft'_symm]
  rfl

@[simp]
theorem AlgEquiv.piCongrLeft'_symm_apply_apply (S : Type*) (A : α → Type*) [CommSemiring S]
    [∀ a, Semiring (A a)] [∀ a, Algebra S (A a)] (e : α ≃ β) (g : (b : β) → A (e.symm b)) (b : β) :
    (piCongrLeft' S A e).symm g (e.symm b) = g b := by
  rw [← Equiv.piCongrLeft'_symm_apply_apply A e g b]
  rfl

@[simps! apply toEquiv]
def AlgEquiv.piCongrLeft (S : Type*) [CommSemiring S] (B : β → Type*) (e : α ≃ β)
    [∀ b, Semiring (B b)] [∀ b, Algebra S (B b)] :
    ((a : α) → B (e a)) ≃ₐ[S] ((b : β) → B b) :=
  (AlgEquiv.piCongrLeft' S B e.symm).symm

@[simps!]
def ContinuousAlgEquiv.piCongrLeft (S : Type*) [CommSemiring S] (B : β → Type*) (e : α ≃ β)
    [∀ b, Semiring (B b)] [∀ b, Algebra S (B b)] [∀ b, TopologicalSpace (B b)]  :
    ((a : α) → B (e a)) ≃A[S] ((b : β) → B b) where
  toAlgEquiv := AlgEquiv.piCongrLeft S B e
  continuous_toFun := continuous_pi <| e.forall_congr_right.mp fun i ↦ by
    simp only [AlgEquiv.toEquiv_eq_coe, AlgEquiv.piCongrLeft, Equiv.toFun_as_coe, EquivLike.coe_coe]
    have := AlgEquiv.piCongrLeft'_symm_apply_apply S B e.symm
    simp only [Equiv.symm_symm_apply] at this
    simp only [this]
    exact continuous_apply _
  continuous_invFun := Pi.continuous_precomp' e

instance : TopologicalSpace (InfiniteAdeleRing K ⊗[K] L) :=
  TopologicalSpace.induced (piLeft_algEquiv K L) inferInstance

def piLeft : InfiniteAdeleRing K ⊗[K] L ≃A[K] ((v : InfinitePlace K) → v.completion ⊗[K] L) where
  __ := piLeft_algEquiv K L
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    convert (piLeft_algEquiv K L).toEquiv.coinduced_symm ▸ continuous_coinduced_rng

def ContinuousAlgEquiv.piCongrRight {R ι : Type*} {A₁ A₂ : ι → Type*} [CommSemiring R]
    [(i : ι) → Semiring (A₁ i)] [(i : ι) → Semiring (A₂ i)] [(i : ι) → TopologicalSpace (A₁ i)]
    [(i : ι) → TopologicalSpace (A₂ i)] [(i : ι) → Algebra R (A₁ i)] [(i : ι) → Algebra R (A₂ i)]
    (e : (i : ι) → A₁ i ≃A[R] A₂ i) :
    ((i : ι) → A₁ i) ≃A[R] (i : ι) → A₂ i where
  __ := AlgEquiv.piCongrRight <| fun _ => (e _).toAlgEquiv
  continuous_toFun := Pi.continuous_postcomp' fun i ↦ (e i).continuous
  continuous_invFun := Pi.continuous_postcomp' fun i ↦ (e i).symm.continuous

def baseChange :
    letI : Algebra K (InfiniteAdeleRing L) := Pi.algebra _ _
    InfiniteAdeleRing K ⊗[K] L ≃A[K] InfiniteAdeleRing L := by
  letI : Algebra K (InfiniteAdeleRing L) := Pi.algebra _ _
  apply piLeft K L |>.trans
  have (v : _) := ContinuousAlgEquiv.restrictScalars K (NumberField.Completion.baseChange K L v)
  apply ContinuousAlgEquiv.piCongrRight this |>.trans
  let γ : (v : InfinitePlace K) → (w : Σ_v) → Type _ :=
    fun v w => w.1.completion
  apply ContinuousAlgEquiv.piCurry K γ |>.symm |>.trans
  have := ContinuousAlgEquiv.piCongrLeft K (fun w => w.completion)
    (NumberField.Completion.equiv_comap K L).symm
  refine ContinuousAlgEquiv.trans ?_ this
  simp_rw [NumberField.Completion.equiv_comap_apply, γ]
  exact ContinuousAlgEquiv.refl _ _

end InfiniteAdeleRing

end NumberField
