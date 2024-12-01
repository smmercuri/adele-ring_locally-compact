/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import AdeleRingLocallyCompact.NumberTheory.NumberField.Completion
import AdeleRingLocallyCompact.Algebra.Ring.Equiv
import AdeleRingLocallyCompact.FromMathlib.LinearAlgebra.TensorProduct.Pi
import AdeleRingLocallyCompact.Topology.Algebra.Algebra
import AdeleRingLocallyCompact.Topology.Homeomorph

open scoped TensorProduct Classical

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
  rw [mul_comm, FiniteDimensional.finrank_mul_finrank]

/- New strategy! because I cannot get a ring equiv, or an algebra equiv out of above
(because ℂ is not ring equiv to ℝ × ℝ !). -/

/- K-algebra isomorphisms: 𝔸_K ⊗[K] L =ₐ[K] (Πᵥ Kᵥ) ⊗[K] L ≃ₐ[K] Πᵥ (Kᵥ ⊗[K] L).-/

def piRight (R S A : Type*) {ι : Type*}  (B : ι → Type*) [CommSemiring R]
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

def AlgEquiv.piLeft : InfiniteAdeleRing K ⊗[K] L ≃ₐ[K]
    ((v : InfinitePlace K) → v.completion ⊗[K] L) := by
  apply AlgEquiv.trans (Algebra.TensorProduct.comm _ _ _)
  apply AlgEquiv.trans (piRight _ _ _ _)
  exact AlgEquiv.piCongrRight <| fun _ => Algebra.TensorProduct.comm _ _ _

instance (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) : Algebra (WithAbs v) (WithAbs w) :=
  inferInstanceAs (Algebra K L)

theorem WithAbs.norm_eq (v : AbsoluteValue K ℝ) (x : WithAbs v) : ‖x‖ = v x := rfl

theorem WithAbs.uniformContinuous_algebraMap (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
    (h : w.comp (algebraMap _ _).injective = v):
    UniformContinuous (algebraMap (WithAbs v) (WithAbs w)) := by
  apply uniformContinuous_of_tendsto_zero
  rw [Metric.nhds_basis_closedBall.tendsto_iff Metric.nhds_basis_closedBall]
  refine fun ε _ => ⟨ε, ‹_›, fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, WithAbs.norm_eq _, ← h] at hx ⊢
  exact hx

theorem NumberField.InfinitePlace.abs_eq_of_comap {v : InfinitePlace K} {w : InfinitePlace L}
    (h : w.comap (algebraMap _ _) = v) : w.1.comp (algebraMap _ _).injective = v.1 := by
  rw [← h]; rfl

variable (w : InfinitePlace L)

local notation "Σ_" v => {w : InfinitePlace L // w.comap (algebraMap K L) = v}

/- Now establish `Kᵥ`-algebra isomorphisms (Note completion as base field now)
Kᵥ ⊗[K] L ≃ₐ[v.completion] Π_{w ∣ v} L_w, where w ∣ v means that
v = w.comap (algebraMap K L). -/
def NumberField.Completion.comap_ringHom {v : InfinitePlace K} (w : Σ_v) :
    v.completion →+* w.1.completion := by
  apply UniformSpace.Completion.mapRingHom (algebraMap (WithAbs v.1) (WithAbs w.1.1))
  exact (WithAbs.uniformContinuous_algebraMap K L v.1 w.1.1
    (NumberField.InfinitePlace.abs_eq_of_comap K L w.2)).continuous

instance : Algebra K (WithAbs w.1) := ‹Algebra K L›

instance : UniformContinuousConstSMul K (WithAbs w.1) :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _

instance : IsScalarTower K L (WithAbs w.1) := inferInstanceAs (IsScalarTower K L L)

instance : SMulCommClass K v.completion v.completion := Algebra.to_smulCommClass

instance (w : Σ_v) : Algebra v.completion w.1.completion := RingHom.toAlgebra <|
  NumberField.Completion.comap_ringHom K L w

noncomputable instance : Algebra K (w.completion) where
  toFun k := algebraMap L w.completion (algebraMap K L k)
  map_one' := by simp only [map_one]
  map_mul' k₁ k₂ := by simp only [map_mul]
  map_zero' := by simp only [map_zero]
  map_add' k₁ k₂ := by simp only [map_add]
  commutes' k lhat := mul_comm _ _
  smul_def' k lhat := by
    rw [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, UniformSpace.Completion.smul_def,
    ← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq,
    UniformSpace.Completion.map_smul_eq_mul_coe, UniformSpace.Completion.algebraMap_def]

noncomputable instance (w : Σ_v) : FiniteDimensional v.completion w.1.completion := sorry

theorem UniformSpace.Completion.mapRingHom_apply {α β : Type*} [Ring α] [UniformSpace α]
    [TopologicalRing α] [UniformAddGroup α] [UniformSpace β] [Ring β] [UniformAddGroup β]
    [TopologicalRing β] (f : α →+* β) (hf : Continuous f) {x : UniformSpace.Completion α} :
    UniformSpace.Completion.mapRingHom f hf x = UniformSpace.Completion.map f x := rfl

theorem NumberField.Completion.algebraMap_eq_coe :
    ⇑(algebraMap K v.completion) = ((↑) : K → v.completion) := rfl

def NumberField.Completion.comap {v : InfinitePlace K} (w : Σ_v) :
    v.completion →ₐ[K] w.1.completion where
  __ := NumberField.Completion.comap_ringHom K L w
  commutes' := by
    intro r
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, comap_ringHom, UniformSpace.Completion.mapRingHom_apply]
    rw [algebraMap_eq_coe, UniformSpace.Completion.map_coe] ; rfl
    exact WithAbs.uniformContinuous_algebraMap K L v.1 w.1.1
      (NumberField.InfinitePlace.abs_eq_of_comap K L w.2)

instance : IsScalarTower K v.completion v.completion := IsScalarTower.right

def NumberField.Completion.comap_extend {v : InfinitePlace K} (w : Σ_v) :
    v.completion →ₐ[v.completion] w.1.completion :=
  (comap K L w).extendScalars _

def NumberField.Completion.comap_injective {v : InfinitePlace K} (w : Σ_v) :
    Function.Injective (NumberField.Completion.comap K L w) :=
  (NumberField.Completion.comap K L w).injective

def NumberField.Completion.comap_extend_injective {v : InfinitePlace K} (w : Σ_v) :
    Function.Injective (comap_extend K L w) :=
  (comap_extend K L w).injective

@[simps!]
def Pi.algHom {I R A : Type*} (f : I → Type*) [CommSemiring R] [s : (i : I) → Semiring (f i)]
    [(i : I) → Algebra R (f i)] [Semiring A] [Algebra R A] (g : (i : I) → A →ₐ[R] f i) :
    A →ₐ[R] (i : I) → f i where
  __ := Pi.ringHom fun i ↦ (g i).toRingHom
  commutes' r := by ext; simp

def NumberField.Completion.comap_pi (v : InfinitePlace K) :
    v.completion →ₐ[K] ((w : Σ_v) → w.1.completion) :=
  Pi.algHom _ <| (fun _ => NumberField.Completion.comap K L _)

def NumberField.Completion.comap_pi_extend (v : InfinitePlace K) :
    v.completion →ₐ[v.completion] ((w : Σ_v) → w.1.completion) :=
  (comap_pi K L v).extendScalars _

def NumberField.Completion.algebraMap_pi_ringHom :
    L →+* ((w : Σ_v) → w.1.completion) :=
  Pi.ringHom <| fun ⟨_, _⟩ => algebraMap _ _

def NumberField.Completion.algebraMap_pi :
    L →ₐ[K] ((w : Σ_v) → w.1.completion) where
  __ := algebraMap_pi_ringHom K v L
  commutes' _ := rfl

theorem NumberField.InfinitePlace.comap_surjective {k : Type u_1} [Field k] {K : Type u_2}
    [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] :
    Function.Surjective fun (x : NumberField.InfinitePlace K) => x.comap (algebraMap k K) :=
  fun w =>
    letI := w.embedding.toAlgebra
    ⟨InfinitePlace.mk (IsAlgClosed.lift (M := ℂ) (R := k)).toRingHom,
      by simp [comap_mk, RingHom.algebraMap_toAlgebra]⟩

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

instance : IsScalarTower K v.completion ((w : Σ_v) → w.1.completion) := by sorry

def NumberField.Completion.baseChange_algHom (v : InfinitePlace K) :
    v.completion ⊗[K] L →ₐ[v.completion] ((w : Σ_v) → w.1.completion) :=
  Algebra.TensorProduct.lift (NumberField.Completion.comap_pi_extend K L v)
    (NumberField.Completion.algebraMap_pi K v L) (fun _ _ => mul_comm _ _)

theorem finrank_eq : FiniteDimensional.finrank v.completion ((w : Σ_v) → w.1.completion) =
    FiniteDimensional.finrank v.completion (v.completion ⊗[K] L) := sorry

theorem NumberField.Completion.baseChange_det_ne_zero (v : InfinitePlace K) :
    let Bv := FiniteDimensional.finBasis v.completion (v.completion ⊗[K] L)
    let Bw := FiniteDimensional.finBasisOfFinrankEq v.completion ((w : Σ_v) → w.1.completion)
      (finrank_eq K v L)
    (LinearMap.toMatrix Bv Bw (baseChange_algHom K L v).toLinearMap).det ≠ 0 := by
  sorry

def NumberField.Completion.baseChange_linearEquiv (v : InfinitePlace K) :
    v.completion ⊗[K] L ≃ₗ[v.completion] ((w : Σ_v) → w.1.completion) :=
  LinearEquiv.ofIsUnitDet (baseChange_det_ne_zero K L v).isUnit

def NumberField.Completion.baseChange (v : InfinitePlace K) :
    v.completion ⊗[K] L ≃ₐ[v.completion] ((w : Σ_v) → w.1.completion) := by
  apply AlgEquiv.ofLinearEquiv (baseChange_linearEquiv K L v)
  · rw [baseChange_linearEquiv]
    rw [LinearEquiv.ofIsUnitDet_apply (baseChange_det_ne_zero K L v).isUnit]
    rw [AlgHom.toLinearMap_apply]
    exact map_one (baseChange_algHom K L v)
  · intro x y
    simp only [baseChange_linearEquiv,
      LinearEquiv.ofIsUnitDet_apply (baseChange_det_ne_zero K L v).isUnit, AlgHom.toLinearMap_apply]
    exact map_mul _ _ _

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

@[simps!]
def AlgEquiv.piCongrLeft (S : Type*) [CommSemiring S] (B : β → Type*) (e : α ≃ β)
    [∀ b, Semiring (B b)] [∀ b, Algebra S (B b)] :
    ((a : α) → B (e a)) ≃ₐ[S] ((b : β) → B b) :=
  (AlgEquiv.piCongrLeft' S B e.symm).symm

def baseChange :
    letI : Algebra K (InfiniteAdeleRing L) := Pi.algebra _ _
    InfiniteAdeleRing K ⊗[K] L ≃ₐ[K] InfiniteAdeleRing L := by
  letI : Algebra K (InfiniteAdeleRing L) := Pi.algebra _ _
  apply AlgEquiv.piLeft K L |>.trans
  have (v : _) := (NumberField.Completion.baseChange K L v).restrictScalars K
  apply AlgEquiv.piCongrRight this |>.trans
  let γ : (v : InfinitePlace K) → (w : Σ_v) → Type _ :=
    fun v w => w.1.completion
  apply AlgEquiv.piCurry K γ |>.symm |>.trans
  have := AlgEquiv.piCongrLeft K (fun w => w.completion)
    (NumberField.Completion.equiv_comap K L).symm
  refine AlgEquiv.trans ?_ this
  simp_rw [NumberField.Completion.equiv_comap_apply, γ]
  exact AlgEquiv.refl

end InfiniteAdeleRing

end NumberField
