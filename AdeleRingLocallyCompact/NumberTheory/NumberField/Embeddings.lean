/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.NumberTheory.NumberField.Embeddings

/-!
# Embeddings of number fields

-/

open scoped Classical

noncomputable section

namespace NumberField.ComplexEmbedding

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (L)

/-- Let K / L be fields. A complex embedding `g` of `L` extends a complex embedding `f` of
`K` if the restriction of `g` to `K` is `f`.  -/
abbrev Extension (f : K →+* ℂ) := { g : L →+* ℂ //  g.comp (algebraMap K L) = f }

variable {L}

/-- Let K / L be fields. If `f` is a complex embedding of `K` and `g` extends `f` to `L`, we
say that `g` is ramified if `f` is real and `g` is complex. -/
def IsRamifiedExtension {f : K →+* ℂ} (g : Extension L f) :=
    ComplexEmbedding.IsReal f ∧ ¬ComplexEmbedding.IsReal g.1

def IsUnramifiedExtension {f : K →+* ℂ} (g : Extension L f) :=
    ¬IsRamifiedExtension g

end ComplexEmbedding

namespace InfinitePlace

open NumberField.ComplexEmbedding

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] (v : InfinitePlace K) (w : InfinitePlace L)

variable {K}

/-- Let K / L be fields. We say that an infinite place `w` of `L` extends an infinite place
`v` of `K` if the restriction of `w` along the injection `K ↪ L` coincides with `v`.
In other words, the infinite place of `w` is represented by a complex embedding that
extends a representative of `v`. -/
abbrev ExtensionPlace := { w : InfinitePlace L // w.comap (algebraMap K L) = v }

variable {L v}
variable (wv : ExtensionPlace L v)

theorem ExtensionPlace.extends_or_conjugate_extends :
    wv.1.embedding.comp (algebraMap K L) = v.embedding ∨
      (ComplexEmbedding.conjugate wv.1.embedding).comp (algebraMap K L) = v.embedding := by
  have := wv.2
  rw [← mk_embedding wv.1, comap_mk] at this
  have := embedding_mk_eq (wv.1.embedding.comp (algebraMap K L))
  cases this with
  | inl h =>
    left
    exact h ▸ congrArg InfinitePlace.embedding this
  | inr h =>
    have := congrArg InfinitePlace.embedding this
    rw [h] at this
    right
    exact this

theorem comap_mk_of_extension (ψ : Extension L v.embedding) :
    (InfinitePlace.mk ψ.1).comap (algebraMap K L) = v := by
  rw [comap_mk, ψ.2, mk_embedding]

theorem isComplex_iff_mult_eq_two : v.IsComplex ↔ v.mult = 2 := by
  simp only [mult, ite_eq_right_iff, OfNat.one_ne_ofNat, imp_false, not_isReal_iff_isComplex]

theorem mult_le_two (v : InfinitePlace K) : v.mult ≤ 2 := by
  simp only [mult]
  by_cases h : v.IsReal
  · simp only [h, if_true, Nat.one_le_ofNat]
  · simp only [h, if_false, le_rfl]

variable (K)

def IsRamified := ¬IsUnramified K w

theorem isRamified_iff : IsRamified K w ↔ w.IsComplex ∧ (w.comap (algebraMap K L)).IsReal :=
  not_isUnramified_iff

variable {K wv}

namespace IsRamified

theorem isComplex (hw : wv.1.IsRamified K) : wv.1.IsComplex := by
  rw [isRamified_iff] at hw
  exact hw.1

theorem extension_embedding_extends (h : IsRamified K wv.1) :
    wv.1.embedding.comp (algebraMap K L) = v.embedding := by
  rw [← mk_embedding wv.1, isRamified_iff, comap_mk, isComplex_mk_iff, isReal_mk_iff] at h
  rw [← embedding_mk_eq_of_isReal h.2, ← comap_mk, mk_embedding wv.1, wv.2]

theorem extension_embedding_conj_extends (h : IsRamified K wv.1) :
    (ComplexEmbedding.conjugate wv.1.embedding).comp (algebraMap K L) = v.embedding := by
  rw [← mk_embedding wv.1, isRamified_iff, comap_mk, isComplex_mk_iff, isReal_mk_iff] at h
  ext k
  simp only [RingHom.coe_comp, Function.comp_apply, conjugate_coe_eq, ← wv.2]
  rw [← mk_embedding wv.1, comap_mk, embedding_mk_eq_of_isReal h.2,
    ← RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 h.2) k, mk_embedding, conjugate_coe_eq,
    RingHom.coe_comp, Function.comp_apply]

/-- If `w` is an unramified infinite place lying above `v`, then the embedding associated to
`w` extends the embedding associated to `v`. -/
abbrev toExtension (h : IsRamified K wv.1) :
    Extension L v.embedding :=
  ⟨wv.1.embedding, h.extension_embedding_extends⟩

theorem toExtension_inj {wv₁ wv₂ : ExtensionPlace L v} (h₁ : IsRamified K wv₁.1)
    (h₂ : IsRamified K wv₂.1) : h₁.toExtension = h₂.toExtension ↔ wv₁ = wv₂ := by
  rw [Subtype.ext_iff_val, Subtype.ext_iff_val, toExtension]
  dsimp
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rw [← mk_embedding wv₁.1, h, mk_embedding]

/-- If `w` is an unramified infinite place lying above `v`, then the conjugate of the embedding
associated to  `w` extends the embedding associated to `v`. -/
abbrev toExtensionConj (h : IsRamified K wv.1) :
    Extension L v.embedding :=
  ⟨ComplexEmbedding.conjugate wv.1.embedding, h.extension_embedding_conj_extends⟩

theorem toExtensionConj_inj {wv₁ wv₂ : ExtensionPlace L v} (h₁ : IsRamified K wv₁.1)
    (h₂ : IsRamified K wv₂.1) :
    h₁.toExtensionConj = h₂.toExtensionConj ↔ wv₁ = wv₂ := by
  rw [Subtype.ext_iff_val, Subtype.ext_iff_val, toExtensionConj]
  dsimp
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  simp only [star_inj] at h
  rw [← mk_embedding wv₁.1, h, mk_embedding]

/-- Ramified extensions of complex embeddings yield ramified extensions of infinite places. -/
theorem of_isRamifiedExtension {ψ : Extension L v.embedding}
    (h : IsRamifiedExtension ψ) : IsRamified K (InfinitePlace.mk ψ.1) := by
  rw [isRamified_iff, isComplex_iff, comap_mk, isReal_iff, ψ.2, embedding_mk_eq_of_isReal h.1]
  refine ⟨?_, h.1⟩
  cases embedding_mk_eq ψ.1 with
  | inl hψ =>
    rw [hψ]; exact h.2
  | inr hψ =>
    rw [hψ, ComplexEmbedding.isReal_conjugate_iff]
    exact h.2

/-- A ramified extension of infinite places determines a ramified extension of the embedding of
the extended place over the embedding of the base place. -/
theorem isRamifiedExtension (h : IsRamified K wv.1) :
    IsRamifiedExtension (toExtension h) := by
  rw [← mk_embedding wv.1, isRamified_iff, comap_mk, isComplex_mk_iff, isReal_mk_iff] at h
  refine ⟨?_, h.1⟩
  convert h.2
  rw [← embedding_mk_eq_of_isReal h.2, ← comap_mk, mk_embedding, wv.2]

/-- A ramified extension of infinite places determines a ramified extension of the conjugate
embedding of the extended place over the embedding of the base place. -/
theorem isRamifiedExtension_conj (h : IsRamified K wv.1) :
    IsRamifiedExtension (toExtensionConj h) := by
  rw [← mk_embedding wv.1, isRamified_iff, comap_mk, isComplex_mk_iff, isReal_mk_iff] at h
  refine ⟨?_, not_congr ComplexEmbedding.isReal_conjugate_iff |>.2 h.1⟩
  convert h.2
  rw [← embedding_mk_eq_of_isReal h.2, ← comap_mk, mk_embedding, wv.2]

/-- The ramified extensions of complex embeddings are equivalent to two copies of the ramified
extensions of infinite places. -/
def sum_equiv_isRamifiedExtension :
    let E_vr := { w : ExtensionPlace L v // IsRamified K w.1 }
    E_vr ⊕ E_vr ≃ { ψ : Extension L v.embedding // IsRamifiedExtension ψ } := by
  let E_vr := { w : ExtensionPlace L v // IsRamified K w.1 }
  let g₁ : E_vr → { ψ : Extension L v.embedding // IsRamifiedExtension ψ } :=
    fun ⟨w, h⟩ => ⟨toExtension h, isRamifiedExtension h⟩
  let g₂ : E_vr → { ψ : Extension L v.embedding // IsRamifiedExtension ψ } :=
    fun ⟨w, h⟩ => ⟨toExtensionConj h, isRamifiedExtension_conj h⟩
  let f := Sum.elim g₁ g₂
  have hg₁_inj : g₁.Injective := by
    intro a b h
    simp only [g₁, toExtension, Subtype.mk.injEq] at h
    ext
    rw [← mk_embedding a.1.1, h, mk_embedding]
  have hg₂_inj : g₂.Injective := by
    intro a b h
    simp only [Subtype.mk.injEq, g₂, toExtension] at h
    simp at h
    ext
    rw [← mk_embedding a.1.1, h, mk_embedding]
  have hg_ne (a : _) (b : _) : g₁ a ≠ g₂ b := by
    simp [g₁, g₂, toExtension, toExtensionConj]
    by_cases hab : a = b
    · --rw [hab, Subtype.mk.injEq]
      rw [hab]
      have := b.2
      rw [isRamified_iff, isComplex_iff, ComplexEmbedding.isReal_iff] at this
      exact Ne.symm this.1
    · contrapose! hab
      have : a.1.1 = b.1.1 := by
        rw [← mk_embedding a.1.1, ← mk_embedding b.1.1, hab, mk_conjugate_eq, mk_embedding]
      let ⟨⟨a, _⟩, _⟩ := a
      let ⟨⟨b, _⟩, _⟩ := b
      congr
  have hf_surj : f.Surjective := by
    intro ⟨ψ, h⟩
    have h' : (mk ψ.1).comap (algebraMap _ _) = v := by rw [comap_mk, ψ.2, mk_embedding]
    cases embedding_mk_eq ψ.1 with
    | inl hl =>
      use Sum.inl ⟨⟨mk ψ.1, h'⟩, of_isRamifiedExtension h⟩
      simp only [toExtension, Sum.elim_inl, hl, Subtype.coe_eta, f, g₁]
    | inr hr =>
      use Sum.inr ⟨⟨mk ψ.1, h'⟩, of_isRamifiedExtension h⟩
      simp only [toExtensionConj, Sum.elim_inr, Subtype.mk.injEq, f, g₂, star_star,
        Subtype.coe_eta, hr]
  exact Equiv.ofBijective _ ⟨hg₁_inj.sum_elim hg₂_inj hg_ne, hf_surj⟩

end IsRamified

namespace IsUnramified

theorem isReal_of_isReal (hv : v.IsReal)
    (hw : wv.1.IsUnramified K) : wv.1.IsReal := by
  refine (InfinitePlace.isUnramified_iff.1 hw).resolve_right ?_
  convert wv.2 ▸ not_isComplex_iff_isReal.2 hv

abbrev toExtension_of_extends
    (he : wv.1.embedding.comp (algebraMap K L) = v.embedding) :
    Extension L v.embedding :=
  ⟨wv.1.embedding, he⟩

abbrev toExtension_of_conj_extends
    (he : (ComplexEmbedding.conjugate wv.1.embedding).comp (algebraMap K L) = v.embedding) :
    Extension L v.embedding :=
  ⟨ComplexEmbedding.conjugate wv.1.embedding, he⟩

theorem isUnramifiedExtension_of_extends (h : IsUnramified K wv.1)
    (he : wv.1.embedding.comp (algebraMap K L) = v.embedding) :
    IsUnramifiedExtension (toExtension_of_extends he) := by
  have := wv.2
  rw [← mk_embedding wv.1] at this
  rw [comap_mk] at this
  contrapose! h
  rw [not_isUnramified_iff]
  rw [IsUnramifiedExtension, not_not] at h
  rw [isComplex_iff]
  use h.2
  rw [isReal_iff]
  rw [← mk_embedding wv.1, comap_mk, he, mk_embedding]
  exact h.1

theorem isUnramifiedExtension_of_conj_extends (h : IsUnramified K wv.1)
    (he : (ComplexEmbedding.conjugate wv.1.embedding).comp (algebraMap K L) = v.embedding) :
    IsUnramifiedExtension (toExtension_of_conj_extends he) := by
  have := wv.2
  rw [← mk_embedding wv.1] at this
  rw [comap_mk] at this
  contrapose! h
  rw [not_isUnramified_iff]
  rw [IsUnramifiedExtension, not_not] at h
  rw [isComplex_iff]
  rw [← NumberField.ComplexEmbedding.isReal_conjugate_iff]
  use h.2
  rw [isReal_iff]
  rw [← mk_embedding wv.1, comap_mk]
  convert h.1

theorem of_isUnramifiedExtension  {ψ : Extension L v.embedding}
    (h' : IsUnramifiedExtension ψ) :
    IsUnramified K (mk ψ.1) := by
  rw [isUnramified_iff]
  rw [IsUnramifiedExtension, IsRamifiedExtension] at h'
  simp at h'
  by_cases h'' : ComplexEmbedding.IsReal v.embedding
  · rw [isReal_iff]
    left
    specialize h' h''
    rwa [embedding_mk_eq_of_isReal h']
  · right
    contrapose! h''
    simp only [comap_mk, not_isComplex_iff_isReal] at h''
    rw [isReal_iff, ComplexEmbedding.isReal_iff] at h''
    rw [ComplexEmbedding.isReal_iff]
    ext k
    simp
    have := RingHom.congr_fun h'' k
    simp at this
    rw [ψ.2] at this
    simp at this
    exact this

open InfinitePlace.ExtensionPlace InfinitePlace

/-- The unramified extensions of complex embeddings are equivalent to the unramified
extensions of infinite places. -/
def equiv_isUnramifiedExtension :
    { w : ExtensionPlace L v // IsUnramified K w.1 } ≃
       { ψ : Extension L v.embedding // IsUnramifiedExtension ψ } := by
  set f : { w : ExtensionPlace L v // IsUnramified K w.1 } →
    { ψ : Extension L v.embedding // IsUnramifiedExtension ψ } :=
      fun ⟨w, h⟩ =>
        if he : w.1.embedding.comp (algebraMap K L) = v.embedding then
          ⟨toExtension_of_extends he, isUnramifiedExtension_of_extends h he⟩ else
          ⟨toExtension_of_conj_extends (w.extends_or_conjugate_extends.resolve_left he),
              isUnramifiedExtension_of_conj_extends h
                (w.extends_or_conjugate_extends.resolve_left he)⟩
  have hf_inj : f.Injective := by
    intro ⟨⟨ψ₁, h₁⟩, h₁'⟩ ⟨⟨ψ₂, h₂⟩, h₂'⟩ h
    simp [f] at h
    simp only [Subtype.mk.injEq]
    by_cases hv : ComplexEmbedding.IsReal v.embedding
    · have : ComplexEmbedding.conjugate ψ₁.embedding = ψ₁.embedding := by
        have := isReal_of_isReal (wv := ⟨ψ₁, h₁⟩) (isReal_iff.2 hv) h₁'
        rw [isReal_iff] at this
        simp at this
        exact this
      simp [toExtension_of_extends, toExtension_of_conj_extends, this] at h
      have : ComplexEmbedding.conjugate ψ₂.embedding = ψ₂.embedding := by
        have := isReal_of_isReal (wv := ⟨ψ₂, h₂⟩) (isReal_iff.2 hv) h₂'
        rw [isReal_iff] at this
        simp at this
        exact this
      simp [this] at h
      split_ifs at h <;>
      · rw [Subtype.mk.injEq, Subtype.mk.injEq] at h
        rw [← mk_embedding ψ₁, h, mk_embedding]
    · split_ifs at h <;> rw [Subtype.mk.injEq, Subtype.mk.injEq] at h
      · rw [← mk_embedding ψ₁, h, mk_embedding]
      · rw [← mk_embedding ψ₁, h]
        simp only [mk_conjugate_eq, mk_embedding]
      · rw [← mk_embedding ψ₂, ← h, mk_conjugate_eq, mk_embedding]
      · simp only [star_inj] at h
        rw [← mk_embedding ψ₁, h, mk_embedding]
  have hf_surj : f.Surjective := by
    intro ⟨ψ, hψ⟩
    by_cases hv : ComplexEmbedding.IsReal v.embedding
    · have hψ' : ComplexEmbedding.IsReal ψ.1 := by
        simp [IsUnramifiedExtension, IsRamifiedExtension] at hψ
        exact hψ hv
      use ⟨⟨mk ψ.1, comap_mk_of_extension ψ⟩, of_isUnramifiedExtension hψ⟩
      simp [f, ψ.2, toExtension_of_extends, embedding_mk_eq_of_isReal hψ']
    cases embedding_mk_eq ψ.1 with
    | inl h =>
      use ⟨⟨mk ψ.1, comap_mk_of_extension ψ⟩, of_isUnramifiedExtension hψ⟩
      simp only [f, ψ.2, toExtension_of_extends, dif_pos, h, hψ, Subtype.coe_eta]
    | inr h =>
      let φ := ComplexEmbedding.conjugate ψ.1
      have h' : (mk φ).comap (algebraMap _ _) = v := by
        rw [← mk_conjugate_eq]
        simp only [φ, star_star]
        exact comap_mk_of_extension ψ
      have : IsUnramified K (mk φ) := by
        rw [← mk_conjugate_eq]
        simp only [φ, star_star]
        exact of_isUnramifiedExtension hψ
      use ⟨⟨mk φ, h'⟩, this⟩
      simp [f]
      have : (mk φ).embedding.comp (algebraMap K L) ≠ v.embedding := by
        rw [← mk_conjugate_eq]
        simp only [φ, star_star, h]
        rw [ComplexEmbedding.isReal_iff] at hv
        intro h
        have := congrArg ComplexEmbedding.conjugate ψ.2
        have h' := congrArg ComplexEmbedding.conjugate h
        simp at h'
        have h'' : ComplexEmbedding.conjugate (ψ.1.comp (algebraMap K L)) =
          (ComplexEmbedding.conjugate ψ.1).comp (algebraMap K L) := rfl
        rw [h'', h'] at this
        exact hv <| Eq.symm this
      simp [this]
      have : (mk ψ.1).embedding = φ := by rw [h]
      simp_rw [← this]
      simp only [toExtension_of_conj_extends, mk_embedding]
      simp only [h]
      simp only [star_star]
  exact Equiv.ofBijective _ ⟨hf_inj, hf_surj⟩

end IsUnramified

namespace ExtensionPlace

theorem card_isUnramified_add_card_isRamified :
    Fintype.card ({w : ExtensionPlace L v // w.1.IsUnramified K}) +
      2 * Fintype.card ({w : ExtensionPlace L v // w.1.IsRamified K}) =
        FiniteDimensional.finrank K L := by
  letI : Algebra K ℂ := v.embedding.toAlgebra
  rw [← AlgHom.card K L ℂ]
  have (φ : L →ₐ[K] ℂ) : φ.toRingHom.comp (algebraMap K L) = v.embedding := by
    have := Function.funext_iff.2 φ.commutes'
    rw [RingHom.algebraMap_toAlgebra] at this
    simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.commutes,
      DFunLike.coe_fn_eq] at this
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower]

  let g : (L →ₐ[K] ℂ) → Extension L v.embedding :=
    fun φ => ⟨φ.toRingHom, this φ⟩

  have hg_inj : g.Injective := by
    intro φ₁ φ₂ h
    simp [g] at h
    exact AlgHom.coe_ringHom_injective h

  have {σ : L →+* ℂ} (h : σ.comp (algebraMap K L) = v.embedding) :
      ∀ (r : K), σ.toFun (algebraMap K L r) = algebraMap K ℂ r := by
    intro k
    rw [RingHom.algebraMap_toAlgebra, ← h]
    rfl

  have hg_surj : g.Surjective := by
    intro ⟨σ, h⟩
    use {
      __ := σ
      commutes' := this h
    }

  have : (L →ₐ[K] ℂ) ≃ Extension L v.embedding :=
    Equiv.ofBijective _ ⟨hg_inj, hg_surj⟩

  rw [Fintype.card_eq.2 ⟨this⟩]

  have : Extension L v.embedding ≃
    { ψ : Extension L v.embedding // IsRamifiedExtension ψ } ⊕
      { ψ : Extension L v.embedding // ¬IsRamifiedExtension ψ } :=
        (Equiv.sumCompl _).symm

  rw [Fintype.card_eq.2 ⟨this⟩]
  rw [Fintype.card_sum]
  rw [Fintype.card_eq.2 ⟨IsRamified.sum_equiv_isRamifiedExtension.symm⟩]
  rw [Fintype.card_sum]
  have : Fintype.card { ψ : Extension L v.embedding // IsUnramifiedExtension ψ } =
      Fintype.card { ψ : Extension L v.embedding // ¬IsRamifiedExtension ψ } := by
    simp only [IsUnramifiedExtension]
    simp only [Fintype.card_subtype_compl]
  rw [← this]
  rw [Fintype.card_eq.2 ⟨IsUnramified.equiv_isUnramifiedExtension.symm⟩]
  ring

def ramificationIdx (w : ExtensionPlace L v) := if w.1.IsUnramified K then 1 else 2

variable (K L v)

theorem sum_ramificationIdx_eq :
    ∑ w : ExtensionPlace L v, w.ramificationIdx = FiniteDimensional.finrank K L := by
  let e : ExtensionPlace L v ≃
      { w : ExtensionPlace L v // w.1.IsUnramified K } ⊕
        { w : ExtensionPlace L v // w.1.IsRamified K } :=
    (Equiv.sumCompl _).symm
  rw [Fintype.sum_equiv e _ ((fun w => w.ramificationIdx) ∘ e.symm)
    (fun _ => by simp only [Function.comp_apply, Equiv.symm_apply_apply])]
  simp only [Function.comp_apply, Fintype.sum_sum_type, e, Equiv.symm_symm, IsRamified,
    Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
  have (x : { w : ExtensionPlace L v // IsUnramified K w.1 }) : x.1.ramificationIdx = 1 := by
    simp [ramificationIdx, x.2]
  simp_rw [this]
  have (x : { w : ExtensionPlace L v // IsRamified K w.1 }) : x.1.ramificationIdx = 2 := by
    simp [ramificationIdx]; rw [← IsRamified]; exact x.2
  simp_rw [this]
  rw [Finset.sum_const, Finset.sum_const, ← Fintype.card, ← Fintype.card, smul_eq_mul, mul_one,
    smul_eq_mul, mul_comm, ← card_isUnramified_add_card_isRamified]
  rfl

variable {K L v}

theorem isReal_extends (hv : v.IsReal) : wv.1.embedding.comp (algebraMap K L) = v.embedding := by
  cases wv.extends_or_conjugate_extends with
  | inl h => exact h
  | inr h =>
    have := conjugate_embedding_eq_of_isReal hv
    rw [← this]
    simp [conjugate] at h
    have : (star (wv.1.embedding)).comp (algebraMap K L) =
      star (wv.1.embedding.comp (algebraMap K L)) := rfl
    rw [this] at h
    rw [← h]
    simp only [star_star]

theorem isComplex_of_isComplex (h : v.IsComplex) : wv.1.IsComplex := by
  rw [isComplex_iff_mult_eq_two] at *
  have := h ▸ wv.2 ▸ wv.1.mult_comap_le _
  exact le_antisymm wv.1.mult_le_two this

end ExtensionPlace

end InfinitePlace
