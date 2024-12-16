/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.Tactic
import AdeleRingLocallyCompact.Analysis.Normed.Ring.WithAbs
import AdeleRingLocallyCompact.FromMathlib.Algebra.Order.GroupWithZero.Unbundled
import AdeleRingLocallyCompact.FromMathlib.Analysis.SpecialFunctions.Pow.Real
import AdeleRingLocallyCompact.FromMathlib.Data.Fin.Lemmas
import AdeleRingLocallyCompact.FromMathlib.LinearAlgebra.TensorProduct.Pi

open scoped Topology Classical

open NumberField

noncomputable section

namespace AbsoluteValue

variable (K L : Type*) [Field K] {v : AbsoluteValue K ℝ} {w : AbsoluteValue K ℝ}

variable {K}

def IsEquivalentTo : AbsoluteValue K ℝ → AbsoluteValue K ℝ → Prop := fun v w =>
  ∃ (t : ℝ) (_: 0 < t), ∀ x, v x = (w x) ^ t

theorem isEquivalentTo_iff : v.IsEquivalentTo w ↔ ∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t :=
  Iff.rfl

def IsNontrivial : AbsoluteValue K ℝ → Prop := fun v => ∃ x ≠ 0, v x ≠ 1

theorem isNontrivial_iff : v.IsNontrivial ↔ ∃ x ≠ 0, v x ≠ 1 := Iff.rfl

theorem not_isNontrivial_iff : ¬v.IsNontrivial ↔ ∀ x ≠ 0, v x = 1 := by
  rw [isNontrivial_iff]
  simp_rw [ne_eq, ← not_or, ← not_forall, not_not, imp_iff_or_not, not_not, or_comm]

theorem inv_pos {x : K} (h : 0 < v x) : 0 < v x⁻¹ := by
  rwa [map_inv₀, _root_.inv_pos]

theorem eq_one_of_forall_one_le (h : ∀ x, 0 < v x → 1 ≤ v x) {x : K} (hx : x ≠ 0) : v x = 1 := by
  apply le_antisymm _ (h x (v.pos hx))
  have := map_inv₀ v _ ▸ h _ (v.inv_pos (v.pos hx))
  rw [one_le_inv_iff] at this
  exact this.2

theorem exists_lt_one_of_nontrivial
    (h : v.IsNontrivial) :
    ∃ x, 0 < v x ∧ v x < 1 := by
  contrapose! h
  rw [not_isNontrivial_iff]
  intro x hx
  exact v.eq_one_of_forall_one_le h hx

theorem exists_one_lt_of_nontrivial
    (h : v.IsNontrivial) :
    ∃ x, 1 < v x := by
  let ⟨x, h⟩ := exists_lt_one_of_nontrivial h
  exact ⟨x⁻¹, by rwa [map_inv₀, one_lt_inv_iff]⟩

theorem ne_zero_of_lt_one {x : K} (hv : 1 < v x) :
    x ≠ 0 := by
  intro hx
  rw [hx, map_zero] at hv
  linarith

theorem nonpos_iff (x : K) : v x ≤ 0 ↔ v x = 0 := by
  simp only [le_antisymm_iff, v.nonneg _, and_true]

theorem inv_lt_one_iff {x : K} : v x⁻¹ < 1 ↔ x = 0 ∨ 1 < v x := by
  simp only [map_inv₀, _root_.inv_lt_one_iff, nonpos_iff, map_eq_zero]

theorem one_lt_inv_iff {x : K} : 1 < v x⁻¹ ↔ 0 < v x ∧ v x < 1 := by
  simp only [map_inv₀, _root_.one_lt_inv_iff, v.pos_iff]

--theorem inv_ne_one {x : K} : v x⁻¹ ≠ 1 ↔ v x ≠ 1 := by
 -- simp only [map_inv₀, ne_eq, inv_eq_one]

theorem one_lt_of_lt_one {v w : AbsoluteValue K ℝ}
    (h : ∀ x, v x < 1 → w x < 1) {x : K} (hv : 1 < v x) : 1 < w x :=
  (inv_lt_one_iff.1 <| h _ <| map_inv₀ v _ ▸ inv_lt_one hv).resolve_left <| ne_zero_of_lt_one hv

theorem one_lt_iff_of_lt_one_iff {v w : AbsoluteValue K ℝ}
    (h : ∀ x, v x < 1 ↔ w x < 1) (x : K) : 1 < v x ↔ 1 < w x :=
  ⟨fun hv => one_lt_of_lt_one (fun _ => (h _).1) hv,
    fun hw => one_lt_of_lt_one (fun _ => (h _).2) hw⟩

theorem eq_one_of_lt_one_iff {v w : AbsoluteValue K ℝ}
    (h : ∀ x, v x < 1 ↔ w x < 1) {x : K} (hv : v x = 1) : w x = 1 := by
  cases eq_or_lt_of_le (not_lt.1 <| (h x).not.1 hv.not_lt) with
  | inl hl => rw [← hl]
  | inr hr => rw [← one_lt_iff_of_lt_one_iff h] at hr; linarith

theorem eq_one_iff_of_lt_one_iff {v w : AbsoluteValue K ℝ}
    (h : ∀ x, v x < 1 ↔ w x < 1) (x : K) : v x = 1 ↔ w x = 1 :=
  ⟨fun hv => eq_one_of_lt_one_iff h hv, fun hw => eq_one_of_lt_one_iff (fun _ => (h _).symm) hw⟩

theorem log_div_image_eq_singleton_of_le_one_iff {v w : AbsoluteValue K ℝ} (hv : v.IsNontrivial)
    (h : ∀ x, v x < 1 ↔ w x < 1) :
    let f : K → ℝ := fun a => Real.log (v a) / Real.log (w a)
    ∃ (a : K) (_ : 1 < v a), ∀ (b : K) (_ : 1 < v b), f b = f a := by
  obtain ⟨a, ha⟩ := exists_one_lt_of_nontrivial hv
  refine ⟨a, ha, fun b hb => ?_⟩
  by_contra! hb₂
  wlog hwlog : Real.log (v b) / Real.log (w b) < Real.log (v a) / Real.log (w a) generalizing a b
  · exact this b hb a ha hb₂.symm <| lt_of_le_of_ne (not_lt.1 hwlog) hb₂.symm
  have : Real.log (v b) / Real.log (v a) < Real.log (w b) / Real.log (w a) := by
    have hwa := (one_lt_iff_of_lt_one_iff h _).1 ha
    have hwb := (one_lt_iff_of_lt_one_iff h _).1 hb
    rw [div_lt_div_iff (Real.log_pos ha) (Real.log_pos hwa)]
    nth_rw 2 [mul_comm]
    rwa [← div_lt_div_iff (Real.log_pos hwb) (Real.log_pos hwa)]
  let ⟨q, hq⟩ := exists_rat_btwn this
  rw [← Rat.num_div_den q, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] at hq
  have h₀ : v (b ^ q.den / a ^ q.num) < 1 := by
    have := hq.1
    have hwb := (one_lt_iff_of_lt_one_iff h _).1 hb
    rwa [div_lt_div_iff (Real.log_pos ha) (by simp only [Nat.cast_pos, q.den_pos]), mul_comm,
      ← Real.log_pow, ← Real.log_zpow,
      Real.log_lt_log_iff (pow_pos (by linarith) _) (zpow_pos_of_pos (by linarith) _),
      ← div_lt_one (zpow_pos_of_pos (by linarith) _), ← map_pow, ← map_zpow₀, ← map_div₀] at this
  have h₁ : 1 < w (b ^ q.den / a ^ q.num) := by
    have hwa := (one_lt_iff_of_lt_one_iff h _).1 ha
    have hwb := (one_lt_iff_of_lt_one_iff h _).1 hb
    have := hq.2
    rw [div_lt_div_iff (by simp only [Nat.cast_pos, q.den_pos]) (Real.log_pos hwa)] at this
    nth_rw 2 [mul_comm] at this
    rwa [← Real.log_pow, ← Real.log_zpow,
      Real.log_lt_log_iff (zpow_pos_of_pos (by linarith) _) (pow_pos (by linarith) _),
      ← one_lt_div (zpow_pos_of_pos (by linarith) _), ← map_pow, ← map_zpow₀, ← map_div₀] at this
  exact not_lt_of_lt ((h _).1 h₀) h₁

open Real in
theorem isEquivalentTo_iff_lt_one_iff (v w : AbsoluteValue K ℝ) (hv : v.IsNontrivial) :
    v.IsEquivalentTo w ↔ (∀ x, v x < 1 ↔ w x < 1) := by
  rw [isEquivalentTo_iff]
  refine ⟨fun ⟨t, ht, h⟩ x => h x ▸ Real.rpow_lt_one_iff' (w.nonneg _) ht, fun h => ?_⟩
  have h' := one_lt_iff_of_lt_one_iff h
  suffices : ∃ (t : ℝ) (_ : t > 0), ∀ x, 1 < v x → v x = w x ^ t
  · obtain ⟨t, ht, hsuff⟩ := this
    refine ⟨t, ht, fun x => ?_⟩
    by_cases h₀ : v x = 0
    · rw [(map_eq_zero v).1 h₀, map_zero, map_zero, zero_rpow (by linarith)]
    · by_cases h₁ : v x = 1
      · rw [h₁, (eq_one_iff_of_lt_one_iff h x).1 h₁, one_rpow]
      · by_cases h₂ : 0 < v x ∧ v x < 1
        · rw [← inv_inj, ← map_inv₀ v, hsuff _ (one_lt_inv_iff.2 h₂), map_inv₀,
            Real.inv_rpow (w.nonneg _)]
        · rw [← one_lt_inv_iff, not_lt] at h₂
          rw [← ne_eq, ← inv_ne_one, ← map_inv₀] at h₁
          exact hsuff _ <| (inv_lt_one_iff.1 <| lt_of_le_of_ne h₂ h₁).resolve_left
            ((map_ne_zero v).1 h₀)
  obtain ⟨a, ha, hlog⟩ := log_div_image_eq_singleton_of_le_one_iff hv h
  use Real.log (v a) / Real.log (w a)
  use div_pos (Real.log_pos ha) (Real.log_pos ((h' a).1 ha))
  intro b hb
  simp_rw [← hlog b hb]
  rw [div_eq_inv_mul, Real.rpow_mul (AbsoluteValue.nonneg _ _),
    Real.rpow_inv_log, Real.exp_one_rpow, Real.exp_log (by linarith)]
  · linarith [(one_lt_iff_of_lt_one_iff h b).1 hb]
  · linarith [(one_lt_iff_of_lt_one_iff h b).1 hb]

end AbsoluteValue

namespace NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]
variable (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
  (v : InfinitePlace K)

theorem eq_of_isEquivalentTo {v w : InfinitePlace K}
    (h : v.1.IsEquivalentTo w.1) :
    v = w := by
  rw [AbsoluteValue.IsEquivalentTo] at h
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

theorem abs_nontrivial : AbsoluteValue.IsNontrivial v.1 := by
  rw [AbsoluteValue.isNontrivial_iff]
  use 2, by norm_num
  let ⟨φ, hφ⟩ := v.2
  rw [← hφ]
  simp only [place_apply, map_ofNat, RCLike.norm_ofNat, ne_eq, OfNat.ofNat_ne_one,
    not_false_eq_true]

theorem exists_lt_one_one_le {v w : InfinitePlace K} (h : v ≠ w) :
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
  exact h <| eq_of_isEquivalentTo K
    ((AbsoluteValue.isEquivalentTo_iff_lt_one_iff _ _ (abs_nontrivial _ _)).2 this)

theorem exists_lt_one_one_lt {v w : InfinitePlace K} (h : v ≠ w) :
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

def toENNReal (v : InfinitePlace K) := ENNReal.ofReal ∘ v

theorem toENNReal_eq (v : InfinitePlace K) (x : K) :
    (toENNReal v x).toReal = v x := by
  simp only [toENNReal, Function.comp_apply, apply_nonneg, ENNReal.toReal_ofReal]

theorem apply_eq_norm (v : InfinitePlace K) {a : K} :
    v a = @norm (WithAbs v.1) _ a :=
  rfl

def unitsEquiv (v : InfinitePlace K) :
    (WithAbs v.1)ˣ ≃ Kˣ := Equiv.refl _

def equiv (v : InfinitePlace K) : WithAbs v.1 ≃ K := Equiv.refl _

abbrev oneAddPow (v : InfinitePlace K) (n : ℕ) : K → WithAbs v.1 :=
  fun a => (equiv v).symm (1 + a ^ n)

abbrev oneSubPow (v : InfinitePlace K) (n : ℕ) : K → WithAbs v.1 :=
  fun a => (equiv v).symm (1 - a ^ n)

theorem one_add_pos {v : InfinitePlace K} {a : K} (ha : v a ≠ 1) :
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

theorem one_add_pow_pos {v : InfinitePlace K} {a : K} (ha : v a ≠ 1) (n : ℕ) :
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

theorem one_add_ne_zero {v : InfinitePlace K} {a : K} (ha : v a ≠ 1) :
    1 + a ≠ 0 := by
  contrapose! ha
  rw [eq_neg_add_of_add_eq ha, add_zero, apply_eq_norm, norm_neg, norm_one]

theorem oneAddPow_ne_zero {v : InfinitePlace K} {a : K} (ha : v a ≠ 1) (n : ℕ) :
    oneAddPow v n a ≠ 0 := by
  by_cases h₀ : n = 0
  · rw [h₀, oneAddPow, equiv, Equiv.refl, pow_zero]
    norm_num
  · have : v (a ^ n) ≠ 1 := by
      rwa [ne_eq, map_pow, pow_eq_one_iff_of_nonneg (AbsoluteValue.nonneg _ _) h₀]
    contrapose! this
    rw [eq_neg_add_of_add_eq this, add_zero, apply_eq_norm, norm_neg, norm_one]

theorem ne_one_inv {v : InfinitePlace K} {a : K} (ha : v a ≠ 1) : v a⁻¹ ≠ 1 := by
  contrapose! ha
  simp at ha
  exact ha

theorem oneAddPow_isUnit {v : InfinitePlace K} {a : K} (ha : v a ≠ 1) (n : ℕ) :
    IsUnit (oneAddPow v n a) := by
  rw [isUnit_iff_ne_zero]
  exact oneAddPow_ne_zero ha n

abbrev oneAddPow_units (v : InfinitePlace K) (n : ℕ) :
    { a : K // v a ≠ 1 } → (WithAbs v.1)ˣ :=
  fun ⟨_, ha⟩ => (oneAddPow_isUnit ha n).unit

theorem apply_add_le (v : InfinitePlace K) (a b : K) : v (a + b) ≤ v a + v b := by
  simp only [apply_eq_norm]
  exact norm_add_le _ _

theorem abs_sub_apply_le (v : InfinitePlace K) (a b : K) :
    |v a - v b| ≤ v (a - b) := by
  simp only [apply_eq_norm]
  exact abs_norm_sub_norm_le _ _

theorem sub_apply_le_of_le {v : InfinitePlace K} (a b : K) (h : v b ≤ v a) :
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

theorem tendsto_oneAddPow_nhds_one {v : InfinitePlace K} {a : K} (ha : v a < 1) :
    Filter.Tendsto (fun n => oneAddPow v n a) Filter.atTop (𝓝 1) := by
  rw [← add_zero (1 : WithAbs v.1)]
  apply Filter.Tendsto.const_add
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_pow]
  apply tendsto_pow_atTop_nhds_zero_of_lt_one (AbsoluteValue.nonneg _ _) ha

theorem tendsto_oneSubPow {v : InfinitePlace K} {a : K} (ha : v a < 1) :
    Filter.Tendsto (fun n => oneSubPow v n a) Filter.atTop (𝓝 1) := by
  rw [← sub_zero 1]
  apply Filter.Tendsto.const_sub
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_pow]
  apply tendsto_pow_atTop_nhds_zero_of_lt_one (AbsoluteValue.nonneg _ _) ha

theorem  tendsto_div_oneAddPow_nhds_one {v : InfinitePlace K} {a : K} (ha : v a < 1) :
    Filter.Tendsto (fun n : ℕ => 1 / (oneAddPow v n a)) Filter.atTop (𝓝 1) := by
  nth_rw 2 [show (1 : WithAbs v.1) = 1 / 1 by norm_num]
  exact Filter.Tendsto.div tendsto_const_nhds (tendsto_oneAddPow_nhds_one ha) one_ne_zero

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

theorem exists_lt_one_one_lt_pi {n : ℕ}
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

instance {w : InfinitePlace L} : Algebra K (WithAbs w.1) := ‹Algebra K L›

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
