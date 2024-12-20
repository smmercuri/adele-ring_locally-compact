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
import AdeleRingLocallyCompact.FromMathlib.Topology.Constructions

open scoped Topology Classical

open NumberField

noncomputable section

namespace AbsoluteValue

variable (K L : Type*) [Field K] {v : AbsoluteValue K ℝ} {w : AbsoluteValue K ℝ}

variable {K}

abbrev norm : (v : AbsoluteValue K ℝ) → (WithAbs v → ℝ) := fun v => Norm.norm (E := WithAbs v)

theorem norm_def : v.norm = Norm.norm (E := WithAbs v) := rfl

theorem inv_pos {x : K} (h : 0 < v x) : 0 < v x⁻¹ := by
  rwa [map_inv₀, _root_.inv_pos]

theorem eq_one_of_forall_one_le (h : ∀ x, 0 < v x → 1 ≤ v x) {x : K} (hx : x ≠ 0) : v x = 1 := by
  apply le_antisymm _ (h x (v.pos hx))
  have := map_inv₀ v _ ▸ h _ (v.inv_pos (v.pos hx))
  rw [one_le_inv_iff] at this
  exact this.2

theorem exists_lt_one_of_exists_ne_one
    (h : ∃ x ≠ 0, v x ≠ 1) :
    ∃ x, 0 < v x ∧ v x < 1 := by
  contrapose! h
  exact fun x hx => v.eq_one_of_forall_one_le h hx

theorem exists_one_lt_of_exists_ne_one
    (h : ∃ x ≠ 0, v x ≠ 1) :
    ∃ x, 1 < v x := by
  let ⟨x, h⟩ := exists_lt_one_of_exists_ne_one h
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

theorem pos_of_pos {v : AbsoluteValue K ℝ} {a : K} (w : AbsoluteValue K ℝ) (hv : 0 < v a) :
    0 < w a := by
  rwa [AbsoluteValue.pos_iff] at hv ⊢

theorem log_div_image_eq_singleton_of_le_one_iff {v w : AbsoluteValue K ℝ}
    (hv : ∃ x ≠ 0, v x ≠ 1)
    (h : ∀ x, v x < 1 ↔ w x < 1) :
    let f : K → ℝ := fun a => Real.log (v a) / Real.log (w a)
    ∃ (a : K) (_ : 1 < v a), ∀ (b : K) (_ : 1 < v b), f b = f a := by
  obtain ⟨a, ha⟩ := exists_one_lt_of_exists_ne_one hv
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
theorem eq_pow_iff_lt_one_iff (v w : AbsoluteValue K ℝ) (hv : ∃ x ≠ 0, v x ≠ 1) :
    (∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t) ↔ (∀ x, v x < 1 ↔ w x < 1) := by
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

theorem exists_lt_one_one_le_of_ne_pow (hv : ∃ x ≠ 0, v x ≠ 1)
    (h : ¬∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t) :
    ∃ a : K, v a < 1 ∧ 1 ≤ w a := by
  by_contra! h'
  let ⟨x₀, hx₀⟩ := exists_lt_one_of_exists_ne_one hv
  have : ∀ a : K, v a < 1 ↔ w a < 1 := by
    intro a
    refine ⟨h' a, ?_⟩
    intro hw
    by_contra h''
    simp at h''
    have (n : ℕ) (hn : n ≠ 0) : w (x₀) < w a ^ n ∧ w a ^ n < 1 := by
      refine ⟨?_, ?_⟩
      · have : v (x₀ * (1 / a ^ n)) < 1 := by
          rw [map_mul]
          have : v (1 / a ^ n) ≤ 1 := by
            rw [one_div, map_inv₀, map_pow]
            apply inv_le_one
            apply one_le_pow₀ h''
          rw [one_div, map_inv₀, map_pow]
          rw [mul_inv_lt_iff, mul_one]
          · apply lt_of_lt_of_le hx₀.2
            apply one_le_pow₀ h''
          · apply pow_pos (by linarith)
        have := h' _ this
        rw [map_mul, one_div, map_inv₀, mul_inv_lt_iff, mul_one, map_pow] at this
        · exact this
        · rw [map_pow]
          apply pow_pos (pos_of_pos w (by linarith))
      · apply pow_lt_one (w.nonneg _) hw hn
    have hwn : Filter.Tendsto (fun n => w.norm a ^ n) Filter.atTop (𝓝 0) := by
      simp only [tendsto_pow_atTop_nhds_zero_iff, abs_norm]
      exact hw
    have hcontr : Filter.Tendsto (fun (_ : ℕ) => w x₀) Filter.atTop (𝓝 0) := by
      have hf : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0) := tendsto_const_nhds
      have hwf : ∀ᶠ (_ : ℕ) in Filter.atTop, 0 ≤ w x₀ := by
        simp only [one_div, map_inv₀, inv_nonneg, apply_nonneg, Filter.eventually_atTop, ge_iff_le,
          implies_true, exists_const]
      have hwn' : ∀ᶠ n in Filter.atTop, w (x₀) ≤ w.norm a ^ n := by
        simp only [Filter.eventually_atTop, ge_iff_le]
        use 1
        intro n hn
        exact le_of_lt (this n (by linarith)).1
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := fun _ => w x₀) hf hwn hwf hwn'
    have hcontr := tendsto_nhds_unique hcontr tendsto_const_nhds |>.symm
    have := pos_of_pos w hx₀.1
    linarith
  rw [eq_pow_iff_lt_one_iff _ _ hv] at h
  exact h this

theorem ne_pow_symm (h : ¬∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t) :
    ¬∃ (t : ℝ) (_ : 0 < t), ∀ x, w x = (v x) ^ t := by
  simp_all
  intro t ht
  let ⟨x, hx⟩ := h t⁻¹ (_root_.inv_pos.2 ht)
  use x
  contrapose! hx
  rw [Real.eq_rpow_inv (v.nonneg _) (w.nonneg _) (by linarith)]
  exact hx.symm

theorem exists_lt_one_one_lt_of_ne_pow
    (hv : ∃ x ≠ 0, v x ≠ 1)
    (hw : ∃ x ≠ 0, w x ≠ 1)
    (h : ¬∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t) :
    ∃ a : K, 1 < v a ∧ w a < 1 := by
  obtain ⟨a, ha⟩ := exists_lt_one_one_le_of_ne_pow hv h
  obtain ⟨b, hb⟩ := exists_lt_one_one_le_of_ne_pow hw (ne_pow_symm h)
  use b / a
  rw [map_div₀, map_div₀]
  constructor
  · rw [one_lt_div]
    · linarith
    · by_contra hv
      simp at hv
      exact v.pos_iff.1 (pos_of_pos v (by linarith)) hv
  · rw [div_lt_one]
    · linarith
    · linarith

end AbsoluteValue

namespace NumberField.InfinitePlace

open AbsoluteValue

variable (K : Type*) [Field K] [NumberField K]
variable (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
  {v w : InfinitePlace K}

variable {K}

-- from mathlib
lemma coe_apply {K : Type*} [Field K] (v : InfinitePlace K) (x : K) :
    v x = v.1 x := rfl

theorem eq_of_eq_pow (h : ∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t) : v = w := by
  let ⟨t, _, h⟩ := h
  have ht : t = 1 := by
    let ⟨ψv, hψv⟩ := v.2
    let ⟨ψw, hψw⟩ := w.2
    simp only [coe_apply, ← hψv, ← hψw, Rat.cast_ofNat, place_apply, map_ofNat,
      RCLike.norm_ofNat] at h
    have := congrArg (Real.logb 2) (h 2)
    norm_num at this
    exact this.symm
  simp only [ht, Real.rpow_one] at h
  exact Subtype.ext <| AbsoluteValue.ext h

theorem eq_pow_of_eq (h : v = w) : ∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t :=
  ⟨1, by linarith, fun x => by rw [h, Real.rpow_one]⟩

variable (v)

theorem exists_ne_one : ∃ x ≠ 0, v x ≠ 1 := by
  use 2, by norm_num
  let ⟨φ, hφ⟩ := v.2
  simp only [coe_apply, ← hφ, place_apply, map_ofNat, RCLike.norm_ofNat, ne_eq, OfNat.ofNat_ne_one,
    not_false_eq_true]

variable {v}

theorem apply_eq_norm (v : InfinitePlace K) {a : K} : v a = v.1.norm a := rfl

theorem one_add_ne_zero {a : K} (ha : v a ≠ 1) :
    1 + a ≠ 0 := by
  contrapose! ha
  rw [eq_neg_add_of_add_eq ha, add_zero, apply_eq_norm, AbsoluteValue.norm, norm_neg, norm_one]

theorem one_add_pow_ne_zero {a : K} (ha : v a ≠ 1) :
    1 + a ^ n ≠ 0 := by
  by_cases h₀ : n = 0
  · rw [h₀]; norm_num
  · have : v (a ^ n) ≠ 1 := by
      rwa [ne_eq, map_pow, pow_eq_one_iff_of_nonneg (AbsoluteValue.nonneg _ _) h₀]
    exact one_add_ne_zero this

theorem apply_one_add_pos {v : InfinitePlace K} {a : K} (ha : v a ≠ 1) :
    0 < v (1 + a) := by
  rw [coe_apply, v.1.pos_iff]
  exact one_add_ne_zero ha

theorem apply_one_add_pow_pos {v : InfinitePlace K} {a : K} (ha : v a ≠ 1) (n : ℕ) :
    0 < v (1 + a ^ n) := by
  rw [coe_apply, v.1.pos_iff]
  exact one_add_pow_ne_zero ha

theorem ne_one_inv {v : InfinitePlace K} {a : K} (ha : v a ≠ 1) : v a⁻¹ ≠ 1 := by
  contrapose! ha
  simp at ha
  exact ha

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

theorem tendsto_pow_mul_atTop {v : InfinitePlace K} {a b : K} (ha : 1 < v a) (hb : 0 < v b) :
    Filter.Tendsto (fun (n : ℕ) => v (a ^ n * b)) Filter.atTop Filter.atTop := by
  simp_rw [map_mul v, map_pow]
  exact Filter.Tendsto.atTop_mul_const hb (tendsto_pow_atTop_atTop_of_one_lt ha)

theorem tendsto_pow_mul_zero {v : InfinitePlace K} {a : K} (ha : v a < 1) (b : K) :
    Filter.Tendsto (fun (n : ℕ) => v (a ^ n * b)) Filter.atTop (𝓝 0) := by
  simp_rw [map_mul, map_pow]
  rw [← zero_mul (v b)]
  exact Filter.Tendsto.mul_const _ <|
    tendsto_pow_atTop_nhds_zero_of_lt_one (AbsoluteValue.nonneg _ _) ha

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

theorem tendsto_apply_div_one_add_pow_nhds_one {v : InfinitePlace K} {a : K} (ha : v a < 1) :
    Filter.Tendsto (fun (n : ℕ) => v (1 / (1 + a ^ n))) Filter.atTop (𝓝 1) := by
  simp_rw [apply_eq_norm, norm_div, norm_one]
  nth_rw 2 [show (1 : ℝ) = 1 / 1 by norm_num]
  apply Filter.Tendsto.div tendsto_const_nhds _ one_ne_zero
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


theorem tendsto_pow_mul_div_one_add_pow_one {v : InfinitePlace K} {a : K}
    (ha : v a < 1) (b : K) :
    Filter.Tendsto (fun (n : ℕ) => v (1 / (1 + a ^ n) * b)) Filter.atTop (𝓝 (v b)) := by
  simp_rw [map_mul]
  nth_rw 2 [← one_mul (v b)]
  apply Filter.Tendsto.mul_const _ (tendsto_apply_div_one_add_pow_nhds_one ha)

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

theorem tendsto_pow_mul_div_one_add_pow_zero {v : InfinitePlace K} {a : K}
    (ha : 1 < v a) (b : K) :
    Filter.Tendsto (fun (n : ℕ) => v ((1 / (1 + a ^ n)) * b)) Filter.atTop (𝓝 0) := by
  simp_rw [map_mul]
  rw [← zero_mul (v b)]
  apply Filter.Tendsto.mul_const _ (tendsto_pow_div_one_add_pow_zero ha)

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

-- Abstract to absolute value

-- 3 cases I need for the above
-- |a|_N < 1 is easy and do not need to take any limits
-- |a|_N = 1 then I need to use a ^ r * b, which → ∞ at i = 0, → 0 for all i ≠ 0, N and
-- obv at N we have = |b|_N < 1
-- |a|_N > 1 then I need to use a ^ r / (1 + a ^ r) * b, which → b at i = 0, N → 0 at i ≠ 0, N,

open Filter in
theorem exists_tendsto_zero_tendsto_atTop_tendsto_const
    {ι : Type*}
    {v : ι → InfinitePlace K}
    {w : InfinitePlace K}
    {a b : K}
    {i : ι}
    (ha : 1 < v i a)
    (haj : ∀ j ≠ i, v j a < 1)
    (haw : w a = 1)
    (hb : 1 < v i b)
    (hbw : w b < 1) :
    ∃ c : ℕ → K,
      Tendsto (fun n => (v i).1.norm (c n)) atTop atTop ∧
        (∀ j ≠ i, Tendsto (fun n => (v j).1.norm (c n)) atTop (𝓝 0)) ∧
          (∀ n, w (c n) < 1) := by
  have h₁ := tendsto_pow_mul_atTop ha (show 0 < v i b by linarith)
  have hₙ (j : _) (hj : j ≠ i) := tendsto_pow_mul_zero (haj j hj) b
  use fun n => a ^ n * b
  use h₁, hₙ
  simp [haw]
  exact hbw

theorem exists_le_one_one_lt_of_eq_one
    {ι : Type*}
    [Fintype ι]
    {v : ι → InfinitePlace K}
    {w : InfinitePlace K}
    {a b : K}
    {i : ι}
    (ha : 1 < v i a)
    (haj : ∀ j ≠ i, v j a < 1)
    (haw : w a = 1)
    (hb : 1 < v i b)
    (hbw : w b < 1) :
    ∃ k : K, 1 < v i k ∧ (∀ j ≠ i, v j k < 1) ∧ w k < 1 := by
  let ⟨c, hc⟩ := exists_tendsto_zero_tendsto_atTop_tendsto_const ha haj haw hb hbw
  simp_rw [Metric.tendsto_nhds] at hc
  simp_rw [Filter.tendsto_atTop_atTop, Filter.eventually_atTop] at hc
  let ⟨r₁, hr₁⟩ := hc.1 2
  choose rₙ hrₙ using fun j hj => hc.2.1 j hj 1 (by linarith)
  simp only [dist_zero_right, norm_norm] at hr₁ hrₙ
  let ri : ι → ℕ := fun j => if h : j = i then r₁ else rₙ j h
  let r := (Finset.univ.sup ri)
  have h₀ : ri i = r₁ := by simp [ri]
  have : r₁ ≤ r := by rw [← h₀]; exact Finset.le_sup (Finset.mem_univ _)
  simp at this
  refine ⟨c r, lt_of_lt_of_le (by linarith) (hr₁ r this), ?_, hc.2.2 r⟩
  intro j hj
  have h' : ri j = rₙ j hj := by simp [ri, hj]
  have : rₙ j hj ≤ r := by rw [← h']; exact Finset.le_sup (Finset.mem_univ _)
  apply hrₙ j hj _ this

open Filter in
theorem exists_tendsto_const_tendsto_zero_tendsto_const
    {ι : Type*}
    {v : ι → InfinitePlace K}
    {w : InfinitePlace K}
    {a b : K}
    {i : ι}
    (ha : 1 < v i a)
    (haj : ∀ j ≠ i, v j a < 1)
    (haw : 1 < w a)
    (hb : 1 < v i b)
    (hbw : w b < 1) :
    ∃ c : ℕ → K,
      Tendsto (fun n => (v i).1.norm (c n)) atTop (𝓝 ((v i).1.norm b)) ∧
        (∀ j ≠ i, Tendsto (fun n => (v j).1.norm (c n)) atTop (𝓝 0)) ∧
          Tendsto (fun n => w.1.norm (c n)) atTop (𝓝 (w.1.norm b)) := by
  have ha₃ := inv_lt_one ha
  simp only [← map_inv₀] at ha₃
  have h₁ := tendsto_pow_mul_div_one_add_pow_one ha₃ b
  have (j : _) (hj : j ≠ i) : 0 < v j a := by
    by_contra h
    simp at h
    have := le_antisymm h (AbsoluteValue.nonneg _ _)
    simp at this
    rw [this, map_zero] at haw
    linarith
  have ha₅ (j : _) (hj : j ≠ i) := one_lt_inv (this j hj) (haj j hj)
  simp_rw [← map_inv₀] at ha₅
  have hₙ (j : _) (hj : j ≠ i) := tendsto_pow_mul_div_one_add_pow_zero (ha₅ j hj) b
  use fun n => (1 / (1 + a⁻¹ ^ n) * b)
  have ha₄ := inv_lt_one haw
  rw [← map_inv₀] at ha₄
  have hN := tendsto_pow_mul_div_one_add_pow_one ha₄ b
  exact ⟨h₁, hₙ, hN⟩

open Filter in
theorem exists_one_lt_of_tendsto_const {v : InfinitePlace K} {b : K} {c : ℕ → K}
    (hb : 1 < v b)
    (hc : Tendsto (fun n => v.1.norm (c n)) atTop (𝓝 (v.1.norm b))) :
    ∃ N, ∀ r ≥ N, 1 < v (c r) := by
  rw [Metric.tendsto_atTop] at hc
  specialize hc (dist 1 (v b) / 2) (div_pos (dist_pos.2 (by linarith)) (by norm_num))
  let ⟨N, hN⟩ := hc
  use N
  intro r hr
  simp_rw [Real.dist_eq] at hN
  have : |1 - v b| = v b - 1 := by
    rw [show v b - 1 = - (1 - v b) by ring]
    rw [abs_eq_neg_self]
    linarith
  rw [this] at hN
  specialize hN r hr
  by_cases h : v b < v (c r)
  · exact lt_trans hb h
  · rw [abs_eq_neg_self.2 ] at hN
    · have : (v b - 1) / 2 < v b - 1 := by
        linarith
      have := lt_trans hN this
      simp [apply_eq_norm] at this
      exact this
    · push_neg at h
      simp only [tsub_le_iff_right, zero_add]
      exact h

open Filter in
theorem exists_lt_one_of_tendsto_const {v : InfinitePlace K} {b : K} {c : ℕ → K}
    (hb : v b < 1)
    (hc : Tendsto (fun n => v.1.norm (c n)) atTop (𝓝 (v.1.norm b))) :
    ∃ N, ∀ r ≥ N, v (c r) < 1 := by
  rw [Metric.tendsto_atTop] at hc
  specialize hc (dist 1 (v b) / 2) (div_pos (dist_pos.2 (by linarith)) (by norm_num))
  let ⟨N, hN⟩ := hc
  use N
  intro r hr
  specialize hN r hr
  simp_rw [Real.dist_eq] at hN
  have : |1 - v b| = 1 - v b:= by
    rw [abs_eq_self]
    linarith
  rw [this] at hN
  by_cases h : v b ≤ v (c r)
  · rw [abs_eq_self.2] at hN
    · have : (1 - v b) / 2 < 1 - v b := by
        linarith
      have := lt_trans hN this
      simp [apply_eq_norm] at this
      exact this
    · simp
      exact h
  · push_neg at h
    exact lt_trans h hb

theorem exists_lt_one_one_lt_of_one_lt
    {ι : Type*}
    [Fintype ι]
    {v : ι → InfinitePlace K}
    {w : InfinitePlace K}
    {a b : K}
    {i : ι}
    (ha : 1 < v i a)
    (haj : ∀ j ≠ i, v j a < 1)
    (haw : 1 < w a)
    (hb : 1 < v i b)
    (hbw : w b < 1) :
    ∃ k : K, 1 < v i k ∧ (∀ j ≠ i, v j k < 1) ∧ w k < 1 := by
  let ⟨c, hc⟩ := exists_tendsto_const_tendsto_zero_tendsto_const ha haj haw hb hbw
  have ha₃ := inv_lt_one ha
  simp only [← map_inv₀] at ha₃
  have h₁ := exists_one_lt_of_tendsto_const hb hc.1
  have hN := exists_lt_one_of_tendsto_const hbw hc.2.2
  have hₙ := hc.2.1
  simp_rw [Metric.tendsto_nhds, Filter.eventually_atTop, dist_zero_right] at h₁ hₙ hN
  choose r₁ hr₁ using h₁
  choose rₙ hrₙ using fun j hj => hₙ j hj 1 (by linarith)
  choose rN hrN using hN
  let ri : ι → ℕ :=
    fun j => if h : j = i then r₁ else rₙ j h
  let r := max (Finset.univ.sup ri) rN
  have h₀ : ri i = r₁ := by simp [ri]
  have : r₁ ≤ r := by
    rw [← h₀]
    rw [le_max_iff]
    left
    apply (Finset.le_sup (Finset.mem_univ _))
  simp at this
  refine ⟨c r, hr₁ r this, fun j hj => ?_, ?_⟩
  · have hj' : ri j = rₙ j hj := by simp [ri, hj]
    have : rₙ j hj ≤ r := by
      rw [← hj']
      rw [le_max_iff]
      left
      apply Finset.le_sup (Finset.mem_univ _)
    simp at hrₙ
    exact hrₙ j hj _ this
  · have : rN ≤ r := by
      rw [le_max_iff]
      right
      exact le_rfl
    exact hrN _ this

theorem exists_lt_one_one_lt_pi {n : ℕ}
    {v : Fin (n + 2) → InfinitePlace K} (h : v.Injective) :
    ∃ (a : K), 1 < v 0 a ∧ ∀ j ≠ 0, v j a < 1 := by
  induction n using Nat.case_strong_induction_on with
  | hz =>
    let ⟨a, ha⟩ := (v 0).1.exists_lt_one_one_lt_of_ne_pow (v 0).exists_ne_one (v 1).exists_ne_one
      (mt eq_of_eq_pow <| h.ne zero_ne_one)
    exact ⟨a, ha.1, by simp [Fin.forall_fin_two]; exact ha.2⟩
  | hi n ih =>
    let ⟨a, ha⟩ := ih n le_rfl <| h.comp (Fin.castSucc_injective _)
    have : ![v 0, v (Fin.last _)].Injective := by
      rw [Function.Injective]
      simp [Fin.forall_fin_two]
      refine ⟨?_, ?_⟩
      · apply h.ne
        rw [ne_eq, Fin.zero_eq_last_iff]
        norm_num
      · apply h.ne
        rw [ne_eq, Fin.last_eq_zero_iff]
        norm_num
    let ⟨b, hb⟩ := ih 0 (by linarith) <| this
    simp [Fin.forall_fin_two] at hb
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
      · let ⟨k, hk⟩ := exists_le_one_one_lt_of_eq_one ha.1 ha.2 ha₁ hb.1 hb.2
        refine ⟨k, hk.1, ?_⟩
        intro j hj
        by_cases h : j ≠ Fin.last _
        · have := hk.2.1 (j.castPred h)
          simp at this
          apply this
          rw [← Fin.castPred_zero, Fin.castPred_inj]
          exact hj
        · push_neg at h
          rw [h]
          exact hk.2.2
      · push_neg at ha₁ ha₀
        have ha₂ : 1 < v (Fin.last _) a := by
          exact lt_of_le_of_ne ha₀ ha₁.symm
        let ⟨k, hk⟩ := exists_lt_one_one_lt_of_one_lt ha.1 ha.2 ha₂ hb.1 hb.2
        refine ⟨k, hk.1, ?_⟩
        intro j hj
        by_cases h : j ≠ Fin.last _
        · have := hk.2.1 (j.castPred h)
          simp at this
          apply this
          rw [← Fin.castPred_zero, Fin.castPred_inj]
          exact hj
        · push_neg at h
          rw [h]
          exact hk.2.2

theorem DenseRange.piMap {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    {f : (i : ι) → (X i) → (Y i)} (hf : ∀ i, DenseRange (f i)):
    DenseRange (Pi.map f) := by
  simp [DenseRange]
  delta Pi.map
  simp_rw [Set.range_dcomp]
  simp [DenseRange] at hf
  exact dense_pi Set.univ (fun i _ => hf i)

instance {w : InfinitePlace L} : Algebra K (WithAbs w.1) := ‹Algebra K L›

open Filter in
theorem exists_tendsto_one_tendsto_zero
    {v : InfinitePlace K}
    {c : K}
    (hv : 1 < v c)
    (h : ∀ w : InfinitePlace K, w ≠ v → w c < 1) :
    ∃ a : ℕ → K,
      Tendsto (β := WithAbs v.1) a atTop (𝓝 1) ∧ (∀ w, w ≠ v →
        Tendsto (β := WithAbs w.1) a atTop (𝓝 0)) := by
  refine ⟨fun n => 1 / (1 + c⁻¹ ^ n), ?_, ?_⟩
  · have hx₁ := inv_lt_one hv
    rw [← map_inv₀] at hx₁
    nth_rw 3 [show (1 : WithAbs v.1) = 1 / 1 by norm_num]
    apply Filter.Tendsto.div tendsto_const_nhds _ one_ne_zero
    nth_rw 2 [← add_zero (1 : WithAbs v.1)]
    apply Filter.Tendsto.const_add
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_pow]
    apply tendsto_pow_atTop_nhds_zero_of_lt_one (AbsoluteValue.nonneg _ _) hx₁
  · intro w hwv
    have : 0 < w c := by
      by_contra! hc
      have := le_antisymm hc (AbsoluteValue.nonneg _ _)
      simp [abs_eq_zero] at this
      simp [this] at hv
      linarith
    have hx' := one_lt_inv this (h w hwv)
    rw [← map_inv₀] at hx'
    simp_rw [div_eq_mul_inv, one_mul]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_inv]
    apply Filter.Tendsto.inv_tendsto_atTop
    have (a : WithAbs w.1) (n : ℕ): ‖a ^ n‖ - 1 ≤  ‖1 + a ^ n‖  := by
      simp_rw [add_comm, ← norm_one (α := WithAbs w.1), tsub_le_iff_right]
      exact norm_le_add_norm_add _ _
    apply Filter.tendsto_atTop_mono (this _)
    apply Filter.tendsto_atTop_add_right_of_le _ (-1) _ (fun _ => le_rfl)
    simp only [inv_pow, norm_inv, norm_pow]
    apply tendsto_atTop_of_geom_le (c := w (c⁻¹))
    · simp only [pow_zero, inv_one, zero_lt_one]
    · exact hx'
    · intro n
      rw [map_inv₀]
      ring_nf
      exact le_rfl

variable (K)

theorem weak_approx :
    DenseRange <| algebraMap K ((v : InfinitePlace K) → WithAbs v.1) := by
  by_cases hcard : Fintype.card (InfinitePlace K) = 1
  · have huniq := Fintype.equivFinOfCardEq hcard |>.unique
    let f := Homeomorph.funUnique (InfinitePlace K) (WithAbs huniq.default.1)
    have := DenseRange.comp f.symm.surjective.denseRange denseRange_id f.continuous_invFun
    convert this <;> exact huniq.uniq _
  rw [Metric.denseRange_iff]
  intro z r hr
  have (v : InfinitePlace K) : ∃ (x : K), 1 < v x ∧ ∀ w, w ≠ v → w x < 1 := by
    let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (InfinitePlace K)
    have : ∃ k, n = k + 2 := by
      use n - 2
      rw [n.sub_add_cancel]
      have : Fintype.card (InfinitePlace K) = n := Fintype.card_fin n ▸ Fintype.card_eq.2 ⟨e⟩
      have hpos : 0 < n := by
        rw [← this]
        exact Fintype.card_pos
      omega
    obtain ⟨k, rfl⟩ := this
    let ⟨m, hm⟩ := e.symm.surjective v
    let e' := e.trans (Equiv.swap 0 m)
    let ⟨x, hx⟩ := NumberField.InfinitePlace.exists_lt_one_one_lt_pi (v := e'.symm)
      (e'.symm.injective) --(e v)
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
  have (v : InfinitePlace K) : ∃ (x : ℕ → WithAbs v.1),
      Filter.Tendsto (fun n => x n) Filter.atTop (𝓝 1) ∧ ∀ w ≠ v,
        Filter.Tendsto (β := WithAbs w.1) (fun n => x n) Filter.atTop (𝓝 0) := by
    obtain ⟨x, hx⟩ := this v
    exact exists_tendsto_one_tendsto_zero hx.1 hx.2
  let x : (v : InfinitePlace K) → (ℕ → WithAbs v.1) := fun v => (this v).choose
  have h := fun v => (this v).choose_spec
  let y := fun n => ∑ v, x v n * z v
  have : Filter.Tendsto
      (fun n v => (∑ v, x v n * z v : WithAbs v.1)) Filter.atTop (𝓝 z) := by
    rw [tendsto_pi_nhds]
    intro v
    have : z v = ∑ w, if w = v then z v else (0 : WithAbs w.1) := by
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [this]
    apply tendsto_finset_sum
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
  exact h N le_rfl

theorem weak_approx' {p : InfinitePlace K → Prop} [Nonempty {v // p v}] :
    DenseRange <| algebraMap K ((v : Subtype p) → WithAbs v.1.1) := by
  have : algebraMap K ((v : Subtype p) → WithAbs v.1.1) =
    Subtype.restrict p ∘ algebraMap K ((v : InfinitePlace K) → WithAbs v.1) := rfl
  rw [this]
  apply DenseRange.comp
  · have := Subtype.surjective_restrict (β := fun v => WithAbs v.1) p
    exact this.denseRange
  · exact weak_approx K
  · continuity
