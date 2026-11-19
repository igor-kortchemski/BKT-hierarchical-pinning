module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Proofs.HardEscape
public import DiamondPinning.Model.FreeEnergy
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Exact coupling at the deterministic floor

This module proves `escape_comparison_of_bandExit`, hence the frozen
`escape_comparison`: deterministic-floor hard means are finite, the hard free
energy transfers to the diamond free energy, and tail-dominated laws meeting
the band-exit criterion give a uniform diamond-free-energy lower bound. It
covers `escape:normalization`, `escape:energy-transfer`, and
`escape:diamond-exit` in `source/escape.tex`, lines 156–189, with the second
conclusion of the band-exit criterion supplied as an explicit hypothesis.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology
open scoped ENNReal

/-- The normalized integer coordinate of a diamond partition function. -/
private noncomputable def scaledFloor (B : ℝ) (n : ℕ) (r : ℝ) : ℕ :=
  ⌊Real.log (r / floorSeq B n) / Real.log (B / floorSeq B n)⌋₊

private lemma scaledFloor_le_div {B : ℝ} {n : ℕ} (hn : 1 ≤ n) (hB : 2 < B)
    {r : ℝ} (hr : floorSeq B n ≤ r) :
    (scaledFloor B n r : ℝ) ≤
      Real.log (r / floorSeq B n) / Real.log (B / floorSeq B n) := by
  have hb : 0 < floorSeq B n :=
    (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)
  have ha : 0 < Real.log (B / floorSeq B n) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hb]
    nlinarith [floorSeq_lt_one hB n]
  have hq : 0 ≤ Real.log (r / floorSeq B n) / Real.log (B / floorSeq B n) := by
    apply div_nonneg _ ha.le
    apply Real.log_nonneg
    exact (le_div_iff₀ hb).2 (by simpa using hr)
  exact Nat.floor_le hq

private lemma scaledFloor_recursion {B : ℝ} {n : ℕ} (hn : 1 ≤ n) (hB : 2 < B)
    {x y : ℝ} (hx : floorSeq B n ≤ x) (hy : floorSeq B n ≤ y) :
    scaledFloor B n x + scaledFloor B n y - 1 ≤
      scaledFloor B n ((x * y + (B - 1)) / B) := by
  let b := floorSeq B n
  let a := Real.log (B / b)
  let q : ℝ → ℝ := fun r => Real.log (r / b) / a
  have hb : 0 < b := (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)
  have hb1 : b < 1 := floorSeq_lt_one hB n
  have hB0 : 0 < B := by linarith
  have ha : 0 < a := by
    dsimp [a]
    apply Real.log_pos
    rw [lt_div_iff₀ hb]
    nlinarith
  have hx0 : 0 < x := hb.trans_le hx
  have hy0 : 0 < y := hb.trans_le hy
  have hxq : 0 ≤ q x := by
    apply div_nonneg _ ha.le
    apply Real.log_nonneg
    exact (le_div_iff₀ hb).2 (by simpa [b] using hx)
  have hyq : 0 ≤ q y := by
    apply div_nonneg _ ha.le
    apply Real.log_nonneg
    exact (le_div_iff₀ hb).2 (by simpa [b] using hy)
  have hrecpos : 0 < (x * y + (B - 1)) / B :=
    div_pos (add_pos_of_pos_of_nonneg (mul_pos hx0 hy0) (by linarith)) hB0
  have hratio : x * y / (B * b) ≤ ((x * y + (B - 1)) / B) / b := by
    calc
      x * y / (B * b) = (x * y / B) / b := by field_simp
      _ ≤ ((x * y + (B - 1)) / B) / b := by
        apply (div_le_div_iff_of_pos_right hb).2
        apply (div_le_div_iff_of_pos_right hB0).2
        nlinarith [mul_nonneg hx0.le hy0.le]
  have ha_eq : a = Real.log B - Real.log b := by
    dsimp [a]
    exact Real.log_div hB0.ne' hb.ne'
  have hlog : Real.log (x / b) + Real.log (y / b) - a ≤
      Real.log (((x * y + (B - 1)) / B) / b) := by
    have hl := Real.log_le_log (by positivity : 0 < x * y / (B * b)) hratio
    have hleft : Real.log (x * y / (B * b)) =
        Real.log (x / b) + Real.log (y / b) - a := by
      rw [Real.log_div (mul_ne_zero hx0.ne' hy0.ne') (mul_ne_zero hB0.ne' hb.ne'),
        Real.log_mul hx0.ne' hy0.ne', Real.log_mul hB0.ne' hb.ne',
        Real.log_div hx0.ne' hb.ne', Real.log_div hy0.ne' hb.ne', ha_eq]
      ring
    rwa [hleft] at hl
  have hq : q x + q y - 1 ≤ q ((x * y + (B - 1)) / B) := by
    dsimp [q]
    rw [show Real.log (x / b) / a + Real.log (y / b) / a - 1 =
      (Real.log (x / b) + Real.log (y / b) - a) / a by
        field_simp [ha.ne']]
    exact (div_le_div_iff_of_pos_right ha).2 hlog
  have hfloorx : (scaledFloor B n x : ℝ) ≤ q x := scaledFloor_le_div hn hB hx
  have hfloory : (scaledFloor B n y : ℝ) ≤ q y := scaledFloor_le_div hn hB hy
  by_cases hxy : scaledFloor B n x + scaledFloor B n y = 0
  · simp [hxy]
  · have hsum : 1 ≤ scaledFloor B n x + scaledFloor B n y := by omega
    apply Nat.le_floor
    rw [Nat.cast_sub hsum, Nat.cast_add, Nat.cast_one]
    dsimp [scaledFloor] at hfloorx hfloory ⊢
    change (⌊q x⌋₊ : ℝ) + (⌊q y⌋₊ : ℝ) - 1 ≤ q _
    linarith


private lemma measurable_scaledFloor (B : ℝ) (n : ℕ) :
    Measurable (scaledFloor B n) := by
  unfold scaledFloor
  fun_prop

private lemma measurable_scaledFloor_comp {α : Type*} [MeasurableSpace α]
    (B : ℝ) (n : ℕ) (g : ℕ → α) :
    Measurable (fun r => g (scaledFloor B n r)) :=
  Measurable.of_discrete.comp (measurable_scaledFloor B n)

private lemma ae_scaledFloor_recursion {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ}
    (hn : 1 ≤ n) (j : ℕ) :
    ∀ᵐ p : ℝ × ℝ ∂((lawR μ B h (n + j)).prod (lawR μ B h (n + j))),
      scaledFloor B n p.1 + scaledFloor B n p.2 - 1 ≤
        scaledFloor B n ((p.1 * p.2 + (B - 1)) / B) := by
  let _ : IsProbabilityMeasure (lawR μ B h (n + j)) :=
    isProbabilityMeasure_lawR B h (n + j)
  have hp : ∀ᵐ p : ℝ × ℝ ∂((lawR μ B h (n + j)).prod (lawR μ B h (n + j))),
      floorSeq B n ≤ p.1 ∧ floorSeq B n ≤ p.2 := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [ae_floorSeq_le_lawR hpos hB h (n + j)] with x hx
    filter_upwards [ae_floorSeq_le_lawR hpos hB h (n + j)] with y hy
    have hnj : n ≤ n + j := Nat.le_add_right n j
    exact ⟨(floorSeq_monotone hB hnj).trans hx, (floorSeq_monotone hB hnj).trans hy⟩
  filter_upwards [hp] with p hp
  exact scaledFloor_recursion hn hB hp.1 hp.2

private lemma lintegral_scaledFloor_diamond {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ}
    (hn : 1 ≤ n) :
    ∀ (j : ℕ) (f : ℕ → ℕ), Monotone f →
      (∫⁻ y, (f y : ℝ≥0∞) ∂hardLaw (floorHardLaw μ B h n) j) ≤
        ∫⁻ r, (f (scaledFloor B n r) : ℝ≥0∞) ∂lawR μ B h (n + j) := by
  intro j
  induction j with
  | zero =>
      intro f hf
      change (∫⁻ y, (f y : ℝ≥0∞) ∂floorHardLaw μ B h n) ≤ _
      rw [show n + 0 = n by simp]
      change (∫⁻ y, (f y : ℝ≥0∞) ∂(lawR μ B h n).map (scaledFloor B n)) ≤ _
      exact le_of_eq (lintegral_map (μ := lawR μ B h n)
        (f := fun y : ℕ => (f y : ℝ≥0∞)) (g := scaledFloor B n)
        (by fun_prop) (measurable_scaledFloor B n))
  | succ j ih =>
      let _ : IsProbabilityMeasure (lawR μ B h (n + j)) :=
        isProbabilityMeasure_lawR B h (n + j)
      let D := (lawR μ B h (n + j)).map (scaledFloor B n)
      have htail : ∀ k : ℕ, hardLaw (floorHardLaw μ B h n) j {y | k ≤ y} ≤
          D {y | k ≤ y} := by
        intro k
        rw [tail_as_lintegral, tail_as_lintegral]
        dsimp [D]
        rw [lintegral_map (by fun_prop) (measurable_scaledFloor B n)]
        exact ih (tailFun k) (tailFun_mono k)
      have hDprod : D.prod D = ((lawR μ B h (n + j)).prod
          (lawR μ B h (n + j))).map
          (fun p : ℝ × ℝ => (scaledFloor B n p.1, scaledFloor B n p.2)) := by
        dsimp [D]
        rw [Measure.map_prod_map _ _ (measurable_scaledFloor B n)
          (measurable_scaledFloor B n)]
        rfl
      intro f hf
      rw [hardLaw_succ, lintegral_map (by fun_prop) (by fun_prop)]
      calc
        (∫⁻ p, (f (p.1 + p.2 - 1) : ℝ≥0∞)
            ∂(hardLaw (floorHardLaw μ B h n) j).prod
              (hardLaw (floorHardLaw μ B h n) j)) ≤
            ∫⁻ p, (f (p.1 + p.2 - 1) : ℝ≥0∞) ∂D.prod D :=
          lintegral_prod_mono_of_tail htail htail _
            (fun b a₁ a₂ ha => hf (by dsimp; omega))
            (fun a b₁ b₂ hb => hf (by dsimp; omega))
        _ = ∫⁻ p : ℝ × ℝ, (f (scaledFloor B n p.1 + scaledFloor B n p.2 - 1) :
              ℝ≥0∞) ∂(lawR μ B h (n + j)).prod (lawR μ B h (n + j)) := by
          rw [hDprod, lintegral_map
            (f := fun p : ℕ × ℕ => (f (p.1 + p.2 - 1) : ℝ≥0∞))
            (g := fun p : ℝ × ℝ => (scaledFloor B n p.1, scaledFloor B n p.2))
            (by fun_prop)
            (((measurable_scaledFloor B n).comp measurable_fst).prodMk
              ((measurable_scaledFloor B n).comp measurable_snd))]
        _ ≤ ∫⁻ p : ℝ × ℝ,
              (f (scaledFloor B n ((p.1 * p.2 + (B - 1)) / B)) : ℝ≥0∞)
              ∂(lawR μ B h (n + j)).prod (lawR μ B h (n + j)) := by
          apply lintegral_mono_ae
          filter_upwards [ae_scaledFloor_recursion hpos hB h hn j] with p hp
          exact_mod_cast hf hp
        _ = ∫⁻ r, (f (scaledFloor B n r) : ℝ≥0∞)
              ∂lawR μ B h (n + (j + 1)) := by
          rw [show n + (j + 1) = (n + j) + 1 by omega, lawR_succ,
            lintegral_map (measurable_scaledFloor_comp B n
              (fun y : ℕ => (f y : ℝ≥0∞))) (by fun_prop)]

private lemma hardMean_le_scaledFloor {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ}
    (hn : 1 ≤ n) (j : ℕ) :
    hardMean (floorHardLaw μ B h n) j ≤
      ∫⁻ r, (scaledFloor B n r : ℝ≥0∞) ∂lawR μ B h (n + j) := by
  exact lintegral_scaledFloor_diamond hpos hB h hn j id monotone_id

private lemma scaledFloor_lintegral_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (hnk : n ≤ k) :
    (∫⁻ r, (scaledFloor B n r : ℝ≥0∞) ∂lawR μ B h k) ≤
      ENNReal.ofReal ((logMoment μ B h k - Real.log (floorSeq B n)) /
        Real.log (B / floorSeq B n)) := by
  let b := floorSeq B n
  let a := Real.log (B / b)
  let q : ℝ → ℝ := fun r => Real.log (r / b) / a
  have hb : 0 < b := (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)
  have ha : 0 < a := by
    dsimp [a]
    apply Real.log_pos
    rw [lt_div_iff₀ hb]
    nlinarith [floorSeq_lt_one hB n]
  let _ : IsProbabilityMeasure (lawR μ B h k) := isProbabilityMeasure_lawR B h k
  have hi : Integrable Real.log (lawR μ B h k) :=
    integrable_log_lawR_of hpos hmean hB h (by omega)
  have hfloor : ∀ᵐ r ∂lawR μ B h k, b ≤ r := by
    exact (ae_floorSeq_le_lawR hpos hB h k).mono fun r hr =>
      (floorSeq_monotone hB hnk).trans hr
  have hqeq : (fun r => q r) =ᵐ[lawR μ B h k]
      (fun r => (Real.log r - Real.log b) / a) := by
    filter_upwards [hfloor] with r hr
    have hr0 : 0 < r := hb.trans_le hr
    dsimp [q]
    rw [Real.log_div hr0.ne' hb.ne']
  have hq : Integrable q (lawR μ B h k) := by
    apply (integrable_congr hqeq).2
    exact (hi.sub (integrable_const _)).div_const a
  have hpoint : ∀ᵐ r ∂lawR μ B h k,
      (scaledFloor B n r : ℝ) ≤ q r := by
    filter_upwards [hfloor] with r hr
    exact scaledFloor_le_div hn hB hr
  have hscaled : Integrable (fun r => (scaledFloor B n r : ℝ)) (lawR μ B h k) := by
    apply hq.mono' (measurable_scaledFloor_comp B n (fun y : ℕ => (y : ℝ))).aestronglyMeasurable
    filter_upwards [hfloor, hpoint] with r hr hle
    have hq0 : 0 ≤ q r := (Nat.cast_nonneg _ : (0 : ℝ) ≤ (scaledFloor B n r : ℝ)).trans hle
    simpa [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hq0] using hle
  have heq : (∫ r, (scaledFloor B n r : ℝ) ∂lawR μ B h k) ≤
      (logMoment μ B h k - Real.log b) / a := by
    calc
      (∫ r, (scaledFloor B n r : ℝ) ∂lawR μ B h k) ≤ ∫ r, q r ∂lawR μ B h k :=
        integral_mono_ae hscaled hq hpoint
      _ = (logMoment μ B h k - Real.log b) / a := by
        rw [integral_congr_ae hqeq, integral_div, integral_sub hi (integrable_const _)]
        simp [logMoment]
  calc
    (∫⁻ r, (scaledFloor B n r : ℝ≥0∞) ∂lawR μ B h k) =
        ∫⁻ r, ENNReal.ofReal (scaledFloor B n r : ℝ) ∂lawR μ B h k := by
      simp only [ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (∫ r, (scaledFloor B n r : ℝ) ∂lawR μ B h k) :=
      (ofReal_integral_eq_lintegral_ofReal hscaled
        (Eventually.of_forall fun r => by positivity)).symm
    _ ≤ ENNReal.ofReal ((logMoment μ B h k - Real.log b) / a) :=
      ENNReal.ofReal_le_ofReal heq

private lemma hardMean_toReal_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    (hardMean (floorHardLaw μ B h n) j).toReal ≤
      (logMoment μ B h (n + j) - Real.log (floorSeq B n)) /
        Real.log (B / floorSeq B n) := by
  have hb : 0 < floorSeq B n :=
    (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)
  have ha : 0 < Real.log (B / floorSeq B n) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hb]
    nlinarith [floorSeq_lt_one hB n]
  let _ : IsProbabilityMeasure (lawR μ B h (n + j)) :=
    isProbabilityMeasure_lawR B h (n + j)
  have hi : Integrable Real.log (lawR μ B h (n + j)) :=
    integrable_log_lawR_of hpos hmean hB h (by omega)
  have hm : Real.log (floorSeq B n) ≤ logMoment μ B h (n + j) := by
    have hle := integral_mono_ae (μ := lawR μ B h (n + j))
      (integrable_const (Real.log (floorSeq B n))) hi
      ((ae_floorSeq_le_lawR hpos hB h (n + j)).mono fun r hr =>
        Real.log_le_log hb ((floorSeq_monotone hB (Nat.le_add_right n j)).trans hr))
    simpa [logMoment] using hle
  have hle := (hardMean_le_scaledFloor hpos hB h hn j).trans
    (scaledFloor_lintegral_le hpos hmean hB h hn (n + j) (Nat.le_add_right n j))
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (by linarith) ha.le) hle


private theorem freeEnergy_ge_scaledHard {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {n : ℕ} (hn : 1 ≤ n) :
    ((2 : ℝ) ^ n)⁻¹ * Real.log (B / floorSeq B n) *
        (hardFreeEnergy (floorHardLaw μ B h n)).toReal ≤ freeEnergy μ B h := by
  let a := Real.log (B / floorSeq B n)
  let c := ((2 : ℝ) ^ n)⁻¹ * a
  let q : ℕ → ℝ := fun j => (logMoment μ B h (n + j) - Real.log (floorSeq B n)) / a
  have hb : 0 < floorSeq B n :=
    (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)
  have ha : 0 < a := by
    dsimp [a]
    apply Real.log_pos
    rw [lt_div_iff₀ hb]
    nlinarith [floorSeq_lt_one hB n]
  let _ : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  let _ : IsProbabilityMeasure (floorHardLaw μ B h n) := by
    change IsProbabilityMeasure ((lawR μ B h n).map _)
    infer_instance
  have hreal := hardFreeEnergy_real_aux (floorHardLaw μ B h n)
    (floorHardMean_ne_top hpos hmean hB h hn)
  have hleft : Tendsto (fun j : ℕ => c * (((2 : ℝ) ^ j)⁻¹ *
      (hardMean (floorHardLaw μ B h n) j).toReal)) atTop
      (𝓝 (c * (hardFreeEnergy (floorHardLaw μ B h n)).toReal)) :=
    tendsto_const_nhds.mul hreal.2.2
  have hpoint : ∀ j : ℕ, c * (((2 : ℝ) ^ j)⁻¹ *
      (hardMean (floorHardLaw μ B h n) j).toReal) ≤
      ((2 : ℝ) ^ (n + j))⁻¹ * logMoment μ B h (n + j) -
        ((2 : ℝ) ^ (n + j))⁻¹ * Real.log (floorSeq B n) := by
    intro j
    have hm := hardMean_toReal_le hpos hmean hB h hn j
    have hleftj : c * (((2 : ℝ) ^ j)⁻¹ *
        (hardMean (floorHardLaw μ B h n) j).toReal) ≤ c * (((2 : ℝ) ^ j)⁻¹ * q j) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ c)
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ j)⁻¹)
      simpa [q] using hm
    calc
      c * (((2 : ℝ) ^ j)⁻¹ * (hardMean (floorHardLaw μ B h n) j).toReal) ≤
          c * (((2 : ℝ) ^ j)⁻¹ * q j) := hleftj
      _ = ((2 : ℝ) ^ (n + j))⁻¹ * logMoment μ B h (n + j) -
          ((2 : ℝ) ^ (n + j))⁻¹ * Real.log (floorSeq B n) := by
        dsimp [c, q]
        rw [pow_add]
        field_simp [ha.ne']
  have hpow : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) := by
    have hh := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (1 : ℝ) / 2) (by norm_num : (1 : ℝ) / 2 < 1)
    have heq : (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) = fun k => ((1 : ℝ) / 2) ^ k := by
      ext k
      simp
    rw [heq]
    exact hh
  have hshift : Tendsto (fun j : ℕ => n + j) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat n
  have hmain : Tendsto (fun j : ℕ => ((2 : ℝ) ^ (n + j))⁻¹ *
      logMoment μ B h (n + j)) atTop (𝓝 (freeEnergy μ B h)) :=
    (freeEnergy_tendsto_aux hpos hmean hB h).comp hshift
  have hcorr : Tendsto (fun j : ℕ => ((2 : ℝ) ^ (n + j))⁻¹ *
      Real.log (floorSeq B n)) atTop (𝓝 0) := by
    simpa using (hpow.comp hshift).mul_const (Real.log (floorSeq B n))
  have hright : Tendsto (fun j : ℕ => ((2 : ℝ) ^ (n + j))⁻¹ *
      logMoment μ B h (n + j) - ((2 : ℝ) ^ (n + j))⁻¹ * Real.log (floorSeq B n))
      atTop (𝓝 (freeEnergy μ B h)) := by
    simpa using hmain.sub hcorr
  have hle := le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hpoint)
  simpa [c] using hle


/-- The exact-coupling comparison: finiteness of the floor hard mean, transfer
of the hard free energy, and a uniform lower bound for tail-dominated laws
meeting the quantitative band-exit criterion. -/
theorem escape_comparison_of_bandExit
    (hBE : ∀ (ν : Measure ℕ) [IsProbabilityMeasure ν] {L : ℕ}, 10 ^ 4 ≤ L →
      (10 : ℝ) ^ 4 ≤ L * bandMoment ν (upperBand L) →
        2⁻¹ * ((2 : ℝ≥0∞) ^ (2 * L))⁻¹ ≤ hardFreeEnergy ν)
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {n : ℕ} (hn : 1 ≤ n) :
    hardMean (floorHardLaw μ B h n) 0 ≠ ∞ ∧
      ((2 : ℝ) ^ n)⁻¹ * Real.log (B / floorSeq B n) *
          (hardFreeEnergy (floorHardLaw μ B h n)).toReal ≤ freeEnergy μ B h ∧
      ∀ (ν : Measure ℕ) [IsProbabilityMeasure ν],
        (∀ k : ℕ, ν {y | k ≤ y} ≤ floorHardLaw μ B h n {y | k ≤ y}) →
        ∀ L : ℕ, 10 ^ 4 ≤ L → (10 : ℝ) ^ 4 ≤ L * bandMoment ν (upperBand L) →
          Real.log (B / floorSeq B n) / 2 * ((2 : ℝ) ^ (n + 2 * L))⁻¹ ≤
            freeEnergy μ B h := by
  have hfin := floorHardMean_ne_top hpos hmean hB h hn
  let _ : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  let _ : IsProbabilityMeasure (floorHardLaw μ B h n) := by
    change IsProbabilityMeasure ((lawR μ B h n).map _)
    infer_instance
  have hreal := hardFreeEnergy_real_aux (floorHardLaw μ B h n) hfin
  refine ⟨hfin, freeEnergy_ge_scaledHard hpos hmean hB h hn, ?_⟩
  intro ν hν htail L hL hband
  have hmono : hardFreeEnergy ν ≤ hardFreeEnergy (floorHardLaw μ B h n) :=
    hardFreeEnergy_mono_of_tail htail
  have hbandReal : (2 : ℝ)⁻¹ * ((2 : ℝ) ^ (2 * L))⁻¹ ≤
      (hardFreeEnergy ν).toReal := by
    have hνfin : hardFreeEnergy ν ≠ ∞ := ne_top_of_le_ne_top hreal.2.1 hmono
    have hbound := ENNReal.toReal_mono hνfin (hBE ν hL hband)
    simpa [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow] using hbound
  have hmonoReal : (hardFreeEnergy ν).toReal ≤
      (hardFreeEnergy (floorHardLaw μ B h n)).toReal :=
    ENNReal.toReal_mono hreal.2.1 hmono
  have ha : 0 ≤ Real.log (B / floorSeq B n) := by
    apply Real.log_nonneg
    have hb : 0 < floorSeq B n :=
      (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)
    apply (one_le_div hb).2
    nlinarith [floorSeq_lt_one hB n]
  let c := ((2 : ℝ) ^ n)⁻¹ * Real.log (B / floorSeq B n)
  calc
    Real.log (B / floorSeq B n) / 2 * ((2 : ℝ) ^ (n + 2 * L))⁻¹ =
        c * ((2 : ℝ)⁻¹ * ((2 : ℝ) ^ (2 * L))⁻¹) := by
      dsimp [c]
      rw [pow_add]
      field_simp
    _ ≤ c * (hardFreeEnergy ν).toReal := by
      exact mul_le_mul_of_nonneg_left hbandReal (by positivity)
    _ ≤ c * (hardFreeEnergy (floorHardLaw μ B h n)).toReal :=
      mul_le_mul_of_nonneg_left hmonoReal (by positivity)
    _ ≤ freeEnergy μ B h := freeEnergy_ge_scaledHard hpos hmean hB h hn

end DiamondPinning
