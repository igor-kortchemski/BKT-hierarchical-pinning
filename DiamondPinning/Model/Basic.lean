module

public import DiamondPinning.Model.Defs
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Elementary properties of the finite-volume recursion

This file proves the deterministic floor, the mean recursion, and the
integrability estimates used in Section 2 of the paper.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter
open scoped Topology

@[simp] theorem lawR_zero (μ : Measure ℝ) (B h : ℝ) :
    lawR μ B h 0 = μ.map fun w => Real.exp h * w := rfl

@[simp] theorem lawR_succ (μ : Measure ℝ) (B h : ℝ) (n : ℕ) :
    lawR μ B h (n + 1) =
      ((lawR μ B h n).prod (lawR μ B h n)).map
        (fun p => (p.1 * p.2 + (B - 1)) / B) := rfl

/-- Every finite-volume law is a probability measure. -/
theorem isProbabilityMeasure_lawR {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (B h : ℝ) (n : ℕ) : IsProbabilityMeasure (lawR μ B h n) := by
  induction n with
  | zero => rw [lawR_zero]; infer_instance
  | succ n ih =>
      rw [lawR_succ]
      letI := ih
      infer_instance

/-- The finite-volume laws are supported on positive reals. -/
theorem ae_pos_lawR {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    ∀ᵐ x ∂(lawR μ B h n), 0 < x := by
  induction n with
  | zero =>
      rw [lawR_zero, ae_map_iff (by fun_prop) measurableSet_Ioi]
      filter_upwards [hpos] with w hw
      exact mul_pos (Real.exp_pos h) hw
  | succ n ih =>
      letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
      rw [lawR_succ, ae_map_iff (by fun_prop) measurableSet_Ioi]
      have hp : ∀ᵐ p : ℝ × ℝ ∂((lawR μ B h n).prod (lawR μ B h n)),
          0 < p.1 ∧ 0 < p.2 := by
        rw [Measure.ae_prod_iff_ae_ae (by measurability)]
        filter_upwards [ih] with x hx
        filter_upwards [ih] with y hy
        exact ⟨hx, hy⟩
      filter_upwards [hp] with p hp
      exact div_pos (by nlinarith [mul_pos hp.1 hp.2])
        (by linarith : (0 : ℝ) < B)

/-- The deterministic floor of the finite-volume recursion. -/
noncomputable def floorSeq (B : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (floorSeq B n ^ 2 + (B - 1)) / B

@[simp] theorem floorSeq_zero (B : ℝ) : floorSeq B 0 = 0 := rfl

@[simp] theorem floorSeq_succ (B : ℝ) (n : ℕ) :
    floorSeq B (n + 1) = (floorSeq B n ^ 2 + (B - 1)) / B := rfl

theorem floorSeq_nonneg {B : ℝ} (hB : 2 < B) (n : ℕ) : 0 ≤ floorSeq B n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [floorSeq_succ]
      exact div_nonneg (by nlinarith [sq_nonneg (floorSeq B n)]) (by linarith)

theorem floorSeq_lt_one {B : ℝ} (hB : 2 < B) (n : ℕ) : floorSeq B n < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [floorSeq_succ, div_lt_one (by linarith : (0 : ℝ) < B)]
      nlinarith [floorSeq_nonneg hB n]

theorem floorSeq_le_one {B : ℝ} (hB : 2 < B) (n : ℕ) : floorSeq B n ≤ 1 :=
  (floorSeq_lt_one hB n).le

theorem floorSeq_mono_step {B : ℝ} (hB : 2 < B) (n : ℕ) :
    floorSeq B n ≤ floorSeq B (n + 1) := by
  rw [floorSeq_succ, le_div_iff₀ (by linarith : (0 : ℝ) < B)]
  nlinarith [floorSeq_nonneg hB n, floorSeq_le_one hB n]

theorem floorSeq_monotone {B : ℝ} (hB : 2 < B) : Monotone (floorSeq B) := by
  apply monotone_nat_of_le_succ
  exact floorSeq_mono_step hB

theorem one_sub_floorSeq_succ {B : ℝ} (hB : 2 < B) (n : ℕ) :
    1 - floorSeq B (n + 1) =
      (1 - floorSeq B n) * (1 + floorSeq B n) / B := by
  rw [floorSeq_succ]
  field_simp
  <;> ring

theorem one_sub_floorSeq_le {B : ℝ} (hB : 2 < B) (n : ℕ) :
    1 - floorSeq B n ≤ (2 / B) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [one_sub_floorSeq_succ hB, pow_succ]
      have hfac : (1 - floorSeq B n) * (1 + floorSeq B n) / B ≤
          (2 / B) * (1 - floorSeq B n) := by
        calc
          (1 - floorSeq B n) * (1 + floorSeq B n) / B
              ≤ ((1 - floorSeq B n) * 2) / B := by
                apply (div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < B)).mpr
                nlinarith [sq_nonneg (1 - floorSeq B n)]
          _ = (2 / B) * (1 - floorSeq B n) := by ring
      calc
        (1 - floorSeq B n) * (1 + floorSeq B n) / B
            ≤ (2 / B) * (1 - floorSeq B n) := hfac
        _ ≤ (2 / B) * (2 / B) ^ n := by
          exact mul_le_mul_of_nonneg_left ih (div_nonneg (by norm_num) (by linarith))
        _ = (2 / B) ^ n * (2 / B) := mul_comm _ _

theorem tendsto_floorSeq {B : ℝ} (hB : 2 < B) :
    Tendsto (floorSeq B) atTop (𝓝 1) := by
  have hratio0 : 0 ≤ (2 : ℝ) / B := div_nonneg (by norm_num) (by linarith)
  have hratio1 : (2 : ℝ) / B < 1 := (div_lt_one (by linarith)).mpr hB
  have hzero : Tendsto (fun n => 1 - floorSeq B n) atTop (𝓝 0) :=
    squeeze_zero (fun n => sub_nonneg.mpr (floorSeq_le_one hB n))
      (one_sub_floorSeq_le hB) (tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1)
  have hlim : Tendsto (fun n : ℕ => (1 : ℝ) - (1 - floorSeq B n)) atTop (𝓝 (1 - 0)) :=
    (tendsto_const_nhds (x := (1 : ℝ))).sub hzero
  simpa only [sub_sub_cancel, sub_zero] using hlim

theorem floorSeq_one_pos {B : ℝ} (hB : 2 < B) : 0 < floorSeq B 1 := by
  rw [show 1 = 0 + 1 by rfl, floorSeq_succ, floorSeq_zero]
  apply div_pos <;> nlinarith

theorem floorSeq_one_le {B : ℝ} (hB : 2 < B) {n : ℕ} (hn : 1 ≤ n) :
    floorSeq B 1 ≤ floorSeq B n := floorSeq_monotone hB hn

/-- The deterministic floor bounds the finite-volume laws almost surely. -/
theorem ae_floorSeq_le_lawR {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    ∀ᵐ x ∂(lawR μ B h n), floorSeq B n ≤ x := by
  induction n with
  | zero =>
      simp only [floorSeq_zero]
      filter_upwards [ae_pos_lawR hpos hB h 0] with x hx
      exact hx.le
  | succ n ih =>
      letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
      rw [lawR_succ, ae_map_iff (by fun_prop) measurableSet_Ici]
      have hp : ∀ᵐ p : ℝ × ℝ ∂((lawR μ B h n).prod (lawR μ B h n)),
          floorSeq B n ≤ p.1 ∧ floorSeq B n ≤ p.2 := by
        rw [Measure.ae_prod_iff_ae_ae (by measurability)]
        filter_upwards [ih] with x hx
        filter_upwards [ih] with y hy
        exact ⟨hx, hy⟩
      filter_upwards [hp] with p hp
      rw [floorSeq_succ, div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < B)]
      nlinarith [floorSeq_nonneg hB n, sq_nonneg (p.1 - floorSeq B n),
        sq_nonneg (p.2 - floorSeq B n)]

/-- The exponent `θ` lies strictly between zero and one. -/
theorem theta_pos {B : ℝ} (hB : 2 < B) : 0 < theta B := by
  exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by linarith))

theorem theta_lt_one {B : ℝ} (hB : 2 < B) : theta B < 1 := by
  rw [theta, div_lt_one (Real.log_pos (by linarith))]
  exact Real.log_lt_log (by norm_num) hB


/-- A real function with Bochner integral one is integrable. -/
theorem integrable_id_of_integral_eq_one {μ : Measure ℝ}
    (hmean : ∫ w, w ∂μ = 1) : Integrable (fun w : ℝ => w) μ := by
  by_contra hi
  rw [integral_undef hi] at hmean
  norm_num at hmean

/-- The identity is integrable against every finite-volume law. -/
theorem integrable_lawR_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (_hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (_hB : 2 < B) (h : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x) (lawR μ B h n) := by
  have hμ : Integrable (fun w : ℝ => w) μ := integrable_id_of_integral_eq_one hmean
  induction n with
  | zero =>
      rw [lawR_zero]
      apply (integrable_map_measure (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable (by fun_prop)).2
      change Integrable (fun w : ℝ => Real.exp h * w) μ
      exact hμ.const_mul (Real.exp h)
  | succ n ih =>
      letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
      rw [lawR_succ]
      apply (integrable_map_measure (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable (by fun_prop)).2
      change Integrable (fun p : ℝ × ℝ => (p.1 * p.2 + (B - 1)) / B)
        ((lawR μ B h n).prod (lawR μ B h n))
      exact ((ih.mul_prod ih).add (integrable_const (B - 1))).div_const B

/-- The mean at level zero is `exp h`. -/
theorem integral_lawR_zero {μ : Measure ℝ} (hmean : ∫ w, w ∂μ = 1) (B h : ℝ) :
    ∫ x, x ∂lawR μ B h 0 = Real.exp h := by
  rw [lawR_zero, integral_map (f := fun x : ℝ => x) (by fun_prop) measurable_id.aestronglyMeasurable]
  change (∫ w, Real.exp h * w ∂μ) = Real.exp h
  rw [integral_const_mul, hmean, mul_one]

/-- The mean obeys the same recursion as the deterministic floor. -/
theorem integral_lawR_succ {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) :
    ∫ x, x ∂lawR μ B h (n + 1) =
      ((∫ x, x ∂lawR μ B h n) ^ 2 + (B - 1)) / B := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have hi := integrable_lawR_of hpos hmean hB h n
  have hp : Integrable (fun p : ℝ × ℝ => p.1 * p.2)
      ((lawR μ B h n).prod (lawR μ B h n)) := hi.mul_prod hi
  rw [lawR_succ, integral_map (f := fun x : ℝ => x) (by fun_prop) measurable_id.aestronglyMeasurable]
  change (∫ p : ℝ × ℝ, (p.1 * p.2 + (B - 1)) / B
    ∂((lawR μ B h n).prod (lawR μ B h n))) = _
  rw [integral_div, integral_add hp (integrable_const _),
    integral_prod_mul (fun x : ℝ => x) (fun x : ℝ => x)]
  simp [pow_two]


/-- A linear domination of every fixed tilted logarithmic power on `(0, ∞)`. -/
theorem exists_tiltedLogPower_bound {B : ℝ} (hB : 2 < B) {q : ℝ} (hq : 0 ≤ q) :
    ∃ C : ℝ, ∀ x : ℝ, 0 < x → x ^ theta B * |Real.log x| ^ q ≤ C * (1 + x) := by
  let δ := min (theta B) (1 - theta B)
  have hδ : 0 < δ := lt_min (theta_pos hB) (sub_pos.mpr (theta_lt_one hB))
  let ε := δ / (q + 1)
  have hq1 : 0 < q + 1 := by linarith
  have hε : 0 < ε := div_pos hδ hq1
  have hεqδ : ε * q ≤ δ := by
    change δ / (q + 1) * q ≤ δ
    rw [div_mul_eq_mul_div, div_le_iff₀ hq1]
    nlinarith [mul_nonneg hδ.le hq]
  have hεqθ : ε * q ≤ theta B := hεqδ.trans (min_le_left _ _)
  have hεq1θ : ε * q ≤ 1 - theta B := hεqδ.trans (min_le_right _ _)
  refine ⟨ε ^ (-q), fun x hx => ?_⟩
  have hx0 : 0 ≤ x := hx.le
  have hC : 0 ≤ ε ^ (-q) := Real.rpow_nonneg hε.le _
  have hrewrite (a : ℝ) :
      x ^ theta B * (x ^ a / ε) ^ q = x ^ (theta B + a * q) * ε ^ (-q) := by
    rw [Real.div_rpow (Real.rpow_nonneg hx0 a) hε.le q, ← Real.rpow_mul hx0, div_eq_mul_inv,
      ← Real.rpow_neg hε.le, ← mul_assoc, ← Real.rpow_add hx]
  rcases le_total x 1 with hx1 | hx1
  · have hlog : |Real.log x| ≤ x ^ (-ε) / ε := by
      rw [abs_of_nonpos (Real.log_nonpos hx0 hx1)]
      have hl := Real.neg_rpow_div_le_log hx0 hε
      calc
        -Real.log x ≤ -(-x ^ (-ε) / ε) := neg_le_neg hl
        _ = x ^ (-ε) / ε := by ring
    have hpow : |Real.log x| ^ q ≤ (x ^ (-ε) / ε) ^ q :=
      Real.rpow_le_rpow (abs_nonneg _) hlog hq
    calc
      x ^ theta B * |Real.log x| ^ q
          ≤ x ^ theta B * (x ^ (-ε) / ε) ^ q :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hx0 _)
      _ = x ^ (theta B + (-ε) * q) * ε ^ (-q) := hrewrite (-ε)
      _ ≤ 1 * ε ^ (-q) := by
        apply mul_le_mul_of_nonneg_right _ hC
        exact Real.rpow_le_one hx0 hx1 (by nlinarith)
      _ ≤ ε ^ (-q) * (1 + x) := by
        have hxC : 0 ≤ ε ^ (-q) * x := mul_nonneg hC hx0
        nlinarith
  · have hlog : |Real.log x| ≤ x ^ ε / ε := by
      rw [abs_of_nonneg (Real.log_nonneg hx1)]
      exact Real.log_le_rpow_div hx0 hε
    have hpow : |Real.log x| ^ q ≤ (x ^ ε / ε) ^ q :=
      Real.rpow_le_rpow (abs_nonneg _) hlog hq
    calc
      x ^ theta B * |Real.log x| ^ q
          ≤ x ^ theta B * (x ^ ε / ε) ^ q :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hx0 _)
      _ = x ^ (theta B + ε * q) * ε ^ (-q) := hrewrite ε
      _ ≤ x * ε ^ (-q) := by
        apply mul_le_mul_of_nonneg_right _ hC
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hx1 (show theta B + ε * q ≤ 1 by linarith)
      _ ≤ ε ^ (-q) * (1 + x) := by
        have hxC : 0 ≤ ε ^ (-q) := hC
        nlinarith

/-- All fixed tilted logarithmic moments of the finite-volume laws are finite. -/
theorem integrable_tiltedLogPower_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ)
    {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun x : ℝ => x ^ theta B * |Real.log x| ^ q) (lawR μ B h n) := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  obtain ⟨C, hC⟩ := exists_tiltedLogPower_bound hB hq
  have hi := integrable_lawR_of hpos hmean hB h n
  have hdom : Integrable (fun x : ℝ => C * (1 + x)) (lawR μ B h n) :=
    ((integrable_const 1).add hi).const_mul C
  have hlogmeas : Measurable (fun x : ℝ => |Real.log x|) := by
    simpa only [Real.norm_eq_abs] using Real.measurable_log.norm
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => x ^ theta B * |Real.log x| ^ q) (lawR μ B h n) :=
    ((Real.continuous_rpow_const (theta_pos hB).le).measurable.mul
      ((Real.continuous_rpow_const hq).measurable.comp hlogmeas)).aestronglyMeasurable
  apply hdom.mono' hmeas
  filter_upwards [ae_pos_lawR hpos hB h n] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg (abs_nonneg _) _))]
  exact hC x hx


/-- On `[b, ∞)` with `0 < b < 1`, the logarithm has a linear majorant. -/
theorem abs_log_le_of_floor {b x : ℝ} (hb : 0 < b) (hb1 : b < 1) (hbx : b ≤ x) :
    |Real.log x| ≤ (-Real.log b + 1) * (1 + x) := by
  have hx : 0 < x := hb.trans_le hbx
  have hx0 : 0 ≤ x := hx.le
  have hlogb : Real.log b < 0 := Real.log_neg hb hb1
  have hC : 0 ≤ -Real.log b + 1 := by linarith
  rcases le_total x 1 with hx1 | hx1
  · rw [abs_of_nonpos (Real.log_nonpos hx0 hx1)]
    have hlog := Real.log_le_log hb hbx
    have hCx : 0 ≤ (-Real.log b + 1) * x := mul_nonneg hC hx0
    nlinarith
  · rw [abs_of_nonneg (Real.log_nonneg hx1)]
    have hlog : Real.log x ≤ x := by
      have := Real.log_le_sub_one_of_pos hx
      linarith
    have hCx : 0 ≤ (-Real.log b + 1) * x := mul_nonneg hC hx0
    nlinarith

/-- The unweighted logarithm is integrable at every positive level. -/
theorem integrable_log_lawR_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ}
    (hn : 1 ≤ n) :
    Integrable Real.log (lawR μ B h n) := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have hi := integrable_lawR_of hpos hmean hB h n
  have hb : 0 < floorSeq B 1 := floorSeq_one_pos hB
  have hb1 : floorSeq B 1 < 1 := floorSeq_lt_one hB 1
  have hdom : Integrable (fun x : ℝ => (-Real.log (floorSeq B 1) + 1) * (1 + x))
      (lawR μ B h n) := ((integrable_const 1).add hi).const_mul _
  apply hdom.mono' Real.measurable_log.aestronglyMeasurable
  filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx
  rw [Real.norm_eq_abs]
  exact abs_log_le_of_floor hb hb1 ((floorSeq_one_le hB hn).trans hx)

end DiamondPinning
