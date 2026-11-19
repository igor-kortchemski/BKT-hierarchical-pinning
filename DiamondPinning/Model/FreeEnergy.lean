module

public import DiamondPinning.Model.Basic
public import DiamondPinning.Model.Env
public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Statements.Env
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Order.OrderClosed

/-!
# Free energy and the critical point

This module constructs the finite-volume logarithmic expectations and the
monotone lower and upper sequences whose common limit is the free energy. It
also proves nonnegativity, monotonicity and Lipschitz continuity in the field,
vanishing at the annealed shift, and the extremal characterization of the
critical point. These are the bounds in `lem:basic-bounds` and its proof,
`source/critical.tex` lines 15–54.

The import of `DiamondPinning.Statements.Env` supplies the environment bridge
between `evalR` and `lawR`; no statement from that module is reproved here.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Set
open scoped Topology

/-- The height-`n` logarithmic moment `∫ log x ∂lawR μ B h n`. -/
noncomputable def logMoment (μ : Measure ℝ) (B h : ℝ) (n : ℕ) : ℝ :=
  ∫ x, Real.log x ∂lawR μ B h n

/-- The nondecreasing lower finite-volume approximant to `freeEnergy`,
normalized by `2 ^ (-max n 1)` and shifted by `Real.log B`. -/
noncomputable def logLowerSeq (μ : Measure ℝ) (B h : ℝ) (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (max n 1))⁻¹ * (logMoment μ B h (max n 1) - Real.log B)

/-- The nonincreasing upper finite-volume approximant to `freeEnergy`,
using the logarithm of the deterministic floor. -/
noncomputable def logUpperSeq (μ : Measure ℝ) (B h : ℝ) (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (max n 1))⁻¹ *
    (logMoment μ B h (max n 1) - Real.log (floorSeq B (max n 1)))

private theorem integral_log_lawR_succ_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    logMoment μ B h (n + 1) =
      ∫ p : ℝ × ℝ, Real.log ((p.1 * p.2 + (B - 1)) / B)
        ∂((lawR μ B h n).prod (lawR μ B h n)) := by
  have hi : Integrable Real.log
      (Measure.map (fun p : ℝ × ℝ => (p.1 * p.2 + (B - 1)) / B)
        ((lawR μ B h n).prod (lawR μ B h n))) := by
    simpa [lawR_succ] using
      (integrable_log_lawR_of hpos hmean hB h (show 1 ≤ n + 1 by omega))
  rw [logMoment, lawR_succ]
  exact integral_map (by fun_prop) hi.aestronglyMeasurable

private theorem logMoment_succ_bounds {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    2 * logMoment μ B h n - Real.log B ≤ logMoment μ B h (n + 1) ∧
    logMoment μ B h (n + 1) - Real.log (floorSeq B (n + 1)) ≤
      2 * (logMoment μ B h n - Real.log (floorSeq B n)) := by
  let ν := lawR μ B h n
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  have hlog : Integrable Real.log ν := integrable_log_lawR_of hpos hmean hB h hn
  have hlogfst : Integrable (fun p : ℝ × ℝ => Real.log p.1) (ν.prod ν) := hlog.comp_fst ν
  have hlogsnd : Integrable (fun p : ℝ × ℝ => Real.log p.2) (ν.prod ν) := hlog.comp_snd ν
  have hsum : Integrable (fun p : ℝ × ℝ => Real.log p.1 + Real.log p.2) (ν.prod ν) :=
    hlogfst.add hlogsnd
  have hlogrec : Integrable
      (fun p : ℝ × ℝ => Real.log ((p.1 * p.2 + (B - 1)) / B)) (ν.prod ν) := by
    have hi : Integrable Real.log
        (Measure.map (fun p : ℝ × ℝ => (p.1 * p.2 + (B - 1)) / B) (ν.prod ν)) := by
      simpa [lawR_succ, ν] using
        (integrable_log_lawR_of hpos hmean hB h (show 1 ≤ n + 1 by omega))
    exact (integrable_map_measure Real.measurable_log.aestronglyMeasurable
      (by fun_prop)).1 hi
  have hb : 0 < floorSeq B n := lt_of_lt_of_le (floorSeq_one_pos hB)
      (floorSeq_one_le hB hn)
  have hb1 : floorSeq B n < 1 := floorSeq_lt_one hB n
  have hbn : 0 < floorSeq B (n + 1) :=
    lt_of_lt_of_le (floorSeq_one_pos hB) (floorSeq_one_le hB (by omega))
  have hpoint : ∀ᵐ p : ℝ × ℝ ∂(ν.prod ν),
      Real.log p.1 + Real.log p.2 - Real.log B ≤
        Real.log ((p.1 * p.2 + (B - 1)) / B) ∧
      Real.log ((p.1 * p.2 + (B - 1)) / B) - Real.log (floorSeq B (n + 1)) ≤
        (Real.log p.1 - Real.log (floorSeq B n)) +
          (Real.log p.2 - Real.log (floorSeq B n)) := by
    have hpair : ∀ᵐ p : ℝ × ℝ ∂(ν.prod ν),
        floorSeq B n ≤ p.1 ∧ floorSeq B n ≤ p.2 := by
      rw [Measure.ae_prod_iff_ae_ae (by measurability)]
      filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx
      filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with y hy
      exact ⟨hx, hy⟩
    filter_upwards [hpair] with p hp
    have hx : 0 < p.1 := hb.trans_le hp.1
    have hy : 0 < p.2 := hb.trans_le hp.2
    have hc : 0 ≤ B - 1 := by linarith
    have hz : 0 < (p.1 * p.2 + (B - 1)) / B := by positivity
    have hlow : p.1 * p.2 / B ≤ (p.1 * p.2 + (B - 1)) / B := by
      apply (div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < B)).2
      linarith
    have hbasic : (p.1 * p.2 + (B - 1)) * floorSeq B n ^ 2 ≤
        p.1 * p.2 * (floorSeq B n ^ 2 + (B - 1)) := by
      have hxy : floorSeq B n ^ 2 ≤ p.1 * p.2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2)]
      nlinarith [mul_nonneg hc (sub_nonneg.mpr hxy)]
    have hratio :
        ((p.1 * p.2 + (B - 1)) / B) / floorSeq B (n + 1) ≤
          (p.1 / floorSeq B n) * (p.2 / floorSeq B n) := by
      rw [floorSeq_succ]
      have hcpos : 0 < floorSeq B n ^ 2 + (B - 1) := by positivity
      calc
        ((p.1 * p.2 + (B - 1)) / B) / ((floorSeq B n ^ 2 + (B - 1)) / B) =
            (p.1 * p.2 + (B - 1)) / (floorSeq B n ^ 2 + (B - 1)) := by
          field_simp [ne_of_gt (show (0 : ℝ) < B by linarith), ne_of_gt hcpos]
        _ ≤ p.1 * p.2 / floorSeq B n ^ 2 :=
          (div_le_div_iff₀ hcpos (sq_pos_of_pos hb)).2 hbasic
        _ = (p.1 / floorSeq B n) * (p.2 / floorSeq B n) := by
          field_simp [ne_of_gt hb]
    have hloglow : Real.log (p.1 * p.2 / B) ≤
        Real.log ((p.1 * p.2 + (B - 1)) / B) :=
      Real.log_le_log (div_pos (mul_pos hx hy) (by linarith)) hlow
    constructor
    · calc
        Real.log p.1 + Real.log p.2 - Real.log B = Real.log (p.1 * p.2 / B) := by
          rw [Real.log_div (mul_ne_zero hx.ne' hy.ne') (by linarith : B ≠ 0),
            Real.log_mul hx.ne' hy.ne']
        _ ≤ Real.log ((p.1 * p.2 + (B - 1)) / B) := hloglow
    · have hlogratio := Real.log_le_log (div_pos hz hbn) hratio
      have hlogrhspos : 0 < (p.1 / floorSeq B n) * (p.2 / floorSeq B n) := by positivity
      rw [Real.log_div hz.ne' hbn.ne',
        Real.log_mul (div_ne_zero hx.ne' hb.ne') (div_ne_zero hy.ne' hb.ne'),
        Real.log_div hx.ne' hb.ne', Real.log_div hy.ne' hb.ne'] at hlogratio
      linarith
  have hlowPoint := hpoint.mono fun p hp => hp.1
  have hupPoint := hpoint.mono fun p hp => hp.2
  have hlowInt := integral_mono_ae
    (hlogfst.add hlogsnd |>.sub (integrable_const (Real.log B))) hlogrec hlowPoint
  have hupperIntegrable : Integrable
      (fun p : ℝ × ℝ => (Real.log p.1 - Real.log (floorSeq B n)) +
        (Real.log p.2 - Real.log (floorSeq B n))) (ν.prod ν) := by
    exact (hlogfst.sub (integrable_const _)).add (hlogsnd.sub (integrable_const _))
  have hrecSubIntegrable : Integrable
      (fun p : ℝ × ℝ => Real.log ((p.1 * p.2 + (B - 1)) / B) -
        Real.log (floorSeq B (n + 1))) (ν.prod ν) :=
    hlogrec.sub (integrable_const _)
  have hupInt := integral_mono_ae hrecSubIntegrable hupperIntegrable hupPoint
  have hcoords : ∫ p : ℝ × ℝ, Real.log p.1 + Real.log p.2 ∂(ν.prod ν) =
      2 * logMoment μ B h n := by
    rw [integral_add hlogfst hlogsnd, integral_fun_fst, integral_fun_snd]
    simp [logMoment, ν]
    ring
  have hcoords' : ∫ p : ℝ × ℝ,
      (Real.log p.1 - Real.log (floorSeq B n)) +
        (Real.log p.2 - Real.log (floorSeq B n)) ∂(ν.prod ν) =
      2 * (logMoment μ B h n - Real.log (floorSeq B n)) := by
    have hfst : ∫ p : ℝ × ℝ, Real.log p.1 - Real.log (floorSeq B n) ∂(ν.prod ν) =
        logMoment μ B h n - Real.log (floorSeq B n) := by
      rw [integral_sub hlogfst (integrable_const _), integral_fun_fst]
      simp [logMoment, ν]
    have hsnd : ∫ p : ℝ × ℝ, Real.log p.2 - Real.log (floorSeq B n) ∂(ν.prod ν) =
        logMoment μ B h n - Real.log (floorSeq B n) := by
      rw [integral_sub hlogsnd (integrable_const _), integral_fun_snd]
      simp [logMoment, ν]
    change (∫ p : ℝ × ℝ, (Real.log p.1 - Real.log (floorSeq B n)) +
      (Real.log p.2 - Real.log (floorSeq B n)) ∂(ν.prod ν)) = _
    calc
      (∫ p : ℝ × ℝ, (Real.log p.1 - Real.log (floorSeq B n)) +
          (Real.log p.2 - Real.log (floorSeq B n)) ∂(ν.prod ν)) =
          (∫ p : ℝ × ℝ, Real.log p.1 - Real.log (floorSeq B n) ∂(ν.prod ν)) +
            ∫ p : ℝ × ℝ, Real.log p.2 - Real.log (floorSeq B n) ∂(ν.prod ν) :=
        integral_add (hlogfst.sub (integrable_const _))
          (hlogsnd.sub (integrable_const _))
      _ = _ := by rw [hfst, hsnd]; ring
  have hrecEq := integral_log_lawR_succ_eq hpos hmean hB h hn
  have hrecEqν : logMoment μ B h (n + 1) =
      ∫ p : ℝ × ℝ, Real.log ((p.1 * p.2 + (B - 1)) / B) ∂(ν.prod ν) := by
    calc
      logMoment μ B h (n + 1) =
          ∫ p : ℝ × ℝ, Real.log ((p.1 * p.2 + (B - 1)) / B)
            ∂((lawR μ B h n).prod (lawR μ B h n)) := hrecEq
      _ = ∫ p : ℝ × ℝ,
          Real.log ((p.1 * p.2 + (B - 1)) / B) ∂(ν.prod ν) := rfl
  have hlowCoord :
      ∫ p : ℝ × ℝ, (Real.log p.1 + Real.log p.2) - Real.log B ∂(ν.prod ν) =
        2 * logMoment μ B h n - Real.log B := by
    rw [integral_sub hsum (integrable_const _), hcoords]
    simp
  have hlowResult : 2 * logMoment μ B h n - Real.log B ≤ logMoment μ B h (n + 1) := by
    calc
      _ = ∫ p : ℝ × ℝ,
          (Real.log p.1 + Real.log p.2) - Real.log B ∂(ν.prod ν) := hlowCoord.symm
      _ ≤ ∫ p : ℝ × ℝ,
          Real.log ((p.1 * p.2 + (B - 1)) / B) ∂(ν.prod ν) := hlowInt
      _ = logMoment μ B h (n + 1) := hrecEqν.symm
  have hupResult : logMoment μ B h (n + 1) - Real.log (floorSeq B (n + 1)) ≤
      2 * (logMoment μ B h n - Real.log (floorSeq B n)) := by
    calc
      _ = ∫ p : ℝ × ℝ,
          Real.log ((p.1 * p.2 + (B - 1)) / B) -
            Real.log (floorSeq B (n + 1)) ∂(ν.prod ν) := by
        rw [hrecEqν, integral_sub hlogrec (integrable_const _)]
        simp
      _ ≤ ∫ p : ℝ × ℝ,
          (Real.log p.1 - Real.log (floorSeq B n)) +
            (Real.log p.2 - Real.log (floorSeq B n)) ∂(ν.prod ν) := hupInt
      _ = 2 * (logMoment μ B h n - Real.log (floorSeq B n)) := hcoords'
  constructor
  · exact hlowResult
  · exact hupResult

/-- The lower finite-volume approximants are nondecreasing from one height to
the next. -/
theorem logLowerSeq_step {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : logLowerSeq μ B h n ≤ logLowerSeq μ B h (n + 1) := by
  by_cases hn : n = 0
  · subst n
    simp [logLowerSeq]
  · have hn' : 1 ≤ n := by omega
    have hr := (logMoment_succ_bounds hpos hmean hB h hn').1
    simp only [logLowerSeq, max_eq_left hn', max_eq_left (by omega : 1 ≤ n + 1)]
    rw [pow_succ]
    have hp : 0 < (2 : ℝ) ^ n := by positivity
    have hq : 0 < ((2 : ℝ) ^ n)⁻¹ := inv_pos.mpr hp
    field_simp
    nlinarith [hr]

/-- The upper finite-volume approximants are nonincreasing from one height to
the next. -/
theorem logUpperSeq_step {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : logUpperSeq μ B h (n + 1) ≤ logUpperSeq μ B h n := by
  by_cases hn : n = 0
  · subst n
    simp [logUpperSeq]
  · have hn' : 1 ≤ n := by omega
    have hr := (logMoment_succ_bounds hpos hmean hB h hn').2
    simp only [logUpperSeq, max_eq_left hn', max_eq_left (by omega : 1 ≤ n + 1)]
    rw [pow_succ]
    have hp : 0 < (2 : ℝ) ^ n := by positivity
    have hq : 0 < ((2 : ℝ) ^ n)⁻¹ := inv_pos.mpr hp
    field_simp
    nlinarith [hr]

/-- Every upper finite-volume approximant is nonnegative. -/
theorem logUpperSeq_nonneg {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : 0 ≤ logUpperSeq μ B h n := by
  let k := max n 1
  have hk : 1 ≤ k := le_max_right _ _
  letI : IsProbabilityMeasure (lawR μ B h k) := isProbabilityMeasure_lawR B h k
  have hi := integrable_log_lawR_of hpos hmean hB h hk
  have hb := floorSeq_one_pos hB
  have hfloor : ∀ᵐ x ∂(lawR μ B h k), floorSeq B k ≤ x :=
    ae_floorSeq_le_lawR hpos hB h k
  have hpoint : ∀ᵐ x ∂(lawR μ B h k),
      Real.log (floorSeq B k) ≤ Real.log x := by
    filter_upwards [hfloor] with x hx
    exact Real.log_le_log (lt_of_lt_of_le hb (floorSeq_one_le hB hk)) hx
  have hm := integral_mono_ae (integrable_const _) hi hpoint
  have hc : ∫ x, Real.log (floorSeq B k) ∂(lawR μ B h k) = Real.log (floorSeq B k) := by
    simp
  have hm' : Real.log (floorSeq B k) ≤ logMoment μ B h k := by
    simpa [logMoment, hc] using hm
  have hlogB : Real.log (floorSeq B k) ≤ 0 :=
    Real.log_nonpos (floorSeq_nonneg hB k) (floorSeq_le_one hB k)
  dsimp [logUpperSeq, k]
  exact mul_nonneg (by positivity)
    (sub_nonneg.mpr hm')

/-- At each height the lower finite-volume approximant is at most the upper
one. -/
theorem logLowerSeq_le_upper {μ : Measure ℝ} {B h : ℝ} (hB : 2 < B)
    (n : ℕ) : logLowerSeq μ B h n ≤ logUpperSeq μ B h n := by
  let k := max n 1
  have hk : 1 ≤ k := le_max_right _ _
  have hb : 0 < floorSeq B k :=
    lt_of_lt_of_le (floorSeq_one_pos hB) (floorSeq_one_le hB hk)
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hlogfloor : Real.log (floorSeq B k) < 0 :=
    Real.log_neg hb (floorSeq_lt_one hB k)
  have hcoef : 0 ≤ ((2 : ℝ) ^ k)⁻¹ := by positivity
  dsimp [logLowerSeq, logUpperSeq, k]
  exact mul_le_mul_of_nonneg_left (by linarith) hcoef

/-- The gap between the upper and lower finite-volume approximants tends to
zero. -/
theorem logSeq_difference_tendsto {μ : Measure ℝ} {B h : ℝ} (hB : 2 < B) :
    Tendsto (fun n => logUpperSeq μ B h n - logLowerSeq μ B h n) atTop (𝓝 0) := by
  have hfloor := tendsto_floorSeq hB
  have hlogfloor : Tendsto (fun n => Real.log (floorSeq B n)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => Real.log (floorSeq B n)) atTop
        (𝓝 (Real.log 1)) :=
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hfloor
    simpa using h
  have hhalf : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hpow : Tendsto (fun n : ℕ => ((2 : ℝ) ^ (max n 1))⁻¹) atTop (𝓝 0) := by
    have heq : (fun n : ℕ => ((2 : ℝ) ^ (max n 1))⁻¹) =ᶠ[atTop]
        fun n => ((1 : ℝ) / 2) ^ n := by
      filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      simp [max_eq_left hn, inv_pow]
    exact hhalf.congr' heq.symm
  have hmax : Tendsto (fun n : ℕ => max n 1) atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_left n 1) tendsto_id
  have hlogMax : Tendsto (fun n : ℕ => Real.log (floorSeq B (max n 1))) atTop (𝓝 0) :=
    hlogfloor.comp hmax
  have hbound : Tendsto (fun n : ℕ => Real.log B - Real.log (floorSeq B (max n 1)))
      atTop (𝓝 (Real.log B)) := by
    simpa using tendsto_const_nhds.sub hlogMax
  have hprod := hpow.mul hbound
  have heq : (fun n => logUpperSeq μ B h n - logLowerSeq μ B h n) =
      fun n => ((2 : ℝ) ^ (max n 1))⁻¹ *
        (Real.log B - Real.log (floorSeq B (max n 1))) := by
    funext n
    simp [logUpperSeq, logLowerSeq]
    ring
  rw [heq]
  simpa using hprod

/-- The normalized logarithmic moments converge to `freeEnergy`; this proves
the convergence underlying the frozen `freeEnergy_tendsto`. -/
theorem freeEnergy_tendsto_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) :
    Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * logMoment μ B h n) atTop
      (𝓝 (freeEnergy μ B h)) := by
  have hu_mono : Monotone (logLowerSeq μ B h) :=
    monotone_nat_of_le_succ (logLowerSeq_step hpos hmean hB h)
  have hv_anti : Antitone (logUpperSeq μ B h) :=
    antitone_nat_of_succ_le (logUpperSeq_step hpos hmean hB h)
  have huv : ∀ n, logLowerSeq μ B h n ≤ logUpperSeq μ B h n :=
    fun n => logLowerSeq_le_upper hB n
  have hv_nonneg : ∀ n, 0 ≤ logUpperSeq μ B h n :=
    fun n => logUpperSeq_nonneg hpos hmean hB h n
  have hu_bdd : BddAbove (range (logLowerSeq μ B h)) := by
    refine ⟨logUpperSeq μ B h 0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact (huv n).trans (hv_anti (Nat.zero_le n))
  have hv_bdd : BddBelow (range (logUpperSeq μ B h)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact hv_nonneg n
  let L := ⨆ n, logLowerSeq μ B h n
  let U := ⨅ n, logUpperSeq μ B h n
  have hL : Tendsto (logLowerSeq μ B h) atTop (𝓝 L) := by
    simpa [L] using tendsto_atTop_ciSup hu_mono hu_bdd
  have hU : Tendsto (logUpperSeq μ B h) atTop (𝓝 U) := by
    simpa [U] using tendsto_atTop_ciInf hv_anti hv_bdd
  have hdiff := logSeq_difference_tendsto (μ := μ) (B := B) (h := h) hB
  have hdiff' : Tendsto (fun n => logUpperSeq μ B h n - logLowerSeq μ B h n)
      atTop (𝓝 (U - L)) := hU.sub hL
  have hUL : U = L := by
    have := tendsto_nhds_unique hdiff' hdiff
    linarith
  have hpow0 : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
    have hh := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (1 : ℝ) / 2) (by norm_num : (1 : ℝ) / 2 < 1)
    have heq : (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) = fun n => ((1 : ℝ) / 2) ^ n := by
      ext n
      simp
    rw [heq]
    exact hh
  have htarget' : Tendsto
      (fun n : ℕ => logLowerSeq μ B h n + ((2 : ℝ) ^ n)⁻¹ * Real.log B)
      atTop (𝓝 L) := by
    have hsmall := hpow0.mul_const (Real.log B)
    simpa [hUL] using hL.add hsmall
  have hEq : (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * logMoment μ B h n) =ᶠ[atTop]
      fun n => logLowerSeq μ B h n + ((2 : ℝ) ^ n)⁻¹ * Real.log B := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    simp [logLowerSeq, max_eq_left hn]
    ring
  have htarget : Tendsto
      (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * logMoment μ B h n) atTop (𝓝 L) :=
    htarget'.congr' hEq.symm
  have hlim : freeEnergy μ B h = L := by
    unfold freeEnergy
    exact htarget.limUnder_eq
  rw [hlim]
  exact htarget

/-- The normalized expectations of `Real.log` under `lawR` converge to
`freeEnergy`, proving the frozen `freeEnergy_tendsto`. -/
theorem freeEnergy_tendsto_statement_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) :
    Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * ∫ x, Real.log x ∂(lawR μ B h n)) atTop
      (𝓝 (freeEnergy μ B h)) := by
  simpa [logMoment] using freeEnergy_tendsto_aux hpos hmean hB h

/-- Increasing the field increases every positive environment partition
function, by at most the factor `exp (2 ^ n * u)` at height `n`. -/
theorem evalR_shift_bounds {B h u : ℝ} (hB : 1 < B) (hu : 0 ≤ u) :
    ∀ n (e : Env n), Env.Pos n e →
      evalR B h n e ≤ evalR B (h + u) n e ∧
        evalR B (h + u) n e ≤ Real.exp ((2 : ℝ) ^ n * u) * evalR B h n e := by
  intro n
  induction n with
  | zero =>
      intro e he
      change 0 < (show ℝ from e) at he
      simp only [evalR_zero, pow_zero, one_mul]
      constructor
      · exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by linarith)) he.le
      · change Real.exp (h + u) * (show ℝ from e) ≤
          Real.exp u * (Real.exp h * (show ℝ from e))
        have heq : Real.exp (h + u) * (show ℝ from e) =
            Real.exp u * (Real.exp h * (show ℝ from e)) := by
          rw [Real.exp_add]
          ring
        exact heq.le
  | succ n ih =>
      intro e he
      rcases e with ⟨e₁, e₂⟩
      rcases he with ⟨he₁, he₂⟩
      have h₁ := ih e₁ he₁
      have h₂ := ih e₂ he₂
      have hp₁ : 0 < evalR B h n e₁ := evalR_pos hB h he₁
      have hp₂ : 0 < evalR B h n e₂ := evalR_pos hB h he₂
      have hq₁ : 0 < evalR B (h + u) n e₁ := evalR_pos hB (h + u) he₁
      have hq₂ : 0 < evalR B (h + u) n e₂ := evalR_pos hB (h + u) he₂
      let q := Real.exp ((2 : ℝ) ^ n * u)
      have hqpos : 0 < q := Real.exp_pos _
      have hqone : 1 ≤ q := by
        dsimp [q]
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (mul_nonneg (by positivity) hu)
      have hc : 0 ≤ B - 1 := by linarith
      have hBpos : 0 < B := by linarith
      have hlowProd : evalR B h n e₁ * evalR B h n e₂ ≤
          evalR B (h + u) n e₁ * evalR B (h + u) n e₂ := by
        calc
          evalR B h n e₁ * evalR B h n e₂ ≤
              evalR B (h + u) n e₁ * evalR B h n e₂ :=
            mul_le_mul_of_nonneg_right h₁.1 hp₂.le
          _ ≤ evalR B (h + u) n e₁ * evalR B (h + u) n e₂ :=
            mul_le_mul_of_nonneg_left h₂.1 hq₁.le
      have hupProd : evalR B (h + u) n e₁ * evalR B (h + u) n e₂ ≤
          q * q * (evalR B h n e₁ * evalR B h n e₂) := by
        calc
          evalR B (h + u) n e₁ * evalR B (h + u) n e₂ ≤
              (q * evalR B h n e₁) * evalR B (h + u) n e₂ :=
            mul_le_mul_of_nonneg_right h₁.2 hq₂.le
          _ ≤ (q * evalR B h n e₁) * (q * evalR B h n e₂) :=
            mul_le_mul_of_nonneg_left h₂.2 (mul_nonneg hqpos.le hp₁.le)
          _ = q * q * (evalR B h n e₁ * evalR B h n e₂) := by ring
      have hqarg : (2 : ℝ) ^ (n + 1) * u =
          ((2 : ℝ) ^ n * u) + ((2 : ℝ) ^ n * u) := by
        rw [pow_succ]
        ring
      have hqeq : Real.exp ((2 : ℝ) ^ (n + 1) * u) = q * q := by
        rw [hqarg, Real.exp_add]
      constructor
      · change (evalR B h n e₁ * evalR B h n e₂ + (B - 1)) / B ≤
          (evalR B (h + u) n e₁ * evalR B (h + u) n e₂ + (B - 1)) / B
        apply (div_le_div_iff_of_pos_right hBpos).2
        nlinarith
      · change (evalR B (h + u) n e₁ * evalR B (h + u) n e₂ + (B - 1)) / B ≤
          Real.exp ((2 : ℝ) ^ (n + 1) * u) *
            ((evalR B h n e₁ * evalR B h n e₂ + (B - 1)) / B)
        have hq2 : 1 ≤ q * q := by nlinarith [sq_nonneg (q - 1)]
        have hconst : B - 1 ≤ q * q * (B - 1) := by
          calc
            B - 1 = 1 * (B - 1) := by ring
            _ ≤ q * q * (B - 1) := mul_le_mul_of_nonneg_right hq2 hc
        have hnum : evalR B (h + u) n e₁ * evalR B (h + u) n e₂ + (B - 1) ≤
            Real.exp ((2 : ℝ) ^ (n + 1) * u) *
              (evalR B h n e₁ * evalR B h n e₂ + (B - 1)) := by
          calc
          evalR B (h + u) n e₁ * evalR B (h + u) n e₂ + (B - 1) ≤
              q * q * (evalR B h n e₁ * evalR B h n e₂) +
                q * q * (B - 1) := add_le_add hupProd hconst
          _ = q * q * (evalR B h n e₁ * evalR B h n e₂ + (B - 1)) := by ring
          _ = Real.exp ((2 : ℝ) ^ (n + 1) * u) *
                (evalR B h n e₁ * evalR B h n e₂ + (B - 1)) := by rw [hqeq]
        calc
          _ ≤ (Real.exp ((2 : ℝ) ^ (n + 1) * u) *
              (evalR B h n e₁ * evalR B h n e₂ + (B - 1))) / B :=
            (div_le_div_iff_of_pos_right hBpos).2 hnum
          _ = _ := by ring

private theorem integral_log_evalR_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    logMoment μ B h n = ∫ e, Real.log (evalR B h n e) ∂envMeasure μ n := by
  unfold logMoment
  have hi : Integrable Real.log
      (Measure.map (evalR B h n) (envMeasure μ n)) := by
    rw [map_evalR_envMeasure μ B h n]
    exact integrable_log_lawR_of hpos hmean hB h hn
  rw [← map_evalR_envMeasure μ B h n]
  exact integral_map (measurable_evalR B h n).aemeasurable hi.aestronglyMeasurable

private theorem integrable_log_evalR {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun e => Real.log (evalR B h n e)) (envMeasure μ n) := by
  have hmap : (envMeasure μ n).map (evalR B h n) = lawR μ B h n :=
    map_evalR_envMeasure μ B h n
  have hi : Integrable Real.log ((envMeasure μ n).map (evalR B h n)) := by
    rw [hmap]
    exact integrable_log_lawR_of hpos hmean hB h hn
  exact (integrable_map_measure Real.measurable_log.aestronglyMeasurable
    (measurable_evalR B h n).aemeasurable).1 hi

/-- A nonnegative field increment changes `freeEnergy` by a nonnegative
amount at most equal to the increment. This proves the corresponding frozen
free-energy increment bound. -/
theorem freeEnergy_field_increment_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ freeEnergy μ B (h + u) - freeEnergy μ B h ∧
      freeEnergy μ B (h + u) - freeEnergy μ B h ≤ u := by
  have hseqLower : ∀ {n : ℕ}, 1 ≤ n →
      ((2 : ℝ) ^ n)⁻¹ * logMoment μ B h n ≤
        ((2 : ℝ) ^ n)⁻¹ * logMoment μ B (h + u) n := by
    intro n hn
    letI : IsProbabilityMeasure (envMeasure μ n) := envMeasure.instIsProbabilityMeasure μ n
    have hB' : 1 < B := by linarith
    have hi₀ := integrable_log_evalR hpos hmean hB h hn
    have hi₁ := integrable_log_evalR hpos hmean hB (h + u) hn
    have hpoint : ∀ᵐ e ∂(envMeasure μ n),
        Real.log (evalR B h n e) ≤ Real.log (evalR B (h + u) n e) := by
      filter_upwards [ae_envPos hpos n] with e he
      exact Real.log_le_log (evalR_pos hB' h he)
        (evalR_shift_bounds (h := h) hB' hu n e he).1
    have hI := integral_mono_ae hi₀ hi₁ hpoint
    rw [← integral_log_evalR_eq hpos hmean hB h hn,
      ← integral_log_evalR_eq hpos hmean hB (h + u) hn] at hI
    exact mul_le_mul_of_nonneg_left hI (by positivity)
  have hseqUpper : ∀ {n : ℕ}, 1 ≤ n →
      ((2 : ℝ) ^ n)⁻¹ * logMoment μ B (h + u) n ≤
        ((2 : ℝ) ^ n)⁻¹ * logMoment μ B h n + u := by
    intro n hn
    letI : IsProbabilityMeasure (envMeasure μ n) := envMeasure.instIsProbabilityMeasure μ n
    have hB' : 1 < B := by linarith
    have hi₀ := integrable_log_evalR hpos hmean hB h hn
    have hi₁ := integrable_log_evalR hpos hmean hB (h + u) hn
    have hpoint : ∀ᵐ e ∂(envMeasure μ n),
        Real.log (evalR B (h + u) n e) ≤
          Real.log (evalR B h n e) + (2 : ℝ) ^ n * u := by
      filter_upwards [ae_envPos hpos n] with e he
      have hp := evalR_pos hB' h he
      have hp' := evalR_pos hB' (h + u) he
      have hq := evalR_shift_bounds (h := h) hB' hu n e he
      have hlog := Real.log_le_log hp' hq.2
      rw [Real.log_mul (Real.exp_ne_zero _) hp.ne', Real.log_exp] at hlog
      simpa [add_comm] using hlog
    have hI := integral_mono_ae hi₁
      (hi₀.add (integrable_const ((2 : ℝ) ^ n * u))) hpoint
    have hI' : ∫ e, Real.log (evalR B (h + u) n e) ∂envMeasure μ n ≤
        (∫ e, Real.log (evalR B h n e) ∂envMeasure μ n) + (2 : ℝ) ^ n * u := by
      calc
        _ ≤ ∫ e, Real.log (evalR B h n e) + (2 : ℝ) ^ n * u ∂envMeasure μ n := hI
        _ = _ := by
          rw [integral_add hi₀ (integrable_const _)]
          simp
    rw [← integral_log_evalR_eq hpos hmean hB (h + u) hn,
      ← integral_log_evalR_eq hpos hmean hB h hn] at hI'
    have hp : 0 < (2 : ℝ) ^ n := by positivity
    have hpow : ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n * u) = u := by
      field_simp
    calc
      ((2 : ℝ) ^ n)⁻¹ * logMoment μ B (h + u) n ≤
          ((2 : ℝ) ^ n)⁻¹ * (logMoment μ B h n + (2 : ℝ) ^ n * u) :=
        mul_le_mul_of_nonneg_left hI' (by positivity)
      _ = ((2 : ℝ) ^ n)⁻¹ * logMoment μ B h n + u := by rw [mul_add, hpow]
  have hS₀ := freeEnergy_tendsto_aux hpos hmean hB h
  have hS₁ := freeEnergy_tendsto_aux hpos hmean hB (h + u)
  have hlow := le_of_tendsto_of_tendsto hS₀ hS₁ <| eventually_atTop.2
    ⟨1, fun n hn => hseqLower hn⟩
  have hupp := le_of_tendsto_of_tendsto hS₁ (hS₀.const_add u) <| eventually_atTop.2
    ⟨1, fun n hn => by simpa [add_comm] using hseqUpper hn⟩
  constructor <;> linarith

/-- The free energy is `1`-Lipschitz as a function of the field; this proves
the Lipschitz consequence of the frozen free-energy increment bound. -/
theorem freeEnergy_lipschitz_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    LipschitzWith 1 (fun h => freeEnergy μ B h) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · have hi := freeEnergy_field_increment_aux hpos hmean hB x
      (u := y - x) (sub_nonneg.mpr hxy)
    have hi' : 0 ≤ freeEnergy μ B y - freeEnergy μ B x ∧
        freeEnergy μ B y - freeEnergy μ B x ≤ y - x := by simpa using hi
    have hmono : freeEnergy μ B x ≤ freeEnergy μ B y := by linarith [hi'.1]
    have hup : freeEnergy μ B y - freeEnergy μ B x ≤ y - x := hi'.2
    rw [abs_of_nonpos (sub_nonpos.mpr hmono), abs_of_nonpos (sub_nonpos.mpr hxy)]
    simpa using hup
  · have hi := freeEnergy_field_increment_aux hpos hmean hB y
      (u := x - y) (sub_nonneg.mpr hyx)
    have hi' : 0 ≤ freeEnergy μ B x - freeEnergy μ B y ∧
        freeEnergy μ B x - freeEnergy μ B y ≤ x - y := by simpa using hi
    have hmono : freeEnergy μ B y ≤ freeEnergy μ B x := by linarith [hi'.1]
    have hup : freeEnergy μ B x - freeEnergy μ B y ≤ x - y := hi'.2
    rw [abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonneg (sub_nonneg.mpr hyx)]
    simpa [abs_sub_comm] using hup

/-- The free energy is nonnegative, proving the frozen `freeEnergy_nonneg`. -/
theorem freeEnergy_nonneg_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) : 0 ≤ freeEnergy μ B h := by
  have hS := freeEnergy_tendsto_aux hpos hmean hB h
  have hfloor := tendsto_floorSeq hB
  have hlogfloor : Tendsto (fun n : ℕ => Real.log (floorSeq B n)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => Real.log (floorSeq B n)) atTop
        (𝓝 (Real.log 1)) :=
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hfloor
    simpa using h
  have hpow : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
    have hh := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (1 : ℝ) / 2) (by norm_num : (1 : ℝ) / 2 < 1)
    have heq : (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) = fun n => ((1 : ℝ) / 2) ^ n := by
      ext n
      simp
    rw [heq]
    exact hh
  have hcorr := hpow.mul hlogfloor
  have hlim : Tendsto
      (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * logMoment μ B h n -
        ((2 : ℝ) ^ n)⁻¹ * Real.log (floorSeq B n)) atTop
      (𝓝 (freeEnergy μ B h)) := by
    simpa using hS.sub hcorr
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ ((2 : ℝ) ^ n)⁻¹ * logMoment μ B h n -
        ((2 : ℝ) ^ n)⁻¹ * Real.log (floorSeq B n) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hv := logUpperSeq_nonneg hpos hmean hB h n
    simpa [logUpperSeq, max_eq_left hn, mul_sub] using hv
  exact ge_of_tendsto hlim hnonneg

private theorem integral_lawR_logc_mean {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    ∀ n, ∫ x, x ∂lawR μ B (Real.log (B - 1)) n = B - 1 := by
  have hc : 0 < B - 1 := by linarith
  intro n
  induction n with
  | zero =>
      rw [integral_lawR_zero hmean]
      exact Real.exp_log hc
  | succ n ih =>
      rw [integral_lawR_succ hpos hmean hB (Real.log (B - 1)) n, ih]
      field_simp [ne_of_gt (show (0 : ℝ) < B by linarith)]
      ring

private theorem logMoment_logc_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (n : ℕ) (hn : 1 ≤ n) :
    logMoment μ B (Real.log (B - 1)) n ≤ Real.log (B - 1) := by
  let ν := lawR μ B (Real.log (B - 1)) n
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B (Real.log (B - 1)) n
  have hc : 0 < B - 1 := by linarith
  have hmeanν : ∫ x, x ∂ν = B - 1 := integral_lawR_logc_mean hpos hmean hB n
  have hiLog : Integrable Real.log ν := integrable_log_lawR_of hpos hmean hB _ hn
  have hiId : Integrable (fun x : ℝ => x) ν := integrable_lawR_of hpos hmean hB _ n
  have hpoint : ∀ᵐ x ∂ν,
      Real.log x ≤ Real.log (B - 1) + (x / (B - 1) - 1) := by
    filter_upwards [ae_floorSeq_le_lawR hpos hB (Real.log (B - 1)) n] with x hx
    have hxpos : 0 < x := by
      exact (floorSeq_one_pos hB).trans_le ((floorSeq_one_le hB hn).trans hx)
    have hlog := Real.log_le_sub_one_of_pos (div_pos hxpos hc)
    rw [Real.log_div hxpos.ne' hc.ne'] at hlog
    nlinarith
  have hiRhs : Integrable (fun x : ℝ => Real.log (B - 1) + (x / (B - 1) - 1)) ν := by
    exact (integrable_const _).add ((hiId.div_const _).sub (integrable_const _))
  have hmono := integral_mono_ae hiLog hiRhs hpoint
  have hscaled : ∫ x, x / (B - 1) ∂ν = 1 := by
    have heq : (fun x : ℝ => x / (B - 1)) = fun x => (B - 1)⁻¹ * x := by
      funext x
      ring
    rw [heq, integral_const_mul, hmeanν]
    field_simp
  have hrhs : ∫ x, Real.log (B - 1) + (x / (B - 1) - 1) ∂ν =
      Real.log (B - 1) := by
    calc
      ∫ x, Real.log (B - 1) + (x / (B - 1) - 1) ∂ν =
          (∫ _x : ℝ, Real.log (B - 1) ∂ν) +
            ((∫ x, x / (B - 1) ∂ν) - (∫ _x : ℝ, (1 : ℝ) ∂ν)) := by
        calc
          ∫ x, Real.log (B - 1) + (x / (B - 1) - 1) ∂ν =
              (∫ _x : ℝ, Real.log (B - 1) ∂ν) +
                (∫ x, x / (B - 1) - 1 ∂ν) :=
            integral_add (integrable_const _) ((hiId.div_const _).sub (integrable_const _))
          _ = _ := by
            rw [integral_sub (hiId.div_const _) (integrable_const _)]
      _ = Real.log (B - 1) := by simp [hscaled]
  change (∫ x, Real.log x ∂ν) ≤ _ at hmono
  simpa [logMoment, ν, hrhs] using hmono

/-- The free energy vanishes at the annealed critical field
`Real.log (B - 1)`. This proves the frozen vanishing statement at that field. -/
theorem freeEnergy_logc_eq_zero_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    freeEnergy μ B (Real.log (B - 1)) = 0 := by
  let ha := Real.log (B - 1)
  have hc : 0 < B - 1 := by linarith
  have hS := freeEnergy_tendsto_aux hpos hmean hB ha
  have hpow : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
    have hh := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (1 : ℝ) / 2) (by norm_num : (1 : ℝ) / 2 < 1)
    have heq : (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) = fun n => ((1 : ℝ) / 2) ^ n := by
      ext n
      simp
    rw [heq]
    exact hh
  have hzero : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * Real.log (B - 1))
      atTop (𝓝 0) := by
    simpa using hpow.mul_const (Real.log (B - 1))
  have hbound : ∀ᶠ n : ℕ in atTop,
      ((2 : ℝ) ^ n)⁻¹ * logMoment μ B ha n ≤
        ((2 : ℝ) ^ n)⁻¹ * Real.log (B - 1) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hm := logMoment_logc_le hpos hmean hB n hn
    exact mul_le_mul_of_nonneg_left hm (by positivity)
  have hle : freeEnergy μ B ha ≤ 0 := by
    have h := le_of_tendsto_of_tendsto hS hzero hbound
    simpa using h
  have hge := freeEnergy_nonneg_aux hpos hmean hB ha
  exact le_antisymm hle hge

/-- The free energy is nondecreasing in the field, proving the frozen
monotonicity consequence of the field-increment bound. -/
theorem freeEnergy_monotone_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    Monotone (freeEnergy μ B) := by
  intro x y hxy
  have hi := freeEnergy_field_increment_aux hpos hmean hB x
    (u := y - x) (sub_nonneg.mpr hxy)
  have heq : x + (y - x) = y := by ring
  have hxle : freeEnergy μ B x ≤ freeEnergy μ B (x + (y - x)) :=
    sub_nonneg.mp hi.1
  simpa [heq] using hxle

/-- The free energy vanishes at every field at or below
`Real.log (B - 1)`. This proves the corresponding frozen zero-region bound. -/
theorem freeEnergy_zero_left_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {h : ℝ} (hh : h ≤ Real.log (B - 1)) : freeEnergy μ B h = 0 := by
  have hmono := freeEnergy_monotone_aux hpos hmean hB
  have hle : freeEnergy μ B h ≤ 0 := by
    calc
      freeEnergy μ B h ≤ freeEnergy μ B (Real.log (B - 1)) := hmono hh
      _ = 0 := freeEnergy_logc_eq_zero_aux hpos hmean hB
  exact le_antisymm hle (freeEnergy_nonneg_aux hpos hmean hB h)

private theorem freeEnergy_ge_first_lower_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) :
    (logMoment μ B h 1 - Real.log B) / 2 ≤ freeEnergy μ B h := by
  have hmono : Monotone (logLowerSeq μ B h) :=
    monotone_nat_of_le_succ (logLowerSeq_step hpos hmean hB h)
  have hS := freeEnergy_tendsto_aux hpos hmean hB h
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hbound : ∀ᶠ n : ℕ in atTop,
      (logMoment μ B h 1 - Real.log B) / 2 ≤
        ((2 : ℝ) ^ n)⁻¹ * logMoment μ B h n := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hinc := hmono hn
    have hfirst : logLowerSeq μ B h 1 =
        (logMoment μ B h 1 - Real.log B) / 2 := by
      simp [logLowerSeq]
      ring
    have hlast : logLowerSeq μ B h n =
        ((2 : ℝ) ^ n)⁻¹ * (logMoment μ B h n - Real.log B) := by
      simp [logLowerSeq, max_eq_left hn]
    have hcompare : ((2 : ℝ) ^ n)⁻¹ *
        (logMoment μ B h n - Real.log B) ≤
          ((2 : ℝ) ^ n)⁻¹ * logMoment μ B h n :=
      mul_le_mul_of_nonneg_left (sub_le_self _ hlogB.le) (by positivity)
    calc
      (logMoment μ B h 1 - Real.log B) / 2 = logLowerSeq μ B h 1 := hfirst.symm
      _ ≤ logLowerSeq μ B h n := hinc
      _ = ((2 : ℝ) ^ n)⁻¹ * (logMoment μ B h n - Real.log B) := hlast
      _ ≤ ((2 : ℝ) ^ n)⁻¹ * logMoment μ B h n := hcompare
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hS hbound

private theorem measure_ge_half_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ w, w ∂μ = 1) : 0 < μ.real (Set.Ici ((1 : ℝ) / 2)) := by
  let S : Set ℝ := Set.Ici ((1 : ℝ) / 2)
  have hId : Integrable (fun w : ℝ => w) μ := integrable_id_of_integral_eq_one hmean
  by_contra hnot
  have hzeroReal : μ.real S = 0 := le_antisymm (le_of_not_gt hnot) (measureReal_nonneg)
  have hzero : μ S = 0 := (measureReal_eq_zero_iff (by finiteness)).mp hzeroReal
  have houtside := measure_eq_zero_iff_ae_notMem.mp hzero
  have hle : ∀ᵐ w ∂μ, w ≤ (1 : ℝ) / 2 := houtside.mono fun w hw => by
    change ¬ w ∈ Set.Ici ((1 : ℝ) / 2) at hw
    simp only [Set.mem_Ici, not_le] at hw
    exact hw.le
  have hInt := integral_mono_ae hId (integrable_const ((1 : ℝ) / 2)) hle
  have hbad : (1 : ℝ) ≤ (1 : ℝ) / 2 := by simpa [hmean] using hInt
  linarith

private theorem exists_freeEnergy_pos_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    ∃ h, 0 < freeEnergy μ B h := by
  let S : Set ℝ := Set.Ici ((1 : ℝ) / 2)
  let p : ℝ := μ.real S
  have hp : 0 < p := measure_ge_half_pos hmean
  let E : Set (Env 1) := S ×ˢ S
  have hEmeas : MeasurableSet E := (measurableSet_Ici).prod measurableSet_Ici
  let rho := envMeasure μ 1
  letI : IsProbabilityMeasure rho := envMeasure.instIsProbabilityMeasure μ 1
  have hEprob : rho.real E = p * p := by
    calc
      rho.real E = (μ.prod μ).real (S ×ˢ S) := by rfl
      _ = μ.real S * μ.real S := measureReal_prod_prod S S
      _ = p * p := by rfl
  have hpE : 0 < rho.real E := by rw [hEprob]; exact mul_pos hp hp
  have hc : 0 < B - 1 := by linarith
  have hBpos : 0 < B := by linarith
  let l₀ := Real.log ((B - 1) / B)
  have hl₀arg : 0 < (B - 1) / B := div_pos hc hBpos
  have hl₀lt : (B - 1) / B < 1 := (div_lt_one hBpos).2 (by linarith)
  have hl₀ : l₀ < 0 := by dsimp [l₀]; exact Real.log_neg hl₀arg hl₀lt
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hd : 0 < Real.log B - l₀ := by linarith
  let A := Real.log B + (Real.log B - l₀ + 1) / (p * p)
  have hAeq : l₀ + p * p * (A - l₀) =
      Real.log B + p * p * (Real.log B - l₀) + 1 := by
    dsimp [A]
    field_simp [ne_of_gt (mul_pos hp hp)]
    ring
  have hGainEvent : Real.log B < l₀ + p * p * (A - l₀) := by
    rw [hAeq]
    nlinarith [mul_pos (mul_pos hp hp) hd]
  have hA : Real.log B < A := by
    dsimp [A]
    have : 0 < (Real.log B - l₀ + 1) / (p * p) :=
      div_pos (by linarith) (mul_pos hp hp)
    linarith
  have hExp : B < Real.exp A := by
    have he := Real.exp_lt_exp.mpr hA
    simpa [Real.exp_log (show 0 < B by linarith)] using he
  have hTpos : 0 < 4 * (B * Real.exp A - (B - 1)) := by
    have hbig : B - 1 < B * Real.exp A := by nlinarith [hExp]
    positivity
  let T := 4 * (B * Real.exp A - (B - 1))
  let h₀ := Real.log T / 2
  have hfieldExp : Real.exp (2 * h₀) = T := by
    dsimp [h₀, T]
    rw [show 2 * (Real.log (4 * (B * Real.exp A - (B - 1))) / 2) =
      Real.log (4 * (B * Real.exp A - (B - 1))) by ring]
    exact Real.exp_log hTpos
  have hEval : ∀ e : Env 1, e ∈ E → Real.exp A ≤ evalR B h₀ 1 e := by
    intro e he
    change e.1 ∈ S ∧ e.2 ∈ S at he
    have hw₁ : (1 : ℝ) / 2 ≤ e.1 := by simpa [S] using he.1
    have hw₂ : (1 : ℝ) / 2 ≤ e.2 := by simpa [S] using he.2
    change (1 : ℝ) / 2 ≤ (show ℝ from e.1) at hw₁
    change (1 : ℝ) / 2 ≤ (show ℝ from e.2) at hw₂
    let q := Real.exp h₀
    have hq : 0 < q := Real.exp_pos h₀
    have hq₁ : q / 2 ≤ q * (show ℝ from e.1) := by
      dsimp [q]
      calc
        Real.exp h₀ / 2 = Real.exp h₀ * ((1 : ℝ) / 2) := by ring
        _ ≤ Real.exp h₀ * (show ℝ from e.1) := mul_le_mul_of_nonneg_left hw₁ hq.le
    have hq₂ : q / 2 ≤ q * (show ℝ from e.2) := by
      dsimp [q]
      calc
        Real.exp h₀ / 2 = Real.exp h₀ * ((1 : ℝ) / 2) := by ring
        _ ≤ Real.exp h₀ * (show ℝ from e.2) := mul_le_mul_of_nonneg_left hw₂ hq.le
    have hwpos₁ : 0 ≤ (show ℝ from e.1) :=
      le_trans (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2) hw₁
    have hqhalf : 0 ≤ q / 2 := by positivity
    have hprod : q ^ 2 / 4 ≤
        (q * (show ℝ from e.1)) * (q * (show ℝ from e.2)) := by
      calc
        q ^ 2 / 4 = (q / 2) * (q / 2) := by ring
        _ ≤ (q * (show ℝ from e.1)) * (q / 2) :=
          mul_le_mul_of_nonneg_right hq₁ hqhalf
        _ ≤ (q * (show ℝ from e.1)) * (q * (show ℝ from e.2)) :=
          mul_le_mul_of_nonneg_left hq₂ (mul_nonneg hq.le hwpos₁)
    have hqexp : q ^ 2 = Real.exp (2 * h₀) := by
      dsimp [q]
      rw [show 2 * h₀ = h₀ + h₀ by ring, Real.exp_add]
      ring
    have hprod' : Real.exp (2 * h₀) / 4 ≤
        (Real.exp h₀ * (show ℝ from e.1)) * (Real.exp h₀ * (show ℝ from e.2)) := by
      calc
        Real.exp (2 * h₀) / 4 = q ^ 2 / 4 := by rw [← hqexp]
        _ ≤ (q * (show ℝ from e.1)) * (q * (show ℝ from e.2)) := hprod
        _ = _ := by dsimp [q]
    have hnum : B * Real.exp A ≤
        (Real.exp h₀ * (show ℝ from e.1)) * (Real.exp h₀ * (show ℝ from e.2)) + (B - 1) := by
      rw [hfieldExp] at hprod'
      dsimp [T] at hprod'
      field_simp at hprod'
      calc
        B * Real.exp A = (B * Real.exp A - (B - 1)) + (B - 1) := by ring
        _ ≤ (Real.exp h₀ ^ 2 * (show ℝ from e.1)) * (show ℝ from e.2) + (B - 1) :=
          add_le_add_left hprod' (B - 1)
        _ = (Real.exp h₀ * (show ℝ from e.1)) *
              (Real.exp h₀ * (show ℝ from e.2)) + (B - 1) := by ring
    rw [evalR_succ, evalR_zero, evalR_zero]
    apply (le_div_iff₀ hBpos).2
    simpa [mul_comm] using hnum
  have hbase : ∀ᵐ e ∂rho, (B - 1) / B ≤ evalR B h₀ 1 e := by
    filter_upwards [ae_envPos hpos 1] with e he
    have hp₁ : 0 < evalR B h₀ 0 e.1 := evalR_pos (by linarith) h₀ he.1
    have hp₂ : 0 < evalR B h₀ 0 e.2 := evalR_pos (by linarith) h₀ he.2
    rw [evalR_succ]
    apply (div_le_div_iff_of_pos_right hBpos).2
    nlinarith [mul_nonneg hp₁.le hp₂.le]
  have hpoint : ∀ᵐ e ∂rho,
      l₀ + E.indicator (fun _ => A - l₀) e ≤ Real.log (evalR B h₀ 1 e) := by
    filter_upwards [ae_envPos hpos 1, hbase] with e he hb
    have hRpos : 0 < evalR B h₀ 1 e := evalR_pos (by linarith) h₀ he
    by_cases hin : e ∈ E
    · have hlog := Real.log_le_log (Real.exp_pos A) (hEval e hin)
      have hval : l₀ + E.indicator (fun _ => A - l₀) e = A := by
        rw [Set.indicator_of_mem hin]
        ring
      rw [hval]
      simpa [Real.log_exp] using hlog
    · have hlog := Real.log_le_log hl₀arg hb
      have hval : l₀ + E.indicator (fun _ => A - l₀) e = l₀ := by
        rw [Set.indicator_of_notMem hin]
        ring
      rw [hval]
      simpa [l₀] using hlog
  have hiEval : Integrable (fun e => Real.log (evalR B h₀ 1 e)) rho :=
    integrable_log_evalR hpos hmean hB h₀ (by norm_num)
  have hlowInt := integral_mono_ae
    ((integrable_const _).add ((integrable_const _).indicator hEmeas)) hiEval hpoint
  have hsimple : ∫ e, l₀ + E.indicator (fun _ => A - l₀) e ∂rho =
      l₀ + p * p * (A - l₀) := by
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hEmeas),
      integral_indicator_const (A - l₀) hEmeas]
    rw [hEprob]
    have hconst : ∫ _e : Env 1, l₀ ∂rho = l₀ := by
      rw [integral_const]
      change (rho Set.univ).toReal * l₀ = l₀
      rw [measure_univ]
      simp
    rw [hconst]
    simp [smul_eq_mul]
  have hm : l₀ + p * p * (A - l₀) ≤ logMoment μ B h₀ 1 := by
    calc
      l₀ + p * p * (A - l₀) = ∫ e, l₀ + E.indicator (fun _ => A - l₀) e ∂rho := hsimple.symm
      _ ≤ ∫ e, Real.log (evalR B h₀ 1 e) ∂rho := hlowInt
      _ = logMoment μ B h₀ 1 := (integral_log_evalR_eq hpos hmean hB h₀ (by norm_num)).symm
  have hmoment : Real.log B < logMoment μ B h₀ 1 := hGainEvent.trans_le hm
  have hfirst : 0 < (logMoment μ B h₀ 1 - Real.log B) / 2 := by linarith
  have hF := freeEnergy_ge_first_lower_aux hpos hmean hB h₀
  exact ⟨h₀, hfirst.trans_le hF⟩

/-- The constructed critical point is the greatest field at which the free
energy vanishes, proving the frozen `criticalPoint_isGreatest`. -/
theorem criticalPoint_isGreatest_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    IsGreatest {h : ℝ | freeEnergy μ B h = 0} (criticalPoint μ B) := by
  let Z : Set ℝ := {h : ℝ | freeEnergy μ B h = 0}
  have hcont : Continuous (freeEnergy μ B) :=
    (freeEnergy_lipschitz_aux hpos hmean hB).continuous
  have hclosed : IsClosed Z := isClosed_eq hcont continuous_const
  have hzero : Real.log (B - 1) ∈ Z := by
    exact freeEnergy_logc_eq_zero_aux hpos hmean hB
  obtain ⟨h₁, hh₁⟩ := exists_freeEnergy_pos_aux hpos hmean hB
  have hnonempty : Z.Nonempty := ⟨Real.log (B - 1), hzero⟩
  have hbdd : BddAbove Z := by
    refine ⟨h₁, ?_⟩
    intro h hh
    by_contra hnot
    have hlt : h₁ < h := lt_of_not_ge hnot
    have hmono := freeEnergy_monotone_aux hpos hmean hB
    have hle : freeEnergy μ B h₁ ≤ 0 := by
      have hhzero : freeEnergy μ B h = 0 := by simpa [Z] using hh
      have hcmp := hmono hlt.le
      rw [hhzero] at hcmp
      exact hcmp
    linarith
  have hmem : criticalPoint μ B ∈ Z := by
    unfold criticalPoint
    exact hclosed.csSup_mem hnonempty hbdd
  refine ⟨hmem, ?_⟩
  intro h hh
  unfold criticalPoint
  exact le_csSup hbdd (by simpa [Z] using hh)

end DiamondPinning
