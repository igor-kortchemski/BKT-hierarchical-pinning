module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Model.Basic
public import DiamondPinning.Model.FreeEnergy
public import DiamondPinning.Model.Scaling
public import DiamondPinning.Model.Profile
public import DiamondPinning.Model.Hard
public import DiamondPinning.Proofs.JensenBarrier
public import DiamondPinning.Proofs.EscapeComparison
public import DiamondPinning.Proofs.EscapePairs
public import DiamondPinning.Proofs.EscapeBandExit
public import DiamondPinning.Proofs.ProductAssembly
public import DiamondPinning.Proofs.ResponseAssembly
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# The free-energy bounds from Section 8

Conditional assemblies that consume the scaling continuation theorem.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

private theorem energy_gamma_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ γ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hγ : γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃)) : 0 < γ := by
  obtain ⟨C, hC, _, _, hEll, _⟩ := criticalProduct_aux hpos hmean hB hshift
  obtain ⟨ℓ₃', hℓpos, hprod⟩ := hEll
  obtain ⟨κ', hκpos, hκlim, _⟩ :=
    response_transversality_aux hpos hmean hB hshift
  have hℓeq : ℓ₃ = ℓ₃' := tendsto_nhds_unique hℓ₃ hprod
  have hκeq : κ = κ' := tendsto_nhds_unique hκ hκlim
  have ha : 0 < Real.log B := Real.log_pos (by linarith)
  rw [hγ, hℓeq, hκeq]
  positivity

private theorem energy_logMoment_succ_upper {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    logMoment μ B h (n + 1) - Real.log (floorSeq B (n + 1)) ≤
      2 * (logMoment μ B h n - Real.log (floorSeq B n)) := by
  let ν := lawR μ B h n
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  have hlog : Integrable Real.log ν := integrable_log_lawR_of hpos hmean hB h hn
  have hlogfst : Integrable (fun p : ℝ × ℝ => Real.log p.1) (ν.prod ν) := hlog.comp_fst ν
  have hlogsnd : Integrable (fun p : ℝ × ℝ => Real.log p.2) (ν.prod ν) := hlog.comp_snd ν
  have hupperIntegrable : Integrable
      (fun p : ℝ × ℝ => (Real.log p.1 - Real.log (floorSeq B n)) +
        (Real.log p.2 - Real.log (floorSeq B n))) (ν.prod ν) :=
    (hlogfst.sub (integrable_const _)).add (hlogsnd.sub (integrable_const _))
  have hlogrec : Integrable
      (fun p : ℝ × ℝ => Real.log ((p.1 * p.2 + (B - 1)) / B)) (ν.prod ν) := by
    have hi : Integrable Real.log
        (Measure.map (fun p : ℝ × ℝ => (p.1 * p.2 + (B - 1)) / B) (ν.prod ν)) := by
      simpa [lawR_succ, ν] using
        (integrable_log_lawR_of hpos hmean hB h (show 1 ≤ n + 1 by omega))
    exact (integrable_map_measure Real.measurable_log.aestronglyMeasurable
      (by fun_prop)).1 hi
  have hrecSubIntegrable : Integrable
      (fun p : ℝ × ℝ => Real.log ((p.1 * p.2 + (B - 1)) / B) -
        Real.log (floorSeq B (n + 1))) (ν.prod ν) := hlogrec.sub (integrable_const _)
  have hb : 0 < floorSeq B n :=
    lt_of_lt_of_le (floorSeq_one_pos hB) (floorSeq_one_le hB hn)
  have hb1 : floorSeq B n < 1 := floorSeq_lt_one hB n
  have hbn : 0 < floorSeq B (n + 1) :=
    lt_of_lt_of_le (floorSeq_one_pos hB) (floorSeq_one_le hB (by omega))
  have hpoint : ∀ᵐ p : ℝ × ℝ ∂(ν.prod ν),
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
    have hlogratio := Real.log_le_log (div_pos hz hbn) hratio
    have hlogrhspos : 0 < (p.1 / floorSeq B n) * (p.2 / floorSeq B n) := by positivity
    rw [Real.log_div hz.ne' hbn.ne',
      Real.log_mul (div_ne_zero hx.ne' hb.ne') (div_ne_zero hy.ne' hb.ne'),
      Real.log_div hx.ne' hb.ne', Real.log_div hy.ne' hb.ne'] at hlogratio
    linarith
  have hupInt := integral_mono_ae hrecSubIntegrable hupperIntegrable hpoint
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
    calc
      (∫ p : ℝ × ℝ, (Real.log p.1 - Real.log (floorSeq B n)) +
          (Real.log p.2 - Real.log (floorSeq B n)) ∂(ν.prod ν)) =
          (∫ p : ℝ × ℝ, Real.log p.1 - Real.log (floorSeq B n) ∂(ν.prod ν)) +
            ∫ p : ℝ × ℝ, Real.log p.2 - Real.log (floorSeq B n) ∂(ν.prod ν) :=
        integral_add (hlogfst.sub (integrable_const _))
          (hlogsnd.sub (integrable_const _))
      _ = _ := by rw [hfst, hsnd]; ring
  have hrecEq : logMoment μ B h (n + 1) =
      ∫ p : ℝ × ℝ, Real.log ((p.1 * p.2 + (B - 1)) / B) ∂(ν.prod ν) := by
    have hi : Integrable Real.log
        (Measure.map (fun p : ℝ × ℝ => (p.1 * p.2 + (B - 1)) / B) (ν.prod ν)) := by
      simpa [lawR_succ, ν] using
        (integrable_log_lawR_of hpos hmean hB h (show 1 ≤ n + 1 by omega))
    rw [logMoment, lawR_succ]
    exact integral_map (by fun_prop) hi.aestronglyMeasurable
  calc
    logMoment μ B h (n + 1) - Real.log (floorSeq B (n + 1)) =
        ∫ p : ℝ × ℝ, Real.log ((p.1 * p.2 + (B - 1)) / B) -
          Real.log (floorSeq B (n + 1)) ∂(ν.prod ν) := by
      rw [hrecEq, integral_sub hlogrec (integrable_const _)]
      simp
    _ ≤ ∫ p : ℝ × ℝ,
        (Real.log p.1 - Real.log (floorSeq B n)) +
          (Real.log p.2 - Real.log (floorSeq B n)) ∂(ν.prod ν) := hupInt
    _ = 2 * (logMoment μ B h n - Real.log (floorSeq B n)) := hcoords'

private theorem energy_freeEnergy_upper_finite {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    freeEnergy μ B h ≤ ((2 : ℝ) ^ n)⁻¹ *
      (logMoment μ B h n - Real.log (floorSeq B n)) := by
  let V : ℕ → ℝ := fun k => ((2 : ℝ) ^ (max k 1))⁻¹ *
    (logMoment μ B h (max k 1) - Real.log (floorSeq B (max k 1)))
  have hanti : Antitone V := by
    apply antitone_nat_of_succ_le
    intro k
    by_cases hk : k = 0
    · subst k
      simp [V]
    · have hk1 : 1 ≤ k := by omega
      have hs := energy_logMoment_succ_upper hpos hmean hB h hk1
      simp only [V, max_eq_left hk1, max_eq_left (by omega : 1 ≤ k + 1)]
      calc
        ((2 : ℝ) ^ (k + 1))⁻¹ *
            (logMoment μ B h (k + 1) - Real.log (floorSeq B (k + 1))) ≤
          ((2 : ℝ) ^ (k + 1))⁻¹ *
            (2 * (logMoment μ B h k - Real.log (floorSeq B k))) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
        _ = ((2 : ℝ) ^ k)⁻¹ *
            (logMoment μ B h k - Real.log (floorSeq B k)) := by
          rw [pow_succ]
          field_simp
  have hpow : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) := by
      have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
      have heq : (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) = fun k => (1 / 2 : ℝ) ^ k := by
        ext k
        simp [one_div_pow]
      rw [heq]
      exact ht
  have hfloor : Tendsto (fun k : ℕ => floorSeq B k) atTop (𝓝 1) := tendsto_floorSeq hB
  have hlogfloor : Tendsto (fun k : ℕ => Real.log (floorSeq B k)) atTop (𝓝 0) := by
    have ht := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hfloor
    simpa [Function.comp_def] using ht
  have hmax : Tendsto (fun k : ℕ => max k 1) atTop atTop :=
    tendsto_atTop_mono (fun k => le_max_left k 1) tendsto_id
  have hVlim : Tendsto V atTop (𝓝 (freeEnergy μ B h)) := by
    have hS := (freeEnergy_tendsto_aux hpos hmean hB h).comp hmax
    have hcor := (hpow.mul hlogfloor).comp hmax
    simpa [V, mul_sub] using hS.sub hcor
  have htail : ∀ᶠ k : ℕ in atTop, V k ≤ ((2 : ℝ) ^ n)⁻¹ *
      (logMoment μ B h n - Real.log (floorSeq B n)) := by
    filter_upwards [eventually_ge_atTop n] with k hk
    exact (hanti hk).trans_eq (by simp [V, max_eq_left hn])
  exact le_of_tendsto hVlim htail

private theorem energy_freeEnergy_pos_above {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {h : ℝ} (hh : criticalPoint μ B < h) : 0 < freeEnergy μ B h := by
  have hnonneg := freeEnergy_nonneg_aux hpos hmean hB h
  by_contra hnot
  have hzero : freeEnergy μ B h = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have hcrit := (criticalPoint_isGreatest_aux hpos hmean hB).2 (by simpa using hzero)
  linarith

private theorem energy_integrable_realMoment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Integrable (fun x : ℝ => x ^ q) (lawR μ B h n) := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have hi := integrable_lawR_of hpos hmean hB h n
  have hdom : Integrable (fun x : ℝ => 1 + x) (lawR μ B h n) :=
    (integrable_const 1).add hi
  apply hdom.mono' (Real.continuous_rpow_const hq0).measurable.aestronglyMeasurable
  filter_upwards [ae_pos_lawR hpos hB h n] with x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le q)]
  rcases le_total x 1 with hx1 | hx1
  · exact (Real.rpow_le_one hx.le hx1 hq0).trans (by linarith)
  · calc
      x ^ q ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hq1
      _ = x := Real.rpow_one x
      _ ≤ 1 + x := by linarith

-- Jensen's integral rearrangement and the finite-size logarithm need more reduction fuel.
set_option maxHeartbeats 400000 in
private theorem energy_freeEnergy_bound_at_scale {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {t s M C ε N P : ℝ}
    (htpos : 0 < t) (hs : 0 < s)
    (hM : 0 < M) (hMdef : M = |P| + 2)
    (hC : 1 ≤ C) (hCdef : C = 2 * M / theta B +
      -Real.log (floorSeq B 1) + 1) (hε : 0 < ε)
    (hN : 0 < N ∧ 1 < N ∧ 1 / t < N ∧ 2 * s / (Real.log B * theta B) < N ∧
      2 * (Real.log C + Real.log 2) / ε < N)
    (hclose : |scaledTransform μ B 1 N t s - P| < 1) :
    0 < freeEnergy μ B (criticalPoint μ B + N⁻¹ ^ 2) ∧
      N⁻¹ * Real.log (freeEnergy μ B (criticalPoint μ B + N⁻¹ ^ 2)) ≤
        -t * Real.log 2 + ε / 2 := by
  rcases hN with ⟨hNpos, hNone, hNtlarge, hNq, hNerr⟩
  let a := Real.log B
  let θ := theta B
  let n := ⌊N * t⌋₊
  let q := weightExponent B N s
  change 2 * s / (a * θ) < N at hNq
  have ha : 0 < Real.log B := Real.log_pos (by linarith)
  have hθ : 0 < theta B := theta_pos hB
  have hθ1 : theta B < 1 := theta_lt_one hB
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNt : (1 : ℝ) ≤ N * t := by
    have hh := (div_lt_iff₀ htpos).1 hNtlarge
    nlinarith
  have hn : 1 ≤ n := by
    apply Nat.le_floor
    norm_num
    exact hNt
  have hθhalf : s / (a * N) < θ / 2 := by
    apply (div_lt_div_iff₀ (mul_pos ha hNpos) (by norm_num : (0 : ℝ) < 2)).2
    have hden : 0 < a * θ := mul_pos ha hθ
    have hNbound := (div_lt_iff₀ hden).1 hNq
    nlinarith
  have hqpos : 0 < q := by
    dsimp [q, weightExponent]
    change s / (Real.log B * N) < theta B / 2 at hθhalf
    nlinarith [hθhalf]
  have hq1 : q < 1 := by
    dsimp [q, weightExponent]
    have hsdiv : 0 < s / (Real.log B * N) := div_pos hs (mul_pos ha hNpos)
    linarith [hθ1, hsdiv]
  have hLupper : scaledTransform μ B 1 N t s ≤ M := by
    have : scaledTransform μ B 1 N t s < P + 1 := by
      have hh := abs_lt.mp hclose
      linarith
    calc
      scaledTransform μ B 1 N t s ≤ P + 1 := le_of_lt this
      _ ≤ |P| + 2 := by nlinarith [le_abs_self P]
      _ = M := hMdef.symm
  have hMoment : realMoment μ B (criticalPoint μ B + N⁻¹ ^ 2) n q - 1 ≤ M / N := by
    have hdef : scaledTransform μ B 1 N t s =
        N * (realMoment μ B (criticalPoint μ B + N⁻¹ ^ 2) n q - 1) := by
      dsimp [scaledTransform, transformAt, scalingField, weightExponent, n, q]
      congr 2
      field_simp [ne_of_gt hNpos]
    rw [hdef] at hLupper
    exact (le_div_iff₀ hNpos).2 (by nlinarith)
  let ν := lawR μ B (criticalPoint μ B + N⁻¹ ^ 2) n
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B _ n
  have hiLog : Integrable Real.log ν := integrable_log_lawR_of hpos hmean hB _ hn
  have hiPow : Integrable (fun x : ℝ => x ^ q) ν :=
    energy_integrable_realMoment hpos hmean hB _ n hqpos.le hq1.le
  have hpoint : ∀ᵐ x ∂ν, q * Real.log x ≤ x ^ q - 1 := by
    filter_upwards [ae_pos_lawR hpos hB _ n] with x hx
    have hr := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx q)
    rw [Real.log_rpow hx q] at hr
    simpa [mul_comm] using hr
  have hJensen : q * logMoment μ B (criticalPoint μ B + N⁻¹ ^ 2) n ≤
      realMoment μ B (criticalPoint μ B + N⁻¹ ^ 2) n q - 1 := by
    have hi := integral_mono_ae (hiLog.const_mul q)
      (hiPow.sub (integrable_const (1 : ℝ))) hpoint
    have hpowInt : ∫ x, (x ^ q - 1) ∂ν =
        realMoment μ B (criticalPoint μ B + N⁻¹ ^ 2) n q - 1 := by
      rw [integral_sub hiPow (integrable_const (1 : ℝ))]
      have hmass : ν.real Set.univ = 1 := MeasureTheory.probReal_univ
      rw [integral_const, smul_eq_mul, mul_one, hmass]
      rfl
    rw [integral_const_mul] at hi
    change q * (∫ x, Real.log x ∂ν) ≤ ∫ x, (x ^ q - 1) ∂ν at hi
    rw [hpowInt] at hi
    simpa [logMoment, ν] using hi
  have hqhalf : θ / 2 ≤ q := by dsimp [q, weightExponent]; linarith
  have hlogq : logMoment μ B (criticalPoint μ B + N⁻¹ ^ 2) n ≤ M / (N * q) := by
    apply (le_div_iff₀ (mul_pos hNpos hqpos)).2
    have hNM := (le_div_iff₀ hNpos).1 hMoment
    have hmul := mul_le_mul_of_nonneg_left hJensen hNpos.le
    nlinarith [hmul, hNM]
  have hlogMoment : logMoment μ B (criticalPoint μ B + N⁻¹ ^ 2) n ≤
      M * 2 / (N * θ) := by
    calc
      logMoment μ B (criticalPoint μ B + N⁻¹ ^ 2) n ≤ M / (N * q) := hlogq
      _ ≤ M * 2 / (N * θ) := by
        have hden : N * (θ / 2) ≤ N * q := mul_le_mul_of_nonneg_left hqhalf hNpos.le
        have hposden : 0 < N * (θ / 2) := by positivity
        calc
          M / (N * q) ≤ M / (N * (θ / 2)) :=
            div_le_div_of_nonneg_left hM.le hposden hden
          _ = M * 2 / (N * θ) := by field_simp <;> ring
  have hfloorlog : Real.log (floorSeq B 1) ≤ Real.log (floorSeq B n) := by
    apply Real.log_le_log (floorSeq_one_pos hB)
    exact floorSeq_monotone hB hn
  have hfinite := energy_freeEnergy_upper_finite hpos hmean hB
    (criticalPoint μ B + N⁻¹ ^ 2) hn
  have hFupper : freeEnergy μ B (criticalPoint μ B + N⁻¹ ^ 2) ≤
      ((2 : ℝ) ^ n)⁻¹ * C := by
    calc
      freeEnergy μ B (criticalPoint μ B + N⁻¹ ^ 2) ≤
          ((2 : ℝ) ^ n)⁻¹ *
            (logMoment μ B (criticalPoint μ B + N⁻¹ ^ 2) n -
              Real.log (floorSeq B n)) := hfinite
      _ ≤ ((2 : ℝ) ^ n)⁻¹ * C := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hratio : M * 2 / (N * θ) ≤ 2 * M / θ := by
          have hrepr : M * 2 / (N * θ) = (2 * M / θ) * N⁻¹ := by
            field_simp <;> ring
          rw [hrepr]
          have hinv : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hNone.le
          have hbase : 0 ≤ (2 * M) / θ :=
            div_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (le_of_lt (by positivity : 0 < M))) hθ.le
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hinv hbase
        rw [hCdef]
        linarith [hlogMoment, hfloorlog]
  have hfield : criticalPoint μ B < criticalPoint μ B + N⁻¹ ^ 2 := by
    have : 0 < N⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hNpos)
    linarith
  have hFpos := energy_freeEnergy_pos_above hpos hmean hB hfield
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hlogupper := Real.log_le_log hFpos hFupper
  have hpowlog : Real.log (((2 : ℝ) ^ n)⁻¹ * C) =
      Real.log C - (n : ℝ) * Real.log 2 := by
    rw [Real.log_mul (inv_ne_zero (by norm_num : (2 : ℝ) ^ n ≠ 0)) hCpos.ne',
      Real.log_inv, Real.log_pow]
    ring
  have hnfloor : (n : ℝ) ≤ N * t := Nat.floor_le (mul_nonneg hNpos.le htpos.le)
  have hnlow : N * t - 1 < n := by nlinarith [Nat.lt_floor_add_one (N * t)]
  have hfinal : N⁻¹ * Real.log (freeEnergy μ B (criticalPoint μ B + N⁻¹ ^ 2)) ≤
      -t * Real.log 2 + ε / 2 := by
    rw [hpowlog] at hlogupper
    have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
    have hErr : (Real.log C + Real.log 2) / N < ε / 2 := by
      apply (div_lt_iff₀ hNpos).2
      have hh := (div_lt_iff₀ hε).1 hNerr
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hlogupper (inv_nonneg.mpr hNpos.le)
    have hdecay : (Real.log C - (n : ℝ) * Real.log 2) / N ≤
        -t * Real.log 2 + (Real.log C + Real.log 2) / N := by
      apply (div_le_iff₀ hNpos).2
      have hgap : N * t - (n : ℝ) < 1 := by linarith [hnlow]
      have hgaple : N * t - (n : ℝ) ≤ 1 := le_of_lt hgap
      have hgapMul := mul_le_mul_of_nonneg_right hgaple hlog2.le
      field_simp [ne_of_gt hNpos]
      nlinarith [hgapMul]
    have hscaled' : N⁻¹ * Real.log (freeEnergy μ B (criticalPoint μ B + N⁻¹ ^ 2)) ≤
        (Real.log C - (n : ℝ) * Real.log 2) / N := by
      simpa [div_eq_mul_inv, mul_comm] using hscaled
    exact hscaled'.trans (hdecay.trans (by linarith [hErr]))
  exact ⟨hFpos, hfinal⟩

-- The continuation binder and its uniform-limit interface require extra reduction fuel.
set_option maxHeartbeats 400000 in
theorem freeEnergy_upper_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ γ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hγ : γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃))
    (hCont : ∀ {lam : ℝ}, 0 < lam → ∀ {I : Set ℝ}, IsCompact I →
      (∀ t ∈ I, IsPrePoleTime (γ * lam) t) → ∀ {s : ℝ}, 0 < s →
      0 < s + sInf (profileB (γ * lam) '' I) →
      TendstoUniformlyOn (fun N t => scaledTransform μ B lam N t s)
          (fun t => profileTransform (γ * lam) t s) atTop I ∧
        ∀ t ∈ I, WeakConvergence
          (fun N => weightedMeasure (scalingMeasure μ B lam N t) s) atTop
          (weightedMeasure (profileMeasure (γ * lam) t) s)) :
    ∀ ε > 0, ∀ᶠ u in 𝓝[>] (0 : ℝ),
      Real.sqrt u * Real.log (freeEnergy μ B (criticalPoint μ B + u)) ≤
        -(Real.pi * Real.log 2) / Real.sqrt γ + ε := by
  have hγpos := energy_gamma_pos hpos hmean hB hshift hℓ₃ hκ hγ
  intro ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let T := Real.pi / Real.sqrt γ
  have hTpos : 0 < T := div_pos Real.pi_pos (Real.sqrt_pos.2 hγpos)
  let d := min (T / 2) (ε / (2 * Real.log 2))
  have hdpos : 0 < d := by
    dsimp [d]
    exact lt_min (by positivity) (div_pos hε (by positivity))
  have hdT : d ≤ T / 2 := min_le_left _ _
  have hdε : d ≤ ε / (2 * Real.log 2) := min_le_right _ _
  let t := T - d
  have htpos : 0 < t := by dsimp [t]; linarith
  have htT : t < T := by dsimp [t]; linarith
  let s := 1 + max 0 (-profileB γ t)
  have hs : 0 < s := by dsimp [s]; positivity
  have hsb : 0 < s + profileB γ t := by
    by_cases hb : 0 ≤ profileB γ t
    · have hm : max 0 (-profileB γ t) = 0 := max_eq_left (by linarith)
      simp only [s, hm]
      linarith
    · have hb' : profileB γ t < 0 := lt_of_not_ge hb
      have hm : max 0 (-profileB γ t) = -profileB γ t :=
        max_eq_right (by linarith)
      simp only [s, hm]
      norm_num
  let I : Set ℝ := {t}
  have hI : IsCompact I := by simp [I]
  have hIpole : ∀ x ∈ I, IsPrePoleTime γ x := by
    intro x hx
    have hx' : x = t := by simpa [I] using hx
    subst x
    refine ⟨htpos, ?_⟩
    intro _
    simpa [T] using htT
  have hadm : 0 < s + sInf (profileB γ '' I) := by
    simpa [I, Set.image_singleton, sInf_singleton] using hsb
  have hIpole' : ∀ x ∈ I, IsPrePoleTime (γ * 1) x := by
    simpa only [mul_one] using hIpole
  have hadm' : 0 < s + sInf (profileB (γ * 1) '' I) := by
    simpa only [mul_one] using hadm
  have hconv := (hCont (lam := 1) (by norm_num) (I := I) hI hIpole'
    (s := s) hs hadm').1.tendsto_at (x := t) (by simp [I])
  let P := profileTransform (γ * 1) t s
  let M := |P| + 2
  have hM : 0 < M := by dsimp [M]; positivity
  have hclose : ∀ᶠ N : ℝ in atTop,
      |scaledTransform μ B 1 N t s - P| < 1 := by
    filter_upwards [hconv.eventually (Metric.ball_mem_nhds P one_pos)] with N hN
    simpa [Real.dist_eq, P] using hN
  let a := Real.log B
  let θ := theta B
  have ha : 0 < a := Real.log_pos (by linarith)
  have hθ : 0 < θ := theta_pos hB
  have hθ1 : θ < 1 := theta_lt_one hB
  let C := 2 * M / θ + (-Real.log (floorSeq B 1)) + 1
  have hC : 1 ≤ C := by
    change (1 : ℝ) ≤ 2 * M / θ + -Real.log (floorSeq B 1) + 1
    have hfloor : floorSeq B 1 < 1 := floorSeq_lt_one hB 1
    have hb : 0 < floorSeq B 1 := floorSeq_one_pos hB
    have hlog : Real.log (floorSeq B 1) < 0 := Real.log_neg hb hfloor
    have hposTerm : 0 < 2 * M / θ := div_pos (by positivity) hθ
    have hlogneg : 0 ≤ -Real.log (floorSeq B 1) := le_of_lt (neg_pos.mpr hlog)
    nlinarith
  have hsmallN : ∀ᶠ N : ℝ in atTop,
      0 < N ∧ 1 < N ∧ 1 / t < N ∧ 2 * s / (a * θ) < N ∧
        2 * (Real.log C + Real.log 2) / ε < N ∧
        |scaledTransform μ B 1 N t s - P| < 1 := by
    let K := max 1 (max (1 / t) (max (2 * s / (a * θ))
      (2 * (Real.log C + Real.log 2) / ε)))
    filter_upwards [eventually_gt_atTop K, hclose] with N hN hcl
    have hKone : (1 : ℝ) ≤ K := le_max_left _ _
    have hKt : 1 / t ≤ K := le_trans (le_max_left _ _)
      (le_max_right _ _)
    have hKq : 2 * s / (a * θ) ≤ K := le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
    have hKerr : 2 * (Real.log C + Real.log 2) / ε ≤ K := le_trans
      (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    have hNone : 1 < N := hKone.trans_lt hN
    have hNpos : 0 < N := lt_trans (by norm_num) hNone
    have hNt : 1 / t < N := hKt.trans_lt hN
    have hNq : 2 * s / (a * θ) < N := hKq.trans_lt hN
    have hNerr : 2 * (Real.log C + Real.log 2) / ε < N := hKerr.trans_lt hN
    exact ⟨hNpos, hNone, hNt, hNq, hNerr, hcl⟩
  have hNresult : ∀ᶠ N : ℝ in atTop,
      0 < freeEnergy μ B (criticalPoint μ B + N⁻¹ ^ 2) ∧
        N⁻¹ * Real.log (freeEnergy μ B (criticalPoint μ B + N⁻¹ ^ 2)) ≤
          -t * Real.log 2 + ε / 2 := by
    filter_upwards [hsmallN] with N hN
    rcases hN with ⟨hNpos, hNone, hNtlarge, hNq, hNerr, hcl⟩
    exact energy_freeEnergy_bound_at_scale hpos hmean hB hshift
      (t := t) (s := s) (M := M) (C := C) (ε := ε) (N := N) (P := P)
      htpos hs hM rfl hC rfl hε
      ⟨hNpos, hNone, hNtlarge, by simpa [a, θ] using hNq, hNerr⟩ hcl
  have hsqrt : Tendsto (fun u : ℝ => Real.sqrt u) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    have hfilter : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) := nhdsWithin_le_nhds
    have hsqrt0 : Tendsto (fun u : ℝ => Real.sqrt u) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      by simpa using Real.continuous_sqrt.continuousAt.tendsto.mono_left hfilter
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hsqrt0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact Real.sqrt_pos.2 hu
  have hNmap : Tendsto (fun u : ℝ => (Real.sqrt u)⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero.comp hsqrt
  filter_upwards [hNmap.eventually hNresult, self_mem_nhdsWithin] with u hu hu0
  rcases hu with ⟨hFpos, hNbound⟩
  let N := (Real.sqrt u)⁻¹
  have hNpos : 0 < N := inv_pos.mpr (Real.sqrt_pos.2 hu0)
  have hNfield : criticalPoint μ B + N⁻¹ ^ 2 = criticalPoint μ B + u := by
    dsimp [N]
    rw [inv_inv, Real.sq_sqrt hu0.le]
  have hsqrtN : Real.sqrt u = N⁻¹ := by simp [N]
  have hTarget : -t * Real.log 2 + ε / 2 ≤
      -(Real.pi * Real.log 2) / Real.sqrt γ + ε := by
    have hdlog : d * Real.log 2 ≤ ε / 2 := by
      calc
        d * Real.log 2 ≤ (ε / (2 * Real.log 2)) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hdε hlog2.le
        _ = ε / 2 := by field_simp
    have hTlog : T * Real.log 2 = (Real.pi * Real.log 2) / Real.sqrt γ := by
      dsimp [T]
      ring
    calc
      -t * Real.log 2 + ε / 2 = -T * Real.log 2 + d * Real.log 2 + ε / 2 := by
        dsimp [t]
        ring
      _ ≤ -T * Real.log 2 + ε := by linarith
      _ = -(Real.pi * Real.log 2) / Real.sqrt γ + ε := by
        rw [show -T * Real.log 2 = -(T * Real.log 2) by ring, hTlog]
        ring
  have hNbound' := hNbound
  rw [hNfield, hsqrtN.symm] at hNbound'
  exact hNbound'.trans hTarget

private theorem energy_profile_time_before_pole {v δ : ℝ} (hv : 0 < v)
    (hδ : 0 < δ) :
    ∃ τ z : ℝ, 0 < τ ∧ τ < Real.pi / Real.sqrt v ∧ 0 < z ∧ z ≤ Real.pi / 4 ∧
      profileB v τ < 0 ∧ profileA v τ ≥ 4 * v / z ^ 2 ∧
      z ^ 2 ≤ Real.exp (-1) * v * δ ^ 2 / 10 ^ 8 := by
  let c : ℝ := Real.exp (-1)
  let z := min (Real.pi / 4) (Real.sqrt (c * v) * δ / 10000)
  have hc : 0 < c := by dsimp [c]; positivity
  have hzpos : 0 < z := by
    dsimp [z]
    exact lt_min (by positivity) (div_pos (mul_pos (Real.sqrt_pos.2 (mul_pos hc hv)) hδ)
      (by norm_num))
  have hzweak : z ≤ Real.sqrt (c * v) * δ / 10000 := min_le_right _ _
  have hzsq : z ^ 2 ≤ c * v * δ ^ 2 / 10 ^ 8 := by
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ z)
      (by positivity : 0 ≤ Real.sqrt (c * v) * δ / 10000)).2 hzweak
    rw [div_pow, mul_pow, Real.sq_sqrt (mul_nonneg hc.le hv.le)] at hsq
    norm_num at hsq ⊢
    nlinarith [hsq]
  have hzpi : z ≤ Real.pi / 4 := min_le_left _ _
  let τ := (Real.pi - z) / Real.sqrt v
  have hτpos : 0 < τ := by
    dsimp [τ]
    apply div_pos
    · linarith [Real.pi_pos, hzpi]
    · exact Real.sqrt_pos.2 hv
  have hτpole : τ < Real.pi / Real.sqrt v := by
    dsimp [τ]
    rw [div_lt_div_iff₀ (Real.sqrt_pos.2 hv) (Real.sqrt_pos.2 hv)]
    exact mul_lt_mul_of_pos_right (by linarith [hzpos]) (Real.sqrt_pos.2 hv)
  have harg : Real.sqrt v * τ = Real.pi - z := by
    dsimp [τ]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hv)]
  have hsin : 0 < Real.sin z :=
    Real.sin_pos_of_mem_Ioo ⟨hzpos, by linarith [hzpi, Real.pi_pos]⟩
  have hcos : 0 < Real.cos z := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [hzpi, Real.pi_pos]
  have hU : profileU v τ = Real.sin z / Real.sqrt v := by
    rw [profileU, if_pos hv, harg, Real.sin_pi_sub]
  have hderiv : deriv (profileU v) τ = -Real.cos z := by
    have hchain : deriv (fun t : ℝ => Real.sin (Real.sqrt v * t)) τ =
        Real.cos (Real.sqrt v * τ) * Real.sqrt v := by
      rw [deriv_sin (by fun_prop : DifferentiableAt ℝ
        (fun t : ℝ => Real.sqrt v * t) τ)]
      simp
    have hd : deriv (fun t : ℝ => Real.sin (Real.sqrt v * t) / Real.sqrt v) τ =
        Real.cos (Real.sqrt v * τ) := by
      change deriv (fun t : ℝ => Real.sin (Real.sqrt v * t) * (Real.sqrt v)⁻¹) τ = _
      rw [deriv_mul_const_field, hchain]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hv)]
    have hfun : profileU v = (fun t : ℝ => Real.sin (Real.sqrt v * t) / Real.sqrt v) := by
      funext t
      rw [profileU, if_pos hv]
    rw [hfun, hd, harg, Real.cos_pi_sub]
  have hB : profileB v τ < 0 := by
    rw [profileB, hU, hderiv]
    have hsden : 0 < Real.sin z / Real.sqrt v := div_pos hsin (Real.sqrt_pos.2 hv)
    have hnum : 2 * -Real.cos z < 0 := by nlinarith [hcos]
    exact div_neg_of_neg_of_pos hnum hsden
  have hA : profileA v τ ≥ 4 * v / z ^ 2 := by
    rw [profileA, hU]
    have hsinle : Real.sin z ≤ z := Real.sin_le hzpos.le
    have hsqs : Real.sin z ^ 2 ≤ z ^ 2 := by nlinarith [hsin, hzpos, hsinle]
    have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ 4 * v)
      (sq_pos_of_pos hsin) hsqs
    have hrewrite : 4 / (Real.sin z / Real.sqrt v) ^ 2 = 4 * v / Real.sin z ^ 2 := by
      field_simp [ne_of_gt hsin, ne_of_gt (Real.sqrt_pos.2 hv)]
      exact Real.sq_sqrt hv.le
    rw [hrewrite]
    exact hdiv
  refine ⟨τ, z, hτpos, hτpole, hzpos, hzpi, hB, hA, ?_⟩
  simpa [c] using hzsq

private theorem energy_bandMoment_map_integral (ν : Measure ℝ) [IsFiniteMeasure ν]
    (f : ℝ → ℕ) (hf : Measurable f) (I : Finset ℕ) :
    bandMoment (ν.map f) I =
      ∫ x, (if f x ∈ I then (2 : ℝ) ^ (f x) else 0) ∂ν := by
  classical
  let g : ℕ → ℝ → ℝ := fun r =>
    Set.indicator (f ⁻¹' {r}) (fun _ => (2 : ℝ) ^ r)
  have hset (r : ℕ) : MeasurableSet (f ⁻¹' {r}) :=
    hf (measurableSet_singleton r)
  have hmap (r : ℕ) : (ν.map f).real {r} = ν.real (f ⁻¹' {r}) := by
    rw [measureReal_def, measureReal_def,
      Measure.map_apply hf (measurableSet_singleton r)]
  have hterm (r : ℕ) :
      (2 : ℝ) ^ r * (ν.map f).real {r} = ∫ x, g r x ∂ν := by
    rw [hmap r, integral_indicator_const _ (hset r), smul_eq_mul]
    ring
  have hgint (r : ℕ) : Integrable (g r) ν := by
    change Integrable (Set.indicator (f ⁻¹' {r}) (fun _ : ℝ => (2 : ℝ) ^ r)) ν
    have hconst : Integrable (fun _ : ℝ => (2 : ℝ) ^ r) ν :=
      (integrable_const_iff_isFiniteMeasure (by positivity)).2 inferInstance
    exact hconst.indicator (hset r)
  calc
    bandMoment (ν.map f) I = ∑ r ∈ I, ∫ x, g r x ∂ν := by
      unfold bandMoment
      apply Finset.sum_congr rfl
      intro r hr
      exact hterm r
    _ = ∫ x, ∑ r ∈ I, g r x ∂ν := by
      symm
      exact integral_finsetSum I (fun r hr => hgint r)
    _ = ∫ x, (if f x ∈ I then (2 : ℝ) ^ (f x) else 0) ∂ν := by
      congr 1
      funext x
      dsimp [g]
      simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
      simp [eq_comm]

noncomputable def energyBandCutoff (δ x : ℝ) : ℝ :=
  max 0 (min 1 (min ((100 / δ) * (x - 4 * δ / 5))
    ((100 / δ) * (9 * δ / 10 - x))))

private noncomputable def energyBandCutoffBCF (δ : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨energyBandCutoff δ, by
      change Continuous (fun x => max 0 (min 1 (min ((100 / δ) * (x - 4 * δ / 5))
        ((100 / δ) * (9 * δ / 10 - x)))))
      fun_prop⟩ 1 (by
      intro x y
      change |energyBandCutoff δ x - energyBandCutoff δ y| ≤ 1
      have hx : 0 ≤ energyBandCutoff δ x ∧ energyBandCutoff δ x ≤ 1 := by
        constructor
        · exact le_max_left _ _
        · exact max_le_iff.mpr ⟨by norm_num, min_le_left _ _⟩
      have hy : 0 ≤ energyBandCutoff δ y ∧ energyBandCutoff δ y ≤ 1 := by
        constructor
        · exact le_max_left _ _
        · exact max_le_iff.mpr ⟨by norm_num, min_le_left _ _⟩
      rw [abs_le]
      constructor <;> linarith)

private theorem energyBandCutoff_range (δ x : ℝ) :
    0 ≤ energyBandCutoff δ x ∧ energyBandCutoff δ x ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le_iff.mpr ⟨by norm_num, min_le_left _ _⟩

private theorem energyBandCutoff_one {δ x : ℝ} (hδ : 0 < δ)
    (hlo : 81 * δ / 100 ≤ x) (hhi : x ≤ 89 * δ / 100) :
    energyBandCutoff δ x = 1 := by
  have hleft : 1 ≤ (100 / δ) * (x - 4 * δ / 5) := by
    rw [div_eq_mul_inv]
    field_simp [ne_of_gt hδ]
    nlinarith
  have hright : 1 ≤ (100 / δ) * (9 * δ / 10 - x) := by
    rw [div_eq_mul_inv]
    field_simp [ne_of_gt hδ]
    nlinarith
  simp [energyBandCutoff, hleft, hright]

private theorem energyBandCutoff_zero {δ x : ℝ} (hδ : 0 < δ)
    (hx : x ∉ Set.Icc (4 * δ / 5) (9 * δ / 10)) : energyBandCutoff δ x = 0 := by
  by_cases hleft : x < 4 * δ / 5
  · have hcoeff : 0 < 100 / δ := div_pos (by norm_num) hδ
    have hdiff : x - 4 * δ / 5 < 0 := by linarith
    have hval : (100 / δ) * (x - 4 * δ / 5) < 0 := mul_neg_of_pos_of_neg hcoeff hdiff
    simp [energyBandCutoff, le_of_lt hleft, hval.le]
  · have hright : 9 * δ / 10 < x := by
      by_contra h
      exact hx ⟨le_of_not_gt hleft, le_of_not_gt h⟩
    have hcoeff : 0 < 100 / δ := div_pos (by norm_num) hδ
    have hdiff : 9 * δ / 10 - x < 0 := by linarith
    have hval : (100 / δ) * (9 * δ / 10 - x) < 0 := mul_neg_of_pos_of_neg hcoeff hdiff
    simp [energyBandCutoff, hval.le]

private theorem energy_integrable_cutoff_bcf_of_finite {ν : Measure ℝ}
    [IsFiniteMeasure ν] (δ : ℝ) :
    Integrable (fun x => energyBandCutoffBCF δ x) ν := by
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) ν :=
    (integrable_const_iff_isFiniteMeasure (by norm_num)).2 inferInstance
  apply hconst.mono' (energyBandCutoffBCF δ).continuous.measurable.aestronglyMeasurable
  filter_upwards [] with x
  have hx := energyBandCutoff_range δ x
  rw [Real.norm_eq_abs]
  change |energyBandCutoff δ x| ≤ 1
  exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩

private theorem energy_rho_floor_small {B τ C : ℝ} (hB : 2 < B)
    (hτ : 0 < τ) (hC : 0 < C) :
    ∀ᶠ N : ℝ in atTop, (N + 1) * (2 / B) ^ ⌊N * τ⌋₊ < C := by
  let ρ := 2 / B
  have hρ : 0 < ρ ∧ ρ < 1 := by
    dsimp [ρ]
    constructor
    · positivity
    · exact (div_lt_one (by linarith : (0 : ℝ) < B)).2 (by linarith)
  have hlogρ : Real.log ρ < 0 := Real.log_neg hρ.1 hρ.2
  let c := τ * (-Real.log ρ)
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos hτ (neg_pos.mpr hlogρ)
  have hExp : Tendsto (fun N : ℝ => N * Real.exp (-c * N)) atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc
    simpa [Real.rpow_one] using h
  let K := 2 / ρ
  have hK : 0 < K := by dsimp [K]; positivity
  have hsmall : ∀ᶠ N : ℝ in atTop, K * (N * Real.exp (-c * N)) < C := by
    have he := hExp.eventually (Iio_mem_nhds (div_pos hC hK))
    filter_upwards [he] with N hN
    have hmul := mul_lt_mul_of_pos_left hN hK
    have hcancel : K * (C / K) = C := by field_simp
    rw [hcancel] at hmul
    exact hmul
  filter_upwards [eventually_gt_atTop (1 : ℝ), hsmall] with N hN hsmallN
  let n := ⌊N * τ⌋₊
  have hfloor : N * τ - 1 < (n : ℝ) := by
    have h := Nat.lt_floor_add_one (N * τ)
    change N * τ < (n : ℝ) + 1 at h
    linarith
  have hpow : ρ ^ n = Real.exp (Real.log ρ * (n : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hρ.1]
  have hpowle : ρ ^ n ≤ ρ⁻¹ * Real.exp (-c * N) := by
    rw [hpow]
    have hexp := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left (le_of_lt hfloor) hlogρ.le)
    have hrew : Real.log ρ * (N * τ - 1) = (-c * N) + (-Real.log ρ) := by
      dsimp [c]
      ring
    calc
      Real.exp (Real.log ρ * (n : ℝ)) ≤
          Real.exp (Real.log ρ * (N * τ - 1)) := hexp
      _ = Real.exp (-c * N) * ρ⁻¹ := by
        rw [hrew, Real.exp_add, Real.exp_neg, Real.exp_log hρ.1]
      _ = ρ⁻¹ * Real.exp (-c * N) := by ring
  have hNpos : 0 < N := by linarith
  have hsum : N + 1 ≤ 2 * N := by linarith
  have hupper : (N + 1) * ρ ^ n ≤ K * (N * Real.exp (-c * N)) := by
    calc
      (N + 1) * ρ ^ n ≤ (2 * N) * (ρ⁻¹ * Real.exp (-c * N)) :=
        mul_le_mul hsum hpowle (by positivity) (by positivity)
      _ = K * (N * Real.exp (-c * N)) := by
        dsimp [K]
        ring
  simpa [ρ, n] using lt_of_le_of_lt hupper hsmallN

private theorem energy_floor_log_small {B τ δ : ℝ} (hB : 2 < B)
    (hτ : 0 < τ) (hδ : 0 < δ) :
    ∀ᶠ N : ℝ in atTop,
      (N * δ + 1) * (-Real.log (floorSeq B ⌊N * τ⌋₊)) / Real.log B < 1 := by
  have ha : 0 < Real.log B := Real.log_pos (by linarith)
  have hb1 : 0 < floorSeq B 1 := floorSeq_one_pos hB
  let C := Real.log B * floorSeq B 1 / (δ + 1)
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos (mul_pos ha hb1) (by linarith)
  have hrho := energy_rho_floor_small hB hτ hC
  have hlarge : ∀ᶠ N : ℝ in atTop, 1 / τ < N := eventually_gt_atTop (1 / τ)
  filter_upwards [hrho, hlarge, eventually_gt_atTop (1 : ℝ)] with N hsmall hlargeN hN
  let n := ⌊N * τ⌋₊
  have hn : 1 ≤ n := by
    have h := (div_lt_iff₀ hτ).1 hlargeN
    have h' : ((1 : ℕ) : ℝ) ≤ N * τ := by exact_mod_cast le_of_lt h
    have h'' : (1 : ℕ) ≤ ⌊N * τ⌋₊ := Nat.le_floor h'
    simpa [n] using h''
  have hbpos : 0 < floorSeq B n :=
    (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)
  have hble : floorSeq B 1 ≤ floorSeq B n := floorSeq_monotone hB hn
  have hdefect : 1 - floorSeq B n ≤ (2 / B) ^ n := one_sub_floorSeq_le hB n
  have hloginv := Real.log_le_sub_one_of_pos (inv_pos.mpr hbpos)
  rw [Real.log_inv] at hloginv
  have hlogbound : -Real.log (floorSeq B n) ≤
      (1 - floorSeq B n) / floorSeq B n := by
    convert hloginv using 1 <;> field_simp
  have hd : -Real.log (floorSeq B n) ≤ (2 / B) ^ n / floorSeq B 1 := by
    calc
      -Real.log (floorSeq B n) ≤ (1 - floorSeq B n) / floorSeq B n := hlogbound
      _ ≤ (2 / B) ^ n / floorSeq B n :=
        div_le_div_of_nonneg_right hdefect hbpos.le
      _ ≤ (2 / B) ^ n / floorSeq B 1 := by
        apply (div_le_div_iff₀ hbpos hb1).2
        exact mul_le_mul_of_nonneg_left hble (by positivity)
  have hNpos : 0 < N := by linarith
  have hfacpos : 0 < N * δ + 1 := by positivity
  have hfac : N * δ + 1 ≤ (δ + 1) * (N + 1) := by nlinarith
  have hprod : (N * δ + 1) * (2 / B) ^ n < Real.log B * floorSeq B 1 := by
    calc
      (N * δ + 1) * (2 / B) ^ n ≤
          (δ + 1) * ((N + 1) * (2 / B) ^ n) := by
            calc
              (N * δ + 1) * (2 / B) ^ n ≤
                  ((δ + 1) * (N + 1)) * (2 / B) ^ n :=
                    mul_le_mul_of_nonneg_right hfac (by positivity)
              _ = (δ + 1) * ((N + 1) * (2 / B) ^ n) := by ring
      _ < (δ + 1) * C := by
        exact mul_lt_mul_of_pos_left hsmall (by linarith)
      _ = Real.log B * floorSeq B 1 := by dsimp [C]; field_simp
  have hprod' : (N * δ + 1) * (-Real.log (floorSeq B n)) < Real.log B := by
    have hmul := mul_le_mul_of_nonneg_left hd (le_of_lt hfacpos)
    have hlt : (N * δ + 1) * ((2 / B) ^ n / floorSeq B 1) < Real.log B := by
      have hh : ((N * δ + 1) * (2 / B) ^ n) / floorSeq B 1 < Real.log B :=
        (div_lt_iff₀ hb1).2 hprod
      simpa [mul_div_assoc] using hh
    exact lt_of_le_of_lt hmul hlt
  have hdiv := (div_lt_one ha).2 hprod'
  simpa [n] using hdiv

private theorem energy_profile_cutoff_integral_large {v τ δ s z : ℝ}
    (hv : 0 < v) (hδ : 0 < δ) (hs : 0 < s) (hz : 0 < z)
    (hA : 4 * v / z ^ 2 ≤ profileA v τ)
    (hzsq : z ^ 2 ≤ Real.exp (-1) * v * δ ^ 2 / 10 ^ 8)
    (hshift : s + profileB v τ = 1 / (2 * δ))
    (hfin : IsFiniteMeasure (weightedMeasure (profileMeasure v τ) s)) :
    10 ^ 6 / δ <
      ∫ x, energyBandCutoffBCF δ x ∂weightedMeasure (profileMeasure v τ) s := by
  let f := energyBandCutoffBCF δ
  let μ₀ := volume.restrict (Set.Ici (0 : ℝ))
  let J : Set ℝ := Set.Icc (81 * δ / 100) (89 * δ / 100)
  let G : ℝ → ℝ := fun x => Real.exp (-(s * x)) * f x * profileDensity v τ x
  have hApos : 0 < profileA v τ := by
    have h0 : 0 < 4 * v / z ^ 2 := div_pos (by positivity) (sq_pos_of_pos hz)
    linarith
  have hdens : ∀ x, 0 ≤ profileDensity v τ x := by
    intro x
    unfold profileDensity
    positivity
  have hfint : Integrable (fun x => f x)
      (weightedMeasure (profileMeasure v τ) s) := by
    letI : IsFiniteMeasure (weightedMeasure (profileMeasure v τ) s) := hfin
    exact energy_integrable_cutoff_bcf_of_finite δ
  have houterint : Integrable
      (fun x => Real.exp (-(s * x)) * f x) (profileMeasure v τ) := by
    have hi := (integrable_withDensity_iff (by fun_prop [profileDensity]) (by simp)
      (g := fun x => f x)).1 hfint
    simpa [weightedMeasure, ENNReal.toReal_ofReal (Real.exp_nonneg _), mul_comm] using hi
  have hGint : Integrable G μ₀ := by
    have hi := (integrable_withDensity_iff (by fun_prop [profileDensity]) (by simp)
      (g := fun x => Real.exp (-(s * x)) * f x)).1
        (show Integrable (fun x => Real.exp (-(s * x)) * f x) (profileMeasure v τ) from houterint)
    simpa [G, profileMeasure, ENNReal.toReal_ofReal (hdens _), mul_assoc, mul_left_comm,
      mul_comm] using hi
  have houter :
      (∫ x, f x ∂weightedMeasure (profileMeasure v τ) s) =
        ∫ x, Real.exp (-(s * x)) * f x ∂profileMeasure v τ := by
    rw [weightedMeasure, integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
    congr 1
    funext x
    simp [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _), mul_comm]
  have hinner :
      (∫ x, Real.exp (-(s * x)) * f x ∂profileMeasure v τ) = ∫ x, G x ∂μ₀ := by
    rw [profileMeasure, integral_withDensity_eq_integral_toReal_smul
      (by fun_prop [profileDensity]) (by simp)]
    congr 1
    funext x
    simp [G, smul_eq_mul, ENNReal.toReal_ofReal (hdens x), mul_assoc, mul_left_comm,
      mul_comm]
  have hJsubset : J ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    simp only [J, Set.mem_Icc] at hx
    simp only [Set.mem_Ici]
    nlinarith [hδ]
  have hinter : J ∩ Set.Ici (0 : ℝ) = J := Set.inter_eq_left.mpr hJsubset
  have hJfinite : μ₀ J < ⊤ := by
    rw [Measure.restrict_apply measurableSet_Icc, hinter, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hJint : Integrable (J.indicator (fun _ => profileA v τ / 2)) μ₀ := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const hJfinite.ne_top
  have hJmeasure : μ₀.real J = 8 * δ / 100 := by
    rw [measureReal_def, Measure.restrict_apply measurableSet_Icc, hinter,
      Real.volume_Icc]
    have hlen : 0 ≤ 89 * δ / 100 - 81 * δ / 100 := by nlinarith [hδ]
    rw [ENNReal.toReal_ofReal hlen]
    ring
  have hpoint : J.indicator (fun _ => profileA v τ / 2) ≤ᵐ[μ₀] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx₀
    by_cases hxJ : x ∈ J
    · have hx := Set.mem_Icc.mp hxJ
      have hcut : f x = 1 := by
        change energyBandCutoff δ x = 1
        exact energyBandCutoff_one hδ (by nlinarith [hx.1]) (by nlinarith [hx.2])
      have hexp : (1 : ℝ) / 2 ≤ Real.exp (-(x / (2 * δ))) := by
        have harg : x / (2 * δ) ≤ 1 / 2 := by
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * δ)).2
          nlinarith [hx.2]
        have h := Real.add_one_le_exp (-(x / (2 * δ)))
        nlinarith
      have hG : G x = profileA v τ * Real.exp (-(x / (2 * δ))) := by
        calc
          G x = Real.exp (-(s * x)) *
              (profileA v τ * Real.exp (-(profileB v τ * x))) := by
                simp [G, f, hcut, profileDensity]
          _ = profileA v τ *
              (Real.exp (-(s * x)) * Real.exp (-(profileB v τ * x))) := by ring
          _ = profileA v τ * Real.exp (-(s * x) + -(profileB v τ * x)) := by
                rw [← Real.exp_add]
          _ = profileA v τ * Real.exp (-(s + profileB v τ) * x) := by
                congr 2
                ring
          _ = profileA v τ * Real.exp (-(x / (2 * δ))) := by
                rw [hshift]
                congr 2
                ring
      rw [Set.indicator_of_mem hxJ, hG]
      have hh := mul_le_mul_of_nonneg_left hexp hApos.le
      nlinarith
    · simp only [Set.indicator_apply, if_neg hxJ]
      have hfx : 0 ≤ f x := (energyBandCutoff_range δ x).1
      have hEx : 0 < Real.exp (-(s * x)) := Real.exp_pos _
      dsimp [G]
      exact mul_nonneg (mul_nonneg hEx.le hfx) (hdens x)
  have hmono := integral_mono_ae hJint hGint hpoint
  have hJintval :
      (∫ x, J.indicator (fun _ => profileA v τ / 2) x ∂μ₀) =
        profileA v τ * δ / 25 := by
    rw [integral_indicator_const _ measurableSet_Icc, hJmeasure, smul_eq_mul]
    ring
  have hlargeA : 16 * 10 ^ 6 / δ ≤ profileA v τ * δ / 25 := by
    have hc : 0 < Real.exp (-1) := Real.exp_pos _
    have hcle : Real.exp (-1) ≤ 1 := by
      have := Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0)
      simpa using this
    have hden : 0 < Real.exp (-1) * v * δ ^ 2 / 10 ^ 8 := by positivity
    have hzpos' : 0 < z ^ 2 := sq_pos_of_pos hz
    have hratio : 4 * v / (Real.exp (-1) * v * δ ^ 2 / 10 ^ 8) ≤ 4 * v / z ^ 2 := by
      apply (div_le_div_iff₀ hden hzpos').2
      nlinarith [hzsq]
    have hA' : 4 * 10 ^ 8 / (Real.exp (-1) * δ ^ 2) ≤ profileA v τ := by
      have heq : 4 * v / (Real.exp (-1) * v * δ ^ 2 / 10 ^ 8) =
          4 * 10 ^ 8 / (Real.exp (-1) * δ ^ 2) := by
        field_simp [ne_of_gt hc, ne_of_gt hv, ne_of_gt hδ]
      have hh := hratio.trans hA
      rw [heq] at hh
      exact hh
    have hAδ : 4 * 10 ^ 8 ≤ profileA v τ * δ ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hA' (sq_nonneg δ)
      have heq : (4 * 10 ^ 8 / (Real.exp (-1) * δ ^ 2)) * δ ^ 2 =
          4 * 10 ^ 8 / Real.exp (-1) := by
        field_simp [ne_of_gt hc, ne_of_gt hδ]
      rw [heq] at hmul
      have hbig : 4 * 10 ^ 8 ≤ 4 * 10 ^ 8 / Real.exp (-1) := by
        apply (le_div_iff₀ hc).2
        nlinarith [hcle]
      linarith
    apply (div_le_iff₀ hδ).2
    nlinarith [hAδ]
  have hstrict : 10 ^ 6 / δ < 16 * 10 ^ 6 / δ := by
    apply (div_lt_div_iff_of_pos_right hδ).2
    norm_num
  calc
    10 ^ 6 / δ < 16 * 10 ^ 6 / δ := hstrict
    _ ≤ profileA v τ * δ / 25 := hlargeA
    _ = ∫ x, J.indicator (fun _ => profileA v τ / 2) x ∂μ₀ := hJintval.symm
    _ ≤ ∫ x, G x ∂μ₀ := hmono
    _ = ∫ x, f x ∂weightedMeasure (profileMeasure v τ) s := (houter.trans hinner).symm

noncomputable def energySourceBandDensity
    (B N s δ : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  N * (r ^ theta B - 1) *
    (Real.exp (-(s * (Real.log r / (Real.log B * N)))) *
      energyBandCutoff δ (Real.log r / (Real.log B * N)))

private theorem energy_source_test_integral_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {B lam N τ δ s : ℝ} (hB : 2 < B) (hN : 0 < N) :
    (∫ x, energyBandCutoffBCF δ x ∂weightedMeasure (scalingMeasure μ B lam N τ) s) =
      ∫ r, energySourceBandDensity B N s δ ⌊N * τ⌋₊ r ∂
        ((lawR μ B (criticalPoint μ B + lam / N ^ 2) ⌊N * τ⌋₊).restrict (Set.Ici 1)) := by
  let ν := lawR μ B (criticalPoint μ B + lam / N ^ 2) ⌊N * τ⌋₊
  let μr := ν.restrict (Set.Ici (1 : ℝ))
  let T := fun r : ℝ => Real.log r / (Real.log B * N)
  have houter :
      (∫ x, energyBandCutoffBCF δ x ∂weightedMeasure (scalingMeasure μ B lam N τ) s) =
        ∫ x, Real.exp (-(s * x)) * energyBandCutoffBCF δ x ∂scalingMeasure μ B lam N τ := by
    rw [weightedMeasure, integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
    congr 1
    funext x
    simp [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  have hmap :
      (∫ x, Real.exp (-(s * x)) * energyBandCutoffBCF δ x ∂scalingMeasure μ B lam N τ) =
        ∫ r, Real.exp (-(s * T r)) * energyBandCutoffBCF δ (T r) ∂
          (μr.withDensity fun r => ENNReal.ofReal (N * (r ^ theta B - 1))) := by
    simp only [scalingMeasure, rescaledMeasure, scalingField, μr, ν, T]
    rw [integral_map (by fun_prop) (by fun_prop)]
  have hdens :
      (∫ r, Real.exp (-(s * T r)) * energyBandCutoffBCF δ (T r) ∂
          (μr.withDensity fun r => ENNReal.ofReal (N * (r ^ theta B - 1)))) =
        ∫ r, N * (r ^ theta B - 1) *
          (Real.exp (-(s * T r)) * energyBandCutoff δ (T r)) ∂μr := by
    rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
    have hrpow : 1 ≤ r ^ theta B := Real.one_le_rpow hr (theta_pos hB).le
    have hn : 0 ≤ N * (r ^ theta B - 1) := by nlinarith [hrpow]
    simp only [smul_eq_mul, ENNReal.toReal_ofReal hn]
    simp [energyBandCutoffBCF, T, mul_assoc, mul_comm]
  simpa [energySourceBandDensity, μr, T] using houter.trans (hmap.trans hdens)

private theorem energy_bandMoment_restrict_le (ν : Measure ℝ) [IsFiniteMeasure ν]
    (f : ℝ → ℕ) (hf : Measurable f) (I : Finset ℕ) :
    bandMoment ((ν.restrict (Set.Ici (1 : ℝ))).map f) I ≤ bandMoment (ν.map f) I := by
  unfold bandMoment
  apply Finset.sum_le_sum
  intro y hy
  have hmap :
      ((ν.restrict (Set.Ici (1 : ℝ))).map f).real {y} ≤ (ν.map f).real {y} := by
    rw [measureReal_def, measureReal_def,
      Measure.map_apply hf (measurableSet_singleton y),
      Measure.map_apply hf (measurableSet_singleton y), Measure.restrict_apply
        (hf (measurableSet_singleton y))]
    exact measureReal_mono Set.inter_subset_left (by finiteness)
  exact mul_le_mul_of_nonneg_left hmap (by positivity)

private theorem energy_source_density_bound {B N s δ : ℝ} {n : ℕ} {r : ℝ}
    (hB : 2 < B) (hN : 0 < N) (hδ : 0 < δ) (hs : 0 < s) (hr : 1 ≤ r) :
    0 ≤ energySourceBandDensity B N s δ n r ∧
      energySourceBandDensity B N s δ n r ≤ N * r ^ theta B := by
  let x := Real.log r / (Real.log B * N)
  have ha : 0 < Real.log B := Real.log_pos (by linarith)
  have hden : 0 < Real.log B * N := mul_pos ha hN
  have hx : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (Real.log_nonneg hr) hden.le
  have hrpow : 1 ≤ r ^ theta B := Real.one_le_rpow hr (theta_pos hB).le
  have hcut := energyBandCutoff_range δ x
  have hexp0 : 0 < Real.exp (-(s * x)) := Real.exp_pos _
  have hexp1 : Real.exp (-(s * x)) ≤ 1 := by
    calc
      Real.exp (-(s * x)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith [hs, hx])
      _ = 1 := Real.exp_zero
  have hweight0 : 0 ≤ Real.exp (-(s * x)) * energyBandCutoff δ x :=
    mul_nonneg hexp0.le hcut.1
  have hweight1 : Real.exp (-(s * x)) * energyBandCutoff δ x ≤ 1 := by
    calc
      Real.exp (-(s * x)) * energyBandCutoff δ x ≤
          Real.exp (-(s * x)) * 1 := mul_le_mul_of_nonneg_left hcut.2 hexp0.le
      _ ≤ 1 := by simpa using hexp1
  have hcore0 : 0 ≤ r ^ theta B - 1 := by linarith
  have hcore1 : r ^ theta B - 1 ≤ r ^ theta B := by linarith
  have hmul0 : 0 ≤ (r ^ theta B - 1) *
      (Real.exp (-(s * x)) * energyBandCutoff δ x) := mul_nonneg hcore0 hweight0
  have hmul1 : (r ^ theta B - 1) *
      (Real.exp (-(s * x)) * energyBandCutoff δ x) ≤ r ^ theta B := by
    calc
      _ ≤ (r ^ theta B - 1) * 1 := mul_le_mul_of_nonneg_left hweight1 hcore0
      _ = r ^ theta B - 1 := by ring
      _ ≤ r ^ theta B := hcore1
  constructor
  · dsimp [energySourceBandDensity, x]
    exact mul_nonneg (mul_nonneg hN.le hcore0) hweight0
  · dsimp [energySourceBandDensity, x]
    calc
      N * (r ^ theta B - 1) *
          (Real.exp (-(s * (Real.log r / (Real.log B * N)))) *
            energyBandCutoff δ (Real.log r / (Real.log B * N))) =
          N * ((r ^ theta B - 1) *
            (Real.exp (-(s * (Real.log r / (Real.log B * N)))) *
              energyBandCutoff δ (Real.log r / (Real.log B * N)))) := by ring
      _ ≤ N * r ^ theta B := mul_le_mul_of_nonneg_left hmul1 hN.le
      _ = N * r ^ theta B := rfl

set_option maxHeartbeats 400000 in
theorem energy_source_integrand_le_band {B N s δ : ℝ} {n L : ℕ} {r : ℝ}
    (hB : 2 < B) (hN : 0 < N) (hδ : 0 < δ) (hs : 0 < s)
    (hn : 1 ≤ n) (hL : 10 ^ 4 ≤ L) (hLdef : L = ⌊N * δ⌋₊)
    (hsmall : (N * δ + 1) * (-Real.log (floorSeq B n)) / Real.log B < 1)
    (hr : 1 ≤ r) (hcut : 0 < energyBandCutoff δ (Real.log r / (Real.log B * N))) :
    energySourceBandDensity B N s δ n r ≤
      8 * N * (if ⌊Real.log (r / floorSeq B n) / Real.log (B / floorSeq B n)⌋₊ ∈
        upperBand L then (2 : ℝ) ^
          ⌊Real.log (r / floorSeq B n) / Real.log (B / floorSeq B n)⌋₊ else 0) := by
  let a := Real.log B
  let b := floorSeq B n
  let d := -Real.log b
  let q := Real.log (r / b) / Real.log (B / b)
  let y := ⌊q⌋₊
  let x := Real.log r / (a * N)
  have ha : 0 < a := by dsimp [a]; exact Real.log_pos (by linarith)
  have hbpos : 0 < b := by
    dsimp [b]
    exact (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)
  have hb1 : b < 1 := by dsimp [b]; exact floorSeq_lt_one hB n
  have hdpos : 0 < d := by
    dsimp [d]
    exact neg_pos.mpr (Real.log_neg hbpos hb1)
  have hlogb : Real.log b = -d := by dsimp [d]; ring
  have han : Real.log (B / b) = a + d := by
    rw [Real.log_div (by linarith : B ≠ 0) hbpos.ne']
    rw [hlogb]
    dsimp [a]
    ring
  have hnum : Real.log (r / b) = Real.log r + d := by
    rw [Real.log_div (by linarith : r ≠ 0) hbpos.ne']
    rw [hlogb]
    ring
  have hdenpos : 0 < a + d := by linarith
  have hNδ : (10 : ℝ) ^ 4 ≤ N * δ := by
    have hLfloor : (L : ℝ) ≤ N * δ := by
      rw [hLdef]
      exact Nat.floor_le (mul_nonneg hN.le hδ.le)
    have hLcast : (10 : ℝ) ^ 4 ≤ (L : ℝ) := by exact_mod_cast hL
    exact hLcast.trans hLfloor
  have hprod : (N * δ + 1) * d < a := by
    have h := (div_lt_one ha).1 hsmall
    simpa [d, mul_comm, mul_left_comm, mul_assoc] using h
  have hda : d / a < 1 / 20 := by
    apply (div_lt_iff₀ ha).2
    have hfac : 0 ≤ N * δ - 19 := by nlinarith [hNδ]
    have hmul := mul_nonneg hfac hdpos.le
    nlinarith [hprod, hmul]
  have hdenUpper : a + d ≤ (21 / 20 : ℝ) * a := by
    have h := (div_lt_iff₀ ha).1 hda
    linarith
  have hcutSupport : x ∈ Set.Icc (4 * δ / 5) (9 * δ / 10) := by
    by_contra hnot
    have hz := energyBandCutoff_zero hδ hnot
    exact (ne_of_gt hcut) (by simpa [x, a] using hz)
  have hxlo : (4 * δ / 5) * (a * N) ≤ Real.log r := by
    have h := (le_div_iff₀ (mul_pos ha hN)).1 hcutSupport.1
    nlinarith
  have hxhi : Real.log r ≤ (9 * δ / 10) * (a * N) := by
    have h := (div_le_iff₀ (mul_pos ha hN)).1 hcutSupport.2
    nlinarith
  have hlogr0 : 0 ≤ Real.log r := Real.log_nonneg hr
  have hnum0 : 0 ≤ Real.log r + d := by linarith
  have hq0 : 0 ≤ q := by
    dsimp [q]
    rw [hnum, han]
    exact div_nonneg hnum0 hdenpos.le
  have hqle : q ≤ (9 / 10 : ℝ) * (N * δ) + 1 / 20 := by
    have hqle' : q ≤ (Real.log r + d) / a := by
      dsimp [q]
      rw [hnum, han]
      apply (div_le_div_iff₀ hdenpos ha).2
      nlinarith [mul_nonneg hnum0 hdpos.le]
    have hlogdiv : Real.log r / a ≤ (9 / 10 : ℝ) * (N * δ) := by
      apply (div_le_iff₀ ha).2
      nlinarith [hxhi]
    have hsplit : (Real.log r + d) / a = Real.log r / a + d / a := by
      field_simp [ne_of_gt ha]
    rw [hsplit] at hqle'
    nlinarith [hlogdiv, hda]
  have hqlo : (16 / 21 : ℝ) * (N * δ) ≤ q := by
    dsimp [q]
    rw [hnum, han]
    apply (le_div_iff₀ hdenpos).2
    have hm := mul_le_mul_of_nonneg_left hdenUpper
      (show 0 ≤ (16 / 21 : ℝ) * (N * δ) by positivity)
    nlinarith [hxlo, hdpos]
  have hLfloor : (L : ℝ) ≤ N * δ := by
    rw [hLdef]
    exact Nat.floor_le (mul_nonneg hN.le hδ.le)
  have hLfloorUpper : N * δ < (L : ℝ) + 1 := by
    rw [hLdef]
    exact Nat.lt_floor_add_one (N * δ)
  have hLgap : N * δ - 1 < (L : ℝ) := by linarith [hLfloorUpper]
  have hyfloor : q < (y : ℝ) + 1 := by
    dsimp [y]
    exact Nat.lt_floor_add_one q
  have hylo : (3 / 4 : ℝ) * (L : ℝ) ≤ (y : ℝ) := by
    have hgap : (3 / 4 : ℝ) * (N * δ) ≤ (16 / 21 : ℝ) * (N * δ) - 1 := by
      nlinarith [hNδ]
    linarith [hqlo, hyfloor, hLfloor]
  have hyhiq : q < (L : ℝ) + 1 := by
    have hqLt : q < N * δ := by nlinarith [hqle, hNδ]
    exact hqLt.trans hLfloorUpper
  have hyhi : y ≤ L := by
    have hyLt : y < L + 1 := by
      have hcast : (q : ℝ) < (L : ℝ) + 1 := hyhiq
      exact (Nat.floor_lt hq0).2 (by exact_mod_cast hcast)
    omega
  have hyceil : ⌈(3 * (L : ℝ)) / 4⌉₊ ≤ y := by
    apply Nat.ceil_le.2
    nlinarith [hylo]
  have hyband : y ∈ upperBand L := by
    simp [upperBand, hyceil, hyhi]
  have hthetaComp : theta B * Real.log r ≤ q * Real.log 2 + Real.log 2 := by
    have hqeq : q * (a + d) = Real.log r + d := by
      dsimp [q]
      rw [hnum, han]
      field_simp [ne_of_gt hdenpos]
    have hbase : (Real.log 2 / a) * (Real.log r + d) =
        q * Real.log 2 + q * Real.log 2 * (d / a) := by
      rw [← hqeq]
      field_simp [ne_of_gt ha]
      <;> ring
    have hsmallQ : q * (d / a) < 1 := by
      have hsmall' : (N * δ + 1) * (d / a) < 1 := by
        have h'' : ((N * δ + 1) * d) / a < 1 := (div_lt_one ha).2 hprod
        simpa [mul_div_assoc] using h''
      have hqfac : q ≤ N * δ + 1 := by nlinarith [hqle, hNδ]
      have hm := mul_le_mul_of_nonneg_right hqfac (div_nonneg hdpos.le ha.le)
      exact lt_of_le_of_lt hm hsmall'
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogrle : Real.log r ≤ Real.log r + d := by linarith
    have hleft : (Real.log 2 / a) * Real.log r ≤
        (Real.log 2 / a) * (Real.log r + d) :=
      mul_le_mul_of_nonneg_left hlogrle (div_nonneg hlog2.le ha.le)
    have hsmalllog : q * Real.log 2 * (d / a) ≤ Real.log 2 := by
      have := mul_le_mul_of_nonneg_left (le_of_lt hsmallQ) hlog2.le
      nlinarith [this]
    rw [theta]
    calc
      (Real.log 2 / a) * Real.log r ≤
          (Real.log 2 / a) * (Real.log r + d) := hleft
      _ = q * Real.log 2 + q * Real.log 2 * (d / a) := hbase
      _ ≤ q * Real.log 2 + Real.log 2 := by nlinarith [hsmalllog]
  have hfactor : r ^ theta B ≤ 8 * (2 : ℝ) ^ y := by
    have hlogfactor : Real.log (r ^ theta B) ≤ Real.log (8 * (2 : ℝ) ^ y) := by
      rw [Real.log_rpow (by linarith : 0 < r),
        show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num,
        Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hqlog : q * Real.log 2 + Real.log 2 ≤
          (y : ℝ) * Real.log 2 + 2 * Real.log 2 := by
        nlinarith [hyfloor, hlog2]
      have hqbound : q * Real.log 2 + Real.log 2 ≤
          3 * Real.log 2 + (y : ℝ) * Real.log 2 := by
        calc
          _ ≤ (y : ℝ) * Real.log 2 + 2 * Real.log 2 := hqlog
          _ ≤ 3 * Real.log 2 + (y : ℝ) * Real.log 2 := by nlinarith [hlog2]
      simpa [add_comm, add_left_comm, add_assoc] using hthetaComp.trans hqbound
    have hexp := Real.exp_le_exp.mpr hlogfactor
    rw [Real.exp_log (Real.rpow_pos_of_pos (by linarith : 0 < r) (theta B)),
      Real.exp_log (by positivity : 0 < 8 * (2 : ℝ) ^ y)] at hexp
    exact hexp
  rw [ite_eq_left hyband]
  calc
    _ ≤ N * r ^ theta B := (energy_source_density_bound hB hN hδ hs hr).2
    _ ≤ N * (8 * (2 : ℝ) ^ y) := mul_le_mul_of_nonneg_left hfactor hN.le
    _ = 8 * N * (2 : ℝ) ^ y := by ring

-- First compare the weighted test integral and the band moment for an
-- arbitrary source law.
set_option maxHeartbeats 400000 in
private theorem energy_source_integral_le_band (ν : Measure ℝ) [IsFiniteMeasure ν]
    {B N s δ : ℝ} {n L : ℕ} (hB : 2 < B) (hN : 0 < N)
    (hδ : 0 < δ) (hs : 0 < s) (hn : 1 ≤ n) (hL : 10 ^ 4 ≤ L)
    (hLdef : L = ⌊N * δ⌋₊)
    (hsmall : (N * δ + 1) * (-Real.log (floorSeq B n)) / Real.log B < 1)
    (hpowInt : Integrable (fun r => r ^ theta B) ν) :
    (∫ r, energySourceBandDensity B N s δ n r ∂(ν.restrict (Set.Ici 1))) ≤
      8 * N * bandMoment (ν.map fun r =>
        ⌊Real.log (r / floorSeq B n) / Real.log (B / floorSeq B n)⌋₊)
        (upperBand L) := by
  let μr := ν.restrict (Set.Ici (1 : ℝ))
  let fcoord : ℝ → ℕ := fun r =>
    ⌊Real.log (r / floorSeq B n) / Real.log (B / floorSeq B n)⌋₊
  let R : ℝ → ℝ := fun r =>
    8 * N * (if fcoord r ∈ upperBand L then (2 : ℝ) ^ (fcoord r) else 0)
  let testF : ℝ → ℝ := fun r => energySourceBandDensity B N s δ n r
  have hdomInt : Integrable (fun r => N * r ^ theta B) μr :=
    (hpowInt.restrict (s := Set.Ici (1 : ℝ))).const_mul N
  have htestMeas : Measurable testF := by
    have hxmeas : Measurable (fun r : ℝ => Real.log r / (Real.log B * N)) := by
      fun_prop
    have hcutmeas : Measurable (fun r : ℝ =>
        energyBandCutoff δ (Real.log r / (Real.log B * N))) := by
      change Measurable (fun r => energyBandCutoffBCF δ
        (Real.log r / (Real.log B * N)))
      exact (energyBandCutoffBCF δ).continuous.measurable.comp hxmeas
    change Measurable (fun r => energySourceBandDensity B N s δ n r)
    dsimp [energySourceBandDensity]
    fun_prop
  have htestInt : Integrable testF μr := by
    apply hdomInt.mono' htestMeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
    have hh := energy_source_density_bound (n := n) hB hN hδ hs hr
    change ‖energySourceBandDensity B N s δ n r‖ ≤ N * r ^ theta B
    rw [Real.norm_of_nonneg hh.1]
    exact hh.2
  have hfcoord : Measurable fcoord := by
    change Measurable (fun r : ℝ =>
      ⌊Real.log (r / floorSeq B n) / Real.log (B / floorSeq B n)⌋₊)
    fun_prop
  have hRmeas : Measurable R := by
    have hset : MeasurableSet {r : ℝ | fcoord r ∈ upperBand L} :=
      hfcoord (upperBand L).measurableSet
    have hpw : Measurable (fun r : ℝ => (2 : ℝ) ^ fcoord r) := by fun_prop
    change Measurable (fun r : ℝ =>
      8 * N * (if fcoord r ∈ upperBand L then (2 : ℝ) ^ (fcoord r) else 0))
    exact measurable_const.mul (Measurable.ite hset hpw measurable_const)
  have hRbound : ∀ r, |R r| ≤ 8 * N * (2 : ℝ) ^ L := by
    intro r
    by_cases hrmem : fcoord r ∈ upperBand L
    · have hrmemIcc : fcoord r ∈ Finset.Icc ⌈(3 * L : ℝ) / 4⌉₊ L := by
        change fcoord r ∈ upperBand L
        exact hrmem
      have hy : fcoord r ≤ L := (Finset.mem_Icc.mp hrmemIcc).2
      have hpow : (2 : ℝ) ^ fcoord r ≤ (2 : ℝ) ^ L := by gcongr <;> norm_num
      have hRpos : 0 ≤ R r := by dsimp [R]; simp [hrmem]; positivity
      have hcoef : 0 ≤ 8 * N := by positivity
      rw [abs_of_nonneg hRpos]
      dsimp [R]
      rw [ite_eq_left hrmem]
      exact mul_le_mul_of_nonneg_left hpow hcoef
    · simp [R, hrmem]
      positivity
  have hRInt : Integrable R μr := by
    have hconst : Integrable (fun _ : ℝ => 8 * N * (2 : ℝ) ^ L) μr := by
      apply (integrable_const_iff_isFiniteMeasure (by positivity)).2 inferInstance
    apply hconst.mono' hRmeas.aestronglyMeasurable
    filter_upwards [] with r
    rw [Real.norm_eq_abs]
    exact hRbound r
  have hpoint : testF ≤ᵐ[μr] R := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
    have hcut0 := (energyBandCutoff_range δ
      (Real.log r / (Real.log B * N))).1
    by_cases hcutpos : 0 < energyBandCutoff δ (Real.log r / (Real.log B * N))
    · have hh := energy_source_integrand_le_band hB hN hδ hs hn hL hLdef
        hsmall hr hcutpos
      simpa [R, testF, fcoord] using hh
    · have hz : energyBandCutoff δ (Real.log r / (Real.log B * N)) = 0 :=
        le_antisymm (le_of_not_gt hcutpos) hcut0
      simp [R, testF, energySourceBandDensity, fcoord, hz]
      positivity
  have htestR :
      (∫ r, testF r ∂μr) ≤ ∫ r, R r ∂μr := integral_mono_ae htestInt hRInt hpoint
  have hRintegral :
      (∫ r, R r ∂μr) = 8 * N * bandMoment (μr.map fcoord) (upperBand L) := by
    dsimp [R]
    rw [integral_const_mul,
      ← energy_bandMoment_map_integral μr fcoord hfcoord (upperBand L)]
  have hrestrictBand := energy_bandMoment_restrict_le ν fcoord hfcoord (upperBand L)
  calc
    _ ≤ ∫ r, R r ∂μr := htestR
    _ = 8 * N * bandMoment (μr.map fcoord) (upperBand L) := hRintegral
    _ ≤ 8 * N * bandMoment (ν.map fcoord) (upperBand L) :=
      mul_le_mul_of_nonneg_left hrestrictBand (by positivity)

-- The weighted weak limit gives a quantitative hard-band moment on a short
-- interval strictly below the profile pole.
set_option maxHeartbeats 400000 in
private theorem energy_band_growth_of_continuation {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hpos : ∀ᵐ w ∂μ, 0 < w)
    (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ γ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n)
      (criticalPoint μ B) / tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hγ : γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃)) {lam : ℝ} (hlam : 0 < lam)
    {ε : ℝ} (hε : 0 < ε)
    (hCont : ∀ {lam : ℝ}, 0 < lam → ∀ {I : Set ℝ}, IsCompact I →
      (∀ t ∈ I, IsPrePoleTime (γ * lam) t) → ∀ {s : ℝ}, 0 < s →
      0 < s + sInf (profileB (γ * lam) '' I) →
      TendstoUniformlyOn (fun N t => scaledTransform μ B lam N t s)
          (fun t => profileTransform (γ * lam) t s) atTop I ∧
        ∀ t ∈ I, WeakConvergence
          (fun N => weightedMeasure (scalingMeasure μ B lam N t) s) atTop
          (weightedMeasure (profileMeasure (γ * lam) t) s)) :
    ∃ τ δ : ℝ, 0 < τ ∧ 0 < δ ∧
      τ + 2 * δ ≤ Real.pi / Real.sqrt (γ * lam) + ε / (2 * Real.log 2) ∧
      ∀ᶠ N : ℝ in atTop,
        0 < N ∧ 1 ≤ ⌊N * τ⌋₊ ∧ 10 ^ 4 ≤ ⌊N * δ⌋₊ ∧
          (10 : ℝ) ^ 4 ≤ (⌊N * δ⌋₊ : ℝ) *
            bandMoment (floorHardLaw μ B (criticalPoint μ B + lam / N ^ 2)
              ⌊N * τ⌋₊) (upperBand ⌊N * δ⌋₊) := by
  have hγpos := energy_gamma_pos hpos hmean hB hshift hℓ₃ hκ hγ
  have hv : 0 < γ * lam := mul_pos hγpos hlam
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let δ := ε / (8 * Real.log 2)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨τ, z, hτ, hτpole, hz, hzpi, hBprofile, hAprofile, hzsq⟩ :=
    energy_profile_time_before_pole hv hδ
  let s := -profileB (γ * lam) τ + 1 / (2 * δ)
  have hs : 0 < s := by
    have hterm : 0 < 1 / (2 * δ) := by positivity
    dsimp [s]
    linarith [hBprofile, hterm]
  have hshiftS : s + profileB (γ * lam) τ = 1 / (2 * δ) := by
    dsimp [s]
    ring
  let I : Set ℝ := {τ}
  have hI : IsCompact I := by simp [I]
  have hIpole : ∀ t ∈ I, IsPrePoleTime (γ * lam) t := by
    intro t ht
    have ht' : t = τ := by simpa [I] using ht
    subst t
    refine ⟨hτ, ?_⟩
    intro _
    simpa [hv] using hτpole
  have hadm : 0 < s + sInf (profileB (γ * lam) '' I) := by
    have hEq : s + sInf (profileB (γ * lam) '' I) = 1 / (2 * δ) := by
      simp [I, Set.image_singleton, sInf_singleton, hshiftS]
    rw [hEq]
    positivity
  have hweak : WeakConvergence
      (fun N => weightedMeasure (scalingMeasure μ B lam N τ) s) atTop
      (weightedMeasure (profileMeasure (γ * lam) τ) s) :=
    (hCont hlam hI hIpole hs hadm).2 τ (by simp [I])
  have hprofileLarge := energy_profile_cutoff_integral_large hv hδ hs hz
    (by simpa [hv] using hAprofile) hzsq hshiftS hweak.1
  have htestEvent : ∀ᶠ N : ℝ in atTop,
      10 ^ 6 / δ <
        ∫ x, energyBandCutoffBCF δ x ∂weightedMeasure (scalingMeasure μ B lam N τ) s :=
    (hweak.2.2 (energyBandCutoffBCF δ)).eventually
      (Ioi_mem_nhds hprofileLarge)
  have hsmallEvent := energy_floor_log_small hB hτ hδ
  have hnEvent : ∀ᶠ N : ℝ in atTop, 1 ≤ ⌊N * τ⌋₊ := by
    filter_upwards [eventually_gt_atTop (1 / τ)] with N hN
    have hmul := (div_lt_iff₀ hτ).1 hN
    have hcast : ((1 : ℕ) : ℝ) ≤ N * τ := by exact_mod_cast le_of_lt hmul
    exact Nat.le_floor hcast
  have hLEvent : ∀ᶠ N : ℝ in atTop, 10 ^ 4 ≤ ⌊N * δ⌋₊ := by
    filter_upwards [eventually_gt_atTop ((10 ^ 4 + 1 : ℝ) / δ)] with N hN
    have hmul := (div_lt_iff₀ hδ).1 hN
    have hcast : ((10 ^ 4 : ℕ) : ℝ) ≤ N * δ := by norm_num at hmul ⊢; linarith
    exact Nat.le_floor hcast
  have hNEvent : ∀ᶠ N : ℝ in atTop, 0 < N := eventually_gt_atTop 0
  have hcost : τ + 2 * δ ≤ Real.pi / Real.sqrt (γ * lam) + ε / (2 * Real.log 2) := by
    have hδcost : 2 * δ ≤ ε / (2 * Real.log 2) := by
      dsimp [δ]
      field_simp [ne_of_gt hlog2]
      linarith
    have hτlt : τ < Real.pi / Real.sqrt (γ * lam) := by simpa [hv] using hτpole
    linarith
  have hband : ∀ᶠ N : ℝ in atTop,
      0 < N ∧ 1 ≤ ⌊N * τ⌋₊ ∧ 10 ^ 4 ≤ ⌊N * δ⌋₊ ∧
        (10 : ℝ) ^ 4 ≤ (⌊N * δ⌋₊ : ℝ) *
          bandMoment (floorHardLaw μ B (criticalPoint μ B + lam / N ^ 2)
            ⌊N * τ⌋₊) (upperBand ⌊N * δ⌋₊) := by
    filter_upwards [htestEvent, hsmallEvent, hnEvent, hLEvent, hNEvent]
      with N htest hsmall hn hL hN
    let n := ⌊N * τ⌋₊
    let L := ⌊N * δ⌋₊
    let ν := lawR μ B (criticalPoint μ B + lam / N ^ 2) n
    letI : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B _ n
    have hpowInt : Integrable (fun r => r ^ theta B) ν :=
      energy_integrable_realMoment hpos hmean hB _ n
        (theta_pos hB).le (theta_lt_one hB).le
    have hsource := energy_source_integral_le_band ν hB hN hδ hs hn hL rfl hsmall hpowInt
    have hsourcele :
        (∫ x, energyBandCutoffBCF δ x ∂
            weightedMeasure (scalingMeasure μ B lam N τ) s) ≤
          8 * N * bandMoment (floorHardLaw μ B
            (criticalPoint μ B + lam / N ^ 2) n) (upperBand L) :=
      (energy_source_test_integral_eq hB hN).trans_le hsource
    have hsourceLower : (10 : ℝ) ^ 6 / δ <
        8 * N * bandMoment (floorHardLaw μ B
          (criticalPoint μ B + lam / N ^ 2) n) (upperBand L) :=
      htest.trans_le hsourcele
    have hMlower :
        (10 : ℝ) ^ 6 / δ / (8 * N) <
          bandMoment (floorHardLaw μ B (criticalPoint μ B + lam / N ^ 2) n)
            (upperBand L) := by
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 8 * N)).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hsourceLower
    have hNδ : (10 : ℝ) ^ 4 ≤ N * δ := by
      have hLf : (L : ℝ) ≤ N * δ := Nat.floor_le (mul_nonneg hN.le hδ.le)
      have hLcast : (10 : ℝ) ^ 4 ≤ (L : ℝ) := by exact_mod_cast hL
      exact hLcast.trans hLf
    have hLhalf : N * δ / 2 ≤ (L : ℝ) := by
      have hgap := Nat.lt_floor_add_one (N * δ)
      change N * δ < (L : ℝ) + 1 at hgap
      linarith
    have hLdiv : δ / 2 ≤ (L : ℝ) / N := by
      apply (le_div_iff₀ hN).2
      nlinarith [hLhalf]
    have hprod := mul_le_mul hLdiv (le_of_lt hMlower)
      (by positivity : 0 ≤ (10 : ℝ) ^ 6 / δ / (8 * N))
      (by positivity : 0 ≤ (L : ℝ) / N)
    have hprodN := mul_le_mul_of_nonneg_left hprod hN.le
    have hprodN' : (10 : ℝ) ^ 6 / 16 ≤ (L : ℝ) *
        bandMoment (floorHardLaw μ B (criticalPoint μ B + lam / N ^ 2) n)
          (upperBand L) := by
      have hleft : N * ((δ / 2) * ((10 : ℝ) ^ 6 / δ / (8 * N))) =
          (10 : ℝ) ^ 6 / 16 := by field_simp [ne_of_gt hδ, ne_of_gt hN]; ring
      have hright : N * (((L : ℝ) / N) *
          bandMoment (floorHardLaw μ B (criticalPoint μ B + lam / N ^ 2) n)
            (upperBand L)) = (L : ℝ) *
              bandMoment (floorHardLaw μ B (criticalPoint μ B + lam / N ^ 2) n)
                (upperBand L) := by field_simp [ne_of_gt hN]
      rw [hleft, hright] at hprodN
      exact hprodN
    have hfinal : (10 : ℝ) ^ 4 ≤ (L : ℝ) *
        bandMoment (floorHardLaw μ B (criticalPoint μ B + lam / N ^ 2) n)
          (upperBand L) := by
      have hnum : (10 : ℝ) ^ 4 ≤ (10 : ℝ) ^ 6 / 16 := by norm_num
      exact hnum.trans hprodN'
    exact ⟨hN, hn, hL, hfinal⟩
  exact ⟨τ, δ, hτ, hδ, hcost, hband⟩

private theorem energy_escape_constant_from_bandGrowth {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hpos : ∀ᵐ w ∂μ, 0 < w)
    (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {γ lam τ δ ε : ℝ} (hγ : 0 < γ) (hlam : 0 < lam)
    (hτ : 0 < τ) (hδ : 0 < δ) (hε : 0 < ε)
    (hcost : τ + 2 * δ ≤ Real.pi / Real.sqrt (γ * lam) + ε / (2 * Real.log 2))
    (hband : ∀ᶠ N : ℝ in atTop,
      0 < N ∧ 1 ≤ ⌊N * τ⌋₊ ∧ 10 ^ 4 ≤ ⌊N * δ⌋₊ ∧
        (10 : ℝ) ^ 4 ≤ (⌊N * δ⌋₊ : ℝ) *
          bandMoment (floorHardLaw μ B (criticalPoint μ B + lam / N ^ 2)
            ⌊N * τ⌋₊) (upperBand ⌊N * δ⌋₊)) :
    ∀ᶠ N : ℝ in atTop,
      0 < freeEnergy μ B (criticalPoint μ B + lam / N ^ 2) ∧
        -(Real.pi / Real.sqrt (γ * lam)) * Real.log 2 - ε ≤
          N⁻¹ * Real.log (freeEnergy μ B (criticalPoint μ B + lam / N ^ 2)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 < Real.log B := Real.log_pos (by linarith)
  have hBE : ∀ (ν : Measure ℕ) [IsProbabilityMeasure ν] {L : ℕ}, 10 ^ 4 ≤ L →
      (10 : ℝ) ^ 4 ≤ L * bandMoment ν (upperBand L) →
        2⁻¹ * ((2 : ℝ≥0∞) ^ (2 * L))⁻¹ ≤ hardFreeEnergy ν := by
    intro ν hν L hL hM
    exact (escape_bandExit_of_pairs
      (fun ν _ {L} hL I hI k hk hkL => escape_pairs_aux ν hL hI hk hkL)
      ν hL hM).2
  let c := |Real.log (Real.log B / 2)|
  let K := max 1 (2 * c / ε)
  have hK : ∀ᶠ N : ℝ in atTop, K < N := eventually_gt_atTop K
  filter_upwards [hband, hK] with N hN hNK
  rcases hN with ⟨hNpos, hn, hL, hM⟩
  let n := ⌊N * τ⌋₊
  let L := ⌊N * δ⌋₊
  have hn' : 1 ≤ n := by simpa [n] using hn
  have hL' : 10 ^ 4 ≤ L := by simpa [L] using hL
  have hM' : (10 : ℝ) ^ 4 ≤ (L : ℝ) *
      bandMoment (floorHardLaw μ B (criticalPoint μ B + lam / N ^ 2) n)
        (upperBand L) := by simpa [L, n] using hM
  letI : IsProbabilityMeasure (lawR μ B (criticalPoint μ B + lam / N ^ 2) n) :=
    isProbabilityMeasure_lawR B _ n
  letI : IsProbabilityMeasure
      (floorHardLaw μ B (criticalPoint μ B + lam / N ^ 2) n) := by
    dsimp [floorHardLaw]
    infer_instance
  have hcomparison := escape_comparison_of_bandExit hBE hpos hmean hB
    (criticalPoint μ B + lam / N ^ 2) hn'
  have hlow := hcomparison.2.2
    (floorHardLaw μ B (criticalPoint μ B + lam / N ^ 2) n)
    (fun k => le_rfl) L hL' hM'
  have hcoeff : 0 < Real.log (B / floorSeq B n) / 2 := by
    apply div_pos
    · apply Real.log_pos
      have hb : floorSeq B n < 1 := floorSeq_lt_one hB n
      have hb0 : 0 < floorSeq B n :=
        (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn')
      rw [lt_div_iff₀ hb0]
      nlinarith [hb, hB]
    · norm_num
  have hlowpos : 0 < Real.log (B / floorSeq B n) / 2 *
      ((2 : ℝ) ^ (n + 2 * L))⁻¹ := by positivity
  have hFpos : 0 < freeEnergy μ B (criticalPoint μ B + lam / N ^ 2) :=
    lt_of_lt_of_le hlowpos hlow
  have hloglow :
      Real.log (Real.log (B / floorSeq B n) / 2 * ((2 : ℝ) ^ (n + 2 * L))⁻¹) ≤
        Real.log (freeEnergy μ B (criticalPoint μ B + lam / N ^ 2)) :=
    Real.log_le_log hlowpos hlow
  have hlogfactor : Real.log (Real.log (B / floorSeq B n) / 2 *
      ((2 : ℝ) ^ (n + 2 * L))⁻¹) =
      Real.log (Real.log (B / floorSeq B n) / 2) -
        (n + 2 * L : ℕ) * Real.log 2 := by
    rw [Real.log_mul hcoeff.ne'
        (inv_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))),
      Real.log_inv, Real.log_pow]
    ring
  have hcoefflog : Real.log (Real.log B / 2) ≤
      Real.log (Real.log (B / floorSeq B n) / 2) := by
    apply Real.log_le_log (div_pos ha (by norm_num))
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
    apply Real.log_le_log (by positivity)
    have hb : floorSeq B n < 1 := floorSeq_lt_one hB n
    have hb0 : 0 < floorSeq B n :=
      (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn')
    rw [le_div_iff₀ hb0]
    calc
      B * floorSeq B n ≤ B * 1 := mul_le_mul_of_nonneg_left hb.le (by linarith)
      _ = B := by ring
  have hnfloor : (n : ℝ) ≤ N * τ := by
    exact Nat.floor_le (mul_nonneg hNpos.le hτ.le)
  have hLfloor : (L : ℝ) ≤ N * δ := by
    exact Nat.floor_le (mul_nonneg hNpos.le hδ.le)
  have hexp : (n + 2 * L : ℝ) ≤ N * τ + 2 * (N * δ) := by
    change (n : ℝ) + 2 * (L : ℝ) ≤ N * τ + 2 * (N * δ)
    exact add_le_add hnfloor (mul_le_mul_of_nonneg_left hLfloor (by norm_num))
  have hexp' : (n + 2 * L : ℝ) ≤ N * (τ + 2 * δ) := by
    rw [mul_add]
    nlinarith [hexp]
  have hcostN := mul_le_mul_of_nonneg_left hcost hNpos.le
  have htotal : (n + 2 * L : ℝ) * Real.log 2 ≤
      N * ((Real.pi / Real.sqrt (γ * lam)) * Real.log 2 + ε / 2) := by
    have hmul := mul_le_mul_of_nonneg_right hexp' hlog2.le
    have hcostmul := mul_le_mul_of_nonneg_right hcostN hlog2.le
    calc
      (n + 2 * L : ℝ) * Real.log 2 ≤ N * (τ + 2 * δ) * Real.log 2 := hmul
      _ ≤ N * (Real.pi / Real.sqrt (γ * lam) + ε / (2 * Real.log 2)) * Real.log 2 :=
        hcostmul
      _ = N * ((Real.pi / Real.sqrt (γ * lam)) * Real.log 2 + ε / 2) := by
        field_simp [ne_of_gt hlog2]
  have hcost' : N⁻¹ * ((n + 2 * L : ℝ) * Real.log 2) ≤
      (Real.pi / Real.sqrt (γ * lam)) * Real.log 2 + ε / 2 := by
    have htmp : ((n + 2 * L : ℝ) * Real.log 2) / N ≤
        (Real.pi / Real.sqrt (γ * lam)) * Real.log 2 + ε / 2 := by
      apply (div_le_iff₀ hNpos).2
      nlinarith [htotal]
    simpa [div_eq_mul_inv, mul_comm] using htmp
  have hErr : c / N < ε / 2 := by
    apply (div_lt_iff₀ hNpos).2
    have hKerr : 2 * c / ε ≤ K := le_max_right _ _
    have hh := hKerr.trans_lt hNK
    have hh' := (div_lt_iff₀ hε).1 hh
    nlinarith
  have hpref : -ε / 2 ≤ Real.log (Real.log B / 2) / N := by
    have habs : -c ≤ Real.log (Real.log B / 2) := neg_abs_le _
    have hErr' := (div_lt_iff₀ hNpos).1 hErr
    apply (le_div_iff₀ hNpos).2
    nlinarith [hErr', habs]
  have hscaled := mul_le_mul_of_nonneg_left hloglow (inv_nonneg.mpr hNpos.le)
  rw [hlogfactor] at hscaled
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hscaled
  have hscaled' : N⁻¹ * Real.log (freeEnergy μ B (criticalPoint μ B + lam / N ^ 2)) ≥
      Real.log (Real.log B / 2) / N -
        N⁻¹ * ((n + 2 * L : ℝ) * Real.log 2) := by
    have hcf := mul_le_mul_of_nonneg_left hcoefflog (inv_nonneg.mpr hNpos.le)
    calc
      Real.log (Real.log B / 2) / N -
          N⁻¹ * ((n + 2 * L : ℝ) * Real.log 2) =
        N⁻¹ * Real.log (Real.log B / 2) -
          N⁻¹ * ((n + 2 * L : ℝ) * Real.log 2) := by rw [div_eq_mul_inv]; ring
      _ ≤ N⁻¹ * Real.log (Real.log (B / floorSeq B n) / 2) -
          N⁻¹ * ((n + 2 * L : ℝ) * Real.log 2) := sub_le_sub_right hcf _
      _ = N⁻¹ * (Real.log (Real.log (B / floorSeq B n) / 2) -
          (n + 2 * L : ℝ) * Real.log 2) := by ring
      _ ≤ N⁻¹ * Real.log (freeEnergy μ B (criticalPoint μ B + lam / N ^ 2)) := hscaled
  have hfinal : -(Real.pi / Real.sqrt (γ * lam)) * Real.log 2 - ε ≤
      N⁻¹ * Real.log (freeEnergy μ B (criticalPoint μ B + lam / N ^ 2)) := by
    calc
      -(Real.pi / Real.sqrt (γ * lam)) * Real.log 2 - ε ≤
          -ε / 2 - ((Real.pi / Real.sqrt (γ * lam)) * Real.log 2 + ε / 2) := by linarith
      _ ≤ Real.log (Real.log B / 2) / N -
            N⁻¹ * ((n + 2 * L : ℝ) * Real.log 2) := by
        have := hpref
        linarith [hcost']
      _ ≤ N⁻¹ * Real.log (freeEnergy μ B (criticalPoint μ B + lam / N ^ 2)) := hscaled'
  exact ⟨hFpos, hfinal⟩

set_option maxHeartbeats 400000 in
theorem escape_constant_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ γ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hγ : γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃)) {lam : ℝ} (hlam : 0 < lam)
    (hCont : ∀ {lam : ℝ}, 0 < lam → ∀ {I : Set ℝ}, IsCompact I →
      (∀ t ∈ I, IsPrePoleTime (γ * lam) t) → ∀ {s : ℝ}, 0 < s →
      0 < s + sInf (profileB (γ * lam) '' I) →
      TendstoUniformlyOn (fun N t => scaledTransform μ B lam N t s)
          (fun t => profileTransform (γ * lam) t s) atTop I ∧
        ∀ t ∈ I, WeakConvergence (fun N => weightedMeasure (scalingMeasure μ B lam N t) s) atTop
          (weightedMeasure (profileMeasure (γ * lam) t) s)) :
    ∀ ε > 0, ∀ᶠ N : ℝ in atTop,
      0 < freeEnergy μ B (criticalPoint μ B + lam / N ^ 2) ∧
        -(Real.pi / Real.sqrt (γ * lam)) * Real.log 2 - ε ≤
          N⁻¹ * Real.log (freeEnergy μ B (criticalPoint μ B + lam / N ^ 2)) := by
  have hγpos := energy_gamma_pos hpos hmean hB hshift hℓ₃ hκ hγ
  intro ε hε
  obtain ⟨τ, δ, hτ, hδ, hcost, hband⟩ :=
    energy_band_growth_of_continuation hpos hmean hB hshift hℓ₃ hκ hγ hlam hε hCont
  exact energy_escape_constant_from_bandGrowth hpos hmean hB hγpos hlam
    hτ hδ hε hcost hband

end DiamondPinning

