module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Proofs.CriticalMoments
public import DiamondPinning.Proofs.Mellin
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Critical returns and the tilted first moment

For the return theorem, a centered polynomial iteration gives the analytic
solution on a common complex disk. Factoring the difference of two quadratic
recurrences identifies this solution with the Mellin moments on a left interval.

For the first-moment estimate, comparing floor-centered correction kernels at
nearby exponents rules out a finite product limit. Differentiating the same
comparison at the critical exponent gives a recurrence that can be summed
backwards after division by the product.
-/

set_option linter.style.longFile 1800

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Set Metric

private theorem integrable_positive_rpow {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {f : α → ℝ} (hf : Measurable f) (hi : Integrable f ν)
    (hp : ∀ᵐ x ∂ν, 0 < f x) {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1) :
    Integrable (fun x => f x ^ q) ν := by
  apply ((integrable_const (1 : ℝ)).add hi).mono'
    ((Real.continuous_rpow_const hq).measurable.comp hf).aestronglyMeasurable
  filter_upwards [hp] with x hx
  change ‖f x ^ q‖ ≤ 1 + f x
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
  rcases le_total (f x) 1 with h | h
  · exact (Real.rpow_le_one hx.le h hq).trans (by linarith)
  · simpa using (Real.rpow_le_rpow_of_exponent_le h hq').trans
      (show f x ^ (1 : ℝ) ≤ 1 + f x by rw [Real.rpow_one]; linarith)

private theorem integral_rpow_continuousOn {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {f : α → ℝ} (hf : Measurable f) (hi : Integrable f ν)
    (hp : ∀ᵐ x ∂ν, 0 < f x) :
    ContinuousOn (fun q : ℝ => ∫ x, f x ^ q ∂ν) (Icc 0 1) := by
  intro q hq
  apply continuousWithinAt_iff_continuousAt_domRestrict _ hq |>.2
  apply continuousAt_of_dominated (bound := fun x => 1 + f x)
  · exact Eventually.of_forall fun p => ((Real.continuous_rpow_const p.2.1).measurable.comp hf).aestronglyMeasurable
  · refine Eventually.of_forall fun p => ?_
    filter_upwards [hp] with x hx
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
    rcases le_total (f x) 1 with h | h
    · exact (Real.rpow_le_one hx.le h p.2.1).trans (by linarith)
    · exact (Real.rpow_le_rpow_of_exponent_le h p.2.2).trans
        (by rw [Real.rpow_one]; linarith)
  · exact (integrable_const _).add hi
  · filter_upwards [hp] with x hx
    exact (Real.continuousAt_const_rpow hx.ne').comp continuous_subtype_val.continuousAt

private theorem realMoment_floor_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1) :
    floorSeq B n ^ q ≤ realMoment μ B h n q := by
  let := isProbabilityMeasure_lawR (μ := μ) B h n
  unfold realMoment
  have hconst : (∫ _x : ℝ, floorSeq B n ^ q ∂lawR μ B h n) = floorSeq B n ^ q := by simp
  rw [← hconst]
  apply integral_mono_ae (integrable_const _)
    (integrable_positive_rpow measurable_id (integrable_lawR_of hpos hmean hB h n)
      (ae_pos_lawR hpos hB h n) hq hq')
  filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx
  exact Real.rpow_le_rpow (floorSeq_nonneg hB n) hx hq

private theorem bpow_theta {B : ℝ} (hB : 2 < B) : B ^ theta B = 2 := by
  have hb : 0 < B := by linarith
  have hl := Real.log_pos (show 1 < B by linarith)
  rw [Real.rpow_def_of_pos hb, theta, ← mul_div_assoc, mul_div_cancel_left₀ _ hl.ne',
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

private theorem returns_lower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, 1 - ε < tiltedMass μ B h n := by
  have hl := (Real.continuous_rpow_const (theta_pos hB).le).continuousAt.tendsto.comp
    (tendsto_floorSeq hB)
  rw [Real.one_rpow] at hl
  filter_upwards [hl.eventually (lt_mem_nhds (show 1 - ε < 1 by linarith))] with n hn
  exact hn.trans_le (realMoment_floor_bound hpos hmean hB h n
    (theta_pos hB).le (theta_lt_one hB).le)

private theorem recurrence_upper_of_bounded {B : ℝ} (hB : 2 < B) {s : ℕ → ℝ}
    (hs : ∀ n, (s n ^ 2 + (B - 1)) / B ≤ s (n + 1))
    (hbounded : ∃ K, ∀ᶠ n in atTop, s n ≤ K) (n : ℕ) : s n ≤ B - 1 := by
  let c := B - 1
  let d := 2 * c / B
  have hb : 0 < B := by linarith
  have hd : 1 < d := (one_lt_div hb).2 (by dsimp [c]; linarith)
  by_contra! hn
  have hgrowth (k : ℕ) : d ^ k * (s n - c) ≤ s (n + k) - c := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.add_succ, pow_succ, mul_right_comm]
      refine (mul_le_mul_of_nonneg_right ih (by linarith)).trans ?_
      have hid (x : ℝ) : (x ^ 2 + c) / B - c = d * (x - c) + (x - c)^2 / B := by
        dsimp [d, c]
        field_simp
        ring
      have hstep := sub_le_sub_right (hs (n + k)) c
      change (s (n + k) ^ 2 + c) / B - c ≤ _ at hstep
      rw [hid] at hstep
      change (s (n + k) - c) * d ≤ s (n + k + 1) - c
      rw [mul_comm]
      exact le_trans (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hb.le)) hstep
  obtain ⟨K, hK⟩ := hbounded
  have hK' : ∀ᶠ k in atTop, s (n + k) ≤ K := by
    have hshift : Tendsto (fun k : ℕ => n + k) atTop atTop := by
      simpa [Nat.add_comm] using tendsto_add_atTop_nat n
    exact hshift.eventually hK
  have hl := ((tendsto_pow_atTop_atTop_of_one_lt hd).atTop_mul_const
    (sub_pos.mpr hn)).eventually (eventually_gt_atTop (K - c))
  obtain ⟨k, hk, hk'⟩ := (hl.and hK').exists
  exact (not_lt_of_ge (sub_le_sub_right hk' c)) (hk.trans_le (hgrowth k))

private theorem moment_upper_of_bounded {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {q : ℝ} (hq : 0 < q) (hq' : q < 1)
    (hbounded : ∃ K, ∀ᶠ n in atTop, realMoment μ B h n q ≤ K) (n : ℕ) :
    realMoment μ B h n q ≤ (B - 1) ^ q := by
  have hnon (k : ℕ) : 0 ≤ realMoment μ B h k q :=
    (Real.rpow_nonneg (floorSeq_nonneg hB k) _).trans
      (realMoment_floor_bound hpos hmean hB h k hq.le hq'.le)
  obtain ⟨K, hK⟩ := hbounded
  have hbnd : ∃ L, ∀ᶠ k in atTop, realMoment μ B h k q ^ (1 / q) ≤ L :=
    ⟨(max K 0) ^ (1 / q), hK.mono fun k hk =>
      Real.rpow_le_rpow (hnon k) (hk.trans (le_max_left _ _)) (by positivity)⟩
  have hs := recurrence_upper_of_bounded hB (jensen_step_aux hpos hmean hB h hq hq') hbnd n
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg (hnon n) (1 / q)) hs hq.le
  rwa [← Real.rpow_mul (hnon n), one_div_mul_cancel hq.ne', Real.rpow_one] at hh

/-- Coordinatewise Picard iteration with a single contraction estimate on the disk. -/
private theorem polynomial_tail_solution {z₀ : ℂ} {R r a d η : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hη : 0 ≤ η) (hη' : η < 1)
    (hcontract : a + 2 * r * d ≤ η)
    (A E : ℕ → ℂ → ℂ) (D : ℕ → ℂ)
    (hA : ∀ n, DifferentiableOn ℂ (A n) (ball z₀ R))
    (hE : ∀ n, DifferentiableOn ℂ (E n) (ball z₀ R))
    (ha : ∀ n z, z ∈ ball z₀ R → ‖A n z‖ ≤ a)
    (hd : ∀ n, ‖D n‖ ≤ d)
    (he : ∀ n z, z ∈ ball z₀ R → ‖E n z‖ ≤ (1 - η) * r) :
    ∃ W : ℕ → ℂ → ℂ,
      (∀ n, DifferentiableOn ℂ (W n) (ball z₀ R)) ∧
      ∀ n z, z ∈ ball z₀ R → ‖W n z‖ ≤ r ∧
        W n z = A n z * W (n + 1) z - D n * W n z ^ 2 + E n z := by
  let K (z : ℂ) (u : ℕ → ℂ) (n : ℕ) := A n z * u (n + 1) - D n * u n ^ 2 + E n z
  let P : ℕ → ℕ → ℂ → ℂ := fun k n z => (K z)^[k] 0 n
  have hP0 (n z) : P 0 n z = 0 := rfl
  have hPstep (k n z) : P (k + 1) n z = K z (fun j => P k j z) n := by
    simp only [P, Function.iterate_succ_apply']
  have hd₀ : 0 ≤ d := (norm_nonneg _).trans (hd 0)
  have ha₀ : 0 ≤ a := (norm_nonneg _).trans (ha 0 z₀ (mem_ball_self hR))
  have hK (z) (hz : z ∈ ball z₀ R) (u v : ℕ → ℂ)
      (hu : ∀ n, ‖u n‖ ≤ r) (hv : ∀ n, ‖v n‖ ≤ r)
      {b : ℝ} (hb : 0 ≤ b) (hbnd : ∀ n, ‖u n - v n‖ ≤ b) (n : ℕ) :
      ‖K z u n - K z v n‖ ≤ η * b := by
    rw [show K z u n - K z v n =
      A n z * (u (n + 1) - v (n + 1)) -
        D n * ((u n + v n) * (u n - v n)) by dsimp [K]; ring]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    have hsum : ‖u n + v n‖ ≤ 2 * r := (norm_add_le _ _).trans (by linarith [hu n, hv n])
    have h₁ := mul_le_mul (ha n z hz) (hbnd (n + 1)) (norm_nonneg _) ha₀
    have h₂ := mul_le_mul (hd n)
      (mul_le_mul hsum (hbnd n) (norm_nonneg _) (by positivity : 0 ≤ 2 * r))
      (by positivity) hd₀
    calc
      _ ≤ (a + 2 * r * d) * b := by linarith only [h₁, h₂,
        show (a + 2 * r * d) * b = a * b + d * (2 * r * b) by ring]
      _ ≤ η * b := mul_le_mul_of_nonneg_right hcontract hb
  have hball (k : ℕ) (z) (hz : z ∈ ball z₀ R) (n : ℕ) : ‖P k n z‖ ≤ r := by
    induction k generalizing n with
    | zero => simp [hP0, hr.le]
    | succ k ih =>
      rw [hPstep]
      have hh := hK z hz (fun j => P k j z) 0 ih (by simp [hr.le])
        hr.le (by simpa using ih) n
      have hzero : K z 0 n = E n z := by simp [K]
      rw [hzero] at hh
      exact (norm_le_norm_sub_add _ _).trans (by linarith [he n z hz])
  have hgeo (k : ℕ) (z) (hz : z ∈ ball z₀ R) (n : ℕ) :
      dist (P k n z) (P (k + 1) n z) ≤ r * η ^ k := by
    induction k generalizing n with
    | zero => simpa [hP0, dist_eq_norm] using hball 1 z hz n
    | succ k ih =>
      rw [dist_eq_norm, hPstep (k + 1) n z, hPstep k n z]
      have hh := hK z hz (fun j => P k j z) (fun j => P (k + 1) j z)
        (hball k z hz) (hball (k + 1) z hz) (b := r * η ^ k) (by positivity)
        (fun j => by simpa only [dist_eq_norm] using ih j) n
      simpa only [pow_succ, mul_left_comm η, mul_comm η] using hh
  have hlim (n z) (hz : z ∈ ball z₀ R) : ∃ w, Tendsto (fun k => P k n z) atTop (𝓝 w) :=
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric η r hη' (fun k => hgeo k z hz n))
  classical
  let W (n : ℕ) (z : ℂ) := if hz : z ∈ ball z₀ R then (hlim n z hz).choose else 0
  have hW (n z) (hz : z ∈ ball z₀ R) : Tendsto (fun k => P k n z) atTop (𝓝 (W n z)) := by
    change Tendsto (fun k => P k n z) atTop (𝓝 (if hz : z ∈ ball z₀ R then (hlim n z hz).choose else 0))
    rw [dite_eq_left hz]
    exact (hlim n z hz).choose_spec
  have hdiff (k n : ℕ) : DifferentiableOn ℂ (P k n) (ball z₀ R) := by
    induction k generalizing n with
    | zero => simpa only [show P 0 n = fun _ => 0 from rfl] using differentiableOn_const 0
    | succ k ih =>
      simp only [show P (k + 1) n = fun z => K z (fun j => P k j z) n from funext (hPstep k n), K]
      exact (((hA n).mul (ih (n + 1))).sub ((differentiableOn_const (c := D n)).mul ((ih n).pow 2))).add (hE n)
  refine ⟨W, fun n => ?_, fun n z hz => ⟨?_, ?_⟩⟩
  · have hunif : TendstoUniformlyOn (fun k => P k n) (W n) atTop (ball z₀ R) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hη hη').const_mul (r / (1 - η))
      rw [mul_zero] at ht
      have hh := ht.eventually (gt_mem_nhds hε)
      filter_upwards [hh] with k hk z hz
      have hg := dist_le_of_le_geometric_of_tendsto η r hη'
        (fun j => hgeo j z hz n) (hW n z hz) k
      rw [dist_comm]
      exact hg.trans_lt (by
        convert hk using 1
        ring)
    exact hunif.tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun k => hdiff k n) isOpen_ball
  · exact le_of_tendsto (hW n z hz).norm (Eventually.of_forall fun k => hball k z hz n)
  · have ht := (((hW (n + 1) z hz).const_mul (A n z)).sub
      (((hW n z hz).pow 2).const_mul (D n))).add_const (E n z)
    apply tendsto_nhds_unique ((hW n z hz).comp (tendsto_add_atTop_nat 1))
    simpa only [Function.comp_def, hPstep, K] using ht

private noncomputable def logPower (x : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z * (Real.log x : ℂ))

private theorem measurable_logPower (z : ℂ) : Measurable (fun x : ℝ => logPower x z) :=
  Complex.measurable_exp.comp
    (measurable_const.mul (Complex.measurable_ofReal.comp Real.measurable_log))

private theorem logPower_eq_cpow {x : ℝ} (hx : 0 < x) (z : ℂ) :
    logPower x z = (x : ℂ) ^ z := by
  rw [logPower, Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    ← Complex.ofReal_log hx.le, mul_comm]

private theorem logPower_ofReal {x : ℝ} (hx : 0 < x) (q : ℝ) :
    logPower x (q : ℂ) = ((x ^ q : ℝ) : ℂ) := by
  rw [logPower_eq_cpow hx, Complex.ofReal_cpow hx.le]

private theorem integrable_logPower {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {f : α → ℝ} (hf : Measurable f) (hi : Integrable f ν)
    (hp : ∀ᵐ x ∂ν, 0 < f x) {z : ℂ} (hz : 0 ≤ z.re) (hz' : z.re ≤ 1) :
    Integrable (fun x => logPower (f x) z) ν := by
  have hm : Measurable (fun x => logPower (f x) z) := (measurable_logPower z).comp hf
  rw [← integrable_norm_iff hm.aestronglyMeasurable]
  apply (integrable_positive_rpow hf hi hp hz hz').congr
  filter_upwards [hp] with x hx
  rw [logPower_eq_cpow hx, Complex.norm_cpow_eq_rpow_re_of_pos hx]

private noncomputable def complexMoment (μ : Measure ℝ) (B h : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ x, logPower x z ∂lawR μ B h n

private theorem complexMoment_real {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) (q : ℝ) :
    complexMoment μ B h n (q : ℂ) = (realMoment μ B h n q : ℂ) := by
  rw [complexMoment, realMoment, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [ae_pos_lawR hpos hB h n] with x hx
  exact logPower_ofReal hx q

private theorem differentiableOn_complexMoment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) :
    DifferentiableOn ℂ (complexMoment μ B h n) (Complex.re ⁻¹' Ioo 0 1) := by
  let := isProbabilityMeasure_lawR (μ := μ) B h n
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  change DifferentiableAt ℂ (ProbabilityTheory.complexMGF Real.log (lawR μ B h n)) z
  apply (ProbabilityTheory.hasDerivAt_complexMGF ?_).differentiableAt
  apply (interior_maximal (t := Ioo (0 : ℝ) 1) ?_ isOpen_Ioo) hz
  intro q hq
  change Integrable (fun x : ℝ => Real.exp (q * Real.log x)) (lawR μ B h n)
  apply (integrable_positive_rpow measurable_id (integrable_lawR_of hpos hmean hB h n)
    (ae_pos_lawR hpos hB h n) hq.1.le hq.2.le).congr
  filter_upwards [ae_pos_lawR hpos hB h n] with x hx
  change x ^ q = _
  rw [Real.rpow_def_of_pos hx, mul_comm]

private theorem complexMoment_recursion {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {z : ℂ} (hz : 0 < z.re) (hz' : z.re < 1) :
    complexMoment μ B h n z ^ 2 =
      logPower B z * complexMoment μ B h (n + 1) z - correction μ B h n z := by
  let ν := lawR μ B h n
  let : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  let p : ℝ × ℝ → ℝ := fun w => w.1 * w.2
  have hm : Measurable p := by fun_prop
  have hp : ∀ᵐ w ∂ν.prod ν, 0 < p w := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    filter_upwards [ae_pos_lawR hpos hB h n] with y hy
    exact mul_pos hx hy
  have hB₀ : 0 < B := by linarith
  have hs : ∀ᵐ w ∂ν.prod ν, 0 < p w + (B - 1) := hp.mono (by intro w hw; linarith)
  have hi : Integrable p (ν.prod ν) :=
    (integrable_lawR_of hpos hmean hB h n).mul_prod (integrable_lawR_of hpos hmean hB h n)
  have hp' := integrable_logPower hm hi hp hz.le hz'.le
  have hs' := integrable_logPower (hm.add_const (B - 1)) (hi.add (integrable_const _))
    hs hz.le hz'.le
  have hsum : (∫ w, logPower (p w + (B - 1)) z ∂ν.prod ν) =
      logPower B z * complexMoment μ B h (n + 1) z := by
    rw [complexMoment, lawR_succ, integral_map (by fun_prop) (measurable_logPower z).aestronglyMeasurable,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hs] with w hw
    change logPower (p w + (B - 1)) z = logPower B z * logPower ((p w + (B - 1)) / B) z
    rw [logPower, logPower, logPower, ← Complex.exp_add,
      Real.log_div hw.ne' hB₀.ne', Complex.ofReal_sub]
    ring_nf
  have hprod : (∫ w, logPower (p w) z ∂ν.prod ν) = complexMoment μ B h n z ^ 2 := by
    rw [complexMoment, pow_two, ← integral_prod_mul]
    apply integral_congr_ae
    change ∀ᵐ w ∂ν.prod ν, logPower (p w) z = logPower w.1 z * logPower w.2 z
    have hml := measurable_logPower z
    apply (Measure.ae_prod_iff_ae_ae (μ := ν) (ν := ν)
      (measurableSet_eq_fun (hml.comp hm)
        ((hml.comp measurable_fst).mul (hml.comp measurable_snd)))).2
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    filter_upwards [ae_pos_lawR hpos hB h n] with y hy
    change logPower (x * y) z = logPower x z * logPower y z
    simp only [logPower, Real.log_mul hx.ne' hy.ne', Complex.ofReal_add, mul_add, Complex.exp_add]
  have hcorr : correction μ B h n z =
      ∫ w, logPower (p w + (B - 1)) z - logPower (p w) z ∂ν.prod ν := by
    rw [correction, productLaw]
    have hae : ∀ᵐ s ∂(ν.prod ν).map p, 0 < s :=
      (ae_map_iff hm.aemeasurable measurableSet_Ioi).2 hp
    have hae' : ∀ᵐ s ∂(ν.prod ν).map p, 0 < s + (B - 1) :=
      hae.mono (by intro s hs; linarith)
    rw [integral_congr_ae (show
      (fun s : ℝ => (↑(s + (B - 1)) : ℂ) ^ z - (s : ℂ) ^ z) =ᵐ[(ν.prod ν).map p]
        fun s => logPower (s + (B - 1)) z - logPower s z from by
      filter_upwards [hae, hae'] with s hs hs'
      rw [logPower_eq_cpow hs', logPower_eq_cpow hs])]
    exact integral_map hm.aemeasurable
      (((measurable_logPower z).comp (measurable_id.add_const _)).sub
        (measurable_logPower z)).aestronglyMeasurable
  rw [hcorr, integral_sub hs' hp', hsum, hprod]
  ring

private theorem uniform_analytic_increment {U : Set ℂ} (hU : IsOpen U) {z₀ : ℂ}
    (hz₀ : z₀ ∈ U) {C : ℕ → ℂ → ℂ} (hC : ∀ n, DifferentiableOn ℂ (C n) U)
    (hbound : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ M, ∀ n z, z ∈ K → ‖C n z‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 z₀, ∀ n, ‖C n z - C n z₀‖ < ε := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hz₀)
  have hhalf : 0 < R / 3 := by positivity
  have hcl : closedBall z₀ (2 * (R / 3)) ⊆ ball z₀ R :=
    closedBall_subset_ball (by linarith)
  obtain ⟨M, hM⟩ := hbound _ (isCompact_closedBall _ _) (hcl.trans hRU)
  have hM₀ := (norm_nonneg _).trans (hM 0 z₀ (mem_closedBall_self (by positivity)))
  have hlocal {w : ℂ} (hw : w ∈ ball z₀ (R / 3)) :
      closedBall w (R / 3) ⊆ closedBall z₀ (2 * (R / 3)) := by
    intro v hv
    exact mem_closedBall.2 (le_trans (dist_triangle v w z₀)
      (by linarith [mem_closedBall.1 hv, mem_ball.1 hw]))
  have hderiv (n : ℕ) (w : ℂ) (hw : w ∈ ball z₀ (R / 3)) :
      ‖deriv (C n) w‖ ≤ M / (R / 3) :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hhalf
      ((hC n).diffContOnCl_ball ((hlocal hw).trans (hcl.trans hRU)))
      (fun v hv => hM n v (hlocal hw (sphere_subset_closedBall hv)))
  have hdiff (n : ℕ) (w : ℂ) (hw : w ∈ ball z₀ (R / 3)) : DifferentiableAt ℂ (C n) w :=
    (hC n).differentiableAt (hU.mem_nhds (hRU (ball_subset_ball (by linarith) hw)))
  have hsmall : ∀ᶠ z : ℂ in 𝓝 z₀, (M / (R / 3)) * ‖z - z₀‖ < ε := by
    apply IsOpen.eventually_mem (s := {z : ℂ | M / (R / 3) * ‖z - z₀‖ < ε})
      (isOpen_lt (continuous_const.mul (continuous_id.sub continuous_const).norm) continuous_const)
    simpa using hε
  filter_upwards [Metric.ball_mem_nhds z₀ hhalf, hsmall] with z hz hs n
  exact (Convex.norm_image_sub_le_of_norm_deriv_le (hdiff n) (hderiv n)
    (convex_ball z₀ _) (mem_ball_self hhalf) hz).trans_lt hs

private theorem eq_of_backward_norm_contraction {u v : ℕ → ℂ} {kappa K : ℝ}
    (hkappa : 0 ≤ kappa) (hkappa' : kappa < 1) (hK : ∀ n, ‖u n - v n‖ ≤ K)
    (hstep : ∀ n, ‖u n - v n‖ ≤ kappa * ‖u (n + 1) - v (n + 1)‖) (n : ℕ) :
    u n = v n := by
  have hgeo (k n : ℕ) : ‖u n - v n‖ ≤ K * kappa ^ k := by
    induction k generalizing n with
    | zero => simpa using hK n
    | succ k ih =>
      refine (hstep n).trans ?_
      simpa only [pow_succ, mul_left_comm kappa, mul_comm kappa] using
        mul_le_mul_of_nonneg_left (ih (n + 1)) hkappa
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hkappa hkappa').const_mul K
  rw [mul_zero] at ht
  exact sub_eq_zero.mp (norm_le_zero_iff.mp
    (le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall fun k => hgeo k n)))

/-- A positive real-part gap identifies the uniformly bounded analytic solution on
a left interval through the factored difference of the two quadratic recurrences. -/
private theorem quadratic_tail_continuation {U : Set ℂ} (hU : IsOpen U) {q₀ : ℝ}
    (hq₀ : (q₀ : ℂ) ∈ U) (b : ℂ → ℂ) (C G : ℕ → ℂ → ℂ)
    (hb : DifferentiableOn ℂ b U) (hC : ∀ n, DifferentiableOn ℂ (C n) U)
    (hG : ∀ n, DifferentiableOn ℂ (G n) U)
    (hcb : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ M, ∀ n z, z ∈ K → ‖C n z‖ ≤ M)
    (hrec : ∀ n z, z ∈ U → G n z ^ 2 = b z * G (n + 1) z - C n z)
    {m l M s : ℝ} (hm : 0 < m) (hs : 0 < s)
    (hgap : ‖b (q₀ : ℂ)‖ < min (2 * m) (m + l))
    (hg : ∀ n, m ≤ (G n (q₀ : ℂ)).re ∧ ‖G n (q₀ : ℂ)‖ ≤ M)
    (hleft : ∀ q ∈ Ioo (q₀ - s) q₀,
      ∃ K, ∀ n, l ≤ (G n (q : ℂ)).re ∧ ‖G n (q : ℂ)‖ ≤ K) :
    ∃ R > 0, ∀ n z, z ∈ ball (q₀ : ℂ) R → ‖G n z‖ ≤ M + 1 := by
  let z₀ : ℂ := q₀
  let g := fun n => G n z₀
  obtain ⟨a, ha, hat⟩ := exists_between hgap
  have ha₀ : 0 < a := (norm_nonneg _).trans_lt ha
  let r := min 1 ((min (2 * m) (m + l) - a) / 4)
  have hr : 0 < r := lt_min (by norm_num) (by linarith)
  have hr₁ : r ≤ 1 := min_le_left _ _
  have hra : 4 * r ≤ min (2 * m) (m + l) - a := by
    have := min_le_right (1 : ℝ) ((min (2 * m) (m + l) - a) / 4)
    linarith
  have ha₂ : a + 2 * r < 2 * m := by linarith [min_le_left (2 * m) (m + l)]
  have ha₃ : a < m + l - r := by linarith [min_le_right (2 * m) (m + l)]
  let η := (a + 2 * r) / (2 * m)
  have hη : 0 ≤ η := by positivity
  have hη' : η < 1 := (div_lt_one (by positivity)).2 ha₂
  let δ := (1 - η) * r * (2 * m)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hM : 0 ≤ M := (norm_nonneg _).trans (hg 0).2
  have hcont := (hb.continuousOn.continuousAt (hU.mem_nhds hq₀))
  have hb₁ : ∀ᶠ z in 𝓝 z₀, ‖b z‖ < a := hcont.norm.eventually (gt_mem_nhds ha)
  have hb₂ : ∀ᶠ z in 𝓝 z₀, ‖b z - b z₀‖ < δ / (2 * (M + 1)) := by
    have hdiff : ContinuousAt (fun z => ‖b z - b z₀‖) z₀ :=
      (hcont.sub (continuousAt_const (y := b z₀))).norm
    have ht := hdiff.tendsto
    rw [sub_self, norm_zero] at ht
    exact ht.eventually (gt_mem_nhds (by positivity))
  have hc := uniform_analytic_increment hU hq₀ hC hcb (show 0 < δ / 2 by positivity)
  have hlocal : {z | z ∈ U ∧ ‖b z‖ < a ∧ ‖b z - b z₀‖ < δ / (2 * (M + 1)) ∧
      ∀ n, ‖C n z - C n z₀‖ < δ / 2} ∈ 𝓝 z₀ :=
    (show ∀ᶠ z in 𝓝 z₀, z ∈ U from hU.mem_nhds hq₀).and (hb₁.and (hb₂.and hc))
  obtain ⟨R, hR, hball'⟩ := Metric.mem_nhds_iff.1 hlocal
  have hball (z : ℂ) (hz : z ∈ ball z₀ R) :
      z ∈ U ∧ ‖b z‖ < a ∧ ‖b z - b z₀‖ < δ / (2 * (M + 1)) ∧
        ∀ n, ‖C n z - C n z₀‖ < δ / 2 := hball' hz
  have hsub : ball z₀ R ⊆ U := fun _ hz => (hball _ hz).1
  let A := fun n z => b z / (2 * g n)
  let D := fun n => (2 * g n)⁻¹
  let E := fun n z =>
    ((b z - b z₀) * g (n + 1) - (C n z - C n z₀)) / (2 * g n)
  have hden (n : ℕ) : 2 * m ≤ ‖2 * g n‖ := by
    rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    exact mul_le_mul_of_nonneg_left ((hg n).1.trans (Complex.re_le_norm _)) (by norm_num)
  have hden₀ (n : ℕ) : 0 < ‖2 * g n‖ := (by positivity : 0 < 2 * m).trans_le (hden n)
  have hAn (n z) (hz : z ∈ ball z₀ R) : ‖A n z‖ ≤ a / (2 * m) := by
    rw [show A n z = b z / (2 * g n) from rfl, norm_div]
    exact div_le_div₀ ha₀.le (hball _ hz).2.1.le (by positivity) (hden n)
  have hDn (n : ℕ) : ‖D n‖ ≤ 1 / (2 * m) := by
    rw [show D n = (2 * g n)⁻¹ from rfl, norm_inv, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (hden n)
  have hEn (n z) (hz : z ∈ ball z₀ R) : ‖E n z‖ ≤ (1 - η) * r := by
    rw [show E n z = _ from rfl, norm_div]
    apply (div_le_iff₀ (hden₀ n)).2
    have hprod : ‖(b z - b z₀) * g (n + 1)‖ ≤ δ / 2 := by
      rw [norm_mul]
      calc
        _ ≤ δ / (2 * (M + 1)) * (M + 1) :=
          mul_le_mul (hball _ hz).2.2.1.le ((hg (n + 1)).2.trans (by linarith))
            (norm_nonneg _) (by positivity)
        _ = δ / 2 := by field_simp
    refine (norm_sub_le _ _).trans ((add_le_add hprod ((hball _ hz).2.2.2 n).le).trans ?_)
    have hh := mul_le_mul_of_nonneg_left (hden n) (show 0 ≤ (1 - η) * r by positivity)
    convert hh using 1
    dsimp [δ]
    ring
  obtain ⟨W, hW, hWrec⟩ := polynomial_tail_solution hR hr hη hη'
    (show a / (2 * m) + 2 * r * (1 / (2 * m)) ≤ η by
      rw [mul_one_div, ← add_div])
    A E D (fun n => (hb.mono hsub).div_const _) (fun n =>
      ((((hb.mono hsub).sub_const _).mul_const _).sub ((hC n).mono hsub |>.sub_const _)).div_const _)
    hAn hDn hEn
  let V := fun n z => g n + W n z
  have hV₁ (n z) (hz : z ∈ ball z₀ R) : m - r ≤ (V n z).re := by
    have hw := (hWrec n z hz).1
    have hw' := (Complex.abs_re_le_norm (W n z)).trans hw
    rw [abs_le] at hw'
    change m - r ≤ (g n).re + (W n z).re
    linarith [(hg n).1, hw'.1]
  have hV₂ (n z) (hz : z ∈ ball z₀ R) : ‖V n z‖ ≤ M + r :=
    (norm_add_le _ _).trans (add_le_add (hg n).2 (hWrec n z hz).1)
  have hVrec (n z) (hz : z ∈ ball z₀ R) :
      V n z ^ 2 = b z * V (n + 1) z - C n z := by
    have hh := (hWrec n z hz).2
    have hd : 2 * g n ≠ 0 := norm_pos_iff.mp (hden₀ n)
    have hbase := hrec n z₀ hq₀
    change g n ^ 2 = b z₀ * g (n + 1) - C n z₀ at hbase
    dsimp [A, D, E] at hh
    rw [inv_mul_eq_div, div_mul_eq_mul_div, ← sub_div, ← add_div] at hh
    have hw := (eq_div_iff hd).1 hh
    change (g n + W n z) ^ 2 = b z * (g (n + 1) + W (n + 1) z) - C n z
    linear_combination hw + hbase
  let τ := min R s
  have hτ : 0 < τ := lt_min hR hs
  have hleftEq (q : ℝ) (hq : q ∈ Ioo (q₀ - τ) q₀) (n : ℕ) :
      G n (q : ℂ) = V n (q : ℂ) := by
    have hqball : (q : ℂ) ∈ ball z₀ R := by
      rw [mem_ball, show z₀ = (q₀ : ℂ) from rfl, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (sub_neg.mpr hq.2)]
      linarith [hq.1, min_le_left R s]
    obtain ⟨K, hK⟩ := hleft q ⟨by linarith [hq.1, min_le_right R s], hq.2⟩
    apply eq_of_backward_norm_contraction (kappa := a / (m + l - r)) (K := K + (M + r))
      (div_nonneg ha₀.le (ha₀.trans ha₃).le) ((div_lt_one (ha₀.trans ha₃)).2 ha₃)
      (fun j => (norm_sub_le _ _).trans (add_le_add (hK j).2 (hV₂ j _ hqball))) _ n
    intro j
    have hsum : m + l - r ≤ ‖G j (q : ℂ) + V j (q : ℂ)‖ := by
      refine le_trans ?_ (Complex.re_le_norm _)
      rw [Complex.add_re]
      linarith [(hK j).1, hV₁ j _ hqball]
    have hid : (G j (q : ℂ) + V j (q : ℂ)) * (G j (q : ℂ) - V j (q : ℂ)) =
        b (q : ℂ) * (G (j + 1) (q : ℂ) - V (j + 1) (q : ℂ)) := by
      linear_combination hrec j _ (hsub hqball) - hVrec j _ hqball
    have hn := congrArg norm hid
    rw [norm_mul, norm_mul] at hn
    rw [div_mul_eq_mul_div, le_div_iff₀ (ha₀.trans ha₃), mul_comm ‖G j (q : ℂ) - V j (q : ℂ)‖]
    calc
      _ ≤ ‖G j (q : ℂ) + V j (q : ℂ)‖ * ‖G j (q : ℂ) - V j (q : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
      _ ≤ a * ‖G (j + 1) (q : ℂ) - V (j + 1) (q : ℂ)‖ :=
        hn.trans_le (mul_le_mul_of_nonneg_right (hball _ hqball).2.1.le (norm_nonneg _))
  have heq (n : ℕ) : EqOn (G n) (V n) (ball z₀ R) := by
    apply ((hG n).mono hsub |>.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_mem_closure
      (((differentiableOn_const (c := g n)).add (hW n)).analyticOnNhd isOpen_ball)
      ((convex_ball z₀ R).isPreconnected) (mem_ball_self hR)
    have hm₀ : q₀ ∈ closure (Ioo (q₀ - τ) q₀) := by
      rw [closure_Ioo (by linarith)]
      exact ⟨by linarith, le_rfl⟩
    refine closure_mono ?_ (image_closure_subset_closure_image Complex.continuous_ofReal
      (mem_image_of_mem _ hm₀))
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨hleftEq q hq n, fun he => hq.2.ne (Complex.ofReal_injective he)⟩
  refine ⟨R, hR, fun n z hz => ?_⟩
  rw [heq n hz]
  exact (hV₂ n z hz).trans (add_le_add le_rfl hr₁)

private theorem realMoment_le_one_add {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {q p : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) (hp : p ≤ 1) :
    realMoment μ B h n q ≤ 1 + realMoment μ B h n p := by
  let := isProbabilityMeasure_lawR (μ := μ) B h n
  have hx := ae_pos_lawR hpos hB h n
  have hi := integrable_lawR_of hpos hmean hB h n
  have hqint := integrable_positive_rpow measurable_id hi hx hq (hqp.trans hp)
  have hpint : Integrable (fun x : ℝ => x ^ p) (lawR μ B h n) :=
    integrable_positive_rpow measurable_id hi hx (hq.trans hqp) hp
  have hh := integral_mono_ae hqint ((integrable_const (1 : ℝ)).add hpint) (by
    filter_upwards [hx] with x hx
    change x ^ q ≤ 1 + x ^ p
    rcases le_total x 1 with h | h
    · exact (Real.rpow_le_one hx.le h hq).trans (by linarith [Real.rpow_nonneg hx.le p])
    · exact (Real.rpow_le_rpow_of_exponent_le h hqp).trans (by linarith))
  change (∫ x, x ^ q ∂lawR μ B h n) ≤ ∫ x, 1 + x ^ p ∂lawR μ B h n at hh
  simpa only [integral_add (integrable_const (1 : ℝ)) hpint, integral_const, probReal_univ,
    one_smul, realMoment] using hh

private theorem moment_continuation {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo 0 1) {N : ℕ} (hN : 1 ≤ N)
    {m l M s : ℝ} (hm : 0 < m) (hs : 0 < s)
    (hgap : B ^ q₀ < min (2 * m) (m + l))
    (hg : ∀ n ≥ N, m ≤ realMoment μ B h n q₀ ∧ realMoment μ B h n q₀ ≤ M)
    (hleft : ∀ q ∈ Ioo (q₀ - s) q₀, ∃ K, ∀ n ≥ N,
      l ≤ realMoment μ B h n q ∧ 0 ≤ realMoment μ B h n q ∧ realMoment μ B h n q ≤ K) :
    ∃ q ∈ Ioo q₀ 1, ∃ K, ∀ᶠ n in atTop, realMoment μ B h n q ≤ K := by
  let U := Complex.re ⁻¹' Ioo (0 : ℝ) 1
  let G := fun n : ℕ => complexMoment μ B h (N + n)
  let C := fun n : ℕ => correction μ B h (N + n)
  have hU : IsOpen U := isOpen_Ioo.preimage Complex.continuous_re
  have hsub : U ⊆ {z : ℂ | z.re < 1} := fun _ hz => hz.2
  have hrec (n : ℕ) (z : ℂ) (hz : z ∈ U) : G n z ^ 2 =
      logPower B z * G (n + 1) z - C n z := by
    simpa only [G, C, Nat.add_assoc] using complexMoment_recursion hpos hmean hB h (N + n) hz.1 hz.2
  have hnorm (q : ℝ) (n : ℕ) (hn : 0 ≤ realMoment μ B h (N + n) q) :
      ‖G n (q : ℂ)‖ = realMoment μ B h (N + n) q := by
    change ‖complexMoment μ B h (N + n) (q : ℂ)‖ = _
    rw [complexMoment_real hpos hB, Complex.norm_real, Real.norm_of_nonneg hn]
  obtain ⟨R, hR, hbound⟩ := quadratic_tail_continuation hU
    (show (q₀ : ℂ) ∈ U by simpa [U] using hq₀) (logPower B) C G
    ((differentiable_id.mul_const (Real.log B : ℂ)).cexp.differentiableOn)
    (fun n => (differentiableOn_correction_aux hpos hmean hB h (n := N + n) (by omega)).mono hsub)
    (fun n => differentiableOn_complexMoment hpos hmean hB h (N + n))
    (fun K hK hs => by
      obtain ⟨K', hK'⟩ := correction_bounded_aux hpos hmean hB h hK (hs.trans hsub)
      exact ⟨K', fun n z hz => hK' (N + n) (by omega) z hz⟩)
    hrec hm hs
    (by rwa [logPower_ofReal (by linarith : 0 < B), Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ B) _)])
    (fun n => by
      obtain ⟨h₁, h₂⟩ := hg (N + n) (by omega)
      refine ⟨?_, (hnorm q₀ n (hm.le.trans h₁)).trans_le h₂⟩
      simpa [G, complexMoment_real hpos hB] using h₁)
    (fun q hq => by
      obtain ⟨K, hK⟩ := hleft q hq
      refine ⟨K, fun n => ?_⟩
      obtain ⟨h₁, h₂, h₃⟩ := hK (N + n) (by omega)
      exact ⟨by simpa [G, complexMoment_real hpos hB] using h₁, (hnorm q n h₂).trans_le h₃⟩)
  obtain ⟨q, hq₁, hq₂⟩ := exists_between (show q₀ < min 1 (q₀ + R) by
    exact lt_min hq₀.2 (lt_add_of_pos_right _ hR))
  have hq : q ∈ Ioo q₀ 1 := ⟨hq₁, hq₂.trans_le (min_le_left _ _)⟩
  have hbq : (q : ℂ) ∈ ball (q₀ : ℂ) R := by
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hq₁)]
    linarith [hq₂.trans_le (min_le_right 1 (q₀ + R))]
  refine ⟨q, hq, M + 1, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  have hh := hbound (n - N) _ hbq
  change ‖complexMoment μ B h (N + (n - N)) (q : ℂ)‖ ≤ _ at hh
  rw [Nat.add_sub_of_le hn, complexMoment_real hpos hB, Complex.norm_real] at hh
  exact (le_abs_self _).trans hh

private theorem no_bounded_moment_above_theta {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {p : ℝ} (hpθ : theta B < p) (hp : p < 1) :
    ¬ ∃ K, ∀ᶠ n in atTop, realMoment μ B (criticalPoint μ B) n p ≤ K := by
  let h := criticalPoint μ B
  let G := fun n => realMoment μ B h n
  let S := {q : ℝ | q ∈ Ioo 0 1 ∧ ∃ K, ∀ᶠ n in atTop, G n q ≤ K}
  intro hpbounded
  have hpS : p ∈ S := ⟨⟨(theta_pos hB).trans hpθ, hp⟩, hpbounded⟩
  have hSn : S.Nonempty := ⟨p, hpS⟩
  have hSb : BddAbove S := ⟨1, fun q hq => hq.1.2.le⟩
  let q₀ := sSup S
  have hθq : theta B < q₀ := hpθ.trans_le (le_csSup hSb hpS)
  have hq₀ : 0 < q₀ := (theta_pos hB).trans hθq
  have hq₁ : q₀ ≤ 1 := csSup_le hSn (fun q hq => hq.1.2.le)
  have hdown {q : ℝ} (hq : 0 < q) (hqq : q < q₀) : q ∈ S := by
    obtain ⟨p, hp, hqp⟩ := exists_lt_of_lt_csSup hSn hqq
    obtain ⟨K, hK⟩ := hp.2
    exact ⟨⟨hq, hqp.trans hp.1.2⟩, 1 + K, hK.mono fun n hn =>
      (realMoment_le_one_add hpos hmean hB h n hq.le hqp.le hp.1.2.le).trans (add_le_add le_rfl hn)⟩
  have hcap (n : ℕ) (q : ℝ) (hq : q ∈ Ioo 0 q₀) : G n q ≤ (B - 1) ^ q :=
    moment_upper_of_bounded hpos hmean hB h hq.1 (hq.2.trans_le hq₁) (hdown hq.1 hq.2).2 n
  have hcap₀ (n : ℕ) : G n q₀ ≤ (B - 1) ^ q₀ := by
    obtain ⟨u, _, hu, hulim⟩ := exists_seq_strictMono_tendsto' hq₀
    have hu' (k : ℕ) : u k ∈ Icc 0 1 := ⟨(hu k).1.le, (hu k).2.le.trans hq₁⟩
    let := isProbabilityMeasure_lawR (μ := μ) B h n
    have hcont : ContinuousWithinAt (G n) (Icc 0 1) q₀ :=
      integral_rpow_continuousOn measurable_id (integrable_lawR_of hpos hmean hB h n)
        (ae_pos_lawR hpos hB h n) q₀ ⟨hq₀.le, hq₁⟩
    have hlim := hcont.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      u hulim (Eventually.of_forall hu'))
    have hlim' := (Real.continuousAt_const_rpow (a := B - 1) (by linarith)).tendsto.comp hulim
    exact le_of_tendsto_of_tendsto hlim hlim' (Eventually.of_forall fun k => hcap n (u k) (hu k))
  have hq₁' : q₀ < 1 := by
    by_contra! hh
    have heq : q₀ = 1 := le_antisymm hq₁ hh
    have hw := hcap₀ 0
    change realMoment μ B h 0 q₀ ≤ _ at hw
    rw [heq, Real.rpow_one, realMoment, integral_congr_ae
      (Eventually.of_forall fun x => Real.rpow_one x), integral_lawR_zero hmean] at hw
    exact (not_lt_of_ge hw) ((Real.log_lt_iff_lt_exp (by linarith)).1 hshift)
  have hbB : 1 < B := by linarith
  have hb2 : 2 < B ^ q₀ := by
    rw [← bpow_theta hB]
    exact Real.rpow_lt_rpow_of_exponent_lt hbB hθq
  obtain ⟨m, hm₁, hm₂⟩ := exists_between (show B ^ q₀ / 2 < B ^ q₀ - 1 by linarith)
  let δ := (B ^ q₀ - 1 - m) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_floorSeq hB).eventually (lt_mem_nhds (show 1 - δ < 1 by linarith)))
  have hnt (n : ℕ) (hn : max 1 N ≤ n) : 1 - δ < floorSeq B n :=
    hN n ((le_max_right 1 N).trans hn)
  have hcont : ContinuousAt (fun q : ℝ => B ^ q) q₀ :=
    Real.continuousAt_const_rpow (by linarith)
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.1
    (hcont.eventually (lt_mem_nhds (show m + 1 + δ < B ^ q₀ by dsimp [δ]; linarith)))
  let s := min R ((q₀ - theta B) / 2)
  have hs : 0 < s := lt_min hR (by positivity)
  have hlower (q : ℝ) (hq : q ∈ Ioc (q₀ - s) q₀) (n : ℕ) (hn : max 1 N ≤ n) :
      m ≤ G n q := by
    have hθq' : theta B < q := by
      linarith [hq.1, min_le_right R ((q₀ - theta B) / 2)]
    have hq' := hq.2.trans_lt hq₁'
    have hqR : q ∈ ball q₀ R := by
      rw [mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hq.2)]
      linarith [hq.1, min_le_left R ((q₀ - theta B) / 2)]
    have hbq := Real.rpow_le_rpow_of_exponent_ge' (floorSeq_nonneg hB n)
      (floorSeq_le_one hB n) ((theta_pos hB).trans hθq').le hq'.le
    rw [Real.rpow_one] at hbq
    have hG := barrier_aux hpos hmean hB hshift hθq' hq' ((le_max_left 1 N).trans hn)
    have hbq' : m + 1 + δ < B ^ q := hRsub hqR
    linarith [hnt n hn]
  obtain ⟨q, hq, hbounded⟩ := moment_continuation hpos hmean hB h ⟨hq₀, hq₁'⟩
    (le_max_left 1 N) (m := m) (l := m) (M := (B - 1) ^ q₀)
    (by linarith) hs (lt_min (by linarith) (by linarith))
    (fun n hn => ⟨hlower q₀ ⟨by linarith, le_rfl⟩ n hn, hcap₀ n⟩)
    (fun q hq => by
      have hq' : 0 < q := by
        linarith [hq.1, theta_pos hB, min_le_right R ((q₀ - theta B) / 2)]
      exact ⟨(B - 1) ^ q, fun n hn =>
        ⟨hlower q ⟨hq.1, hq.2.le⟩ n hn, by
          linarith [hlower q ⟨hq.1, hq.2.le⟩ n hn], hcap n q ⟨hq', hq.2⟩⟩⟩)
  exact hq.1.not_ge (le_csSup hSb ⟨⟨hq₀.trans hq.1, hq.2⟩, hbounded⟩)

theorem returns_to_one_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) :
    (∀ ε > 0, ∃ᶠ n in atTop, tiltedMass μ B (criticalPoint μ B) n < 1 + ε) ∧
    (∀ ε > 0, ∀ᶠ n in atTop, 1 - ε < tiltedMass μ B (criticalPoint μ B) n) := by
  let h := criticalPoint μ B
  refine ⟨?_, returns_lower hpos hmean hB h⟩
  intro ε hε
  by_contra hfail
  have hh : ∀ᶠ n in atTop, 1 + ε ≤ tiltedMass μ B h n := by
    simpa only [Filter.Frequently, not_not, not_lt] using hfail
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hh.and ((tendsto_floorSeq hB).eventually (lt_mem_nhds (show 1 - ε / 2 < 1 by linarith))))
  obtain ⟨C, hC⟩ := criticalMoments_aux hB
  have hA := (hC μ hpos hmean h (criticalPoint_isGreatest_aux hpos hmean hB).1).1
  have hθ := theta_pos hB
  have hθ' := theta_lt_one hB
  obtain ⟨q, hq, hbounded⟩ := moment_continuation hpos hmean hB h ⟨hθ, hθ'⟩
    (le_max_left 1 N) (m := 1 + ε) (l := 1 - ε / 2) (M := (B - 1) ^ theta B)
    (by linarith) (s := theta B / 2) (by positivity)
    (by rw [bpow_theta hB]; exact lt_min (by linarith) (by linarith))
    (fun n hn => ⟨(hN n ((le_max_right 1 N).trans hn)).1,
      (hA n ((le_max_left 1 N).trans hn)).1⟩)
    (fun q hq => by
      have hqpos : 0 < q := by linarith [hq.1]
      refine ⟨1 + (B - 1) ^ theta B, fun n hn => ?_⟩
      have hbq := Real.rpow_le_rpow_of_exponent_ge' (floorSeq_nonneg hB n)
        (floorSeq_le_one hB n) hqpos.le (hq.2.trans hθ').le
      rw [Real.rpow_one] at hbq
      have hlow := realMoment_floor_bound hpos hmean hB h n hqpos.le (hq.2.trans hθ').le
      exact ⟨((hN n ((le_max_right 1 N).trans hn)).2.le.trans hbq).trans hlow,
        (Real.rpow_nonneg (floorSeq_nonneg hB n) _).trans hlow,
        (realMoment_le_one_add hpos hmean hB h n hqpos.le hq.2.le hθ'.le).trans
          (add_le_add le_rfl (hA n ((le_max_left 1 N).trans hn)).1)⟩)
  exact no_bounded_moment_above_theta hpos hmean hB hshift hq.1 hq.2 hbounded

private noncomputable def defectKernel (c b q x : ℝ) : ℝ :=
  x ^ q - (x + c) ^ q - (b ^ q - (b + c) ^ q)

private noncomputable def defectFactor (b θ q : ℝ) : ℝ :=
  ((1 - q) / (1 - θ)) * b ^ (q - θ)

private theorem defectKernel_compare {c b θ q r x : ℝ} (hc : 0 ≤ c) (hb : 0 < b)
    (hbr : b ≤ r) (hrx : r ≤ x) (hθ : 0 < θ) (hθq : θ ≤ q) (hq : q < 1) :
    defectFactor b θ q * defectKernel c r θ x ≤ defectKernel c r q x := by
  have hθ₁ := hθq.trans_lt hq
  have hw : 0 ≤ defectFactor b θ q := by
    unfold defectFactor
    exact mul_nonneg (div_nonneg (sub_nonneg.mpr hq.le) (sub_nonneg.mpr hθ₁.le))
      (Real.rpow_nonneg hb.le _)
  have hinner (s : ℝ) (hs : b ≤ s) :
      defectFactor b θ q * (s ^ (θ - 1) - (s + c) ^ (θ - 1)) ≤
        s ^ (q - 1) - (s + c) ^ (q - 1) := by
    let f := fun t : ℝ => defectFactor b θ q * t ^ (θ - 1) - t ^ (q - 1)
    have hderiv (t : ℝ) (ht : b ≤ t) : HasDerivAt f
        (defectFactor b θ q * ((θ - 1) * t ^ (θ - 2)) - (q - 1) * t ^ (q - 2)) t := by
      have ht₀ := hb.trans_le ht
      convert ((Real.hasDerivAt_rpow_const (p := θ - 1) (Or.inl ht₀.ne')).const_mul
        (defectFactor b θ q)).sub
          (Real.hasDerivAt_rpow_const (p := q - 1) (Or.inl ht₀.ne')) using 1
      ring_nf
    have hmono : MonotoneOn f (Ici b) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici b)
      · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
      · exact fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht' : b ≤ t := interior_subset ht
        rw [(hderiv t ht').deriv]
        have htp := Real.rpow_le_rpow hb.le ht' (sub_nonneg.mpr hθq)
        have he : t ^ (q - 2) = t ^ (θ - 2) * t ^ (q - θ) := by
          rw [← Real.rpow_add (hb.trans_le ht')]
          congr 1
          ring
        rw [he]
        unfold defectFactor
        have hid : (1 - q) / (1 - θ) * b ^ (q - θ) * ((θ - 1) * t ^ (θ - 2)) =
            (q - 1) * (t ^ (θ - 2) * b ^ (q - θ)) := by
          field_simp [sub_ne_zero.mpr hθ₁.ne.symm]
          ring
        rw [hid]
        have hh := mul_le_mul_of_nonneg_left htp (Real.rpow_nonneg (hb.trans_le ht').le (θ - 2))
        exact sub_nonneg.mpr (mul_le_mul_of_nonpos_left hh (sub_nonpos.mpr hq.le))
    have hh := hmono hs (show s + c ∈ Ici b from hs.trans (le_add_of_nonneg_right hc))
      (le_add_of_nonneg_right hc)
    dsimp [f] at hh
    linarith only [hh, show defectFactor b θ q * (s ^ (θ - 1) - (s + c) ^ (θ - 1)) =
      defectFactor b θ q * s ^ (θ - 1) - defectFactor b θ q * (s + c) ^ (θ - 1) by ring]
  let f := fun t : ℝ => t ^ q - (t + c) ^ q -
    defectFactor b θ q * (t ^ θ - (t + c) ^ θ)
  have hderiv (t : ℝ) (ht : b ≤ t) : HasDerivAt f
      (q * (t ^ (q - 1) - (t + c) ^ (q - 1)) -
        defectFactor b θ q * (θ * (t ^ (θ - 1) - (t + c) ^ (θ - 1)))) t := by
    have htx := hb.trans_le ht
    have htc : 0 < t + c := htx.trans_le (le_add_of_nonneg_right hc)
    have hshift (p : ℝ) := (Real.hasDerivAt_rpow_const (p := p) (Or.inl htc.ne')).comp t
      ((hasDerivAt_id t).add_const c)
    convert ((Real.hasDerivAt_rpow_const (p := q) (Or.inl htx.ne')).sub (hshift q)).sub
      (((Real.hasDerivAt_rpow_const (p := θ) (Or.inl htx.ne')).sub (hshift θ)).const_mul
        (defectFactor b θ q)) using 1
    · funext u
      simp [f, Function.comp_def, add_comm]
    · ring
  have hmono : MonotoneOn f (Ici b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici b)
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : b ≤ t := interior_subset ht
      rw [(hderiv t ht').deriv]
      have hp : 0 ≤ t ^ (θ - 1) - (t + c) ^ (θ - 1) := sub_nonneg.mpr
        (Real.rpow_le_rpow_of_nonpos (hb.trans_le ht') (le_add_of_nonneg_right hc) (by linarith))
      have hle := mul_le_mul_of_nonneg_left (hinner t ht') (hθ.le.trans hθq)
      have hle' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hθq hp) hw
      nlinarith only [hle, hle']
  have hh := hmono hbr (hbr.trans hrx : x ∈ Ici b) hrx
  dsimp [f, defectKernel] at hh ⊢
  linarith only [hh, show defectFactor b θ q *
    (x ^ θ - (x + c) ^ θ - (r ^ θ - (r + c) ^ θ)) =
    defectFactor b θ q * (x ^ θ - (x + c) ^ θ) -
      defectFactor b θ q * (r ^ θ - (r + c) ^ θ) by ring]

private theorem defectKernel_nonneg {c r q x : ℝ} (hc : 0 ≤ c) (hr : 0 < r)
    (hrx : r ≤ x) (hq : 0 ≤ q) (hq' : q < 1) :
    0 ≤ defectKernel c r q x := by
  let f := fun t : ℝ => t ^ q - (t + c) ^ q
  have hderiv (t : ℝ) (ht : r ≤ t) :
      HasDerivAt f (q * (t ^ (q - 1) - (t + c) ^ (q - 1))) t := by
    have hp := hr.trans_le ht
    have hc' : 0 < t + c := hp.trans_le (le_add_of_nonneg_right hc)
    convert (Real.hasDerivAt_rpow_const (p := q) (Or.inl hp.ne')).sub
      ((Real.hasDerivAt_rpow_const (p := q) (Or.inl hc'.ne')).comp t
        ((hasDerivAt_id t).add_const c)) using 1
    · rfl
    · ring
  have hmono : MonotoneOn f (Ici r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici r)
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : r ≤ t := interior_subset ht
      rw [(hderiv t ht').deriv]
      exact mul_nonneg hq (sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos
        (hr.trans_le ht') (le_add_of_nonneg_right hc) (by linarith)))
  exact sub_nonneg.mpr (hmono (show r ∈ Ici r from le_rfl) hrx hrx)

private noncomputable def floorDefect (μ : Measure ℝ) (B h : ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  ∫ w : ℝ × ℝ, defectKernel (B - 1) (floorSeq B n ^ 2) q (w.1 * w.2)
    ∂(lawR μ B h n).prod (lawR μ B h n)

private noncomputable def floorExcess (μ : Measure ℝ) (B h : ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  realMoment μ B h n q - floorSeq B n ^ q

private theorem floorExcess_nonneg {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {q : ℝ} (hq : q ∈ Icc 0 1) : 0 ≤ floorExcess μ B h n q :=
  sub_nonneg.mpr (realMoment_floor_bound hpos hmean hB h n hq.1 hq.2)

private theorem floorDefect_data {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    let ν := (lawR μ B h n).prod (lawR μ B h n)
    (∀ᵐ w : ℝ × ℝ ∂ν, floorSeq B n ^ 2 ≤ w.1 * w.2) ∧
    ∀ q ∈ Icc (0 : ℝ) 1,
      Integrable (fun w : ℝ × ℝ => defectKernel (B - 1) (floorSeq B n ^ 2) q (w.1 * w.2)) ν := by
  let τ := lawR μ B h n
  let : IsProbabilityMeasure τ := isProbabilityMeasure_lawR B h n
  have hae : ∀ᵐ w : ℝ × ℝ ∂τ.prod τ, floorSeq B n ^ 2 ≤ w.1 * w.2 := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx
    filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with y hy
    rw [pow_two]
    exact mul_le_mul hx hy (floorSeq_nonneg hB n) ((floorSeq_nonneg hB n).trans hx)
  refine ⟨hae, fun q hq => ?_⟩
  have hp : ∀ᵐ w : ℝ × ℝ ∂τ.prod τ, 0 < w.1 * w.2 :=
    hae.mono (fun w hw => (sq_pos_of_pos ((floorSeq_one_pos hB).trans_le
      (floorSeq_one_le hB hn))).trans_le hw)
  have hi := integrable_lawR_of hpos hmean hB h n
  have hh : Integrable (fun w : ℝ × ℝ => w.1 * w.2) (τ.prod τ) := hi.mul_prod hi
  have hq₁ := integrable_positive_rpow (by fun_prop) hh hp hq.1 hq.2
  have hshift : ∀ᵐ w : ℝ × ℝ ∂τ.prod τ, 0 < w.1 * w.2 + (B - 1) :=
    hp.mono (by intro w hw; linarith)
  have hq₂ := integrable_positive_rpow (by fun_prop) (hh.add (integrable_const _)) hshift hq.1 hq.2
  exact (hq₁.sub hq₂).sub (integrable_const _)

private theorem floorDefect_nonneg_compare {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq : theta B ≤ q) (hq' : q < 1) :
    let k := defectFactor (floorSeq B 1 ^ 2) (theta B) q
    0 ≤ floorDefect μ B h n (theta B) ∧ k * floorDefect μ B h n (theta B) ≤ floorDefect μ B h n q := by
  obtain ⟨hae, hi⟩ := floorDefect_data hpos hmean hB h hn
  have hb := floorSeq_one_pos hB
  have hbn := hb.trans_le (floorSeq_one_le hB hn)
  have hsq : floorSeq B 1 ^ 2 ≤ floorSeq B n ^ 2 :=
    pow_le_pow_left₀ hb.le (floorSeq_one_le hB hn) 2
  have hθ := theta_pos hB
  refine ⟨integral_nonneg_of_ae ?_, ?_⟩
  · filter_upwards [hae] with w hw using
      defectKernel_nonneg (by linarith : 0 ≤ B - 1) (sq_pos_of_pos hbn) hw hθ.le (theta_lt_one hB)
  · dsimp
    unfold floorDefect
    rw [← integral_const_mul]
    apply integral_mono_ae ((hi _ ⟨hθ.le, (theta_lt_one hB).le⟩).const_mul _)
      (hi _ ⟨hθ.le.trans hq, hq'.le⟩)
    filter_upwards [hae] with w hw using
      defectKernel_compare (by linarith : 0 ≤ B - 1) (sq_pos_of_pos hb) hsq hw hθ hq hq'

private theorem floorExcess_recursion {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq : q ∈ Ioo 0 1) :
    floorExcess μ B h (n + 1) q =
      (2 * floorSeq B n ^ q * floorExcess μ B h n q + floorExcess μ B h n q ^ 2 -
        floorDefect μ B h n q) / B ^ q := by
  let ν := lawR μ B h n
  let : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  let f : ℝ × ℝ → ℝ := fun w => w.1 * w.2
  let b := floorSeq B n
  let c := B - 1
  have hb : 0 < b := (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hB₀ : 0 < B := by linarith
  have hp := (floorDefect_data hpos hmean hB h hn).1
  have hf₀ : ∀ᵐ w ∂ν.prod ν, 0 < f w := hp.mono (fun _ hw => (sq_pos_of_pos hb).trans_le hw)
  have hs₀ : ∀ᵐ w ∂ν.prod ν, 0 < f w + c := hf₀.mono (fun _ hw =>
    add_pos_of_pos_of_nonneg hw hc)
  have hm := integrable_lawR_of hpos hmean hB h n
  have hf : Integrable f (ν.prod ν) := hm.mul_prod hm
  have hi₁ : Integrable (fun w => f w ^ q) (ν.prod ν) :=
    integrable_positive_rpow (by fun_prop) hf hf₀ hq.1.le hq.2.le
  have hi₂ : Integrable (fun w => (f w + c) ^ q) (ν.prod ν) :=
    integrable_positive_rpow (by fun_prop) (hf.add (integrable_const c)) hs₀ hq.1.le hq.2.le
  have hprod : (∫ w, f w ^ q ∂ν.prod ν) = realMoment μ B h n q ^ 2 := by
    have hae : ∀ᵐ w ∂ν.prod ν, f w ^ q = w.1 ^ q * w.2 ^ q := by
      rw [Measure.ae_prod_iff_ae_ae (by
        dsimp [f]
        measurability)]
      filter_upwards [ae_pos_lawR hpos hB h n] with x hx
      filter_upwards [ae_pos_lawR hpos hB h n] with y hy
      exact Real.mul_rpow hx.le hy.le
    rw [integral_congr_ae hae, integral_prod_mul (fun x : ℝ => x ^ q) (fun x : ℝ => x ^ q), realMoment, pow_two]
  have hrec : realMoment μ B h (n + 1) q =
      (∫ w, (f w + c) ^ q ∂ν.prod ν) / B ^ q := by
    rw [realMoment, lawR_succ, integral_map (by fun_prop)
      (Real.continuous_rpow_const hq.1.le).measurable.aestronglyMeasurable, ← integral_div]
    apply integral_congr_ae
    filter_upwards [hs₀] with w hw
    exact Real.div_rpow hw.le hB₀.le q
  have hD : floorDefect μ B h n q =
      realMoment μ B h n q ^ 2 - (∫ w, (f w + c) ^ q ∂ν.prod ν) - ((b ^ 2) ^ q - (b ^ 2 + c) ^ q) := by
    unfold floorDefect defectKernel
    change (∫ w, f w ^ q - (f w + c) ^ q - ((b ^ 2) ^ q - (b ^ 2 + c) ^ q) ∂ν.prod ν) = _
    have hi : Integrable (fun w => f w ^ q - (f w + c) ^ q) (ν.prod ν) := hi₁.sub hi₂
    rw [integral_sub hi (integrable_const _), integral_sub hi₁ hi₂, hprod]
    simp
  have hbpow : (b ^ 2) ^ q = (b ^ q) ^ 2 := by
    simp only [pow_two, Real.mul_rpow hb.le hb.le]
  have hfloor : floorSeq B (n + 1) ^ q = (b ^ 2 + c) ^ q / B ^ q := by
    rw [floorSeq_succ, Real.div_rpow (by positivity : 0 ≤ b ^ 2 + c) hB₀.le]
  simp only [floorExcess]
  rw [hrec, hfloor, hD, hbpow, ← sub_div]
  congr 1
  ring

private noncomputable def logDerivative (μ : Measure ℝ) (B h : ℝ) (n : ℕ) : ℝ :=
  tiltedLogMoment μ B h 1 n + Real.log B * tiltedMass μ B h n

private theorem hasDerivAt_realMoment_theta {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) :
    HasDerivAt (realMoment μ B h n) (logDerivative μ B h n) (theta B) := by
  let ν := lawR μ B h n
  let : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  have hp := ae_pos_lawR hpos hB h n
  have hi := integrable_lawR_of hpos hmean hB h n
  have hmgf : realMoment μ B h n = ProbabilityTheory.mgf Real.log ν := by
    funext q
    apply integral_congr_ae
    filter_upwards [hp] with x hx
    rw [Real.rpow_def_of_pos hx, mul_comm]
  have hmem : theta B ∈ interior (ProbabilityTheory.integrableExpSet Real.log ν) := by
    apply (interior_maximal (t := Ioo 0 1) ?_ isOpen_Ioo) ⟨theta_pos hB, theta_lt_one hB⟩
    intro q hq
    change Integrable (fun x : ℝ => Real.exp (q * Real.log x)) ν
    apply (integrable_positive_rpow measurable_id hi hp hq.1.le hq.2.le).congr
    filter_upwards [hp] with x hx
    change x ^ q = Real.exp (q * Real.log x)
    rw [Real.rpow_def_of_pos hx, mul_comm]
  have hlogabs := integrable_tiltedLogPower_of hpos hmean hB h n (q := 1) (by norm_num)
  simp only [Real.rpow_one] at hlogabs
  have hlog : Integrable (fun x : ℝ => x ^ theta B * Real.log x) ν := by
    apply hlogabs.mono'
      (((Real.continuous_rpow_const (theta_pos hB).le).measurable.mul
        Real.measurable_log).aestronglyMeasurable)
    filter_upwards [hp] with x hx
    change |x ^ theta B * Real.log x| ≤ _
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _)]
  have h₂ : Integrable (fun x : ℝ => Real.log B * x ^ theta B) ν :=
    (integrable_positive_rpow measurable_id hi hp (theta_pos hB).le (theta_lt_one hB).le).const_mul _
  have h₁ : Integrable (fun x : ℝ => x ^ theta B * (Real.log x - Real.log B)) ν := by
    convert hlog.sub h₂ using 1
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [hmgf]
  convert ProbabilityTheory.hasDerivAt_mgf hmem using 1
  unfold logDerivative tiltedLogMoment tiltedMass
  simp only [pow_one]
  rw [← integral_const_mul, ← integral_add h₁ h₂]
  apply integral_congr_ae
  filter_upwards [hp] with x hx
  rw [Real.rpow_def_of_pos hx, mul_comm (Real.log x) (theta B)]
  ring

private theorem hasDerivAt_base_rpow {b q : ℝ} (hb : 0 < b) :
    HasDerivAt (fun t : ℝ => b ^ t) (Real.log b * b ^ q) q := by
  simp only [Real.rpow_def_of_pos hb]
  convert (((hasDerivAt_id q).const_mul (Real.log b)).exp) using 1
  · ext t
    simp [mul_comm]
  · simp [mul_comm]

private theorem deriv_le_of_right_comparison {f g : ℝ → ℝ} {q df dg : ℝ}
    (hf : HasDerivAt f df q) (hg : HasDerivAt g dg q) (heq : f q = g q)
    (hle : ∀ᶠ t : ℝ in 𝓝[>] 0, f (q + t) ≤ g (q + t)) : df ≤ dg := by
  apply le_of_tendsto_of_tendsto hf.tendsto_slope_zero_right hg.tendsto_slope_zero_right
  filter_upwards [hle, self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht ht₀
  rw [heq]
  exact smul_le_smul_of_nonneg_left (sub_le_sub_right ht _) (inv_nonneg.mpr ht₀.le)

private theorem eventual_add_lt {q : ℝ} (hq : q < 1) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧ q + t < 1 := by
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ)),
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (show 0 < 1 - q by linarith))] with t ht ht'
  exact ⟨ht, by linarith⟩

private noncomputable def inverseCoefficient (B q : ℝ) : ℝ := 2 / B ^ q

private theorem inverseCoefficient_theta {B : ℝ} (hB : 2 < B) :
    inverseCoefficient B (theta B) = 1 := by simp [inverseCoefficient, bpow_theta hB]

private theorem hasDerivAt_inverseCoefficient {B : ℝ} (hB : 2 < B) :
    HasDerivAt (inverseCoefficient B) (-Real.log B) (theta B) := by
  have hB₀ : 0 < B := by linarith
  convert (hasDerivAt_const (theta B) (2 : ℝ)).div (hasDerivAt_base_rpow hB₀ (q := theta B))
    (by rw [bpow_theta hB]; norm_num) using 1
  · rfl
  · rw [bpow_theta hB]
    ring

private theorem defectFactor_theta {b θ : ℝ} (hθ : θ < 1) : defectFactor b θ θ = 1 := by
  simp [defectFactor, (sub_pos.mpr hθ).ne']

private theorem hasDerivAt_defectFactor {b θ : ℝ} (hb : 0 < b) (hθ : θ < 1) :
    HasDerivAt (defectFactor b θ) (Real.log b - 1 / (1 - θ)) θ := by
  have hlin := ((hasDerivAt_const θ (1 : ℝ)).sub (hasDerivAt_id θ)).div_const (1 - θ)
  have hsub : HasDerivAt (fun q : ℝ => q - θ) 1 θ := (hasDerivAt_id θ).sub_const θ
  have hpow := (hasDerivAt_base_rpow hb (q := θ - θ)).comp θ (h := fun q : ℝ => q - θ) hsub
  convert hlin.mul hpow using 1
  · rfl
  · change Real.log b - 1 / (1 - θ) =
      (0 - 1) / (1 - θ) * b ^ (θ - θ) +
        (1 - θ) / (1 - θ) * (Real.log b * b ^ (θ - θ) * 1)
    rw [sub_self θ, Real.rpow_zero, div_self (sub_pos.mpr hθ).ne']
    ring

private noncomputable def floorLog (B : ℝ) (n : ℕ) : ℝ :=
  (Real.log (floorSeq B n) - Real.log B) * floorSeq B n ^ theta B

private theorem floor_log_bounds {B : ℝ} (hB : 2 < B) {n : ℕ} (hn : 1 ≤ n) :
    let b := floorSeq B n
    let ρ := 2 / B
    (-ρ ^ n / floorSeq B 1 ≤ Real.log b ∧ Real.log b ≤ 0 ∧
      0 ≤ 1 - b ^ theta B ∧ 1 - b ^ theta B ≤ ρ ^ n) := by
  let b := floorSeq B n
  have hb := (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)
  have hb' := floorSeq_le_one hB n
  have hbpow : b ≤ b ^ theta B := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hb hb' (theta_lt_one hB).le
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hb)
  rw [Real.log_inv] at hlog
  have he : b⁻¹ - 1 = (1 - b) / b := by
    have hb'' : b ≠ 0 := hb.ne'
    field_simp [hb'']
  rw [he] at hlog
  have hb0 := floorSeq_one_pos hB
  have hle := div_le_div₀ (pow_nonneg (show 0 ≤ 2 / B by positivity) n)
    (one_sub_floorSeq_le hB n) hb0 (floorSeq_one_le hB hn)
  exact ⟨by rw [neg_div]; exact neg_le.mp (hlog.trans hle), Real.log_nonpos hb.le hb',
    sub_nonneg.mpr (Real.rpow_le_one hb.le hb' (theta_pos hB).le),
    (sub_le_sub_left hbpow _).trans (one_sub_floorSeq_le hB n)⟩

private theorem floorLog_error {B : ℝ} (hB : 2 < B) {n : ℕ} (hn : 1 ≤ n) :
    |floorLog B n + Real.log B| ≤ (Real.log B + (floorSeq B 1)⁻¹) * (2 / B) ^ n := by
  obtain ⟨hl, hl', hb, hb'⟩ := floor_log_bounds hB hn
  let b := floorSeq B n
  let a := Real.log B
  let ρ := 2 / B
  have ha : 0 ≤ a := (Real.log_pos (by linarith : 1 < B)).le
  have hb₀ : 0 ≤ b ^ theta B := Real.rpow_nonneg (floorSeq_nonneg hB n) _
  have hsplit : floorLog B n + a = Real.log b * b ^ theta B + a * (1 - b ^ theta B) := by
    dsimp [floorLog, b, a]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonpos hl', abs_of_nonneg hb₀,
    abs_of_nonneg ha, abs_of_nonneg hb, add_mul]
  have h₁ : -Real.log b * b ^ theta B ≤ ρ ^ n / floorSeq B 1 := by
    calc
      _ ≤ -Real.log b := mul_le_of_le_one_right (neg_nonneg.mpr hl') (by linarith)
      _ ≤ _ := by
        rw [neg_div] at hl
        exact neg_le.mp hl
  have h₂ := mul_le_mul_of_nonneg_left hb' ha
  change -Real.log b * b ^ theta B + a * (1 - b ^ theta B) ≤
    a * ρ ^ n + (floorSeq B 1)⁻¹ * ρ ^ n
  rw [add_comm (a * ρ ^ n), mul_comm (floorSeq B 1)⁻¹, ← div_eq_mul_inv]
  exact add_le_add h₁ h₂

private theorem floorLog_step_error {B : ℝ} (hB : 2 < B) {n : ℕ} (hn : 1 ≤ n) :
    floorLog B (n + 1) - floorLog B n * floorSeq B n ^ theta B ≤
      (3 * Real.log B + 2 * (floorSeq B 1)⁻¹) * (2 / B) ^ n := by
  let ρ := 2 / B
  let a := Real.log B
  let M := a + (floorSeq B 1)⁻¹
  let f := floorSeq B n ^ theta B
  have hρ : 0 ≤ ρ := by positivity
  have hρ' : ρ ≤ 1 := (div_le_one (by linarith)).2 hB.le
  have ha : 0 ≤ a := (Real.log_pos (by linarith : 1 < B)).le
  have hM : 0 ≤ M := add_nonneg ha (inv_nonneg.mpr (floorSeq_one_pos hB).le)
  have hf : 0 ≤ f := Real.rpow_nonneg (floorSeq_nonneg hB n) _
  have hff := (floor_log_bounds hB hn).2.2
  have h₁ := (le_abs_self _).trans (floorLog_error hB (n := n + 1) (by omega))
  have h₂ := (neg_le_abs _).trans (floorLog_error hB hn)
  have h₃ : -(floorLog B n + a) * f ≤ M * ρ ^ n := by
    refine (mul_le_mul_of_nonneg_right h₂ hf).trans (mul_le_of_le_one_right (by positivity) ?_)
    linarith [hff.1]
  have h₄ : floorLog B (n + 1) + a ≤ M * ρ ^ n := by
    exact h₁.trans (mul_le_mul_of_nonneg_left (by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hρ n) hρ') hM)
  have h₅ : 0 ≤ a * (1 - f) := mul_nonneg ha hff.1
  rw [show 3 * Real.log B + 2 * (floorSeq B 1)⁻¹ = 2 * M + a by dsimp only [M, a]; ring,
    add_mul, two_mul]
  change floorLog B (n + 1) - floorLog B n * f ≤ (M + M) * ρ ^ n + a * ρ ^ n
  nlinarith only [h₃, h₄, h₅, mul_nonneg ha (pow_nonneg hρ n)]

private theorem floorExcess_hasDerivAt {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    HasDerivAt (floorExcess μ B h n)
      (logDerivative μ B h n - Real.log (floorSeq B n) * floorSeq B n ^ theta B) (theta B) :=
  (hasDerivAt_realMoment_theta hpos hmean hB h n).sub
    (hasDerivAt_base_rpow ((floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)))

private theorem signedMoment_defect_step {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    let c := 2 * Real.log B - Real.log (floorSeq B 1 ^ 2) + 1 / (1 - theta B)
    let E := 3 * Real.log B + 2 * (floorSeq B 1)⁻¹
    tiltedLogMoment μ B h 1 (n + 1) + c * floorExcess μ B h (n + 1) (theta B) ≤
      tiltedMass μ B h n * (tiltedLogMoment μ B h 1 n + c * floorExcess μ B h n (theta B)) +
        E * (2 / B) ^ n := by
  let θ := theta B
  let u := inverseCoefficient B
  let k := defectFactor (floorSeq B 1 ^ 2) θ
  let J := fun i q => u q * floorExcess μ B h i q
  let a := Real.log B
  let A := tiltedMass μ B h n
  let H := fun i => tiltedLogMoment μ B h 1 i
  let f := fun q : ℝ => floorSeq B n ^ q
  let d := floorDefect μ B h n θ
  let y := floorExcess μ B h n θ
  let y' := floorExcess μ B h (n + 1) θ
  let κ := Real.log (floorSeq B 1 ^ 2) - 1 / (1 - θ)
  let c := 2 * a - κ
  let E := 3 * a + 2 * (floorSeq B 1)⁻¹
  have hc : 0 ≤ c := by
    have ha := Real.log_pos (show 1 < B by linarith)
    have hf := pow_le_one₀ (floorSeq_nonneg hB 1) (floorSeq_le_one hB 1) (n := 2)
    have hlog := Real.log_nonpos (sq_nonneg (floorSeq B 1)) hf
    have hθ := theta_lt_one hB
    change 0 ≤ 2 * Real.log B - (Real.log (floorSeq B 1 ^ 2) - 1 / (1 - theta B))
    linarith only [ha, hlog, one_div_nonneg.mpr (sub_nonneg.mpr hθ.le)]
  have hu : u θ = 1 := inverseCoefficient_theta hB
  have hk : k θ = 1 := defectFactor_theta (theta_lt_one hB)
  have hdd := hasDerivAt_defectFactor (sq_pos_of_pos (floorSeq_one_pos hB)) (theta_lt_one hB)
  have hdu := hasDerivAt_inverseCoefficient hB
  have hdf := hasDerivAt_base_rpow (q := θ)
    ((floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn))
  have hJ (i : ℕ) (hi : 1 ≤ i) : HasDerivAt (J i) (H i - floorLog B i) θ := by
    have hd := hdu.mul (floorExcess_hasDerivAt hpos hmean hB h hi)
    change HasDerivAt (J i) _ θ at hd
    change HasDerivAt (J i)
      ((-a) * floorExcess μ B h i θ + u θ *
        (logDerivative μ B h i - Real.log (floorSeq B i) * floorSeq B i ^ θ)) θ at hd
    rw [hu] at hd
    convert hd using 1
    unfold floorLog logDerivative floorExcess realMoment tiltedMass
    dsimp [H, a, θ]
    ring
  have hJh (i : ℕ) : J i θ = floorExcess μ B h i θ := by dsimp [J]; rw [hu, one_mul]
  let g := fun q => u q * f q * J n q + J n q ^ 2 / 2 - u q ^ 2 * k q * d / 2
  have hrec := floorExcess_recursion hpos hmean hB h hn ⟨theta_pos hB, theta_lt_one hB⟩
  rw [bpow_theta hB] at hrec
  change y' = (2 * f θ * y + y^2 - d) / 2 at hrec
  have hbase : J (n + 1) θ = g θ := by
    change J (n + 1) θ = u θ * f θ * J n θ + J n θ ^ 2 / 2 - u θ ^ 2 * k θ * d / 2
    rw [hu, hk, hJh, hJh]
    linarith
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, J (n + 1) (θ + t) ≤ g (θ + t) := by
    filter_upwards [eventual_add_lt (theta_lt_one hB)] with t ht
    let q := θ + t
    have htq : theta B ≤ q := le_add_of_nonneg_right ht.1.le
    have hrecq := floorExcess_recursion hpos hmean hB h hn
      ⟨(theta_pos hB).trans_le htq, ht.2⟩
    have hdq := (floorDefect_nonneg_compare hpos hmean hB h hn htq ht.2).2
    change k q * d ≤ floorDefect μ B h n q at hdq
    have hbq : 0 < B ^ q := Real.rpow_pos_of_pos (by linarith) _
    change J (n + 1) q ≤ g q
    dsimp [J, g, u, inverseCoefficient, f]
    rw [hrecq]
    field_simp
    nlinarith only [hdq]
  have hdg' := (((hdu.mul hdf).mul (hJ n hn)).add
    (((hJ n hn).pow 2).div_const 2)).sub
      ((((hdu.pow 2).mul hdd).mul_const d).div_const 2)
  change HasDerivAt g _ θ at hdg'
  have hdg : HasDerivAt g
      (A * (H n - floorLog B n) + floorLog B n * y + c * d / 2) θ := by
    convert hdg' using 1
    simp only [Pi.mul_apply, Pi.pow_apply, inverseCoefficient_theta hB,
      defectFactor_theta (theta_lt_one hB), hJh]
    rw [show J n (theta B) = y from hJh n]
    have hid : A = f θ + y := by unfold A f y floorExcess realMoment tiltedMass; ring
    rw [hid]
    dsimp only [floorLog, c, κ, θ, f, a]
    norm_num
    ring
  have hineq := deriv_le_of_right_comparison (hJ (n + 1) (by omega)) hdg hbase hbound
  have hfloor := floorLog_step_error hB hn
  have hy : 0 ≤ y := floorExcess_nonneg hpos hmean hB h n ⟨(theta_pos hB).le, (theta_lt_one hB).le⟩
  have hid : A = f θ + y := by unfold A f y floorExcess realMoment tiltedMass; ring
  have hdle : d / 2 ≤ A * y - y' := by
    rw [hid]
    nlinarith only [hrec, sq_nonneg y]
  have hdle' := mul_le_mul_of_nonneg_left hdle hc
  dsimp only
  rw [show 2 * Real.log B - Real.log (floorSeq B 1 ^ 2) + 1 / (1 - theta B) = c by
    dsimp only [c, κ, a, θ]; ring]
  change H (n + 1) + c * y' ≤ A * (H n + c * y) + E * (2 / B) ^ n
  change floorLog B (n + 1) - floorLog B n * f θ ≤ E * (2 / B) ^ n at hfloor
  rw [hid] at hineq ⊢ hdle'
  nlinarith only [hineq, hdle', hfloor]

open scoped BigOperators

private noncomputable def returnProduct (A : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, A i

private theorem returnProduct_succ (A : ℕ → ℝ) (n : ℕ) :
    returnProduct A (n + 1) = returnProduct A n * A n := Finset.prod_range_succ _ _

private theorem returnProduct_pos {A : ℕ → ℝ} (hA : ∀ n, 0 < A n) (n : ℕ) :
    0 < returnProduct A n := Finset.prod_pos fun i _ => hA i

private theorem returnProduct_classify {A : ℕ → ℝ} (hA : ∀ n, 0 < A n)
    {r K : ℝ} (hr : 0 ≤ r) (hr' : r < 1) (hK : 0 ≤ K)
    (hlog : ∀ n, -(K * r ^ (n + 1)) ≤ Real.log (A n)) :
    (∀ n m : ℕ, n ≤ m → Real.exp (-K / (1 - r)) ≤ returnProduct A m / returnProduct A n) ∧
    (Tendsto (returnProduct A) atTop atTop ∨ ∃ L > 0, Tendsto (returnProduct A) atTop (𝓝 L)) := by
  let P := returnProduct A
  let e := fun n : ℕ => K * r ^ (n + 1) / (1 - r)
  let Q := fun n => Real.log (P n) - e n
  have he (n : ℕ) : 0 ≤ e n := div_nonneg (by positivity) (sub_nonneg.mpr hr'.le)
  have he' (n : ℕ) : e n ≤ K / (1 - r) :=
    (div_le_div_iff_of_pos_right (sub_pos.mpr hr')).2
      (mul_le_of_le_one_right hK (pow_le_one₀ hr hr'.le))
  have hdiff (n : ℕ) : e n - e (n + 1) = K * r ^ (n + 1) := by
    dsimp [e]
    rw [pow_succ r (n + 1)]
    field_simp [ne_of_gt (sub_pos.mpr hr')]
  have hmono : Monotone Q := monotone_nat_of_le_succ fun n => by
    change Real.log (P n) - e n ≤ Real.log (P (n + 1)) - e (n + 1)
    rw [show P (n + 1) = P n * A n from returnProduct_succ A n,
      Real.log_mul (returnProduct_pos hA n).ne' (hA n).ne']
    linarith only [hdiff n, hlog n]
  have hpos (n : ℕ) : 0 < P n := returnProduct_pos hA n
  refine ⟨?_, ?_⟩
  · intro n m hnm
    have hnm' := hmono hnm
    change Real.log (P n) - e n ≤ Real.log (P m) - e m at hnm'
    change Real.exp (-K / (1 - r)) ≤ P m / P n
    rw [← Real.exp_log (div_pos (hpos m) (hpos n)), Real.exp_le_exp,
      Real.log_div (hpos m).ne' (hpos n).ne']
    rw [neg_div]
    linarith only [hnm', he m, he' n]
  · rcases tendsto_atTop_of_monotone hmono with ht | ⟨l, hl⟩
    · left
      have hlog' : Tendsto (fun n => Real.log (P n)) atTop atTop :=
        tendsto_atTop_mono (fun n => sub_le_self _ (he n)) ht
      have ht' := Real.tendsto_exp_atTop.comp hlog'
      exact ht'.congr fun n => Real.exp_log (hpos n)
    · right
      have hr0 := tendsto_pow_atTop_nhds_zero_of_lt_one hr hr'
      have her : Tendsto e atTop (𝓝 0) := by
        have htmp := ((hr0.comp (tendsto_add_atTop_nat 1)).const_mul K).div_const (1 - r)
        simpa only [Function.comp_def, mul_zero, zero_div] using htmp
      have hQ : Tendsto (fun n => Real.log (P n)) atTop (𝓝 l) := by
        convert hl.add her using 1
        · funext n
          dsimp [Q]
          ring
        · simp
      refine ⟨Real.exp l, Real.exp_pos _, ?_⟩
      exact ((Real.continuous_exp.continuousAt.tendsto.comp hQ)).congr
        (fun n => Real.exp_log (hpos n))

private theorem inverseCoefficient_pos_le_one {B q : ℝ} (hB : 2 < B) (hq : theta B ≤ q) :
    0 < inverseCoefficient B q ∧ inverseCoefficient B q ≤ 1 := by
  have hpos := Real.rpow_pos_of_pos (show 0 < B by linarith) q
  refine ⟨div_pos (by norm_num) hpos, (div_le_one hpos).2 ?_⟩
  rw [← bpow_theta hB]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) hq

private theorem defectFactor_nonneg_le_one {b θ q : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1)
    (hθ : θ ≤ q) (hq : q < 1) : 0 ≤ defectFactor b θ q ∧ defectFactor b θ q ≤ 1 := by
  have hθ' : 0 < 1 - θ := sub_pos.mpr (hθ.trans_lt hq)
  have hratio : 0 ≤ (1 - q) / (1 - θ) := div_nonneg (sub_nonneg.mpr hq.le) hθ'.le
  have hrat₁ : (1 - q) / (1 - θ) ≤ 1 := (div_le_one hθ').2 (by linarith)
  exact ⟨mul_nonneg hratio (Real.rpow_nonneg hb _),
    (mul_le_of_le_one_right hratio (Real.rpow_le_one hb hb' (sub_nonneg.mpr hθ))).trans hrat₁⟩

private noncomputable def excessFactor (B q : ℝ) : ℝ :=
  inverseCoefficient B q * defectFactor (floorSeq B 1 ^ 2) (theta B) q

private theorem excessFactor_theta {B : ℝ} (hB : 2 < B) : excessFactor B (theta B) = 1 := by
  simp [excessFactor, inverseCoefficient_theta hB, defectFactor_theta (theta_lt_one hB)]

private theorem floor_excess_comparison_step {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq : theta B ≤ q) (hq' : q < 1) :
    let Y := fun i => floorExcess μ B h i (theta B)
    let X := fun i => max (floorExcess μ B h i q - excessFactor B q * Y i) 0
    X (n + 1) ≤ inverseCoefficient B q *
      (tiltedMass μ B h n * X n + X n ^ 2 / 2) := by
  let θ := theta B
  let u := inverseCoefficient B q
  let k := defectFactor (floorSeq B 1 ^ 2) θ q
  let v := excessFactor B q
  let Y := fun i => floorExcess μ B h i θ
  let X := fun i => max (floorExcess μ B h i q - v * Y i) 0
  change X (n + 1) ≤ u * (tiltedMass μ B h n * X n + X n ^ 2 / 2)
  obtain ⟨hu, hu'⟩ := inverseCoefficient_pos_le_one hB hq
  obtain ⟨hk, hk'⟩ := defectFactor_nonneg_le_one (sq_nonneg (floorSeq B 1))
    (pow_le_one₀ (floorSeq_nonneg hB 1) (floorSeq_le_one hB 1)) hq hq'
  have hv : 0 ≤ v := mul_nonneg hu.le hk
  have hv' : v ≤ 1 := (mul_le_of_le_one_right hu.le hk').trans hu'
  have hb₀ := (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)
  have hf := Real.rpow_le_rpow_of_exponent_ge hb₀ (floorSeq_le_one hB n) hq
  have hf₀ := Real.rpow_nonneg hb₀.le q
  have hfθ := Real.rpow_nonneg hb₀.le θ
  have hy : 0 ≤ Y n := floorExcess_nonneg hpos hmean hB h n
    ⟨(theta_pos hB).le, (theta_lt_one hB).le⟩
  have hyq : 0 ≤ floorExcess μ B h n q := floorExcess_nonneg hpos hmean hB h n
    ⟨(theta_pos hB).le.trans hq, hq'.le⟩
  have hx : 0 ≤ X n := le_max_right _ _
  have hyx : floorExcess μ B h n q ≤ v * Y n + X n := by
    have hh : floorExcess μ B h n q - v * Y n ≤ X n := le_max_left _ _
    linarith
  have hstepq := floorExcess_recursion hpos hmean hB h hn ⟨(theta_pos hB).trans_le hq, hq'⟩
  have hstept := floorExcess_recursion hpos hmean hB h hn ⟨theta_pos hB, theta_lt_one hB⟩
  rw [bpow_theta hB] at hstept
  have hA : tiltedMass μ B h n = floorSeq B n ^ θ + Y n := by
    change realMoment μ B h n θ = floorSeq B n ^ θ + (realMoment μ B h n θ - floorSeq B n ^ θ)
    ring
  have hd := (floorDefect_nonneg_compare hpos hmean hB h hn hq hq').2
  have hqd : floorExcess μ B h (n + 1) q ≤
      u * (floorSeq B n ^ q * (v * Y n + X n) + (v * Y n + X n) ^ 2 / 2 -
        k * floorDefect μ B h n θ / 2) := by
    rw [hstepq]
    have hBq : 0 < B ^ q := Real.rpow_pos_of_pos (by linarith) q
    dsimp [u, inverseCoefficient]
    apply (div_le_iff₀ hBq).2
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hBq.ne']
    have h₁ := mul_le_mul_of_nonneg_left hyx hf₀
    have h₂ := pow_le_pow_left₀ hyq hyx 2
    linarith only [h₁, h₂, hd]
  have hfy : u * floorSeq B n ^ q ≤ floorSeq B n ^ θ :=
    (mul_le_of_le_one_left hf₀ hu').trans hf
  have hfy' : u * v ≤ 1 := (mul_le_of_le_one_right hu.le hv').trans hu'
  have hvy : v * Y n ≤ Y n := mul_le_of_le_one_left hy hv'
  have hvye : 0 ≤ v * Y n := mul_nonneg hv hy
  have h₁ := mul_le_mul_of_nonneg_right hfy hvye
  have h₂ := mul_le_mul_of_nonneg_right hfy' (mul_nonneg hvye hy)
  have h₃ := mul_le_mul_of_nonneg_right (add_le_add hf hvy) (mul_nonneg hu.le hx)
  have hdident : u * k = v := rfl
  have heq : u * (k * floorDefect μ B h n θ / 2) = v * floorDefect μ B h n θ / 2 := by
    rw [← hdident]
    ring
  change Y (n + 1) =
    (2 * floorSeq B n ^ θ * Y n + Y n ^ 2 - floorDefect μ B h n θ) / 2 at hstept
  change max (floorExcess μ B h (n + 1) q - v * Y (n + 1)) 0 ≤
    u * (tiltedMass μ B h n * X n + X n ^ 2 / 2)
  apply max_le
  · rw [hA]
    have hvstep := congrArg (fun x => v * x) hstept
    nlinarith only [hqd, hvstep, heq, h₁, h₂, h₃]
  · rw [hA]
    positivity

private theorem critical_floor_product_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {C : ℝ}
    (hC : ∀ n : ℕ, 1 ≤ n → tiltedMass μ B (criticalPoint μ B) n ≤ (B - 1) ^ theta B ∧
      tiltedLogMoment μ B (criticalPoint μ B) 1 n ≤ C * (2 / B) ^ n)
    (hclass : Tendsto (returnProduct (fun n => tiltedMass μ B (criticalPoint μ B) (n + 1))) atTop atTop ∨
      ∃ L > 0, Tendsto (returnProduct (fun n => tiltedMass μ B (criticalPoint μ B) (n + 1))) atTop (𝓝 L)) :
    Tendsto (returnProduct (fun n => tiltedMass μ B (criticalPoint μ B) (n + 1))) atTop atTop := by
  rcases hclass with ht | ⟨L, hL, hP⟩
  · exact ht
  exfalso
  let h := criticalPoint μ B
  let θ := theta B
  let a := Real.log B
  let ρ := 2 / B
  let A := fun n : ℕ => tiltedMass μ B h (n + 1)
  let P := returnProduct A
  let Y := fun n q => floorExcess μ B h (n + 1) q
  let v := excessFactor B
  let κ := Real.log (floorSeq B 1 ^ 2) - 1 / (1 - θ)
  have ha : 0 < a := Real.log_pos (by linarith)
  have hρ : 0 ≤ ρ := div_nonneg (by norm_num) (by linarith)
  have hρ' : ρ < 1 := (div_lt_one (by linarith)).2 hB
  have hb (n : ℕ) : 0 < floorSeq B (n + 1) :=
    (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB (by omega))
  have hA (n : ℕ) : 0 < A n :=
    (Real.rpow_pos_of_pos (hb n) _).trans_le
      (realMoment_floor_bound hpos hmean hB h _ (theta_pos hB).le (theta_lt_one hB).le)
  have hp (n : ℕ) : 0 < P n := returnProduct_pos hA n
  change Tendsto P atTop (𝓝 L) at hP
  have hAlim : Tendsto A atTop (𝓝 1) := by
    have ht := ((hP.comp (tendsto_add_atTop_nat 1)).div hP hL.ne')
    rw [div_self hL.ne'] at ht
    refine ht.congr fun n => ?_
    change P (n + 1) / P n = A n
    rw [show P (n + 1) = P n * A n from returnProduct_succ A n, mul_comm,
      mul_div_cancel_right₀ _ (hp n).ne']
  have hflim := (tendsto_floorSeq hB).comp (tendsto_add_atTop_nat 1)
  have hfpow : Tendsto (fun n => floorSeq B (n + 1) ^ θ) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.one_rpow] using
      (Real.continuous_rpow_const (theta_pos hB).le).continuousAt.tendsto.comp hflim
  have hloglim : Tendsto (fun n => Real.log (floorSeq B (n + 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hflim
  have hY : Tendsto (fun n => Y n θ) atTop (𝓝 0) := by simpa [Y, floorExcess, A, tiltedMass, realMoment] using hAlim.sub hfpow
  have herr : Tendsto (fun n : ℕ => C * ρ ^ (n + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ').comp (tendsto_add_atTop_nat 1)).const_mul C
  let U := fun n : ℕ => C * ρ ^ (n + 1) + a * A n -
    Real.log (floorSeq B (n + 1)) * floorSeq B (n + 1) ^ θ - (κ - a) * Y n θ
  have hU : Tendsto U atTop (𝓝 a) := by
    simpa only [U, mul_zero, zero_mul, mul_one, zero_add, sub_zero] using
      (((herr.add (hAlim.const_mul a)).sub (hloglim.mul hfpow)).sub (hY.const_mul (κ - a)))
  have hevP := hP.eventually (Ioo_mem_nhds
    (show (99 / 100 : ℝ) * L < L by linarith)
    (show L < (101 / 100 : ℝ) * L by linarith))
  have hevA := hAlim.eventually (lt_mem_nhds (show (9 / 10 : ℝ) < 1 by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hevP.and hevA).and
    (hU.eventually (gt_mem_nhds (show a < 5 * a / 4 by linarith))))
  have hratio (n : ℕ) (hn : N ≤ n) : P n / P N ≤ 11 / 10 := by
    apply (div_le_iff₀ (hp N)).2
    have hlow : (99 / 100 : ℝ) * L < P N := (hN N le_rfl).1.1.1
    have hupp : P n < (101 / 100 : ℝ) * L := (hN n hn).1.1.2
    linarith
  have hvl := (hasDerivAt_inverseCoefficient hB).mul
    (hasDerivAt_defectFactor (sq_pos_of_pos (floorSeq_one_pos hB)) (theta_lt_one hB))
  have hv' : HasDerivAt v (κ - a) θ := by
    change HasDerivAt v ((-a) * defectFactor (floorSeq B 1 ^ 2) θ θ +
      inverseCoefficient B θ * κ) θ at hvl
    rw [defectFactor_theta (theta_lt_one hB), inverseCoefficient_theta hB] at hvl
    simpa only [mul_one, one_mul, sub_eq_add_neg, add_comm] using hvl
  let init := fun q => Y N q - v q * Y N θ
  have hinit : init θ = 0 := by dsimp [init, v]; rw [excessFactor_theta hB]; ring
  have hinitd := (floorExcess_hasDerivAt hpos hmean hB h (n := N + 1) (by omega)).sub
    (hv'.mul_const (Y N θ))
  let d := logDerivative μ B h (N + 1) - Real.log (floorSeq B (N + 1)) *
    floorSeq B (N + 1) ^ θ - (κ - a) * Y N θ
  have hderiv : HasDerivAt init d θ := hinitd
  have hd₁ : d ≤ U N := by
    dsimp only [d, U, logDerivative]
    linarith only [(hC (N + 1) (by omega)).2]
  have hd₂ : d < 3 * a / 2 := by linarith [ (hN N le_rfl).2]
  have hevinit := hderiv.tendsto_slope_zero_right.eventually (gt_mem_nhds hd₂)
  obtain ⟨t, ht, ht'⟩ := (hevinit.and (eventual_add_lt (theta_lt_one hB))).exists
  let q := θ + t
  have hq : theta B < q := lt_add_of_pos_right _ ht'.1
  have hq' : q < 1 := ht'.2
  have hinitupper : init q ≤ 3 * a * t / 2 := by
    have hh : t⁻¹ * (init (θ + t) - init θ) < 3 * a / 2 := ht
    rw [hinit, sub_zero, inv_mul_eq_div] at hh
    have hw := (div_lt_iff₀ ht'.1).1 hh
    linarith
  let X := fun n => max (Y n q - v q * Y n θ) 0
  let z := 3 * a * t / 2
  have htt := ht'.1
  have hz : 0 ≤ z := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha.le) htt.le) (by norm_num)
  have hX₀ : X N ≤ z := max_le hinitupper hz
  have hgap : 2 * a * t ≤ B ^ q - 2 := by
    have hB₀ : 0 < B := by linarith
    have hid : B ^ q = 2 * Real.exp (a * t) := by
      change B ^ (theta B + t) = _
      rw [Real.rpow_add hB₀, bpow_theta hB, Real.rpow_def_of_pos hB₀]
    rw [hid]
    linarith only [Real.add_one_le_exp (a * t)]
  have hX (k : ℕ) : X (N + k) ≤ P (N + k) / P N * z := by
    induction k with
    | zero => simpa [div_self (hp N).ne'] using hX₀
    | succ k ih =>
      let n := N + k
      have hn : N ≤ n := by dsimp [n]; omega
      have hAn : (9 / 10 : ℝ) < A n := (hN n hn).1.2
      have hleg : X n ≤ A n * (B ^ q - 2) := by
        have h₁ := ih.trans (mul_le_mul_of_nonneg_right (hratio n hn) hz)
        have h₂ := mul_le_mul_of_nonneg_left hgap (hA n).le
        have h₃ := mul_le_mul_of_nonneg_right hAn.le (show 0 ≤ 2 * a * t by positivity)
        change X n ≤ (11 / 10) * (3 * a * t / 2) at h₁
        nlinarith only [h₁, h₂, h₃, mul_nonneg ha.le htt.le]
      have hx : 0 ≤ X n := le_max_right _ _
      have hBq : 0 < B ^ q := Real.rpow_pos_of_pos (by linarith) _
      have hun : inverseCoefficient B q * (A n + X n / 2) ≤ A n := by
        unfold inverseCoefficient
        rw [div_mul_eq_mul_div, div_le_iff₀ hBq]
        linarith only [hleg]
      have hs := floor_excess_comparison_step hpos hmean hB h (n := n + 1) (by omega) hq.le hq'
      change X (n + 1) ≤ inverseCoefficient B q * (A n * X n + X n ^ 2 / 2) at hs
      have hh : inverseCoefficient B q * (A n * X n + X n ^ 2 / 2) =
          (inverseCoefficient B q * (A n + X n / 2)) * X n := by ring
      change X (n + 1) ≤ P (n + 1) / P N * z
      rw [show P (n + 1) = P n * A n from returnProduct_succ A n]
      calc
        _ ≤ A n * X n := hs.trans (hh ▸ mul_le_mul_of_nonneg_right hun hx)
        _ ≤ A n * (P n / P N * z) := mul_le_mul_of_nonneg_left ih (hA n).le
        _ = _ := by ring
  have hV : 0 ≤ v q ∧ v q ≤ 1 := by
    obtain ⟨hu, hu'⟩ := inverseCoefficient_pos_le_one hB hq.le
    obtain ⟨hk, hk'⟩ := defectFactor_nonneg_le_one (sq_nonneg (floorSeq B 1))
      (pow_le_one₀ (floorSeq_nonneg hB 1) (floorSeq_le_one hB 1)) hq.le hq'
    exact ⟨mul_nonneg hu.le hk, (mul_le_of_le_one_right hu.le hk').trans hu'⟩
  apply no_bounded_moment_above_theta hpos hmean hB hshift hq hq'
  refine ⟨1 + (B - 1) ^ theta B + 11 / 10 * z, ?_⟩
  filter_upwards [eventually_ge_atTop (N + 1)] with i hi
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have hn : N ≤ n := by omega
  have hxn : X n ≤ 11 / 10 * z := by
    have hh := hX (n - N)
    rw [Nat.add_sub_of_le hn] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hratio n hn) hz)
  have hy : 0 ≤ Y n θ :=
    floorExcess_nonneg hpos hmean hB h _ ⟨(theta_pos hB).le, (theta_lt_one hB).le⟩
  have hyb : Y n θ ≤ A n := by
    exact sub_le_self _ (Real.rpow_nonneg (floorSeq_nonneg hB _) _)
  have hxyn : Y n q ≤ v q * Y n θ + X n := by
    have hh : Y n q - v q * Y n θ ≤ X n := le_max_left _ _
    linarith
  have hfq := Real.rpow_le_one (floorSeq_nonneg hB (n + 1)) (floorSeq_le_one hB (n + 1))
    ((theta_pos hB).trans hq).le
  have hyt := (mul_le_of_le_one_left hy hV.2).trans (hyb.trans (hC (n + 1) (by omega)).1)
  rw [show realMoment μ B h (n + 1) q = Y n q + floorSeq B (n + 1) ^ q by
    dsimp only [Y, floorExcess]; ring]
  linarith only [hxyn, hxn, hfq, hyt]

private theorem product_backward_bound {A V : ℕ → ℝ} (hA : ∀ n, 0 < A n)
    {r D E M : ℝ} (hr : 0 ≤ r) (hr' : r < 1) (hD : 0 < D) (hE : 0 ≤ E)
    (hratio : ∀ n m : ℕ, n ≤ m → D ≤ returnProduct A m / returnProduct A n)
    (hP : Tendsto (returnProduct A) atTop atTop) (hV : ∀ n, |V n| ≤ M)
    (hstep : ∀ n, V (n + 1) ≤ A n * V n + E * r ^ (n + 1)) (n : ℕ) :
    -(E / D / (1 - r) * r ^ (n + 1)) ≤ V n := by
  let P := returnProduct A
  let Z := fun k : ℕ => V (n + k) * P n / P (n + k)
  let T := fun k : ℕ => E / D / (1 - r) * r ^ (n + k + 1)
  have hpos (n : ℕ) : 0 < P n := returnProduct_pos hA n
  have hT (k : ℕ) : T k - T (k + 1) = E / D * r ^ (n + k + 1) := by
    dsimp only [T]
    rw [show n + (k + 1) + 1 = n + k + 1 + 1 by omega, pow_succ]
    field_simp [ne_of_gt (sub_pos.mpr hr')] <;> ring
  have hZ (k : ℕ) : Z (k + 1) ≤ Z k + E / D * r ^ (n + k + 1) := by
    let j := n + k
    have hratio' : P n / P (j + 1) ≤ 1 / D := by
      rw [div_le_div_iff₀ (hpos _) hD]
      simpa only [one_mul, mul_comm] using
        (le_div_iff₀ (hpos n)).1 (hratio n (j + 1) (by dsimp [j]; omega))
    have hu : 0 ≤ E * r ^ (j + 1) := by positivity
    have h := mul_le_mul_of_nonneg_right (hstep j) ((div_nonneg (hpos n).le (hpos (j + 1)).le))
    have herr := mul_le_mul_of_nonneg_left hratio' hu
    change V (j + 1) * P n / P (j + 1) ≤ V j * P n / P j + E / D * r ^ (j + 1)
    have hcancel : (A j * V j) * (P n / P (j + 1)) = V j * P n / P j := by
      rw [show P (j + 1) = P j * A j from returnProduct_succ A j]
      field_simp [(hA j).ne', (hpos j).ne'] <;> ring
    rw [add_mul, hcancel] at h
    linarith only [h, herr,
      show E * r ^ (j + 1) * (1 / D) = E / D * r ^ (j + 1) by ring,
      show V (j + 1) * (P n / P (j + 1)) = V (j + 1) * P n / P (j + 1) by ring]
  have hbound (k : ℕ) : Z k + T k ≤ V n + T 0 := by
    induction k with
    | zero =>
      have hz : Z 0 = V n := by
        change V n * P n / P n = V n
        rw [mul_div_cancel_right₀ _ (hpos n).ne']
      rw [hz]
    | succ k ih => linarith only [hZ k, hT k, ih]
  have hnlim : Tendsto (fun k : ℕ => n + k) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat n
  have hzlim : Tendsto Z atTop (𝓝 0) := by
    have hf := (hP.comp hnlim).inv_tendsto_atTop.const_mul (M * P n)
    rw [mul_zero] at hf
    refine squeeze_zero_norm' (f := Z) ?_ hf
    exact Eventually.of_forall fun k => by
      change ‖V (n + k) * P n / P (n + k)‖ ≤ M * P n * (P (n + k))⁻¹
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (hpos n), abs_of_pos (hpos _), ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hV _) (hpos n).le) (hpos _).le
  have htlim : Tendsto T atTop (𝓝 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr').comp
      ((tendsto_add_atTop_nat 1).comp hnlim)
    simpa only [T, Function.comp_def, mul_zero] using hp.const_mul (E / D / (1 - r))
  have hfinal : 0 ≤ V n + T 0 := by
    have hh := hzlim.add htlim
    rw [zero_add] at hh
    exact le_of_tendsto hh (Eventually.of_forall hbound)
  change 0 ≤ V n + E / D / (1 - r) * r ^ (n + 1) at hfinal
  linarith only [hfinal]

private theorem abs_tiltedLogMoment_one_le {μ : Measure ℝ}
    (hpos : ∀ᵐ w ∂μ, 0 < w) [IsProbabilityMeasure μ] {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) :
    |tiltedLogMoment μ B h 1 n| ≤ absTiltedLogMoment μ B h 1 n := by
  simp only [tiltedLogMoment, absTiltedLogMoment, pow_one, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  filter_upwards [ae_pos_lawR hpos hB h n] with x hx
  rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]

theorem criticalProduct_Hsmall_aux {B : ℝ} (hB : 2 < B) :
    ∃ C : ℝ, ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], (∀ᵐ w ∂μ, 0 < w) →
      ∫ w, w ∂μ = 1 → Real.log (B - 1) < criticalPoint μ B → ∀ n : ℕ, 1 ≤ n →
        |tiltedLogMoment μ B (criticalPoint μ B) 1 n| ≤
          C * (max (tiltedMass μ B (criticalPoint μ B) n - 1) 0 + (2 / B) ^ n) := by
  obtain ⟨C₀, hcritical⟩ := criticalMoments_aux hB
  let r := 2 / B
  let b := floorSeq B 1
  let a := Real.log B
  let c := 2 * a - Real.log (b ^ 2) + 1 / (1 - theta B)
  let E := 3 * a + 2 * b⁻¹
  let D := Real.exp (-b⁻¹ / (1 - r))
  let T := E / D / (1 - r)
  have hr : 0 ≤ r := div_nonneg (by norm_num) (by linarith)
  have hr' : r < 1 := (div_lt_one (by linarith)).2 hB
  have ha : 0 ≤ a := (Real.log_pos (by linarith : 1 < B)).le
  have hb : 0 < b := floorSeq_one_pos hB
  have hc : 0 ≤ c := by
    have h := Real.log_nonpos (sq_nonneg b) (pow_le_one₀ hb.le (floorSeq_le_one hB 1))
    exact add_nonneg (sub_nonneg.mpr (h.trans (by positivity)))
      (one_div_nonneg.mpr (sub_nonneg.mpr (theta_lt_one hB).le))
  have hE : 0 ≤ E := add_nonneg (mul_nonneg (by norm_num) ha)
    (mul_nonneg (by norm_num) (inv_nonneg.mpr hb.le))
  have hD : 0 < D := Real.exp_pos _
  have hT : 0 ≤ T := div_nonneg (div_nonneg hE hD.le) (sub_nonneg.mpr hr'.le)
  let C := max C₀ (c + T)
  have hC : 0 ≤ C := (add_nonneg hc hT).trans (le_max_right _ _)
  refine ⟨C, fun μ _ hpos hmean hshift n hn => ?_⟩
  let h := criticalPoint μ B
  let A := fun k : ℕ => tiltedMass μ B h (k + 1)
  let H := fun k : ℕ => tiltedLogMoment μ B h 1 (k + 1)
  let Y := fun k : ℕ => floorExcess μ B h (k + 1) (theta B)
  let V := fun k => H k + c * Y k
  have hzero : freeEnergy μ B h = 0 := (criticalPoint_isGreatest_aux hpos hmean hB).1
  obtain ⟨hAH, M, hM⟩ := hcritical μ hpos hmean h hzero
  have hfloor (k : ℕ) : floorSeq B (k + 1) ^ theta B ≤ A k :=
    realMoment_floor_bound hpos hmean hB h _ (theta_pos hB).le (theta_lt_one hB).le
  have hA (k : ℕ) : 0 < A k :=
    (Real.rpow_pos_of_pos (hb.trans_le (floorSeq_one_le hB (by omega))) _).trans_le (hfloor k)
  have hlog (k : ℕ) : -(b⁻¹ * r ^ (k + 1)) ≤ Real.log (A k) := by
    have hfb : 0 < floorSeq B (k + 1) := hb.trans_le (floorSeq_one_le hB (by omega))
    have hfbA : floorSeq B (k + 1) ≤ A k := by
      refine le_trans ?_ (hfloor k)
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge hfb (floorSeq_le_one hB _) (theta_lt_one hB).le
    have hlog' := (floor_log_bounds hB (n := k + 1) (by omega)).1
    have hh : -(b⁻¹ * r ^ (k + 1)) ≤ Real.log (floorSeq B (k + 1)) := by
      rw [mul_comm b⁻¹, ← neg_mul, ← div_eq_mul_inv]
      exact hlog'
    exact hh.trans (Real.log_le_log hfb hfbA)
  obtain ⟨hRat, hClass⟩ := returnProduct_classify hA hr hr' (inv_nonneg.mpr hb.le) hlog
  have hp := critical_floor_product_tendsto hpos hmean hB hshift hAH hClass
  have hY (k : ℕ) : 0 ≤ Y k := sub_nonneg.mpr (hfloor k)
  have hYb (k : ℕ) : Y k ≤ max (A k - 1) 0 + r ^ (k + 1) := by
    have hh := (floor_log_bounds hB (n := k + 1) (by omega)).2.2.2
    change 1 - floorSeq B (k + 1) ^ theta B ≤ r ^ (k + 1) at hh
    change A k - floorSeq B (k + 1) ^ theta B ≤ _
    linarith only [hh, le_max_left (A k - 1) 0]
  have hV (k : ℕ) : |V k| ≤ M + c * (B - 1) ^ theta B := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (abs_tiltedLogMoment_one_le hpos hB h (k + 1)).trans (hM _)
    · rw [abs_of_nonneg (mul_nonneg hc (hY k))]
      have hy : Y k ≤ A k := sub_le_self _ (Real.rpow_nonneg (floorSeq_nonneg hB _) _)
      exact mul_le_mul_of_nonneg_left (hy.trans (hAH _ (by omega)).1) hc
  have hstep (k : ℕ) : V (k + 1) ≤ A k * V k + E * r ^ (k + 1) := by
    have hh := signedMoment_defect_step hpos hmean hB h (n := k + 1) (by omega)
    change H (k + 1) + (2 * a - Real.log (b ^ 2) + 1 / (1 - theta B)) * Y (k + 1) ≤
      A k * (H k + (2 * a - Real.log (b ^ 2) + 1 / (1 - theta B)) * Y k) + E * r ^ (k + 1) at hh
    exact hh
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hlower := product_backward_bound hA hr hr' hD hE hRat hp hV hstep k
  change -(T * r ^ (k + 1)) ≤ H k + c * Y k at hlower
  change |H k| ≤ C * (max (A k - 1) 0 + r ^ (k + 1))
  apply abs_le.mpr
  have hsum : 0 ≤ max (A k - 1) 0 + r ^ (k + 1) := add_nonneg (le_max_right _ _) (by positivity)
  constructor
  · have h₁ := mul_le_mul_of_nonneg_left (hYb k) hc
    have h₂ := mul_le_mul_of_nonneg_left
      (show r ^ (k + 1) ≤ max (A k - 1) 0 + r ^ (k + 1) by
        linarith only [le_max_right (A k - 1) (0 : ℝ)]) hT
    have h₃ := mul_le_mul_of_nonneg_right (le_max_right C₀ (c + T)) hsum
    change (c + T) * (max (A k - 1) 0 + r ^ (k + 1)) ≤
      C * (max (A k - 1) 0 + r ^ (k + 1)) at h₃
    linarith only [hlower, h₁, h₂, h₃]
  · have hh : H k ≤ C₀ * r ^ (k + 1) := (hAH _ (by omega)).2
    exact hh.trans ((mul_le_mul_of_nonneg_right (le_max_left C₀ (c + T)) (pow_nonneg hr _)).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (le_max_right _ _)) hC))

end DiamondPinning
