module

public import DiamondPinning.Proofs.CompactnessProof

/-!
# Proof of `scaling:compactness`, part 2: the rescaled measures, the scaled window
bounds and the extraction

Continuation of `DiamondPinning.Proofs.CompactnessProof`. This module proves
`scaling_compactness_of`: the statement of `scaling_compactness`
(`DiamondPinning.Statements.Scaling`) with the conclusions of `criticalProduct`,
`response_transversality`, `windowMoments` and `window_derivBounds` as hypotheses.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Set
open scoped BoundedContinuousFunction

/-! ### Test functions with real weights -/

theorem exp_neg_mul_max_mem_Icc' (s x : ℝ) :
    Real.exp (-(max s 0 * max x 0)) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2
    (neg_nonpos.2 (mul_nonneg (le_max_right s 0) (le_max_right x 0)))⟩

/-- `x ↦ e^{-s max(x, 0)}` (for `s ≥ 0`) as a bounded continuous function. -/
noncomputable def expBCF (s : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => Real.exp (-(max s 0 * max x 0)),
      Real.continuous_exp.comp ((continuous_const.mul (continuous_id.max continuous_const)).neg)⟩
    1 fun x y => dist_le_one_of_mem_Icc (exp_neg_mul_max_mem_Icc' s x)
      (exp_neg_mul_max_mem_Icc' s y)

theorem expBCF_apply {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    expBCF s x = Real.exp (-(s * max x 0)) := by
  show Real.exp (-(max s 0 * max x 0)) = _
  rw [max_eq_left hs]

theorem expBCF_mem_Icc (s x : ℝ) : expBCF s x ∈ Set.Icc (0 : ℝ) 1 :=
  exp_neg_mul_max_mem_Icc' s x

theorem laplaceBCF_eq_expBCF (k : ℕ) : laplaceBCF k = expBCF k := by
  ext x
  rw [laplaceBCF_apply, expBCF_apply (Nat.cast_nonneg k)]

theorem dist_le_of_mem_Icc {x y K : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) K)
    (hy : y ∈ Set.Icc (0 : ℝ) K) : dist x y ≤ 2 * K := by
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem sevenHalves_mem_Icc (k : ℕ) (z : ℝ) :
    min (max z 0) (k : ℝ) ^ 3 * Real.sqrt (min (max z 0) k) ∈
      Set.Icc (0 : ℝ) ((k : ℝ) ^ 3 * Real.sqrt k) := by
  have h0 : 0 ≤ min (max z 0) (k : ℝ) := le_min (le_max_right _ _) (Nat.cast_nonneg k)
  have h1 : min (max z 0) (k : ℝ) ≤ k := min_le_right _ _
  refine ⟨by positivity, ?_⟩
  exact mul_le_mul (pow_le_pow_left₀ h0 h1 3) (Real.sqrt_le_sqrt h1)
    (Real.sqrt_nonneg _) (by positivity)

/-- `x ↦ min(max(x, 0), k)³ √(min(max(x, 0), k))`, a bounded continuous truncation of
`(x⁺)^{7/2}`. -/
noncomputable def sevenHalvesBCF (k : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min (max x 0) k ^ 3 * Real.sqrt (min (max x 0) k), by fun_prop⟩
    (2 * ((k : ℝ) ^ 3 * Real.sqrt k)) fun x y => dist_le_of_mem_Icc (sevenHalves_mem_Icc k x)
      (sevenHalves_mem_Icc k y)

theorem sevenHalvesBCF_apply (k : ℕ) (x : ℝ) :
    sevenHalvesBCF k x = min (max x 0) k ^ 3 * Real.sqrt (min (max x 0) k) := rfl

theorem sevenHalvesBCF_nonneg (k : ℕ) (x : ℝ) : 0 ≤ sevenHalvesBCF k x := by
  rw [sevenHalvesBCF_apply]
  have h0 : 0 ≤ min (max x 0) (k : ℝ) := le_min (le_max_right _ _) (Nat.cast_nonneg k)
  positivity

theorem sevenHalvesBCF_le (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    sevenHalvesBCF k x ≤ x ^ 3 * Real.sqrt x := by
  rw [sevenHalvesBCF_apply]
  have h0 : 0 ≤ min (max x 0) (k : ℝ) := le_min (le_max_right _ _) (Nat.cast_nonneg k)
  have h1 : min (max x 0) (k : ℝ) ≤ x := (min_le_left _ _).trans (max_le le_rfl hx)
  exact mul_le_mul (pow_le_pow_left₀ h0 h1 3) (Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg _)
    (by positivity)

/-! ### The rescaled measures -/

section Rescaled

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- Integrals against the rescaled measure `ν = N E[(R^θ - 1) 1{R ≥ 1} δ_{log R/(aN)}]`. -/
theorem integral_rescaledMeasure {B : ℝ} (hB : 2 < B) (h N : ℝ) (n : ℕ) (hN : 0 ≤ N)
    {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ x, g x ∂(rescaledMeasure μ B h N n) =
      ∫ x, (Set.Ici (1 : ℝ)).indicator
        (fun x => N * (x ^ theta B - 1) * g (Real.log x / (Real.log B * N))) x
        ∂(lawR μ B h n) := by
  rw [rescaledMeasure, integral_map (Real.measurable_log.div_const _).aemeasurable
      hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (f := fun x : ℝ => ENNReal.ofReal (N * (x ^ theta B - 1)))
      (ENNReal.measurable_ofReal.comp (measurable_const.mul
        ((measurable_id.pow_const _).sub measurable_const)))
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_indicator measurableSet_Ici]
  refine setIntegral_congr_fun measurableSet_Ici fun x hx => ?_
  have hx1 : (1 : ℝ) ≤ x := hx
  have hθ : 1 ≤ x ^ theta B := Real.one_le_rpow hx1 (theta_pos hB).le
  rw [ENNReal.toReal_ofReal (mul_nonneg hN (by linarith)), smul_eq_mul]

theorem isFiniteMeasure_rescaledMeasure (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1)
    {B : ℝ} (hB : 2 < B) (h : ℝ) {N : ℝ} (hN : 0 < N) (n : ℕ) :
    IsFiniteMeasure (rescaledMeasure μ B h N n) :=
  (rescaledMeasure_finite_aux hpos hmean hB h hN n).1

/-- The Laplace transform of the rescaled measure is the transform `L_{n,N}(s)` up to the
deterministic floor error. -/
theorem laplace_rescaled_bound (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ}
    (hB : 2 < B) (h N s : ℝ) {n : ℕ} (hn : 1 ≤ n) (hN : 0 < N) (hs : 0 ≤ s)
    (hsθ : s / (Real.log B * N) ≤ theta B) :
    |∫ x, expBCF s x ∂(rescaledMeasure μ B h N n) - transformAt μ B h N n s| ≤
      N * (1 - floorSeq B n) + s / (Real.log B * theta B) *
        ((tiltedMass μ B h n - 1) + (1 - floorSeq B n)) := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have ha := log_pos_of_two_lt hB
  have hθ0 := theta_pos hB
  have hθ1 := theta_lt_one hB
  have hu0 : 0 ≤ s / (Real.log B * N) := div_nonneg hs (mul_pos ha hN).le
  have hq : weightExponent B N s = theta B - s / (Real.log B * N) := rfl
  have hq0 : 0 ≤ weightExponent B N s := by rw [hq]; linarith
  have hq1 : weightExponent B N s ≤ 1 := by rw [hq]; linarith
  have hbn0 : 0 < floorSeq B n := lt_of_lt_of_le (floorSeq_one_pos hB) (floorSeq_one_le hB hn)
  have hbn1 : floorSeq B n ≤ 1 := floorSeq_le_one hB n
  have i0 := integrable_tiltedPow hpos hmean hB h n
  have iq : Integrable (fun x : ℝ => x ^ weightExponent B N s) (lawR μ B h n) :=
    integrable_rpow_lawR hpos hmean hB h hn hq1
  have hmeasE : Measurable fun x : ℝ => expBCF s (Real.log x / (Real.log B * N)) :=
    (expBCF s).continuous.measurable.comp (Real.measurable_log.div_const _)
  have hmeasI : Measurable ((Set.Ici (1 : ℝ)).indicator
      (fun x => N * (x ^ theta B - 1) * expBCF s (Real.log x / (Real.log B * N)))) :=
    ((measurable_const.mul ((measurable_id.pow_const _).sub measurable_const)).mul
      hmeasE).indicator measurableSet_Ici
  have iI : Integrable ((Set.Ici (1 : ℝ)).indicator
      (fun x => N * (x ^ theta B - 1) * expBCF s (Real.log x / (Real.log B * N))))
      (lawR μ B h n) := by
    have iB : Integrable (fun x : ℝ => N * (x ^ theta B + 1)) (lawR μ B h n) :=
      (i0.add (integrable_const 1)).const_mul N
    refine iB.mono' hmeasI.aestronglyMeasurable ?_
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    have hE := expBCF_mem_Icc s (Real.log x / (Real.log B * N))
    by_cases hx1 : x ∈ Set.Ici (1 : ℝ)
    · rw [Set.indicator_of_mem hx1, Real.norm_eq_abs]
      have h1 : 1 ≤ x ^ theta B := Real.one_le_rpow hx1 hθ0.le
      rw [abs_mul, abs_mul, abs_of_pos hN, abs_of_nonneg (by linarith : 0 ≤ x ^ theta B - 1),
        abs_of_nonneg hE.1]
      have h2 : N * (x ^ theta B - 1) * expBCF s (Real.log x / (Real.log B * N)) ≤
          N * (x ^ theta B - 1) * 1 :=
        mul_le_mul_of_nonneg_left hE.2 (mul_nonneg hN.le (by linarith))
      show N * (x ^ theta B - 1) * expBCF s (Real.log x / (Real.log B * N)) ≤
        N * (x ^ theta B + 1)
      nlinarith
    · rw [Set.indicator_of_notMem hx1, norm_zero]
      exact mul_nonneg hN.le (by have := Real.rpow_pos_of_pos hx (theta B); linarith)
  have iq1 : Integrable (fun x : ℝ => N * (x ^ weightExponent B N s - 1)) (lawR μ B h n) :=
    (iq.sub (integrable_const 1)).const_mul N
  -- the integral identity
  have hint : ∫ x, expBCF s x ∂(rescaledMeasure μ B h N n) - transformAt μ B h N n s =
      ∫ x, ((Set.Ici (1 : ℝ)).indicator
        (fun x => N * (x ^ theta B - 1) * expBCF s (Real.log x / (Real.log B * N))) x -
          N * (x ^ weightExponent B N s - 1)) ∂(lawR μ B h n) := by
    rw [integral_rescaledMeasure hB h N n hN.le (expBCF s).continuous.measurable,
      integral_sub iI iq1, integral_const_mul,
      integral_sub iq (integrable_const 1), transformAt, realMoment]
    simp
  -- pointwise bounds
  have hpt : ∀ᵐ x ∂(lawR μ B h n), 0 ≤ (Set.Ici (1 : ℝ)).indicator
        (fun x => N * (x ^ theta B - 1) * expBCF s (Real.log x / (Real.log B * N))) x -
          N * (x ^ weightExponent B N s - 1) ∧
      (Set.Ici (1 : ℝ)).indicator
        (fun x => N * (x ^ theta B - 1) * expBCF s (Real.log x / (Real.log B * N))) x -
          N * (x ^ weightExponent B N s - 1) ≤
        N * (1 - floorSeq B n) + s / (Real.log B * theta B) * (x ^ theta B - floorSeq B n) := by
    filter_upwards [ae_pos_lawR hpos hB h n, ae_floorSeq_le_lawR hpos hB h n] with x hx hxb
    have hθx : x ≤ 1 → x ≤ x ^ theta B := fun hx1 => by
      simpa using Real.rpow_le_rpow_of_exponent_ge hx hx1 hθ1.le
    by_cases hx1 : x ∈ Set.Ici (1 : ℝ)
    · have hx1' : (1 : ℝ) ≤ x := hx1
      rw [Set.indicator_of_mem hx1]
      have hw : 0 ≤ Real.log x := Real.log_nonneg hx1'
      have hxq : x ^ weightExponent B N s =
          x ^ theta B * Real.exp (-(Real.log x * (s / (Real.log B * N)))) := by
        rw [hq, Real.rpow_sub hx, Real.rpow_def_of_pos hx (s / (Real.log B * N)), Real.exp_neg,
          div_eq_mul_inv]
      have hE : expBCF s (Real.log x / (Real.log B * N)) =
          Real.exp (-(Real.log x * (s / (Real.log B * N)))) := by
        rw [expBCF_apply hs, max_eq_left (div_nonneg hw (mul_pos ha hN).le)]
        congr 1
        ring
      rw [hE, hxq]
      set e := Real.exp (-(Real.log x * (s / (Real.log B * N)))) with he
      have he1 : e ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hw hu0))
      have he2 : 1 - Real.log x * (s / (Real.log B * N)) ≤ e := by
        have := Real.add_one_le_exp (-(Real.log x * (s / (Real.log B * N))))
        linarith
      have hlog : theta B * Real.log x ≤ x ^ theta B - 1 := by
        have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (theta B))
        rwa [Real.log_rpow hx] at this
      have hid : N * (x ^ theta B - 1) * e - N * (x ^ theta B * e - 1) = N * (1 - e) := by ring
      rw [hid]
      constructor
      · exact mul_nonneg hN.le (by linarith)
      · have k1 : N * (1 - e) ≤ s / Real.log B * Real.log x := by
          have : N * (1 - e) ≤ N * (Real.log x * (s / (Real.log B * N))) :=
            mul_le_mul_of_nonneg_left (by linarith) hN.le
          calc N * (1 - e) ≤ N * (Real.log x * (s / (Real.log B * N))) := this
            _ = s / Real.log B * Real.log x := by field_simp
        have k2 : s / Real.log B * Real.log x ≤ s / (Real.log B * theta B) * (x ^ theta B - 1) := by
          rw [show s / (Real.log B * theta B) * (x ^ theta B - 1) =
            s / Real.log B * ((x ^ theta B - 1) / theta B) by field_simp]
          exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hθ0).2 (by linarith))
            (div_nonneg hs ha.le)
        have k3 : 0 ≤ N * (1 - floorSeq B n) := mul_nonneg hN.le (by linarith)
        have k4 : s / (Real.log B * theta B) * (x ^ theta B - 1) ≤
            s / (Real.log B * theta B) * (x ^ theta B - floorSeq B n) :=
          mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hs (mul_pos ha hθ0).le)
        linarith
    · have hx1' : x < 1 := lt_of_not_ge hx1
      rw [Set.indicator_of_notMem hx1, zero_sub]
      have hxq1 : x ^ weightExponent B N s ≤ 1 := Real.rpow_le_one hx.le hx1'.le hq0
      have hxq2 : x ≤ x ^ weightExponent B N s := by
        simpa using Real.rpow_le_rpow_of_exponent_ge hx hx1'.le hq1
      have hxθ := hθx hx1'.le
      constructor
      · nlinarith
      · have k1 : -(N * (x ^ weightExponent B N s - 1)) ≤ N * (1 - floorSeq B n) := by
          nlinarith
        have k2 : 0 ≤ s / (Real.log B * theta B) * (x ^ theta B - floorSeq B n) :=
          mul_nonneg (div_nonneg hs (mul_pos ha hθ0).le) (by linarith)
        linarith
  have iθb : Integrable (fun x : ℝ => s / (Real.log B * theta B) * (x ^ theta B - floorSeq B n))
      (lawR μ B h n) := (i0.sub (integrable_const _)).const_mul _
  have iG : Integrable (fun x : ℝ => N * (1 - floorSeq B n) +
      s / (Real.log B * theta B) * (x ^ theta B - floorSeq B n)) (lawR μ B h n) :=
    (integrable_const _).add iθb
  have iF : Integrable (fun x : ℝ => (Set.Ici (1 : ℝ)).indicator
        (fun x => N * (x ^ theta B - 1) * expBCF s (Real.log x / (Real.log B * N))) x -
          N * (x ^ weightExponent B N s - 1)) (lawR μ B h n) := iI.sub iq1
  rw [hint, abs_of_nonneg (integral_nonneg_of_ae (hpt.mono fun x hx => hx.1))]
  refine (integral_mono_ae iF iG (hpt.mono fun x hx => hx.2)).trans (le_of_eq ?_)
  rw [integral_add (integrable_const _) iθb, integral_const, integral_const_mul,
    integral_sub i0 (integrable_const _)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [tiltedMass]
  ring

/-- A tail bound for the rescaled measure from the first tilted logarithmic moment. -/
theorem tail_rescaled_bound (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ}
    (hB : 2 < B) (h N R : ℝ) {n : ℕ} (hn : 1 ≤ n) (hN : 0 < N) (hR : 0 < R) :
    (rescaledMeasure μ B h N n).real (Set.Ioi R) ≤
      (tiltedLogMoment μ B h 1 n + (Real.log B + 2 * (-Real.log (floorSeq B 1))) *
        tiltedMass μ B h n) / (Real.log B * R) := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  letI := isFiniteMeasure_rescaledMeasure hpos hmean hB h hN n
  have ha := log_pos_of_two_lt hB
  have hb1 : 0 < floorSeq B 1 := floorSeq_one_pos hB
  have hβ0 : 0 ≤ -Real.log (floorSeq B 1) :=
    neg_nonneg.2 (Real.log_nonpos hb1.le (floorSeq_le_one hB 1))
  have i0 := integrable_tiltedPow hpos hmean hB h n
  have i1 := integrable_tiltedLogPow hpos hmean hB h n 1
  have hmeasg : Measurable ((Set.Ioi R).indicator fun _ => (1 : ℝ)) :=
    measurable_const.indicator measurableSet_Ioi
  have heq : (rescaledMeasure μ B h N n).real (Set.Ioi R) =
      ∫ x, (Set.Ioi R).indicator (fun _ => (1 : ℝ)) x ∂(rescaledMeasure μ B h N n) := by
    rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_one]
  rw [heq, integral_rescaledMeasure hB h N n hN.le hmeasg]
  have iG : Integrable (fun x : ℝ => (x ^ theta B * (Real.log x - Real.log B) ^ 1 +
      (Real.log B + 2 * (-Real.log (floorSeq B 1))) * x ^ theta B) / (Real.log B * R))
      (lawR μ B h n) := (i1.add (i0.const_mul _)).div_const _
  have hpt : ∀ᵐ x ∂(lawR μ B h n), ‖(Set.Ici (1 : ℝ)).indicator (fun x => N * (x ^ theta B - 1) *
      (Set.Ioi R).indicator (fun _ => (1 : ℝ)) (Real.log x / (Real.log B * N))) x‖ ≤
      (x ^ theta B * (Real.log x - Real.log B) ^ 1 +
        (Real.log B + 2 * (-Real.log (floorSeq B 1))) * x ^ theta B) / (Real.log B * R) := by
    filter_upwards [ae_pos_lawR hpos hB h n, ae_floor_one_le hpos hB h hn] with x hx hxb
    have hθx : 0 < x ^ theta B := Real.rpow_pos_of_pos hx _
    have hlog : -(-Real.log (floorSeq B 1)) ≤ Real.log x := by
      rw [neg_neg]; exact Real.log_le_log hb1 hxb
    have hG0 : 0 ≤ (x ^ theta B * (Real.log x - Real.log B) ^ 1 +
        (Real.log B + 2 * (-Real.log (floorSeq B 1))) * x ^ theta B) / (Real.log B * R) := by
      apply div_nonneg _ (mul_pos ha hR).le
      have : x ^ theta B * (Real.log x - Real.log B) ^ 1 +
          (Real.log B + 2 * (-Real.log (floorSeq B 1))) * x ^ theta B =
          x ^ theta B * (Real.log x + 2 * (-Real.log (floorSeq B 1))) := by ring
      rw [this]
      exact mul_nonneg hθx.le (by linarith)
    by_cases hx1 : x ∈ Set.Ici (1 : ℝ)
    · rw [Set.indicator_of_mem hx1]
      have hx1' : (1 : ℝ) ≤ x := hx1
      by_cases hxR : Real.log x / (Real.log B * N) ∈ Set.Ioi R
      · rw [Set.indicator_of_mem hxR, mul_one, Real.norm_eq_abs]
        have h1 : 1 ≤ x ^ theta B := Real.one_le_rpow hx1' (theta_pos hB).le
        rw [abs_of_nonneg (mul_nonneg hN.le (by linarith))]
        have hxR' : R < Real.log x / (Real.log B * N) := hxR
        have hlx : 1 ≤ Real.log x / (Real.log B * N * R) := by
          rw [le_div_iff₀ (by positivity)]
          rw [lt_div_iff₀ (mul_pos ha hN)] at hxR'
          linarith
        calc N * (x ^ theta B - 1) ≤ N * x ^ theta B := by nlinarith
          _ ≤ N * x ^ theta B * (Real.log x / (Real.log B * N * R)) :=
              le_mul_of_one_le_right (by positivity) hlx
          _ = x ^ theta B * Real.log x / (Real.log B * R) := by field_simp
          _ ≤ _ := by
              apply div_le_div_of_nonneg_right _ (mul_pos ha hR).le
              have : x ^ theta B * Real.log x ≤
                  x ^ theta B * (Real.log x + 2 * (-Real.log (floorSeq B 1))) :=
                mul_le_mul_of_nonneg_left (by linarith) hθx.le
              linarith
      · rw [Set.indicator_of_notMem hxR, mul_zero, norm_zero]
        exact hG0
    · rw [Set.indicator_of_notMem hx1, norm_zero]
      exact hG0
  have hmeasF : Measurable ((Set.Ici (1 : ℝ)).indicator (fun x => N * (x ^ theta B - 1) *
      (Set.Ioi R).indicator (fun _ => (1 : ℝ)) (Real.log x / (Real.log B * N)))) :=
    ((measurable_const.mul ((measurable_id.pow_const _).sub measurable_const)).mul
      (hmeasg.comp (Real.measurable_log.div_const _))).indicator measurableSet_Ici
  refine (le_trans (le_abs_self _) ?_)
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le iG hpt).trans (le_of_eq ?_)
  rw [integral_div, integral_add i1 (i0.const_mul _), integral_const_mul]
  rfl

theorem cube_sqrt_le {l v a : ℝ} (hl : 0 ≤ l) (hv : 0 ≤ v) (ha : 0 ≤ a) (h : l ≤ v + a) :
    l ^ 3 * Real.sqrt l ≤ 12 * (v ^ 3 * Real.sqrt v + a ^ 3 * Real.sqrt a) := by
  set m := max v a with hm
  have hm0 : 0 ≤ m := le_max_of_le_left hv
  have hl2 : l ≤ 2 * m := by
    have := le_max_left v a; have := le_max_right v a; linarith
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h1 : l ^ 3 ≤ (2 * m) ^ 3 := pow_le_pow_left₀ hl hl2 3
  have h2 : Real.sqrt l ≤ 3 / 2 * Real.sqrt m := by
    calc Real.sqrt l ≤ Real.sqrt (2 * m) := Real.sqrt_le_sqrt hl2
      _ = Real.sqrt 2 * Real.sqrt m := Real.sqrt_mul (by norm_num) m
      _ ≤ 3 / 2 * Real.sqrt m := mul_le_mul_of_nonneg_right hs2 (Real.sqrt_nonneg m)
  have h3 : l ^ 3 * Real.sqrt l ≤ 12 * (m ^ 3 * Real.sqrt m) := by
    calc l ^ 3 * Real.sqrt l ≤ (2 * m) ^ 3 * (3 / 2 * Real.sqrt m) :=
          mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
      _ = 12 * (m ^ 3 * Real.sqrt m) := by ring
  have h4 : m ^ 3 * Real.sqrt m ≤ v ^ 3 * Real.sqrt v + a ^ 3 * Real.sqrt a := by
    rcases max_choice v a with h | h <;> rw [hm, h]
    · have : 0 ≤ a ^ 3 * Real.sqrt a := by positivity
      linarith
    · have : 0 ≤ v ^ 3 * Real.sqrt v := by positivity
      linarith
  linarith

/-- The truncated `7/2` moments of the rescaled measure are controlled by the `7/2` tilted
moment. -/
theorem sevenHalves_rescaled_bound (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ}
    (hB : 2 < B) (h N : ℝ) {n : ℕ} (hN : 0 < N) (k : ℕ) :
    ∫ x, sevenHalvesBCF k x ∂(rescaledMeasure μ B h N n) ≤
      12 / (Real.log B ^ 3 * Real.sqrt (Real.log B) * (N ^ 2 * Real.sqrt N)) *
        (absTiltedLogRpowMoment μ B h (7 / 2) n +
          Real.log B ^ 3 * Real.sqrt (Real.log B) * tiltedMass μ B h n) := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have ha := log_pos_of_two_lt hB
  set a := Real.log B with ha_def
  have i0 := integrable_tiltedPow hpos hmean hB h n
  have h72 := integrable_absTiltedLogRpow_aux hpos hmean hB h n (s := (7 : ℝ) / 2) (by norm_num)
  have h72' : Integrable (fun x : ℝ => x ^ theta B * (|Real.log x - a| ^ 3 *
      Real.sqrt |Real.log x - a|)) (lawR μ B h n) := by
    refine h72.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [rpow_seven_halves_mul_sqrt (abs_nonneg _)]
  set K := 12 / (a ^ 3 * Real.sqrt a * (N ^ 2 * Real.sqrt N)) with hK
  have hK0 : 0 ≤ K := by positivity
  have iG : Integrable (fun x : ℝ => K * (x ^ theta B * (|Real.log x - a| ^ 3 *
      Real.sqrt |Real.log x - a|) + a ^ 3 * Real.sqrt a * x ^ theta B)) (lawR μ B h n) :=
    (h72'.add (i0.const_mul _)).const_mul _
  rw [integral_rescaledMeasure hB h N n hN.le (sevenHalvesBCF k).continuous.measurable]
  have hpt : ∀ᵐ x ∂(lawR μ B h n), (Set.Ici (1 : ℝ)).indicator (fun x => N * (x ^ theta B - 1) *
      sevenHalvesBCF k (Real.log x / (a * N))) x ≤
      K * (x ^ theta B * (|Real.log x - a| ^ 3 * Real.sqrt |Real.log x - a|) +
        a ^ 3 * Real.sqrt a * x ^ theta B) := by
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    have hθx : 0 < x ^ theta B := Real.rpow_pos_of_pos hx _
    have hG0 : 0 ≤ K * (x ^ theta B * (|Real.log x - a| ^ 3 * Real.sqrt |Real.log x - a|) +
        a ^ 3 * Real.sqrt a * x ^ theta B) := by positivity
    by_cases hx1 : x ∈ Set.Ici (1 : ℝ)
    · rw [Set.indicator_of_mem hx1]
      have hx1' : (1 : ℝ) ≤ x := hx1
      have hl : 0 ≤ Real.log x := Real.log_nonneg hx1'
      have hw : 0 ≤ Real.log x / (a * N) := div_nonneg hl (mul_pos ha hN).le
      have h1 : 1 ≤ x ^ theta B := Real.one_le_rpow hx1' (theta_pos hB).le
      have hg := sevenHalvesBCF_le k hw
      have hg0 := sevenHalvesBCF_nonneg k (Real.log x / (a * N))
      have hcube := cube_sqrt_le hl (abs_nonneg (Real.log x - a)) ha.le
        (by have := le_abs_self (Real.log x - a); linarith)
      have hw' : (Real.log x / (a * N)) ^ 3 * Real.sqrt (Real.log x / (a * N)) =
          Real.log x ^ 3 * Real.sqrt (Real.log x) / (a ^ 3 * Real.sqrt a * (N ^ 3 * Real.sqrt N)) := by
        rw [Real.sqrt_div' _ (mul_pos ha hN).le, Real.sqrt_mul ha.le]
        field_simp
      calc N * (x ^ theta B - 1) * sevenHalvesBCF k (Real.log x / (a * N))
          ≤ N * x ^ theta B * ((Real.log x / (a * N)) ^ 3 * Real.sqrt (Real.log x / (a * N))) :=
            mul_le_mul (by nlinarith) hg hg0 (by positivity)
        _ = x ^ theta B * (Real.log x ^ 3 * Real.sqrt (Real.log x)) *
              (12 / (a ^ 3 * Real.sqrt a * (N ^ 2 * Real.sqrt N))) / 12 := by
            rw [hw']; field_simp
        _ ≤ x ^ theta B * (12 * (|Real.log x - a| ^ 3 * Real.sqrt |Real.log x - a| +
              a ^ 3 * Real.sqrt a)) * (12 / (a ^ 3 * Real.sqrt a * (N ^ 2 * Real.sqrt N))) / 12 := by
            gcongr
        _ = _ := by rw [hK]; ring
    · rw [Set.indicator_of_notMem hx1]
      exact hG0
  have hmeasF : Measurable ((Set.Ici (1 : ℝ)).indicator (fun x => N * (x ^ theta B - 1) *
      sevenHalvesBCF k (Real.log x / (a * N)))) :=
    ((measurable_const.mul ((measurable_id.pow_const _).sub measurable_const)).mul
      ((sevenHalvesBCF k).continuous.measurable.comp
        (Real.measurable_log.div_const _))).indicator measurableSet_Ici
  have iF : Integrable ((Set.Ici (1 : ℝ)).indicator (fun x => N * (x ^ theta B - 1) *
      sevenHalvesBCF k (Real.log x / (a * N)))) (lawR μ B h n) := by
    refine iG.mono' hmeasF.aestronglyMeasurable ?_
    filter_upwards [hpt] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hx
    · by_cases hx1 : x ∈ Set.Ici (1 : ℝ)
      · rw [Set.indicator_of_mem hx1]
        have hx1' : (1 : ℝ) ≤ x := hx1
        have h1 : 1 ≤ x ^ theta B := Real.one_le_rpow hx1' (theta_pos hB).le
        exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (sevenHalvesBCF_nonneg _ _)
      · rw [Set.indicator_of_notMem hx1]
  refine (integral_mono_ae iF iG hpt).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add h72' (i0.const_mul _), integral_const_mul]
  have e1 : ∫ x, x ^ theta B * (|Real.log x - a| ^ 3 * Real.sqrt |Real.log x - a|)
      ∂(lawR μ B h n) = absTiltedLogRpowMoment μ B h (7 / 2) n := by
    rw [absTiltedLogRpowMoment]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [rpow_seven_halves_mul_sqrt (abs_nonneg _)]
  rw [e1]
  rfl

end Rescaled

/-! ### The scaled window bounds -/

/-- The generation-level window bounds produced by `gen_window`. -/
def WinBounds (μ : Measure ℝ) (B : ℝ) (n₀ : ℕ) (η C c : ℝ) : Prop :=
  ∀ n : ℕ, n₀ ≤ n → ∀ u : ℝ, 0 ≤ u → u * ((n : ℝ) + 1) ^ 2 ≤ η →
    c / n - C * u * ((n : ℝ) + 1) ≤ tiltedMass μ B (criticalPoint μ B + u) n - 1 ∧
    tiltedMass μ B (criticalPoint μ B + u) n - 1 ≤ C / n + C * u * ((n : ℝ) + 1) ∧
    |tiltedLogMoment μ B (criticalPoint μ B + u) 1 n| ≤
      C / n + C * u * ((n : ℝ) + 1) ^ 2 + C * u ^ 2 * ((n : ℝ) + 1) ^ 4 ∧
    c * n - C * u * ((n : ℝ) + 1) ^ 3 ≤ tiltedLogMoment μ B (criticalPoint μ B + u) 2 n ∧
    tiltedLogMoment μ B (criticalPoint μ B + u) 2 n ≤ C * n + C * u * ((n : ℝ) + 1) ^ 3 ∧
    c * ((n : ℝ) + 1) ^ 2 - C * u * ((n : ℝ) + 1) ^ 4 ≤
      tiltedLogMoment μ B (criticalPoint μ B + u) 3 n ∧
    tiltedLogMoment μ B (criticalPoint μ B + u) 3 n ≤
      C * ((n : ℝ) + 1) ^ 2 + C * u * ((n : ℝ) + 1) ^ 4 ∧
    absTiltedLogRpowMoment μ B (criticalPoint μ B + u) (7 / 2) n ≤
      C * ((n : ℝ) + 1) ^ ((5 : ℝ) / 2)

/-- The generation-level matching estimate produced by `gen_window`. -/
def WinMatching (μ : Measure ℝ) (B κ ℓ₃ : ℝ) (η C : ℝ) : Prop :=
  ∀ ε > 0, ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∀ u : ℝ, 0 ≤ u → u * ((n : ℝ) + 1) ^ 2 ≤ η →
    |tiltedLogMoment μ B (criticalPoint μ B + u) 1 n -
        u * (κ / ℓ₃) * tiltedLogMoment μ B (criticalPoint μ B + u) 3 n| ≤
      C / n + ε * u * ((n : ℝ) + 1) ^ 2 + C * u ^ 2 * ((n : ℝ) + 1) ^ 4

/-- Elementary facts on `n = ⌊N t⌋` when `N t ≥ 2`. -/
theorem floor_facts {N t : ℝ} (hN : 0 < N) (ht : 0 < t) (hNt : 2 ≤ N * t) :
    let n := ⌊N * t⌋₊
    (1 : ℝ) ≤ n ∧ N * t / 2 ≤ n ∧ (n : ℝ) ≤ N * t ∧ N * t ≤ (n : ℝ) + 1 ∧
      (n : ℝ) + 1 ≤ 2 * (N * t) := by
  intro n
  have h1 : (n : ℝ) ≤ N * t := Nat.floor_le (by positivity)
  have h2 : N * t < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨by linarith, by linarith, h1, h2.le, by linarith⟩

theorem window_cond {lam N t : ℝ} (hlam : 0 ≤ lam) (hN : 0 < N) (hn1 : (⌊N * t⌋₊ : ℝ) + 1 ≤ 2 * (N * t))
    {η : ℝ} (hwin : lam * (2 * t) ^ 2 ≤ η) :
    lam / N ^ 2 * ((⌊N * t⌋₊ : ℝ) + 1) ^ 2 ≤ η := by
  have h0 : 0 ≤ (⌊N * t⌋₊ : ℝ) + 1 := by positivity
  have h1 : ((⌊N * t⌋₊ : ℝ) + 1) ^ 2 ≤ (2 * (N * t)) ^ 2 := pow_le_pow_left₀ h0 hn1 2
  calc lam / N ^ 2 * ((⌊N * t⌋₊ : ℝ) + 1) ^ 2 ≤ lam / N ^ 2 * (2 * (N * t)) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = lam * (2 * t) ^ 2 := by field_simp
    _ ≤ η := hwin

theorem scale_pow_le {K X t : ℝ} (hK : 0 ≤ K) (hX0 : 0 ≤ X) (hX : X ≤ 2 * t) (k : ℕ) :
    K * X ^ k ≤ K * 2 ^ k * t ^ k := by
  have := pow_le_pow_left₀ hX0 hX k
  rw [mul_pow] at this
  calc K * X ^ k ≤ K * (2 ^ k * t ^ k) := mul_le_mul_of_nonneg_left this hK
    _ = K * 2 ^ k * t ^ k := by ring

set_option maxHeartbeats 400000 in
-- eight scaled bounds share one elaboration
/-- The scaled window bounds at `n = ⌊N t⌋` and `u = λ/N²`. -/
theorem scaled_window {μ : Measure ℝ} {B : ℝ} (hB : 2 < B) {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C)
    (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) {lam N t : ℝ} (hlam : 0 ≤ lam) (hN : 0 < N)
    (ht : 0 < t) (hNt2 : 2 ≤ N * t) (hNt0 : (n₀ : ℝ) + 1 ≤ N * t) (hwin : lam * (2 * t) ^ 2 ≤ η) :
    n₀ ≤ ⌊N * t⌋₊ ∧ 1 ≤ ⌊N * t⌋₊ ∧
    c / t - 2 * C * lam * t ≤ scaledMass μ B lam N t ∧
    scaledMass μ B lam N t ≤ 2 * C / t + 2 * C * lam * t ∧
    |scaledDrift μ B lam N t| ≤
      (2 * C / (N * t) + 4 * C * lam * t ^ 2 + 16 * C * lam ^ 2 * t ^ 4) / Real.log B ∧
    (c * t / 2 - 8 * C * lam * t ^ 3) / Real.log B ^ 2 ≤ scaledSecond μ B lam N t ∧
    scaledSecond μ B lam N t ≤ (C * t + 8 * C * lam * t ^ 3) / Real.log B ^ 2 ∧
    (c * t ^ 2 - 16 * C * lam * t ^ 4) / Real.log B ^ 3 ≤ scaledThird μ B lam N t ∧
    scaledThird μ B lam N t ≤ (4 * C * t ^ 2 + 16 * C * lam * t ^ 4) / Real.log B ^ 3 ∧
    absTiltedLogRpowMoment μ B (scalingField μ B lam N) (7 / 2) ⌊N * t⌋₊ ≤
      8 * C * (N ^ 2 * Real.sqrt N) * (t ^ 2 * Real.sqrt t) := by
  obtain ⟨hn1, hnlo, hnhi, hn1lo, hn1hi⟩ := floor_facts hN ht hNt2
  set n := ⌊N * t⌋₊ with hn_def
  have ha := log_pos_of_two_lt hB
  have hnpos : (0 : ℝ) < n := by linarith
  have hn₀ : n₀ ≤ n := by
    have : ((n₀ : ℕ) : ℝ) < (n : ℝ) + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  have hu : 0 ≤ lam / N ^ 2 := by positivity
  have hun := window_cond hlam hN hn1hi hwin
  obtain ⟨wA1, wA2, wH, wK1, wK2, wJ1, wJ2, w72⟩ := hW n hn₀ (lam / N ^ 2) hu hun
  have hfield : scalingField μ B lam N = criticalPoint μ B + lam / N ^ 2 := rfl
  -- scaling identities
  have hX : ((n : ℝ) + 1) / N ≤ 2 * t := by rw [div_le_iff₀ hN]; linarith
  have hX0 : 0 ≤ ((n : ℝ) + 1) / N := by positivity
  have hY : (n : ℝ) / N ≤ t := by rw [div_le_iff₀ hN]; linarith
  have hY0 : t / 2 ≤ (n : ℝ) / N := by rw [le_div_iff₀ hN]; linarith
  have hNn1 : 1 / t ≤ N / n := by rw [div_le_div_iff₀ ht hnpos]; linarith
  have hNn2 : N / n ≤ 2 / t := by rw [div_le_div_iff₀ hnpos ht]; linarith
  have e1 : N * (C * (lam / N ^ 2) * ((n : ℝ) + 1)) = C * lam * (((n : ℝ) + 1) / N) := by
    field_simp
  have hsplit2 : ∀ x : ℝ, x / (Real.log B ^ 2 * N) = x / N / Real.log B ^ 2 := fun x => by
    rw [div_div, mul_comm]
  have hsplit3 : ∀ x : ℝ, x / (Real.log B ^ 3 * N ^ 2) = x / N ^ 2 / Real.log B ^ 3 := fun x => by
    rw [div_div, mul_comm]
  have e1' : C * lam * (((n : ℝ) + 1) / N) ≤ 2 * C * lam * t := by
    have := mul_le_mul_of_nonneg_left hX (by positivity : 0 ≤ C * lam)
    linarith
  refine ⟨hn₀, by exact_mod_cast hn1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- lower bound on `S_N`
    rw [scaledMass, ← hn_def, hfield]
    have k1 : c / t ≤ N * (c / n) := by
      rw [show N * (c / n) = c * (N / n) by ring, show c / t = c * (1 / t) by ring]
      exact mul_le_mul_of_nonneg_left hNn1 hc.le
    have k2 : N * (c / n - C * (lam / N ^ 2) * ((n : ℝ) + 1)) ≤
        N * (tiltedMass μ B (criticalPoint μ B + lam / N ^ 2) n - 1) :=
      mul_le_mul_of_nonneg_left wA1 hN.le
    rw [mul_sub, e1] at k2
    linarith
  · rw [scaledMass, ← hn_def, hfield]
    have k1 : N * (C / n) ≤ 2 * C / t := by
      rw [show N * (C / n) = C * (N / n) by ring, show 2 * C / t = C * (2 / t) by ring]
      exact mul_le_mul_of_nonneg_left hNn2 hC.le
    have k2 : N * (tiltedMass μ B (criticalPoint μ B + lam / N ^ 2) n - 1) ≤
        N * (C / n + C * (lam / N ^ 2) * ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left wA2 hN.le
    rw [mul_add, e1] at k2
    linarith
  · rw [scaledDrift, ← hn_def, hfield, abs_div, abs_of_pos ha]
    apply div_le_div_of_nonneg_right _ ha.le
    refine wH.trans ?_
    have k1 : C / n ≤ 2 * C / (N * t) := by
      rw [div_le_div_iff₀ hnpos (by positivity)]
      have := mul_le_mul_of_nonneg_left hnlo hC.le
      linarith
    have k2 : C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 2 ≤ 4 * C * lam * t ^ 2 := by
      have : C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 2 = C * lam * (((n : ℝ) + 1) / N) ^ 2 := by
        field_simp
      rw [this]
      have := scale_pow_le (K := C * lam) (by positivity) hX0 hX 2
      linarith
    have k3 : C * (lam / N ^ 2) ^ 2 * ((n : ℝ) + 1) ^ 4 ≤ 16 * C * lam ^ 2 * t ^ 4 := by
      have : C * (lam / N ^ 2) ^ 2 * ((n : ℝ) + 1) ^ 4 =
          C * lam ^ 2 * (((n : ℝ) + 1) / N) ^ 4 := by field_simp
      rw [this]
      have := scale_pow_le (K := C * lam ^ 2) (by positivity) hX0 hX 4
      linarith
    linarith
  · rw [scaledSecond, ← hn_def, hfield, hsplit2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have k1 : c * t / 2 ≤ c * ((n : ℝ) / N) := by
      have := mul_le_mul_of_nonneg_left hY0 hc.le
      linarith
    have k2 : C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 3 / N ≤ 8 * C * lam * t ^ 3 := by
      have : C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 3 / N = C * lam * (((n : ℝ) + 1) / N) ^ 3 := by
        field_simp
      rw [this]
      have := scale_pow_le (K := C * lam) (by positivity) hX0 hX 3
      linarith
    have k3 : (c * n - C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 3) / N ≤
        tiltedLogMoment μ B (criticalPoint μ B + lam / N ^ 2) 2 n / N :=
      div_le_div_of_nonneg_right wK1 hN.le
    have k4 : (c * n - C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 3) / N =
        c * ((n : ℝ) / N) - C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 3 / N := by ring
    linarith
  · rw [scaledSecond, ← hn_def, hfield, hsplit2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have k2 : C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 3 / N ≤ 8 * C * lam * t ^ 3 := by
      have : C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 3 / N = C * lam * (((n : ℝ) + 1) / N) ^ 3 := by
        field_simp
      rw [this]
      have := scale_pow_le (K := C * lam) (by positivity) hX0 hX 3
      linarith
    have k3 : tiltedLogMoment μ B (criticalPoint μ B + lam / N ^ 2) 2 n / N ≤
        (C * n + C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 3) / N :=
      div_le_div_of_nonneg_right wK2 hN.le
    have k4 : (C * n + C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 3) / N =
        C * ((n : ℝ) / N) + C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 3 / N := by ring
    have k6 : C * ((n : ℝ) / N) ≤ C * t := mul_le_mul_of_nonneg_left hY hC.le
    linarith
  · rw [scaledThird, ← hn_def, hfield, hsplit3]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hX1 : t ≤ ((n : ℝ) + 1) / N := by rw [le_div_iff₀ hN]; linarith
    have k1 : c * t ^ 2 ≤ c * (((n : ℝ) + 1) / N) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le hX1 2) hc.le
    have k2 : C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 4 / N ^ 2 ≤ 16 * C * lam * t ^ 4 := by
      have : C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 4 / N ^ 2 =
          C * lam * (((n : ℝ) + 1) / N) ^ 4 := by field_simp
      rw [this]
      have := scale_pow_le (K := C * lam) (by positivity) hX0 hX 4
      linarith
    have k3 : (c * ((n : ℝ) + 1) ^ 2 - C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 4) / N ^ 2 ≤
        tiltedLogMoment μ B (criticalPoint μ B + lam / N ^ 2) 3 n / N ^ 2 :=
      div_le_div_of_nonneg_right wJ1 (by positivity)
    have k4 : (c * ((n : ℝ) + 1) ^ 2 - C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 4) / N ^ 2 =
        c * (((n : ℝ) + 1) / N) ^ 2 - C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 4 / N ^ 2 := by
      field_simp
    linarith
  · rw [scaledThird, ← hn_def, hfield, hsplit3]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have k1 : C * (((n : ℝ) + 1) / N) ^ 2 ≤ 4 * C * t ^ 2 := by
      have := scale_pow_le (K := C) hC.le hX0 hX 2
      linarith
    have k2 : C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 4 / N ^ 2 ≤ 16 * C * lam * t ^ 4 := by
      have : C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 4 / N ^ 2 =
          C * lam * (((n : ℝ) + 1) / N) ^ 4 := by field_simp
      rw [this]
      have := scale_pow_le (K := C * lam) (by positivity) hX0 hX 4
      linarith
    have k3 : tiltedLogMoment μ B (criticalPoint μ B + lam / N ^ 2) 3 n / N ^ 2 ≤
        (C * ((n : ℝ) + 1) ^ 2 + C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 4) / N ^ 2 :=
      div_le_div_of_nonneg_right wJ2 (by positivity)
    have k4 : (C * ((n : ℝ) + 1) ^ 2 + C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 4) / N ^ 2 =
        C * (((n : ℝ) + 1) / N) ^ 2 + C * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 4 / N ^ 2 := by
      field_simp
    linarith
  · rw [hfield]
    refine w72.trans ?_
    have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [rpow_five_halves hn0]
    have k1 : ((n : ℝ) + 1) ^ 2 ≤ 4 * (N ^ 2 * t ^ 2) := by
      calc ((n : ℝ) + 1) ^ 2 ≤ (2 * (N * t)) ^ 2 := pow_le_pow_left₀ hn0 hn1hi 2
        _ = 4 * (N ^ 2 * t ^ 2) := by ring
    have k2 : Real.sqrt ((n : ℝ) + 1) ≤ 2 * (Real.sqrt N * Real.sqrt t) := by
      calc Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt (2 * (N * t)) := Real.sqrt_le_sqrt hn1hi
        _ = Real.sqrt 2 * (Real.sqrt N * Real.sqrt t) := by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul hN.le]
        _ ≤ 2 * (Real.sqrt N * Real.sqrt t) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [Real.sqrt_le_left (by norm_num)]; norm_num
    calc C * (((n : ℝ) + 1) ^ 2 * Real.sqrt ((n : ℝ) + 1))
        ≤ C * ((4 * (N ^ 2 * t ^ 2)) * (2 * (Real.sqrt N * Real.sqrt t))) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          exact mul_le_mul k1 k2 (Real.sqrt_nonneg _) (by positivity)
      _ = 8 * C * (N ^ 2 * Real.sqrt N) * (t ^ 2 * Real.sqrt t) := by ring

/-- The scaled matching estimate: `d_N - α P_N` with `α = λ κ a²/ℓ₃`. -/
theorem scaled_matching {μ : Measure ℝ} {B : ℝ} (hB : 2 < B) {κ ℓ₃ η C ε : ℝ} {n₁ : ℕ}
    (hC : 0 < C) (hε : 0 < ε) (hM : ∀ n : ℕ, n₁ ≤ n → ∀ u : ℝ, 0 ≤ u →
      u * ((n : ℝ) + 1) ^ 2 ≤ η →
      |tiltedLogMoment μ B (criticalPoint μ B + u) 1 n -
          u * (κ / ℓ₃) * tiltedLogMoment μ B (criticalPoint μ B + u) 3 n| ≤
        C / n + ε * u * ((n : ℝ) + 1) ^ 2 + C * u ^ 2 * ((n : ℝ) + 1) ^ 4)
    {lam N t : ℝ} (hlam : 0 ≤ lam) (hN : 0 < N) (ht : 0 < t) (hNt2 : 2 ≤ N * t)
    (hNt1 : (n₁ : ℝ) + 1 ≤ N * t) (hwin : lam * (2 * t) ^ 2 ≤ η) :
    |scaledDrift μ B lam N t - lam * κ * Real.log B ^ 2 / ℓ₃ * scaledThird μ B lam N t| ≤
      (2 * C / (N * t) + 4 * ε * lam * t ^ 2 + 16 * C * lam ^ 2 * t ^ 4) / Real.log B := by
  obtain ⟨hn1, hnlo, hnhi, hn1lo, hn1hi⟩ := floor_facts hN ht hNt2
  set n := ⌊N * t⌋₊ with hn_def
  have ha := log_pos_of_two_lt hB
  have hnpos : (0 : ℝ) < n := by linarith
  have hn₁ : n₁ ≤ n := by
    have : ((n₁ : ℕ) : ℝ) < (n : ℝ) + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  have hu : 0 ≤ lam / N ^ 2 := by positivity
  have hun := window_cond hlam hN hn1hi hwin
  have hm := hM n hn₁ (lam / N ^ 2) hu hun
  have hX : ((n : ℝ) + 1) / N ≤ 2 * t := by rw [div_le_iff₀ hN]; linarith
  have hX0 : 0 ≤ ((n : ℝ) + 1) / N := by positivity
  have heq : scaledDrift μ B lam N t - lam * κ * Real.log B ^ 2 / ℓ₃ * scaledThird μ B lam N t =
      (tiltedLogMoment μ B (criticalPoint μ B + lam / N ^ 2) 1 n -
        lam / N ^ 2 * (κ / ℓ₃) * tiltedLogMoment μ B (criticalPoint μ B + lam / N ^ 2) 3 n) /
        Real.log B := by
    rw [scaledDrift, scaledThird, ← hn_def]
    show tiltedLogMoment μ B (criticalPoint μ B + lam / N ^ 2) 1 n / Real.log B -
      lam * κ * Real.log B ^ 2 / ℓ₃ *
        (tiltedLogMoment μ B (criticalPoint μ B + lam / N ^ 2) 3 n / (Real.log B ^ 3 * N ^ 2)) = _
    by_cases hℓ : ℓ₃ = 0
    · simp [hℓ]
    · field_simp
  rw [heq, abs_div, abs_of_pos ha]
  apply div_le_div_of_nonneg_right _ ha.le
  refine hm.trans ?_
  have k1 : C / n ≤ 2 * C / (N * t) := by
    rw [div_le_div_iff₀ hnpos (by positivity)]
    have := mul_le_mul_of_nonneg_left hnlo hC.le
    linarith
  have k2 : ε * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 2 ≤ 4 * ε * lam * t ^ 2 := by
    have : ε * (lam / N ^ 2) * ((n : ℝ) + 1) ^ 2 = ε * lam * (((n : ℝ) + 1) / N) ^ 2 := by
      field_simp
    rw [this]
    have := scale_pow_le (K := ε * lam) (by positivity) hX0 hX 2
    linarith
  have k3 : C * (lam / N ^ 2) ^ 2 * ((n : ℝ) + 1) ^ 4 ≤ 16 * C * lam ^ 2 * t ^ 4 := by
    have : C * (lam / N ^ 2) ^ 2 * ((n : ℝ) + 1) ^ 4 =
        C * lam ^ 2 * (((n : ℝ) + 1) / N) ^ 4 := by field_simp
    rw [this]
    have := scale_pow_le (K := C * lam ^ 2) (by positivity) hX0 hX 4
    linarith
  linarith

section ScaledEstimates

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- The scaled Taylor bound for `ℋ_N`. -/
theorem scaled_taylor (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hW : WinBounds μ B n₀ η C c)
    {lam N t s : ℝ} (hlam : 0 ≤ lam) (hN : 0 < N) (ht : 0 < t) (hNt2 : 2 ≤ N * t)
    (hNt0 : (n₀ : ℝ) + 1 ≤ N * t) (hwin : lam * (2 * t) ^ 2 ≤ η) (hs : 0 ≤ s) (hsN : s ≤ N)
    (hsmall : s / (Real.log B * N) * (Real.log B - Real.log (floorSeq B 1)) ≤ 1) :
    |scaledCompensated μ B lam N t s - (-(s * scaledDrift μ B lam N t) +
        s ^ 2 * scaledSecond μ B lam N t / 2 - s ^ 3 * scaledThird μ B lam N t / 6)| ≤
      s ^ 2 / N + s / N * |scaledMass μ B lam N t| +
        s / N * |-(s * scaledDrift μ B lam N t) + s ^ 2 * scaledSecond μ B lam N t / 2 -
          s ^ 3 * scaledThird μ B lam N t / 6| +
        32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (s ^ 3 * Real.sqrt s) *
          (t ^ 2 * Real.sqrt t) := by
  have ha := log_pos_of_two_lt hB
  obtain ⟨-, hn1, -, -, -, -, -, -, -, h72⟩ :=
    scaled_window hB hC hc hW hlam hN ht hNt2 hNt0 hwin
  obtain ⟨hid, hR⟩ := transform_sub_eq hpos hmean hB (scalingField μ B lam N) N s hN hn1 hs hsmall
  have hcomp : scaledCompensated μ B lam N t s = s + (transformAt μ B (scalingField μ B lam N) N
      ⌊N * t⌋₊ s - transformAt μ B (scalingField μ B lam N) N ⌊N * t⌋₊ 0) := by
    rw [scaledCompensated]; ring
  rw [hcomp, hid]
  have hT := taylor_algebra (a := Real.log B) (A := tiltedMass μ B (scalingField μ B lam N) ⌊N * t⌋₊)
    (H := tiltedLogMoment μ B (scalingField μ B lam N) 1 ⌊N * t⌋₊)
    (K := tiltedLogMoment μ B (scalingField μ B lam N) 2 ⌊N * t⌋₊)
    (J := tiltedLogMoment μ B (scalingField μ B lam N) 3 ⌊N * t⌋₊)
    (R := taylorRemMoment μ B (scalingField μ B lam N) ⌊N * t⌋₊ (s / (Real.log B * N)))
    ha hN hs hsN
  refine hT.trans ?_
  simp only [scaledDrift, scaledSecond, scaledThird, scaledMass]
  have hRN : N * |taylorRemMoment μ B (scalingField μ B lam N) ⌊N * t⌋₊ (s / (Real.log B * N))| ≤
      32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (s ^ 3 * Real.sqrt s) *
        (t ^ 2 * Real.sqrt t) := by
    have hc0 : 0 ≤ s / (Real.log B * N) := div_nonneg hs (mul_pos ha hN).le
    have hsqrt : Real.sqrt (s / (Real.log B * N)) =
        Real.sqrt s / (Real.sqrt (Real.log B) * Real.sqrt N) := by
      rw [Real.sqrt_div' _ (mul_pos ha hN).le, Real.sqrt_mul ha.le]
    have hsa : 0 < Real.sqrt (Real.log B) := Real.sqrt_pos.2 ha
    have hsN' : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
    calc N * |taylorRemMoment μ B (scalingField μ B lam N) ⌊N * t⌋₊ (s / (Real.log B * N))|
        ≤ N * (4 * ((s / (Real.log B * N)) ^ 3 * Real.sqrt (s / (Real.log B * N))) *
            (8 * C * (N ^ 2 * Real.sqrt N) * (t ^ 2 * Real.sqrt t))) := by
          apply mul_le_mul_of_nonneg_left _ hN.le
          refine hR.trans ?_
          exact mul_le_mul_of_nonneg_left h72 (by positivity)
      _ = 32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (s ^ 3 * Real.sqrt s) *
            (t ^ 2 * Real.sqrt t) := by
          rw [hsqrt]
          have h1 := hsN'.ne'
          have h2 := hsa.ne'
          have h3 := ha.ne'
          have h4 := hN.ne'
          field_simp
          ring
  linarith

/-- The scaled Lipschitz bound in the weight. -/
theorem scaled_lipschitz (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {lam N t s s' : ℝ} (hN : 0 < N) (hn1 : 1 ≤ ⌊N * t⌋₊) (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (hsmall : max s s' / (Real.log B * N) * (-Real.log (floorSeq B 1)) ≤ Real.log 2) :
    |scaledCompensated μ B lam N t s - scaledCompensated μ B lam N t s'| ≤
      |s - s'| * (1 + 2 * |scaledDrift μ B lam N t| +
        2 * (1 + 2 * (-Real.log (floorSeq B 1)) / Real.log B) *
          (1 + scaledMass μ B lam N t / N)) := by
  have ha := log_pos_of_two_lt hB
  have hL := transform_lipschitz hpos hmean hB (scalingField μ B lam N) N s s' hN hn1 hs hs' hsmall
  have hcomp : scaledCompensated μ B lam N t s - scaledCompensated μ B lam N t s' =
      (s - s') + (transformAt μ B (scalingField μ B lam N) N ⌊N * t⌋₊ s -
        transformAt μ B (scalingField μ B lam N) N ⌊N * t⌋₊ s') := by
    rw [scaledCompensated, scaledCompensated]; ring
  rw [hcomp]
  have hA : tiltedMass μ B (scalingField μ B lam N) ⌊N * t⌋₊ = 1 + scaledMass μ B lam N t / N := by
    rw [scaledMass]; field_simp; ring
  have hH : 2 / Real.log B * tiltedLogMoment μ B (scalingField μ B lam N) 1 ⌊N * t⌋₊ ≤
      2 * |scaledDrift μ B lam N t| := by
    rw [scaledDrift]
    have : 2 / Real.log B * tiltedLogMoment μ B (scalingField μ B lam N) 1 ⌊N * t⌋₊ =
        2 * (tiltedLogMoment μ B (scalingField μ B lam N) 1 ⌊N * t⌋₊ / Real.log B) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
  have hbound : |s - s'| * (2 / Real.log B) * (tiltedLogMoment μ B (scalingField μ B lam N) 1 ⌊N * t⌋₊ +
      (Real.log B + 2 * (-Real.log (floorSeq B 1))) *
        tiltedMass μ B (scalingField μ B lam N) ⌊N * t⌋₊) ≤
      |s - s'| * (2 * |scaledDrift μ B lam N t| +
        2 * (1 + 2 * (-Real.log (floorSeq B 1)) / Real.log B) *
          (1 + scaledMass μ B lam N t / N)) := by
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [mul_add, ← hA]
    have : 2 / Real.log B * ((Real.log B + 2 * (-Real.log (floorSeq B 1))) *
        tiltedMass μ B (scalingField μ B lam N) ⌊N * t⌋₊) =
        2 * (1 + 2 * (-Real.log (floorSeq B 1)) / Real.log B) *
          tiltedMass μ B (scalingField μ B lam N) ⌊N * t⌋₊ := by field_simp
    linarith
  calc |s - s' + (transformAt μ B (scalingField μ B lam N) N ⌊N * t⌋₊ s -
        transformAt μ B (scalingField μ B lam N) N ⌊N * t⌋₊ s')|
      ≤ |s - s'| + |transformAt μ B (scalingField μ B lam N) N ⌊N * t⌋₊ s -
        transformAt μ B (scalingField μ B lam N) N ⌊N * t⌋₊ s'| := abs_add_le _ _
    _ ≤ _ := by nlinarith [abs_nonneg (s - s')]

/-- The scaled Riccati sum: `ℋ_N(t₂) - ℋ_N(t₁)` is the Riemann sum of the Riccati right-hand
side up to `C/N`. -/
theorem scaled_riccati (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {r T s₁ M : ℝ} (hr : 0 < r) (hrT : r ≤ T) (hs₁ : 0 ≤ s₁) :
    ∃ N₁ Cr : ℝ, ∀ N : ℝ, N₁ ≤ N → ∀ lam : ℝ,
      (∀ t ∈ Set.Icc (r / 2) T, |scaledMass μ B lam N t| ≤ M) →
      ∀ s ∈ Set.Icc 0 s₁, ∀ t₁ t₂ : ℝ, r ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
        |scaledCompensated μ B lam N t₂ s - scaledCompensated μ B lam N t₁ s -
          (∑ n ∈ Finset.Ico ⌊N * t₁⌋₊ ⌊N * t₂⌋₊,
            riccatiGen μ B (scalingField μ B lam N) N n s) / N| ≤ Cr / N := by
  obtain ⟨N₁, Cr, hD⟩ := transform_difference_aux hpos hmean hB (r / 2) (T - r / 2) 0 s₁ M
    (by linarith) (by linarith) le_rfl hs₁
  refine ⟨max N₁ (2 / r), Cr, fun N hN lam hM s hs t₁ t₂ h1 h12 h2 => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) (le_max_right _ _ |>.trans hN)
  have hNr : 2 ≤ N * r := by
    have := (le_max_right _ _).trans hN
    rw [div_le_iff₀ hr] at this
    linarith
  have hsum := hD N ((le_max_left _ _).trans hN) (scalingField μ B lam N) (fun t ht => by
    rw [show r / 2 + (T - r / 2) = T by ring] at ht
    rw [transformAt_zero]
    exact hM t ht) s hs
  rw [show r / 2 + (T - r / 2) = T by ring] at hsum
  have htel := compGen_telescope μ B (scalingField μ B lam N) N s hNpos.ne' ⌊N * t₁⌋₊ ⌊N * t₂⌋₊
    (Nat.floor_le_floor (mul_le_mul_of_nonneg_left h12 hNpos.le))
  have hsub : Finset.Ico ⌊N * t₁⌋₊ ⌊N * t₂⌋₊ ⊆ Finset.Ico ⌈r / 2 * N⌉₊ ⌈T * N⌉₊ := by
    apply Finset.Ico_subset_Ico
    · apply Nat.ceil_le.2
      have h3 : N * t₁ - 1 < (⌊N * t₁⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one (N * t₁); linarith
      have h4 : N * r ≤ N * t₁ := mul_le_mul_of_nonneg_left h1 hNpos.le
      linarith
    · refine (Nat.floor_le_floor (mul_le_mul_of_nonneg_left h2 hNpos.le)).trans
        ((Nat.floor_le_ceil _).trans (le_of_eq (by rw [mul_comm])))
  have heq : scaledCompensated μ B lam N t₂ s - scaledCompensated μ B lam N t₁ s -
      (∑ n ∈ Finset.Ico ⌊N * t₁⌋₊ ⌊N * t₂⌋₊, riccatiGen μ B (scalingField μ B lam N) N n s) / N =
      ∑ n ∈ Finset.Ico ⌊N * t₁⌋₊ ⌊N * t₂⌋₊, transformError μ B (scalingField μ B lam N) N n s 0 := by
    show compGen μ B (scalingField μ B lam N) N ⌊N * t₂⌋₊ s -
      compGen μ B (scalingField μ B lam N) N ⌊N * t₁⌋₊ s - _ = _
    rw [htel]
    ring
  rw [heq]
  calc |∑ n ∈ Finset.Ico ⌊N * t₁⌋₊ ⌊N * t₂⌋₊, transformError μ B (scalingField μ B lam N) N n s 0|
      ≤ ∑ n ∈ Finset.Ico ⌊N * t₁⌋₊ ⌊N * t₂⌋₊,
          |transformError μ B (scalingField μ B lam N) N n s 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Ico ⌈r / 2 * N⌉₊ ⌈T * N⌉₊,
          |transformError μ B (scalingField μ B lam N) N n s 0| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
    _ ≤ Cr / N := hsum

/-- The scaled one-sided Lipschitz bound for `S_N`. -/
theorem scaled_oneSided (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {r T M : ℝ} (hr : 0 < r) (hrT : r < T) :
    ∃ N₁ CS : ℝ, ∃ ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ N : ℝ, N₁ ≤ N → ∀ lam : ℝ,
      (∀ t ∈ Set.Icc r T, |scaledMass μ B lam N t| ≤ M) →
      ∀ t₁ t₂ : ℝ, r ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
        scaledMass μ B lam N t₂ - scaledMass μ B lam N t₁ ≤ CS * (t₂ - t₁) + ε N := by
  obtain ⟨Cb, hCb⟩ := transform_bounded_aux hpos hmean hB
  obtain ⟨N₁, CM, ε, hε, hb⟩ := hCb r (T - r) 0 M hr (by linarith) le_rfl
  refine ⟨N₁, CM, ε, hε, fun N hN lam hM t₁ t₂ h1 h12 h2 => ?_⟩
  have hb' := hb N hN (scalingField μ B lam N) (fun t ht => by
    rw [show r + (T - r) = T by ring] at ht
    rw [transformAt_zero]
    exact hM t ht)
  have := hb'.2.2.2 t₁ t₂ h1 h12 (by linarith)
  rw [transformAt_zero, transformAt_zero] at this
  exact this

end ScaledEstimates

/-! ### Uniform Cauchy helpers -/

theorem uniformCauchySeqOn_of_approx {α : Type*} {f : ℕ → α → ℝ} {K : Set α}
    (h : ∀ ε > 0, ∃ g : ℕ → α → ℝ, UniformCauchySeqOn g atTop K ∧
      ∀ᶠ j in atTop, ∀ x ∈ K, |f j x - g j x| ≤ ε) :
    UniformCauchySeqOn f atTop K := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := h (ε / 3) (by linarith)
  obtain ⟨N₁, hN₁⟩ := Metric.uniformCauchySeqOn_iff.1 hg (ε / 3) (by linarith)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hfg
  refine ⟨max N₁ N₂, fun m hm n hn x hx => ?_⟩
  have h1 := hN₁ m ((le_max_left _ _).trans hm) n ((le_max_left _ _).trans hn) x hx
  have h2 := abs_le.1 (hN₂ m ((le_max_right _ _).trans hm) x hx)
  have h3 := abs_le.1 (hN₂ n ((le_max_right _ _).trans hn) x hx)
  rw [Real.dist_eq] at h1 ⊢
  have h1' := abs_lt.1 h1
  rw [abs_lt]
  constructor <;> linarith [h1'.1, h1'.2, h2.1, h2.2, h3.1, h3.2]

/-- A linear combination of fixed-weight slices of a uniformly Cauchy sequence on a product
is uniformly Cauchy. -/
theorem uniformCauchySeqOn_slices {F : ℕ → ℝ × ℝ → ℝ} {K₁ K₂ : Set ℝ}
    (hF : UniformCauchySeqOn F atTop (K₁ ×ˢ K₂)) (σ w : Fin 3 → ℝ) (hσ : ∀ i, σ i ∈ K₂) :
    UniformCauchySeqOn (fun j t => ∑ i, w i * F j (t, σ i)) atTop K₁ := by
  rw [Metric.uniformCauchySeqOn_iff] at hF ⊢
  intro ε hε
  set W := ∑ i, |w i| + 1 with hW
  have hW0 : 0 < W := by positivity
  obtain ⟨N, hN⟩ := hF (ε / W) (div_pos hε hW0)
  refine ⟨N, fun m hm n hn t ht => ?_⟩
  rw [Real.dist_eq, ← Finset.sum_sub_distrib]
  calc |∑ i, (w i * F m (t, σ i) - w i * F n (t, σ i))|
      ≤ ∑ i, |w i * F m (t, σ i) - w i * F n (t, σ i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w i| * (ε / W) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← mul_sub, abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have := hN m hm n hn (t, σ i) ⟨ht, hσ i⟩
        rw [Real.dist_eq] at this
        exact this.le
    _ = (∑ i, |w i|) * (ε / W) := by rw [Finset.sum_mul]
    _ < W * (ε / W) := by
        apply mul_lt_mul_of_pos_right (by linarith) (div_pos hε hW0)
    _ = ε := by field_simp

/-! ### Uniform window bounds -/

section Assembly

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- Uniform bounds on `[r, T]` for large `N`. -/
theorem unif_bounds {B : ℝ} (hB : 2 < B) {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hW : WinBounds μ B n₀ η C c) {lam T : ℝ} (hlam : 0 ≤ lam) (hT : 0 < T)
    (hlamT : lam * (2 * T) ^ 2 ≤ η) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ N in atTop, 0 < N ∧ ∀ t ∈ Set.Icc r T,
      2 ≤ N * t ∧ (n₀ : ℝ) + 1 ≤ N * t ∧ 1 ≤ ⌊N * t⌋₊ ∧
      |scaledMass μ B lam N t| ≤ (2 * C + c) / r + 2 * C * lam * T ∧
      |scaledDrift μ B lam N t| ≤
        (C + 4 * C * lam * T ^ 2 + 16 * C * lam ^ 2 * T ^ 4) / Real.log B ∧
      |scaledSecond μ B lam N t| ≤ (C * T + 8 * C * lam * T ^ 3) / Real.log B ^ 2 ∧
      |scaledThird μ B lam N t| ≤ (4 * C * T ^ 2 + 16 * C * lam * T ^ 4) / Real.log B ^ 3 ∧
      absTiltedLogRpowMoment μ B (scalingField μ B lam N) (7 / 2) ⌊N * t⌋₊ ≤
        8 * C * (N ^ 2 * Real.sqrt N) * (t ^ 2 * Real.sqrt t) := by
  have ha := log_pos_of_two_lt hB
  filter_upwards [eventually_ge_atTop (max 1 (max (2 / r) (((n₀ : ℝ) + 1) / r)))] with N hN
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 / r ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN3 : ((n₀ : ℝ) + 1) / r ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNpos : 0 < N := by linarith
  refine ⟨hNpos, fun t ht => ?_⟩
  have htpos : 0 < t := lt_of_lt_of_le hr ht.1
  have hNt2 : 2 ≤ N * t := by
    rw [div_le_iff₀ hr] at hN2
    nlinarith [ht.1]
  have hNt0 : (n₀ : ℝ) + 1 ≤ N * t := by
    rw [div_le_iff₀ hr] at hN3
    nlinarith [ht.1]
  have hwin : lam * (2 * t) ^ 2 ≤ η := by
    have : (2 * t) ^ 2 ≤ (2 * T) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith [ht.2]) 2
    exact (mul_le_mul_of_nonneg_left this hlam).trans hlamT
  obtain ⟨-, hn1, hS1, hS2, hd, hK1, hK2, hP1, hP2, h72⟩ :=
    scaled_window hB hC hc hW hlam hNpos htpos hNt2 hNt0 hwin
  have htT : t ≤ T := ht.2
  refine ⟨hNt2, hNt0, hn1, ?_, ?_, ?_, ?_, h72⟩
  · rw [abs_le]
    have e1 : c / t ≤ c / r := div_le_div_of_nonneg_left hc.le hr ht.1
    have e2 : 2 * C / t ≤ 2 * C / r := div_le_div_of_nonneg_left (by positivity) hr ht.1
    have e3 : 2 * C * lam * t ≤ 2 * C * lam * T :=
      mul_le_mul_of_nonneg_left htT (by positivity)
    have e4 : 0 ≤ c / t := by positivity
    have e5 : (2 * C + c) / r = 2 * C / r + c / r := by ring
    have e6 : 0 ≤ 2 * C / r := by positivity
    have e7 : 0 ≤ c / r := by positivity
    constructor <;> linarith
  · refine hd.trans (div_le_div_of_nonneg_right ?_ ha.le)
    have e1 : 2 * C / (N * t) ≤ C := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have e2 : 4 * C * lam * t ^ 2 ≤ 4 * C * lam * T ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htpos.le htT 2) (by positivity)
    have e3 : 16 * C * lam ^ 2 * t ^ 4 ≤ 16 * C * lam ^ 2 * T ^ 4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htpos.le htT 4) (by positivity)
    linarith
  · rw [abs_le]
    have e1 : C * t + 8 * C * lam * t ^ 3 ≤ C * T + 8 * C * lam * T ^ 3 := by
      have := mul_le_mul_of_nonneg_left htT hC.le
      have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htpos.le htT 3)
        (by positivity : 0 ≤ 8 * C * lam)
      linarith
    have e2 : (c * t / 2 - 8 * C * lam * t ^ 3) / Real.log B ^ 2 ≥
        -((C * T + 8 * C * lam * T ^ 3) / Real.log B ^ 2) := by
      rw [ge_iff_le, neg_div', div_le_div_iff_of_pos_right (by positivity)]
      have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htpos.le htT 3)
        (by positivity : 0 ≤ 8 * C * lam)
      have : 0 ≤ c * t / 2 := by positivity
      have : 0 ≤ C * T := by positivity
      linarith
    constructor
    · linarith
    · exact hK2.trans (div_le_div_of_nonneg_right e1 (by positivity))
  · rw [abs_le]
    have e1 : 4 * C * t ^ 2 + 16 * C * lam * t ^ 4 ≤ 4 * C * T ^ 2 + 16 * C * lam * T ^ 4 := by
      have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htpos.le htT 2)
        (by positivity : 0 ≤ 4 * C)
      have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htpos.le htT 4)
        (by positivity : 0 ≤ 16 * C * lam)
      linarith
    have e2 : (c * t ^ 2 - 16 * C * lam * t ^ 4) / Real.log B ^ 3 ≥
        -((4 * C * T ^ 2 + 16 * C * lam * T ^ 4) / Real.log B ^ 3) := by
      rw [ge_iff_le, neg_div', div_le_div_iff_of_pos_right (by positivity)]
      have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htpos.le htT 4)
        (by positivity : 0 ≤ 16 * C * lam)
      have : 0 ≤ c * t ^ 2 := by positivity
      have : 0 ≤ 4 * C * T ^ 2 := by positivity
      linarith
    constructor
    · linarith
    · exact hP2.trans (div_le_div_of_nonneg_right e1 (by positivity))

/-- The countable dense set of times: `T` and the rationals in `(0, T)`. -/
def timeGrid (T : ℝ) : Set ℝ := {T} ∪ (Set.range ((↑) : ℚ → ℝ) ∩ Set.Ioo 0 T)

theorem timeGrid_subset {T : ℝ} (hT : 0 < T) : timeGrid T ⊆ Set.Ioc 0 T := by
  rintro t (ht | ⟨-, ht⟩)
  · rw [Set.mem_singleton_iff.1 ht]; exact ⟨hT, le_rfl⟩
  · exact ⟨ht.1, ht.2.le⟩

/-- The Lipschitz estimate in the weight on the window `[r/4, T] × [0, M+1]`. -/
theorem win_lip (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {lam T r M MS MD N : ℝ} (hN : 0 < N) (hN1 : 1 ≤ N)
    (hsm : (M + 1) / (Real.log B * N) * (-Real.log (floorSeq B 1)) ≤ Real.log 2)
    (hb : ∀ t ∈ Set.Icc (r / 4) T, 1 ≤ ⌊N * t⌋₊ ∧ |scaledMass μ B lam N t| ≤ MS ∧
      |scaledDrift μ B lam N t| ≤ MD) :
    ∀ t ∈ Set.Icc (r / 4) T, ∀ s ∈ Set.Icc 0 (M + 1), ∀ s' ∈ Set.Icc 0 (M + 1),
      |scaledCompensated μ B lam N t s - scaledCompensated μ B lam N t s'| ≤
        (1 + 2 * MD + 2 * (1 + 2 * (-Real.log (floorSeq B 1)) / Real.log B) * (1 + MS)) *
          |s - s'| := by
  intro t ht s hs s' hs'
  have ha := log_pos_of_two_lt hB
  have hβ0 : 0 ≤ -Real.log (floorSeq B 1) :=
    neg_nonneg.2 (Real.log_nonpos (floorSeq_one_pos hB).le (floorSeq_le_one hB 1))
  obtain ⟨hn1, hS, hd⟩ := hb t ht
  have hsmall : max s s' / (Real.log B * N) * (-Real.log (floorSeq B 1)) ≤ Real.log 2 := by
    refine le_trans ?_ hsm
    apply mul_le_mul_of_nonneg_right _ hβ0
    exact div_le_div_of_nonneg_right (max_le hs.2 hs'.2) (mul_pos ha hN).le
  refine (scaled_lipschitz hpos hmean hB hN hn1 hs.1 hs'.1 hsmall).trans ?_
  rw [mul_comm _ |s - s'|]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have e1 : 1 + scaledMass μ B lam N t / N ≤ 1 + MS := by
    have : scaledMass μ B lam N t / N ≤ |scaledMass μ B lam N t| := by
      rw [div_le_iff₀ hN]
      have h1 := le_abs_self (scaledMass μ B lam N t)
      have h2 : |scaledMass μ B lam N t| ≤ |scaledMass μ B lam N t| * N :=
        le_mul_of_one_le_right (abs_nonneg _) hN1
      linarith
    linarith
  have e2 : 0 ≤ 2 * (1 + 2 * (-Real.log (floorSeq B 1)) / Real.log B) := by positivity
  have e3 := mul_le_mul_of_nonneg_left e1 e2
  have e4 : 2 * |scaledDrift μ B lam N t| ≤ 2 * MD := by linarith
  linarith

/-- The time modulus of `ℋ_N` from the Riccati sum. -/
theorem win_time {B lam T r M MS L MF Cr N : ℝ} (hr : 0 < r) (hN : 0 < N) (hN4 : 4 / r ≤ N)
    (hMF : MF = MS * ((M + 1) * L) + ((M + 1) * L) ^ 2 / 2 + (M + 1) ^ 2 / 2)
    (hMS0 : 0 ≤ MS) (hL0 : 0 ≤ L) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Set.Icc (r / 4) T, |scaledMass μ B lam N t| ≤ MS)
    (hsize : ∀ t ∈ Set.Icc (r / 4) T, ∀ s ∈ Set.Icc 0 (M + 1),
      |scaledCompensated μ B lam N t s| ≤ (M + 1) * L)
    (hric : ∀ s ∈ Set.Icc 0 (M + 1), ∀ t₁ t₂ : ℝ, r / 2 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
      |scaledCompensated μ B lam N t₂ s - scaledCompensated μ B lam N t₁ s -
        (∑ n ∈ Finset.Ico ⌊N * t₁⌋₊ ⌊N * t₂⌋₊,
          riccatiGen μ B (scalingField μ B lam N) N n s) / N| ≤ Cr / N) :
    ∀ s ∈ Set.Icc 0 (M + 1), ∀ t₁ t₂ : ℝ, r / 2 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
      |scaledCompensated μ B lam N t₂ s - scaledCompensated μ B lam N t₁ s| ≤
        MF * (t₂ - t₁) + (MF + Cr) / N := by
  intro s hs t₁ t₂ h1 h12 h2
  have hMF0 : 0 ≤ MF := by rw [hMF]; positivity
  have hric' := hric s hs t₁ t₂ h1 h12 h2
  have hterm : ∀ n ∈ Finset.Ico ⌊N * t₁⌋₊ ⌊N * t₂⌋₊,
      |riccatiGen μ B (scalingField μ B lam N) N n s| ≤ MF := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    set τ := (n : ℝ) / N with hτ
    have hfl : ⌊N * τ⌋₊ = n := by
      rw [hτ, show N * ((n : ℝ) / N) = n by field_simp, Nat.floor_natCast]
    have hτ1 : r / 4 ≤ τ := by
      have h3 : N * t₁ - 1 < (⌊N * t₁⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one (N * t₁); linarith
      have h4 : (⌊N * t₁⌋₊ : ℝ) ≤ n := by exact_mod_cast hn.1
      rw [hτ, le_div_iff₀ hN]
      have h5 : N * (r / 2) ≤ N * t₁ := mul_le_mul_of_nonneg_left h1 hN.le
      have h6 : 4 ≤ N * r := by rw [div_le_iff₀ hr] at hN4; linarith
      linarith
    have hτ2 : τ ≤ T := by
      have h4 : (n : ℝ) < ⌊N * t₂⌋₊ := by exact_mod_cast hn.2
      have h5 : (⌊N * t₂⌋₊ : ℝ) ≤ N * t₂ := Nat.floor_le (mul_nonneg hN.le (by linarith))
      have h6 : N * t₂ ≤ N * T := mul_le_mul_of_nonneg_left h2 hN.le
      rw [hτ, div_le_iff₀ hN]
      linarith
    have hS := hb τ ⟨hτ1, hτ2⟩
    have hH := hsize τ ⟨hτ1, hτ2⟩ s hs
    have heq : riccatiGen μ B (scalingField μ B lam N) N n s =
        scaledMass μ B lam N τ * scaledCompensated μ B lam N τ s +
          scaledCompensated μ B lam N τ s ^ 2 / 2 - s ^ 2 / 2 := by
      rw [riccatiGen, compGen, scaledMass, scaledCompensated, hfl, transformAt_zero]
    rw [heq]
    have k1 : |scaledMass μ B lam N τ * scaledCompensated μ B lam N τ s| ≤
        MS * ((M + 1) * L) := by
      rw [abs_mul]; exact mul_le_mul hS hH (abs_nonneg _) hMS0
    have k2 : scaledCompensated μ B lam N τ s ^ 2 ≤ ((M + 1) * L) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hH 2
    have k3 : s ^ 2 ≤ (M + 1) ^ 2 := pow_le_pow_left₀ hs.1 hs.2 2
    have k4 : 0 ≤ scaledCompensated μ B lam N τ s ^ 2 := sq_nonneg _
    have k5 : 0 ≤ s ^ 2 := sq_nonneg _
    have k6 : 0 ≤ ((M + 1) * L) ^ 2 := sq_nonneg _
    have k8 : 0 ≤ MS * ((M + 1) * L) := by positivity
    have := abs_le.1 k1
    rw [abs_le, hMF]
    constructor <;> linarith
  have hsum : |∑ n ∈ Finset.Ico ⌊N * t₁⌋₊ ⌊N * t₂⌋₊,
      riccatiGen μ B (scalingField μ B lam N) N n s| ≤
      MF * ((⌊N * t₂⌋₊ : ℝ) - ⌊N * t₁⌋₊) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_comm,
      Nat.cast_sub (Nat.floor_le_floor (mul_le_mul_of_nonneg_left h12 hN.le))]
  have hcount : (⌊N * t₂⌋₊ : ℝ) - ⌊N * t₁⌋₊ ≤ N * (t₂ - t₁) + 1 := by
    have h3 : (⌊N * t₂⌋₊ : ℝ) ≤ N * t₂ := Nat.floor_le (mul_nonneg hN.le (by linarith))
    have h4 : N * t₁ - 1 < (⌊N * t₁⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one (N * t₁); linarith
    linarith
  have hsum' : |(∑ n ∈ Finset.Ico ⌊N * t₁⌋₊ ⌊N * t₂⌋₊,
      riccatiGen μ B (scalingField μ B lam N) N n s) / N| ≤ MF * (t₂ - t₁) + MF / N := by
    rw [abs_div, abs_of_pos hN, div_le_iff₀ hN]
    calc _ ≤ MF * ((⌊N * t₂⌋₊ : ℝ) - ⌊N * t₁⌋₊) := hsum
      _ ≤ MF * (N * (t₂ - t₁) + 1) := mul_le_mul_of_nonneg_left hcount hMF0
      _ = (MF * (t₂ - t₁) + MF / N) * N := by field_simp
  have h1' := abs_le.1 hric'
  have h2' := abs_le.1 hsum'
  rw [abs_le]
  have : (MF + Cr) / N = MF / N + Cr / N := by ring
  constructor <;> linarith

set_option maxHeartbeats 400000 in
-- the equicontinuity argument collects the Lipschitz, size and time estimates
/-- Equicontinuity of `ℋ_N` and convergence on the grid give a uniformly Cauchy sequence on
`[r, T] × [0, M]`. -/
theorem ucs_H (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) {n₀ : ℕ}
    {η C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hlamT : lam * (2 * T) ^ 2 ≤ η) {Ns : ℕ → ℝ}
    (hNs : Tendsto Ns atTop atTop)
    (hconv : ∀ t ∈ timeGrid T, ∀ q : ℚ, (0 : ℝ) ≤ q →
      ∃ L, Tendsto (fun j => scaledCompensated μ B lam (Ns j) t q) atTop (𝓝 L))
    {r M : ℝ} (hr : 0 < r) (hrT : r ≤ T) (hM : 0 ≤ M) :
    UniformCauchySeqOn (fun j (p : ℝ × ℝ) => scaledCompensated μ B lam (Ns j) p.1 p.2) atTop
      (Set.Icc r T ×ˢ Set.Icc 0 M) := by
  have ha := log_pos_of_two_lt hB
  set β := -Real.log (floorSeq B 1) with hβ
  have hβ0 : 0 ≤ β := neg_nonneg.2 (Real.log_nonpos (floorSeq_one_pos hB).le (floorSeq_le_one hB 1))
  set MS := (2 * C + c) / (r / 4) + 2 * C * lam * T with hMS
  set MD := (C + 4 * C * lam * T ^ 2 + 16 * C * lam ^ 2 * T ^ 4) / Real.log B with hMD
  have hMS0 : 0 ≤ MS := by positivity
  have hMD0 : 0 ≤ MD := by positivity
  set L := 1 + 2 * MD + 2 * (1 + 2 * β / Real.log B) * (1 + MS) with hL
  have hL0 : 0 ≤ L := by positivity
  set MF := MS * ((M + 1) * L) + ((M + 1) * L) ^ 2 / 2 + (M + 1) ^ 2 / 2 with hMF
  have hMF0 : 0 ≤ MF := by positivity
  obtain ⟨N₁, Cr, hric⟩ := scaled_riccati (μ := μ) hpos hmean hB (r := r / 2) (T := T)
    (s₁ := M + 1) (M := MS) (by linarith) (by linarith) (by linarith)
  -- eventual bounds on `[r/4, T]`
  have hev := unif_bounds hB hC hc hW hlam hT hlamT (r := r / 4) (by linarith)
  have hev2 : ∀ᶠ N in atTop, 0 < N ∧ 1 ≤ N ∧ N₁ ≤ N ∧ 4 / r ≤ N ∧
      (M + 1) / (Real.log B * N) * β ≤ Real.log 2 ∧
      ∀ t ∈ Set.Icc (r / 4) T, 1 ≤ ⌊N * t⌋₊ ∧ |scaledMass μ B lam N t| ≤ MS ∧
        |scaledDrift μ B lam N t| ≤ MD := by
    have hsm : ∀ᶠ N in atTop, (M + 1) / (Real.log B * N) * β ≤ Real.log 2 := by
      have h1 : Tendsto (fun N : ℝ => (M + 1) / (Real.log B * N) * β) atTop (𝓝 0) := by
        have := (tendsto_const_nhds (x := (M + 1) / Real.log B * β)).mul
          (tendsto_inv_atTop_zero (𝕜 := ℝ))
        rw [mul_zero] at this
        refine this.congr fun N => ?_
        ring
      exact ((tendsto_order.1 h1).2 _ (Real.log_pos (by norm_num))).mono fun N hN => hN.le
    filter_upwards [hev, eventually_ge_atTop 1, eventually_ge_atTop N₁, eventually_ge_atTop (4 / r),
      hsm] with N hN h1 h2 h3 h4
    refine ⟨hN.1, h1, h2, h3, h4, fun t ht => ?_⟩
    obtain ⟨-, -, hn1, hS, hd, -⟩ := hN.2 t ht
    exact ⟨hn1, hS, hd⟩
  -- Lipschitz and size bounds
  have hlip : ∀ N : ℝ, 0 < N → 1 ≤ N → (M + 1) / (Real.log B * N) * β ≤ Real.log 2 →
      (∀ t ∈ Set.Icc (r / 4) T, 1 ≤ ⌊N * t⌋₊ ∧ |scaledMass μ B lam N t| ≤ MS ∧
        |scaledDrift μ B lam N t| ≤ MD) →
      ∀ t ∈ Set.Icc (r / 4) T, ∀ s ∈ Set.Icc 0 (M + 1), ∀ s' ∈ Set.Icc 0 (M + 1),
        |scaledCompensated μ B lam N t s - scaledCompensated μ B lam N t s'| ≤ L * |s - s'| :=
    fun N hN hN1 hsm hb => win_lip hpos hmean hB hN hN1 hsm hb
  have hsize : ∀ N : ℝ, 0 < N → 1 ≤ N → (M + 1) / (Real.log B * N) * β ≤ Real.log 2 →
      (∀ t ∈ Set.Icc (r / 4) T, 1 ≤ ⌊N * t⌋₊ ∧ |scaledMass μ B lam N t| ≤ MS ∧
        |scaledDrift μ B lam N t| ≤ MD) →
      ∀ t ∈ Set.Icc (r / 4) T, ∀ s ∈ Set.Icc 0 (M + 1),
        |scaledCompensated μ B lam N t s| ≤ (M + 1) * L := by
    intro N hN hN1 hsm hb t ht s hs
    have h0 : scaledCompensated μ B lam N t 0 = 0 := by simp [scaledCompensated]
    have := hlip N hN hN1 hsm hb t ht s hs 0 ⟨le_rfl, by linarith⟩
    rw [h0, sub_zero, sub_zero, abs_of_nonneg hs.1] at this
    calc _ ≤ L * s := this
      _ ≤ L * (M + 1) := mul_le_mul_of_nonneg_left hs.2 hL0
      _ = (M + 1) * L := by ring
  -- the time modulus
  have htime : ∀ N : ℝ, 0 < N → 1 ≤ N → N₁ ≤ N → 4 / r ≤ N →
      (M + 1) / (Real.log B * N) * β ≤ Real.log 2 →
      (∀ t ∈ Set.Icc (r / 4) T, 1 ≤ ⌊N * t⌋₊ ∧ |scaledMass μ B lam N t| ≤ MS ∧
        |scaledDrift μ B lam N t| ≤ MD) →
      ∀ s ∈ Set.Icc 0 (M + 1), ∀ t₁ t₂ : ℝ, r / 2 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
        |scaledCompensated μ B lam N t₂ s - scaledCompensated μ B lam N t₁ s| ≤
          MF * (t₂ - t₁) + (MF + Cr) / N := by
    intro N hN hN1 hNN₁ hN4 hsm hb
    exact win_time hr hN hN4 hMF hMS0 hL0 hM (fun t ht => (hb t ht).2.1)
      (hsize N hN hN1 hsm hb) (fun s hs t₁ t₂ h1 h12 h2 =>
        hric N hNN₁ lam (fun t ht => (hb t ⟨by linarith [ht.1], ht.2⟩).2.1) s hs t₁ t₂ h1 h12 h2)
  -- apply the dense-set lemma
  have hK : IsCompact (Set.Icc r T ×ˢ Set.Icc 0 M) := isCompact_Icc.prod isCompact_Icc
  let D : Set (ℝ × ℝ) := {p | p.1 ∈ timeGrid T ∧ r / 2 ≤ p.1 ∧
    ∃ q : ℚ, (q : ℝ) = p.2 ∧ 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ M + 1}
  refine uniformCauchySeqOn_of_dense _ hK (D := D) ?_ ?_ ?_
  · -- density
    rintro ⟨t, s⟩ ⟨ht, hs⟩ δ hδ
    obtain ⟨q₂, hq₂1, hq₂2⟩ := exists_rat_btwn (show s < s + min (δ / 2) (1 / 2) by
      have : 0 < min (δ / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
      linarith)
    have hmin1 : min (δ / 2) (1 / 2) ≤ δ / 2 := min_le_left _ _
    have hmin2 : min (δ / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have hs2 : |s - q₂| < δ := by
      rw [abs_lt]; constructor <;> linarith
    rcases lt_or_eq_of_le ht.2 with htT | htT
    · obtain ⟨q₁, hq₁1, hq₁2⟩ := exists_rat_btwn (show t < min (t + δ / 2) T by
        exact lt_min (by linarith) htT)
      refine ⟨((q₁ : ℝ), (q₂ : ℝ)), ⟨Or.inr ⟨⟨q₁, rfl⟩, ⟨by linarith [ht.1], lt_of_lt_of_le hq₁2
        (min_le_right _ _)⟩⟩, by linarith [ht.1], q₂, rfl, by linarith [hs.1], by
          linarith [hs.2]⟩, ?_⟩
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      refine max_lt ?_ hs2
      rw [abs_lt]; constructor <;> linarith [min_le_left (t + δ / 2) T]
    · refine ⟨(T, (q₂ : ℝ)), ⟨Or.inl rfl, by linarith, q₂, rfl, by linarith [hs.1], by
          linarith [hs.2]⟩, ?_⟩
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, htT, sub_self, abs_zero]
      exact max_lt hδ hs2
  · -- convergence on the grid
    rintro ⟨t, s⟩ ⟨ht, -, q, rfl, hq, -⟩
    exact hconv t ht q hq
  · -- equicontinuity
    intro ε hε
    set δ := min (r / 2) (min 1 (ε / (3 * (L + MF + 1)))) with hδ
    have hδ0 : 0 < δ := lt_min (by linarith) (lt_min one_pos (by positivity))
    have hδ1 : δ ≤ r / 2 := min_le_left _ _
    have hδ2 : δ ≤ ε / (3 * (L + MF + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    have hδ3 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    refine ⟨δ, hδ0, ?_⟩
    have hsmallN : ∀ᶠ N in atTop, (MF + Cr) / N < ε / 3 := by
      have h1 : Tendsto (fun N : ℝ => (MF + Cr) / N) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      exact (tendsto_order.1 h1).2 _ (by linarith)
    filter_upwards [hNs.eventually (hev2.and hsmallN)] with j ⟨⟨hN, hN1, hNN₁, hN4, hsm, hb⟩, hεN⟩
    rintro ⟨t, s⟩ ⟨ht, hs⟩ ⟨t', s'⟩ ⟨ht', hrt', q, hq, hq0, hqM⟩ hdist
    simp only at hq hrt' ht' ⊢
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hdist
    have hdt : |t - t'| < δ := lt_of_le_of_lt (le_max_left _ _) hdist
    have hds : |s - s'| < δ := lt_of_le_of_lt (le_max_right _ _) hdist
    have ht'T : t' ≤ T := (timeGrid_subset hT ht').2
    have hsI : s ∈ Set.Icc 0 (M + 1) := ⟨hs.1, by linarith [hs.2]⟩
    have hs'I : s' ∈ Set.Icc 0 (M + 1) := ⟨by rw [← hq]; exact hq0, by rw [← hq]; exact hqM⟩
    have htI : t ∈ Set.Icc (r / 4) T := ⟨by linarith [ht.1], ht.2⟩
    have k1 := hlip (Ns j) hN hN1 hsm hb t htI s hsI s' hs'I
    have k2 : |scaledCompensated μ B lam (Ns j) t s' - scaledCompensated μ B lam (Ns j) t' s'| ≤
        MF * |t - t'| + (MF + Cr) / Ns j := by
      rcases le_total t t' with h | h
      · have := htime (Ns j) hN hN1 hNN₁ hN4 hsm hb s' hs'I t t' (by linarith [ht.1]) h ht'T
        rw [abs_sub_comm, abs_sub_comm t t', abs_of_nonneg (by linarith : 0 ≤ t' - t)]
        exact this
      · have := htime (Ns j) hN hN1 hNN₁ hN4 hsm hb s' hs'I t' t hrt' h ht.2
        rw [abs_of_nonneg (by linarith : 0 ≤ t - t')]
        exact this
    have k3 : L * |s - s'| ≤ L * δ := mul_le_mul_of_nonneg_left hds.le hL0
    have k4 : MF * |t - t'| ≤ MF * δ := mul_le_mul_of_nonneg_left hdt.le hMF0
    have k5 : (L + MF) * δ < ε / 3 * 2 := by
      have : (L + MF) * δ ≤ (L + MF) * (ε / (3 * (L + MF + 1))) :=
        mul_le_mul_of_nonneg_left hδ2 (by positivity)
      have h6 : (L + MF) * (ε / (3 * (L + MF + 1))) < ε / 3 := by
        have hp : 0 < L + MF + 1 := by positivity
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
        have e : (L + MF) * ε * 3 + 3 * ε = ε * (3 * (L + MF + 1)) := by ring
        linarith only [e, hε]
      linarith only [this, h6, hε]
    calc |scaledCompensated μ B lam (Ns j) t s - scaledCompensated μ B lam (Ns j) t' s'|
        ≤ |scaledCompensated μ B lam (Ns j) t s - scaledCompensated μ B lam (Ns j) t s'| +
          |scaledCompensated μ B lam (Ns j) t s' - scaledCompensated μ B lam (Ns j) t' s'| :=
          abs_sub_le _ _ _
      _ < ε := by linarith only [k1, k2, k3, k4, k5, hεN]

/-- The Taylor error of `ℋ_N` is uniformly controlled on `[r, T] × [0, 3]` for large `N`. -/
theorem taylor_window (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hlamT : lam * (2 * T) ^ 2 ≤ η) {r : ℝ} (hr : 0 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ N in atTop, ∀ t ∈ Set.Icc r T, ∀ σ ∈ Set.Icc (0 : ℝ) 3,
      |scaledCompensated μ B lam N t σ - (-(σ * scaledDrift μ B lam N t) +
        σ ^ 2 * scaledSecond μ B lam N t / 2 - σ ^ 3 * scaledThird μ B lam N t / 6)| ≤
        A / N + 32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (T ^ 2 * Real.sqrt T) *
          (σ ^ 3 * Real.sqrt σ) := by
  have ha := log_pos_of_two_lt hB
  set MS := (2 * C + c) / r + 2 * C * lam * T
  set MD := (C + 4 * C * lam * T ^ 2 + 16 * C * lam ^ 2 * T ^ 4) / Real.log B
  set MK := (C * T + 8 * C * lam * T ^ 3) / Real.log B ^ 2
  set MP := (4 * C * T ^ 2 + 16 * C * lam * T ^ 4) / Real.log B ^ 3
  have hMS : 0 ≤ MS := by positivity
  have hMD : 0 ≤ MD := by positivity
  have hMK : 0 ≤ MK := by positivity
  have hMP : 0 ≤ MP := by positivity
  set Mp := 3 * MD + 9 * MK / 2 + 27 * MP / 6
  set A := 9 + 3 * MS + 3 * Mp
  refine ⟨A, by positivity, ?_⟩
  have hsm : ∀ᶠ N in atTop, 3 / (Real.log B * N) * (Real.log B - Real.log (floorSeq B 1)) ≤ 1 := by
    have h1 : Tendsto (fun N : ℝ => 3 / (Real.log B * N) * (Real.log B - Real.log (floorSeq B 1)))
        atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := 3 / Real.log B *
        (Real.log B - Real.log (floorSeq B 1)))).mul (tendsto_inv_atTop_zero (𝕜 := ℝ))
      rw [mul_zero] at this
      refine this.congr fun N => ?_
      ring
    exact ((tendsto_order.1 h1).2 _ one_pos).mono fun N hN => hN.le
  have hlb : 0 ≤ Real.log B - Real.log (floorSeq B 1) := by
    have := Real.log_nonpos (floorSeq_one_pos hB).le (floorSeq_le_one hB 1); linarith
  filter_upwards [unif_bounds hB hC hc hW hlam hT hlamT hr, eventually_ge_atTop 3, hsm]
    with N hN hN3 hsm3
  intro t ht σ hσ
  obtain ⟨hNpos, hb⟩ := hN
  obtain ⟨hNt2, hNt0, hn1, hS, hd, hK, hP, -⟩ := hb t ht
  have htpos : 0 < t := lt_of_lt_of_le hr ht.1
  have hwin : lam * (2 * t) ^ 2 ≤ η := by
    have : (2 * t) ^ 2 ≤ (2 * T) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith [ht.2]) 2
    exact (mul_le_mul_of_nonneg_left this hlam).trans hlamT
  have hσsmall : σ / (Real.log B * N) * (Real.log B - Real.log (floorSeq B 1)) ≤ 1 := by
    refine le_trans ?_ hsm3
    apply mul_le_mul_of_nonneg_right _ hlb
    exact div_le_div_of_nonneg_right hσ.2 (mul_pos ha hNpos).le
  have hT := scaled_taylor hpos hmean hB hC hc hW hlam hNpos htpos hNt2 hNt0 hwin hσ.1
    (by linarith [hσ.2]) hσsmall
  refine hT.trans ?_
  have hp : |-(σ * scaledDrift μ B lam N t) + σ ^ 2 * scaledSecond μ B lam N t / 2 -
      σ ^ 3 * scaledThird μ B lam N t / 6| ≤ Mp := by
    have h1 : |σ * scaledDrift μ B lam N t| ≤ 3 * MD := by
      rw [abs_mul, abs_of_nonneg hσ.1]; exact mul_le_mul hσ.2 hd (abs_nonneg _) (by norm_num)
    have h2 : |σ ^ 2 * scaledSecond μ B lam N t / 2| ≤ 9 * MK / 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg σ), abs_two]
      have : σ ^ 2 ≤ 9 := by nlinarith [hσ.1, hσ.2]
      have := mul_le_mul this hK (abs_nonneg _) (by norm_num)
      linarith
    have h3 : |σ ^ 3 * scaledThird μ B lam N t / 6| ≤ 27 * MP / 6 := by
      rw [abs_div, abs_mul, abs_of_nonneg (pow_nonneg hσ.1 3)]
      have : σ ^ 3 ≤ 27 := by
        have := pow_le_pow_left₀ hσ.1 hσ.2 3; norm_num at this; linarith
      have := mul_le_mul this hP (abs_nonneg _) (by norm_num)
      rw [show |(6 : ℝ)| = 6 by norm_num]
      linarith
    have e1 := abs_sub (-(σ * scaledDrift μ B lam N t) + σ ^ 2 * scaledSecond μ B lam N t / 2)
      (σ ^ 3 * scaledThird μ B lam N t / 6)
    have e2 := abs_add_le (-(σ * scaledDrift μ B lam N t)) (σ ^ 2 * scaledSecond μ B lam N t / 2)
    have e3 : |-(σ * scaledDrift μ B lam N t)| = |σ * scaledDrift μ B lam N t| := abs_neg _
    rw [show Mp = 3 * MD + 9 * MK / 2 + 27 * MP / 6 from rfl]
    linarith
  have k1 : σ ^ 2 / N ≤ 9 / N := div_le_div_of_nonneg_right (by nlinarith [hσ.1, hσ.2]) hNpos.le
  have k2 : σ / N * |scaledMass μ B lam N t| ≤ 3 * MS / N := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul hσ.2 hS (abs_nonneg _) (by norm_num)) hNpos.le
  have k3 : σ / N * |-(σ * scaledDrift μ B lam N t) + σ ^ 2 * scaledSecond μ B lam N t / 2 -
      σ ^ 3 * scaledThird μ B lam N t / 6| ≤ 3 * Mp / N := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul hσ.2 hp (abs_nonneg _) (by norm_num)) hNpos.le
  have k4 : 32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (σ ^ 3 * Real.sqrt σ) *
      (t ^ 2 * Real.sqrt t) ≤ 32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) *
        (T ^ 2 * Real.sqrt T) * (σ ^ 3 * Real.sqrt σ) := by
    have e1 : t ^ 2 * Real.sqrt t ≤ T ^ 2 * Real.sqrt T :=
      mul_le_mul (pow_le_pow_left₀ htpos.le ht.2 2) (Real.sqrt_le_sqrt ht.2) (Real.sqrt_nonneg _)
        (by positivity)
    have e2 : 0 ≤ 32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (σ ^ 3 * Real.sqrt σ) := by
      have := hσ.1; positivity
    calc _ ≤ 32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (σ ^ 3 * Real.sqrt σ) *
          (T ^ 2 * Real.sqrt T) := mul_le_mul_of_nonneg_left e1 e2
      _ = _ := by ring
  have k5 : A / N = 9 / N + 3 * MS / N + 3 * Mp / N := by ring
  linarith

theorem uniformCauchySeqOn_slices3 {F : ℕ → ℝ × ℝ → ℝ} {K₁ K₂ : Set ℝ}
    (hF : UniformCauchySeqOn F atTop (K₁ ×ˢ K₂)) {σ₁ σ₂ σ₃ : ℝ} (w₁ w₂ w₃ : ℝ)
    (h₁ : σ₁ ∈ K₂) (h₂ : σ₂ ∈ K₂) (h₃ : σ₃ ∈ K₂) :
    UniformCauchySeqOn (fun j t => w₁ * F j (t, σ₁) + w₂ * F j (t, σ₂) + w₃ * F j (t, σ₃))
      atTop K₁ := by
  rw [Metric.uniformCauchySeqOn_iff] at hF ⊢
  intro ε hε
  set W := |w₁| + |w₂| + |w₃| + 1 with hW
  have hW0 : 0 < W := by positivity
  obtain ⟨N, hN⟩ := hF (ε / W) (div_pos hε hW0)
  refine ⟨N, fun m hm n hn t ht => ?_⟩
  have e : ∀ (w σ : ℝ), σ ∈ K₂ → |w * F m (t, σ) - w * F n (t, σ)| ≤ |w| * (ε / W) := by
    intro w σ hσ
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := hN m hm n hn (t, σ) ⟨ht, hσ⟩
    rw [Real.dist_eq] at this
    exact this.le
  have e1 := e w₁ σ₁ h₁
  have e2 := e w₂ σ₂ h₂
  have e3 := e w₃ σ₃ h₃
  rw [Real.dist_eq]
  have hsplit : w₁ * F m (t, σ₁) + w₂ * F m (t, σ₂) + w₃ * F m (t, σ₃) -
      (w₁ * F n (t, σ₁) + w₂ * F n (t, σ₂) + w₃ * F n (t, σ₃)) =
      (w₁ * F m (t, σ₁) - w₁ * F n (t, σ₁)) + (w₂ * F m (t, σ₂) - w₂ * F n (t, σ₂)) +
        (w₃ * F m (t, σ₃) - w₃ * F n (t, σ₃)) := by ring
  rw [hsplit]
  have t1 := abs_add_le ((w₁ * F m (t, σ₁) - w₁ * F n (t, σ₁)) +
    (w₂ * F m (t, σ₂) - w₂ * F n (t, σ₂))) (w₃ * F m (t, σ₃) - w₃ * F n (t, σ₃))
  have t2 := abs_add_le (w₁ * F m (t, σ₁) - w₁ * F n (t, σ₁)) (w₂ * F m (t, σ₂) - w₂ * F n (t, σ₂))
  have t3 : (|w₁| + |w₂| + |w₃|) * (ε / W) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ hW0, hW]
    nlinarith
  have t4 : (|w₁| + |w₂| + |w₃|) * (ε / W) = |w₁| * (ε / W) + |w₂| * (ε / W) + |w₃| * (ε / W) := by
    ring
  linarith

theorem small_pow_facts {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    s ^ 3 * Real.sqrt s ≤ s * s ∧ s ^ 2 ≤ s := by
  have h1 : Real.sqrt s ≤ 1 := by simpa using Real.sqrt_le_sqrt hs1
  have h2 : s * s * s ≤ s * s * 1 := mul_le_mul_of_nonneg_left hs1 (by positivity)
  have h3 : s * s ≤ s * 1 := mul_le_mul_of_nonneg_left hs1 hs0.le
  constructor
  · calc s ^ 3 * Real.sqrt s ≤ s ^ 3 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = s * s * s := by ring
      _ ≤ s * s * 1 := h2
      _ = s * s := by ring
  · calc s ^ 2 = s * s := by ring
      _ ≤ s * 1 := h3
      _ = s := by ring

/-- Uniform bounds and the Taylor error on `[r, T]` for large `N`. -/
theorem dKP_prep (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hlamT : lam * (2 * T) ^ 2 ≤ η) {r : ℝ} (hr : 0 < r) :
    ∃ A MK MP C7 : ℝ, 0 ≤ A ∧ 0 ≤ MK ∧ 0 ≤ MP ∧ 0 ≤ C7 ∧ ∀ᶠ N in atTop, 0 < N ∧
      ∀ t ∈ Set.Icc r T, |scaledSecond μ B lam N t| ≤ MK ∧ |scaledThird μ B lam N t| ≤ MP ∧
        ∀ σ ∈ Set.Icc (0 : ℝ) 3,
          |scaledCompensated μ B lam N t σ - (-(σ * scaledDrift μ B lam N t) +
            σ ^ 2 * scaledSecond μ B lam N t / 2 - σ ^ 3 * scaledThird μ B lam N t / 6)| ≤
            A / N + C7 * (σ ^ 3 * Real.sqrt σ) := by
  have ha := log_pos_of_two_lt hB
  obtain ⟨A, hA, hev⟩ := taylor_window hpos hmean hB hC hc hW hlam hT hlamT hr
  refine ⟨A, (C * T + 8 * C * lam * T ^ 3) / Real.log B ^ 2,
    (4 * C * T ^ 2 + 16 * C * lam * T ^ 4) / Real.log B ^ 3,
    32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (T ^ 2 * Real.sqrt T), hA,
    by positivity, by positivity, by positivity, ?_⟩
  filter_upwards [hev, unif_bounds hB hC hc hW hlam hT hlamT hr] with N h1 h2
  refine ⟨h2.1, fun t ht => ?_⟩
  obtain ⟨-, -, -, -, -, hK, hP, -⟩ := h2.2 t ht
  exact ⟨hK, hP, h1 t ht⟩

/-- The scaled moments `d_N, 𝒦_N, 𝒫_N` are uniformly Cauchy on `[r, T]` once `ℋ_N` is. -/
theorem ucs_dKP (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hlamT : lam * (2 * T) ^ 2 ≤ η) {Ns : ℕ → ℝ}
    (hNs : Tendsto Ns atTop atTop) {r : ℝ} (hr : 0 < r)
    (hH : UniformCauchySeqOn (fun j (p : ℝ × ℝ) => scaledCompensated μ B lam (Ns j) p.1 p.2)
      atTop (Set.Icc r T ×ˢ Set.Icc 0 3)) :
    UniformCauchySeqOn (fun j t => scaledDrift μ B lam (Ns j) t) atTop (Set.Icc r T) ∧
    UniformCauchySeqOn (fun j t => scaledSecond μ B lam (Ns j) t) atTop (Set.Icc r T) ∧
    UniformCauchySeqOn (fun j t => scaledThird μ B lam (Ns j) t) atTop (Set.Icc r T) := by
  obtain ⟨A, MK, MP, C7, hA, hMK, hMP, hC7, hev⟩ :=
    dKP_prep hpos hmean hB hC hc hW hlam hT hlamT hr
  have hev' := hNs.eventually hev
  -- the error bound at the three weights
  have hE : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᶠ j in atTop, ∀ t ∈ Set.Icc r T,
      |scaledSecond μ B lam (Ns j) t| ≤ MK ∧ |scaledThird μ B lam (Ns j) t| ≤ MP ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ 3 →
        |scaledCompensated μ B lam (Ns j) t (k * s) - (-((k * s) * scaledDrift μ B lam (Ns j) t) +
          (k * s) ^ 2 * scaledSecond μ B lam (Ns j) t / 2 -
          (k * s) ^ 3 * scaledThird μ B lam (Ns j) t / 6)| ≤
          A / Ns j + C7 * (k ^ 3 * 2 * (s ^ 3 * Real.sqrt s)) := by
    intro s hs0 hs1
    filter_upwards [hev'] with j ⟨hN, hj⟩ t ht
    obtain ⟨hK, hP, hT'⟩ := hj t ht
    refine ⟨hK, hP, fun k hk1 hk3 => ?_⟩
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hk3R : (k : ℝ) ≤ 3 := by exact_mod_cast hk3
    have hσ : (k : ℝ) * s ∈ Set.Icc (0 : ℝ) 3 := ⟨by positivity, by nlinarith⟩
    refine (hT' _ hσ).trans ?_
    have hsq : Real.sqrt ((k : ℝ) * s) ≤ 2 * Real.sqrt s := by
      rw [Real.sqrt_mul (by positivity)]
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      rw [Real.sqrt_le_left (by norm_num)]; linarith
    have : ((k : ℝ) * s) ^ 3 * Real.sqrt ((k : ℝ) * s) ≤ (k : ℝ) ^ 3 * 2 * (s ^ 3 * Real.sqrt s) := by
      calc ((k : ℝ) * s) ^ 3 * Real.sqrt ((k : ℝ) * s) ≤ ((k : ℝ) * s) ^ 3 * (2 * Real.sqrt s) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = _ := by ring
    have := mul_le_mul_of_nonneg_left this hC7
    linarith
  have hsmall : ∀ x : ℝ, 0 < x → ∀ᶠ j in atTop, A / Ns j ≤ x := by
    intro x hx
    have h1 : Tendsto (fun j => A / Ns j) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hNs
    exact ((tendsto_order.1 h1).2 _ hx).mono fun j hj => hj.le
  refine ⟨?_, ?_, ?_⟩
  · -- the drift
    refine uniformCauchySeqOn_of_approx fun ε hε => ?_
    set K₁ := MK / 2 + MP / 6 + 2 * C7 + 1 with hK₁
    have hK₁0 : 0 < K₁ := by positivity
    set s := min 1 (ε / (2 * K₁)) with hs
    have hs0 : 0 < s := lt_min one_pos (by positivity)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hsK : s * K₁ ≤ ε / 2 := by
      have := mul_le_mul_of_nonneg_right (min_le_right 1 (ε / (2 * K₁))) hK₁0.le
      rw [← hs] at this
      calc s * K₁ ≤ ε / (2 * K₁) * K₁ := this
        _ = ε / 2 := by field_simp
    refine ⟨fun j t => (-1 / s) * scaledCompensated μ B lam (Ns j) t s + 0 *
      scaledCompensated μ B lam (Ns j) t s + 0 * scaledCompensated μ B lam (Ns j) t s,
      uniformCauchySeqOn_slices3 hH _ _ _ ⟨hs0.le, by linarith⟩ ⟨hs0.le, by linarith⟩
        ⟨hs0.le, by linarith⟩, ?_⟩
    filter_upwards [hE s hs0 hs1, hsmall (s * (ε / 2)) (by positivity)] with j hj hAj t ht
    obtain ⟨hK, hP, hT1⟩ := hj t ht
    have e1 := hT1 1 le_rfl (by norm_num)
    simp only [Nat.cast_one, one_mul, one_pow] at e1
    set H1 := scaledCompensated μ B lam (Ns j) t s
    set d := scaledDrift μ B lam (Ns j) t
    set K := scaledSecond μ B lam (Ns j) t
    set P := scaledThird μ B lam (Ns j) t
    have hid : d - ((-1 / s) * H1 + 0 * H1 + 0 * H1) =
        (H1 - (-(s * d) + s ^ 2 * K / 2 - s ^ 3 * P / 6)) / s + (s * K / 2 - s ^ 2 * P / 6) := by
      field_simp
      ring
    rw [hid]
    obtain ⟨hs3, hs2⟩ := small_pow_facts hs0 hs1
    have k1 : |(H1 - (-(s * d) + s ^ 2 * K / 2 - s ^ 3 * P / 6)) / s| ≤
        A / Ns j / s + 2 * C7 * s := by
      rw [abs_div, abs_of_pos hs0, div_le_iff₀ hs0, add_mul,
        show A / Ns j / s * s = A / Ns j by field_simp]
      have : C7 * (1 * 2 * (s ^ 3 * Real.sqrt s)) ≤ 2 * C7 * s * s := by
        have := mul_le_mul_of_nonneg_left hs3 hC7; linarith
      linarith
    have k2 : |s * K / 2 - s ^ 2 * P / 6| ≤ s * MK / 2 + s * MP / 6 := by
      have h1 : |s * K / 2| ≤ s * MK / 2 := by
        rw [abs_div, abs_mul, abs_of_pos hs0, abs_two]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hK hs0.le) (by norm_num)
      have h2 : |s ^ 2 * P / 6| ≤ s * MP / 6 := by
        rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg s), show |(6 : ℝ)| = 6 by norm_num]
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul hs2 hP (abs_nonneg _) hs0.le
      exact (abs_sub _ _).trans (add_le_add h1 h2)
    have k3 : A / Ns j / s ≤ ε / 2 := by
      rw [div_le_iff₀ hs0]; linarith
    have k4 : s * MK / 2 + s * MP / 6 + 2 * C7 * s ≤ s * K₁ := by
      rw [hK₁]; linarith
    calc _ ≤ |(H1 - (-(s * d) + s ^ 2 * K / 2 - s ^ 3 * P / 6)) / s| +
          |s * K / 2 - s ^ 2 * P / 6| := abs_add_le _ _
      _ ≤ ε := by linarith
  · -- the second moment
    refine uniformCauchySeqOn_of_approx fun ε hε => ?_
    set K₂ := MP + 20 * C7 + 1 with hK₂
    have hK₂0 : 0 < K₂ := by positivity
    set s := min 1 (ε / (2 * K₂)) with hs
    have hs0 : 0 < s := lt_min one_pos (by positivity)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hsK : s * K₂ ≤ ε / 2 := by
      have := mul_le_mul_of_nonneg_right (min_le_right 1 (ε / (2 * K₂))) hK₂0.le
      rw [← hs] at this
      calc s * K₂ ≤ ε / (2 * K₂) * K₂ := this
        _ = ε / 2 := by field_simp
    refine ⟨fun j t => (-2 / s ^ 2) * scaledCompensated μ B lam (Ns j) t s +
      (1 / s ^ 2) * scaledCompensated μ B lam (Ns j) t (2 * s) +
      0 * scaledCompensated μ B lam (Ns j) t s,
      uniformCauchySeqOn_slices3 hH _ _ _ ⟨hs0.le, by linarith⟩ ⟨by linarith, by linarith⟩
        ⟨hs0.le, by linarith⟩, ?_⟩
    filter_upwards [hE s hs0 hs1, hsmall (s ^ 2 * (ε / 6)) (by positivity)] with j hj hAj t ht
    obtain ⟨hK, hP, hT1⟩ := hj t ht
    have e1 := hT1 1 le_rfl (by norm_num)
    have e2 := hT1 2 (by norm_num) (by norm_num)
    simp only [Nat.cast_one, one_mul, one_pow, Nat.cast_ofNat] at e1 e2
    set H1 := scaledCompensated μ B lam (Ns j) t s
    set H2 := scaledCompensated μ B lam (Ns j) t (2 * s)
    set d := scaledDrift μ B lam (Ns j) t
    set K := scaledSecond μ B lam (Ns j) t
    set P := scaledThird μ B lam (Ns j) t
    have hid : K - ((-2 / s ^ 2) * H1 + (1 / s ^ 2) * H2 + 0 * H1) =
        s * P - ((H2 - (-((2 * s) * d) + (2 * s) ^ 2 * K / 2 - (2 * s) ^ 3 * P / 6)) -
          2 * (H1 - (-(s * d) + s ^ 2 * K / 2 - s ^ 3 * P / 6))) / s ^ 2 := by
      field_simp
      ring
    rw [hid]
    obtain ⟨hs3, hs2⟩ := small_pow_facts hs0 hs1
    have hs2' : 0 < s ^ 2 := by positivity
    have k1 : |((H2 - (-((2 * s) * d) + (2 * s) ^ 2 * K / 2 - (2 * s) ^ 3 * P / 6)) -
        2 * (H1 - (-(s * d) + s ^ 2 * K / 2 - s ^ 3 * P / 6))) / s ^ 2| ≤
        3 * (A / Ns j) / s ^ 2 + 20 * C7 * s := by
      rw [abs_div, abs_of_pos hs2', div_le_iff₀ hs2', add_mul,
        show 3 * (A / Ns j) / s ^ 2 * s ^ 2 = 3 * (A / Ns j) by field_simp]
      have t1 := abs_sub (H2 - (-((2 * s) * d) + (2 * s) ^ 2 * K / 2 - (2 * s) ^ 3 * P / 6))
        (2 * (H1 - (-(s * d) + s ^ 2 * K / 2 - s ^ 3 * P / 6)))
      rw [abs_mul, abs_two] at t1
      have t2 : C7 * (s ^ 3 * Real.sqrt s) ≤ C7 * (s * s ^ 2) := by
        have h1 : Real.sqrt s ≤ 1 := by simpa using Real.sqrt_le_sqrt hs1
        refine mul_le_mul_of_nonneg_left ?_ hC7
        calc s ^ 3 * Real.sqrt s ≤ s ^ 3 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = s * s ^ 2 := by ring
      have t3 : (2 : ℝ) ^ 3 * 2 * (s ^ 3 * Real.sqrt s) = 16 * (s ^ 3 * Real.sqrt s) := by
        norm_num
      rw [t3] at e2
      linarith
    have k2 : |s * P| ≤ s * MP := by
      rw [abs_mul, abs_of_pos hs0]; exact mul_le_mul_of_nonneg_left hP hs0.le
    have k3 : 3 * (A / Ns j) / s ^ 2 ≤ ε / 2 := by
      rw [div_le_iff₀ hs2']; linarith
    have k4 : s * MP + 20 * C7 * s ≤ s * K₂ := by
      rw [hK₂]; linarith
    calc _ ≤ |s * P| + |((H2 - (-((2 * s) * d) + (2 * s) ^ 2 * K / 2 - (2 * s) ^ 3 * P / 6)) -
          2 * (H1 - (-(s * d) + s ^ 2 * K / 2 - s ^ 3 * P / 6))) / s ^ 2| := abs_sub _ _
      _ ≤ ε := by linarith
  · -- the third moment
    refine uniformCauchySeqOn_of_approx fun ε hε => ?_
    set K₃ := 2 * (110 * C7 + 1) with hK₃
    have hK₃0 : 0 < K₃ := by positivity
    set s := min 1 ((ε / K₃) ^ 2) with hs
    have hs0 : 0 < s := lt_min one_pos (by positivity)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hsq : Real.sqrt s ≤ ε / K₃ := by
      rw [Real.sqrt_le_left (by positivity)]; exact min_le_right _ _
    have hsK : 110 * C7 * Real.sqrt s ≤ ε / 2 := by
      calc 110 * C7 * Real.sqrt s ≤ 110 * C7 * (ε / K₃) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ ≤ ε / 2 := by
            rw [hK₃, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            linarith
    refine ⟨fun j t => (-3 / s ^ 3) * scaledCompensated μ B lam (Ns j) t s +
      (3 / s ^ 3) * scaledCompensated μ B lam (Ns j) t (2 * s) +
      (-1 / s ^ 3) * scaledCompensated μ B lam (Ns j) t (3 * s),
      uniformCauchySeqOn_slices3 hH _ _ _ ⟨hs0.le, by linarith⟩ ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩, ?_⟩
    filter_upwards [hE s hs0 hs1, hsmall (s ^ 3 * (ε / 14)) (by positivity)] with j hj hAj t ht
    obtain ⟨hK, hP, hT1⟩ := hj t ht
    have e1 := hT1 1 le_rfl (by norm_num)
    have e2 := hT1 2 (by norm_num) (by norm_num)
    have e3 := hT1 3 (by norm_num) le_rfl
    simp only [Nat.cast_one, one_mul, one_pow, Nat.cast_ofNat] at e1 e2 e3
    set H1 := scaledCompensated μ B lam (Ns j) t s
    set H2 := scaledCompensated μ B lam (Ns j) t (2 * s)
    set H3 := scaledCompensated μ B lam (Ns j) t (3 * s)
    set d := scaledDrift μ B lam (Ns j) t
    set K := scaledSecond μ B lam (Ns j) t
    set P := scaledThird μ B lam (Ns j) t
    set E1 := H1 - (-(s * d) + s ^ 2 * K / 2 - s ^ 3 * P / 6)
    set E2 := H2 - (-((2 * s) * d) + (2 * s) ^ 2 * K / 2 - (2 * s) ^ 3 * P / 6)
    set E3 := H3 - (-((3 * s) * d) + (3 * s) ^ 2 * K / 2 - (3 * s) ^ 3 * P / 6)
    have hid : P - ((-3 / s ^ 3) * H1 + (3 / s ^ 3) * H2 + (-1 / s ^ 3) * H3) =
        (E3 - 3 * E2 + 3 * E1) / s ^ 3 := by
      field_simp
      ring
    rw [hid]
    have hs3' : 0 < s ^ 3 := by positivity
    rw [abs_div, abs_of_pos hs3', div_le_iff₀ hs3']
    have t1 := abs_add_le (E3 - 3 * E2) (3 * E1)
    have t2 := abs_sub E3 (3 * E2)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at t1 t2
    have t3 : (3 : ℝ) ^ 3 * 2 * (s ^ 3 * Real.sqrt s) = 54 * (s ^ 3 * Real.sqrt s) := by norm_num
    have t4 : (2 : ℝ) ^ 3 * 2 * (s ^ 3 * Real.sqrt s) = 16 * (s ^ 3 * Real.sqrt s) := by norm_num
    rw [t3] at e3
    rw [t4] at e2
    have t6 : C7 * (s ^ 3 * Real.sqrt s) * 108 ≤ ε / 2 * s ^ 3 := by
      have := mul_le_mul_of_nonneg_left hsK (by positivity : (0 : ℝ) ≤ s ^ 3)
      have : 0 ≤ C7 * (s ^ 3 * Real.sqrt s) := by positivity
      linarith
    linarith

/-- Eventual bounds for `S_N`, `ℋ_N` and the Riccati right-hand side on `[r, T] × [0, M]`. -/
theorem riccati_bounds (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hlamT : lam * (2 * T) ^ 2 ≤ η) {r M : ℝ} (hr : 0 < r)
    (hM : 0 ≤ M) :
    ∃ MF : ℝ, 0 ≤ MF ∧ ∀ᶠ N in atTop, 0 < N ∧ ∀ τ ∈ Set.Icc r T, ∀ s ∈ Set.Icc 0 M,
      |scaledMass μ B lam N τ| ≤ MF ∧ |scaledCompensated μ B lam N τ s| ≤ MF ∧
      |scaledMass μ B lam N τ * scaledCompensated μ B lam N τ s +
        scaledCompensated μ B lam N τ s ^ 2 / 2 - s ^ 2 / 2| ≤ MF := by
  have ha := log_pos_of_two_lt hB
  set MS := (2 * C + c) / (4 * r / 4) + 2 * C * lam * T
  set MD := (C + 4 * C * lam * T ^ 2 + 16 * C * lam ^ 2 * T ^ 4) / Real.log B
  have hMS0 : 0 ≤ MS := by positivity
  have hMD0 : 0 ≤ MD := by positivity
  set L := 1 + 2 * MD + 2 * (1 + 2 * (-Real.log (floorSeq B 1)) / Real.log B) * (1 + MS)
  have hβ0 : 0 ≤ -Real.log (floorSeq B 1) :=
    neg_nonneg.2 (Real.log_nonpos (floorSeq_one_pos hB).le (floorSeq_le_one hB 1))
  have hL0 : 0 ≤ L := by positivity
  set MH := (M + 1) * L
  have hMH0 : 0 ≤ MH := by positivity
  refine ⟨MS + MH + MS * MH + MH ^ 2 / 2 + M ^ 2 / 2, by positivity, ?_⟩
  have hsm : ∀ᶠ N in atTop, (M + 1) / (Real.log B * N) * (-Real.log (floorSeq B 1)) ≤
      Real.log 2 := by
    have h1 : Tendsto (fun N : ℝ => (M + 1) / (Real.log B * N) * (-Real.log (floorSeq B 1)))
        atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := (M + 1) / Real.log B *
        (-Real.log (floorSeq B 1)))).mul (tendsto_inv_atTop_zero (𝕜 := ℝ))
      rw [mul_zero] at this
      refine this.congr fun N => ?_
      ring
    exact ((tendsto_order.1 h1).2 _ (Real.log_pos (by norm_num))).mono fun N hN => hN.le
  have hr4 : (0 : ℝ) < 4 * r / 4 := by positivity
  filter_upwards [unif_bounds hB hC hc hW hlam hT hlamT hr4, eventually_ge_atTop 1, hsm]
    with N hN hN1 hsmN
  obtain ⟨hNpos, hb⟩ := hN
  have hb' : ∀ t ∈ Set.Icc ((4 * r) / 4) T, 1 ≤ ⌊N * t⌋₊ ∧ |scaledMass μ B lam N t| ≤ MS ∧
      |scaledDrift μ B lam N t| ≤ MD := fun t ht => by
    obtain ⟨-, -, hn1, hS, hd, -⟩ := hb t ht
    exact ⟨hn1, hS, hd⟩
  have hlip := win_lip hpos hmean hB (r := 4 * r) (M := M) (MS := MS) (MD := MD) hNpos hN1 hsmN hb'
  refine ⟨hNpos, fun τ hτ s hs => ?_⟩
  have hτ' : τ ∈ Set.Icc ((4 * r) / 4) T := by
    rw [show (4 * r) / 4 = r by ring]; exact hτ
  have hS := (hb' τ hτ').2.1
  have hsI : s ∈ Set.Icc 0 (M + 1) := ⟨hs.1, by linarith [hs.2]⟩
  have h0 : scaledCompensated μ B lam N τ 0 = 0 := by simp [scaledCompensated]
  have hH : |scaledCompensated μ B lam N τ s| ≤ MH := by
    have := hlip τ hτ' s hsI 0 ⟨le_rfl, by linarith⟩
    rw [h0, sub_zero, sub_zero, abs_of_nonneg hs.1] at this
    calc _ ≤ L * s := this
      _ ≤ L * (M + 1) := mul_le_mul_of_nonneg_left (by linarith [hs.2]) hL0
      _ = MH := by ring
  have k1 : |scaledMass μ B lam N τ * scaledCompensated μ B lam N τ s| ≤ MS * MH := by
    rw [abs_mul]; exact mul_le_mul hS hH (abs_nonneg _) hMS0
  have k2 : scaledCompensated μ B lam N τ s ^ 2 ≤ MH ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hH 2
  have k3 : s ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hs.1 hs.2 2
  have k4 : 0 ≤ scaledCompensated μ B lam N τ s ^ 2 := sq_nonneg _
  have k5 : 0 ≤ s ^ 2 := sq_nonneg _
  have k6 : 0 ≤ MS * MH := by positivity
  have k7 : 0 ≤ MH ^ 2 := sq_nonneg _
  have k8 : 0 ≤ M ^ 2 := sq_nonneg _
  have k1' := abs_le.1 k1
  refine ⟨by linarith, by linarith, ?_⟩
  rw [abs_le]
  constructor <;> linarith

theorem riccatiGen_floor_eq (μ : Measure ℝ) (B lam N τ s : ℝ) :
    riccatiGen μ B (scalingField μ B lam N) N ⌊N * τ⌋₊ s =
      scaledMass μ B lam N τ * scaledCompensated μ B lam N τ s +
        scaledCompensated μ B lam N τ s ^ 2 / 2 - s ^ 2 / 2 := by
  rw [riccatiGen, compGen, scaledMass, scaledCompensated, transformAt_zero]

/-- Changing the endpoints of an interval integral of a bounded function. -/
theorem abs_integral_endpoints_le {f : ℝ → ℝ} {a b a' b' M : ℝ}
    (hi : ∀ x y : ℝ, IntervalIntegrable f volume x y)
    (ha : ∀ x ∈ Set.uIcc a a', |f x| ≤ M) (hb : ∀ x ∈ Set.uIcc b b', |f x| ≤ M) :
    |(∫ x in a'..b', f x) - ∫ x in a..b, f x| ≤ M * (|a' - a| + |b' - b|) := by
  rw [intervalIntegral.integral_interval_sub_interval_comm' (hi a' b') (hi a b) (hi a' a)]
  have h1 : ‖∫ x in b..b', f x‖ ≤ M * |b' - b| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      hb x (Set.uIoc_subset_uIcc hx)
  have h2 : ‖∫ x in a..a', f x‖ ≤ M * |a' - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      ha x (Set.uIoc_subset_uIcc hx)
  rw [Real.norm_eq_abs] at h1 h2
  calc |(∫ x in b..b', f x) - ∫ x in a..a', f x| ≤
      |∫ x in b..b', f x| + |∫ x in a..a', f x| := abs_sub _ _
    _ ≤ _ := by linarith

theorem floor_div_near {N x : ℝ} (hN : 0 < N) (hx : 0 ≤ x) :
    (⌊N * x⌋₊ : ℝ) / N ≤ x ∧ x - 1 / N < (⌊N * x⌋₊ : ℝ) / N := by
  have h1 : (⌊N * x⌋₊ : ℝ) ≤ N * x := Nat.floor_le (by positivity)
  have h2 : N * x < (⌊N * x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  constructor
  · rw [div_le_iff₀ hN]; linarith
  · have : x - 1 / N = (N * x - 1) / N := by field_simp
    rw [this, div_lt_div_iff_of_pos_right hN]; linarith

/-- The Riccati identity in the limit. -/
theorem riccati_limit (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hlamT : lam * (2 * T) ^ 2 ≤ η) {Ns : ℕ → ℝ}
    (hNs : Tendsto Ns atTop atTop) {S : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hS : ∀ t ∈ Set.Ioc 0 T, Tendsto (fun j => scaledMass μ B lam (Ns j) t) atTop (𝓝 (S t)))
    (hH : ∀ t ∈ Set.Ioc 0 T, ∀ s : ℝ, 0 ≤ s →
      Tendsto (fun j => scaledCompensated μ B lam (Ns j) t s) atTop (𝓝 (H t s)))
    {s : ℝ} (hs : 0 ≤ s) {r t : ℝ} (hr : 0 < r) (hrt : r ≤ t) (htT : t ≤ T) :
    H t s - H r s = ∫ τ in r..t, (S τ * H τ s + H τ s ^ 2 / 2 - s ^ 2 / 2) := by
  obtain ⟨MF, hMF0, hev⟩ := riccati_bounds hpos hmean hB hC hc hW hlam hT hlamT
    (r := r / 2) (M := s) (by linarith) hs
  obtain ⟨N₁, Cr, hric⟩ := scaled_riccati (μ := μ) hpos hmean hB (r := r) (T := T) (s₁ := s)
    (M := MF) hr (hrt.trans htT) hs
  -- the integrands
  set F : ℕ → ℝ → ℝ := fun j τ =>
    riccatiGen μ B (scalingField μ B lam (Ns j)) (Ns j) ⌊Ns j * τ⌋₊ s with hF
  have hFeq : ∀ j τ, F j τ = scaledMass μ B lam (Ns j) τ * scaledCompensated μ B lam (Ns j) τ s +
      scaledCompensated μ B lam (Ns j) τ s ^ 2 / 2 - s ^ 2 / 2 :=
    fun j τ => riccatiGen_floor_eq μ B lam (Ns j) τ s
  have hev' := hNs.eventually (hev.and ((eventually_ge_atTop N₁).and (eventually_ge_atTop (2 / r))))
  -- convergence of the integrals
  have hlimInt : Tendsto (fun j => ∫ τ in r..t, F j τ) atTop
      (𝓝 (∫ τ in r..t, (S τ * H τ s + H τ s ^ 2 / 2 - s ^ 2 / 2))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => MF) ?_ ?_
      intervalIntegrable_const ?_
    · exact Eventually.of_forall fun j => (measurable_floor_comp
        (fun n => riccatiGen μ B (scalingField μ B lam (Ns j)) (Ns j) n s) (Ns j)).aestronglyMeasurable
    · filter_upwards [hev'] with j hj
      refine Eventually.of_forall fun τ hτ => ?_
      have hτI : τ ∈ Set.Icc (r / 2) T := by
        rw [Set.uIoc_of_le hrt] at hτ
        exact ⟨by linarith [hτ.1], hτ.2.trans htT⟩
      rw [Real.norm_eq_abs, hFeq]
      exact (hj.1.2 τ hτI s ⟨hs, le_rfl⟩).2.2
    · refine Eventually.of_forall fun τ hτ => ?_
      rw [Set.uIoc_of_le hrt] at hτ
      have hτI : τ ∈ Set.Ioc 0 T := ⟨by linarith [hτ.1], hτ.2.trans htT⟩
      simp only [hFeq]
      exact (((hS τ hτI).mul (hH τ hτI s hs)).add ((hH τ hτI s hs).pow 2 |>.div_const 2)).sub
        tendsto_const_nhds
  -- the Riemann sums
  have hdiff : Tendsto (fun j => (scaledCompensated μ B lam (Ns j) t s -
      scaledCompensated μ B lam (Ns j) r s) - ∫ τ in r..t, F j τ) atTop (𝓝 0) := by
    have hbound : ∀ᶠ j in atTop, |(scaledCompensated μ B lam (Ns j) t s -
        scaledCompensated μ B lam (Ns j) r s) - ∫ τ in r..t, F j τ| ≤ (Cr + 2 * MF) / Ns j := by
      filter_upwards [hev'] with j ⟨⟨hNpos, hb⟩, hN₁, hN2⟩
      set N := Ns j with hN_def
      have hNr : 1 / N ≤ r / 2 := by
        rw [div_le_iff₀ hNpos]; rw [div_le_iff₀ hr] at hN2; linarith
      have h1 := hric N hN₁ lam (fun τ hτ => (hb τ hτ s ⟨hs, le_rfl⟩).1) s ⟨hs, le_rfl⟩ r t le_rfl
        hrt htT
      have hsum : (∑ n ∈ Finset.Ico ⌊N * r⌋₊ ⌊N * t⌋₊,
          riccatiGen μ B (scalingField μ B lam N) N n s) / N =
          ∫ τ in (⌊N * r⌋₊ : ℝ) / N..(⌊N * t⌋₊ : ℝ) / N, F j τ := by
        rw [integral_floor_comp (fun n => riccatiGen μ B (scalingField μ B lam N) N n s) hNpos _ _
          (Nat.floor_le_floor (mul_le_mul_of_nonneg_left hrt hNpos.le))]
      rw [hsum] at h1
      obtain ⟨hr1, hr2⟩ := floor_div_near hNpos hr.le
      obtain ⟨ht1, ht2⟩ := floor_div_near hNpos (hr.le.trans hrt)
      have hbd : ∀ x ∈ Set.Icc (r / 2) T, |F j x| ≤ MF := fun x hx => by
        rw [hFeq]; exact (hb x hx s ⟨hs, le_rfl⟩).2.2
      have h2 := abs_integral_endpoints_le (f := F j) (a := r) (b := t)
        (a' := (⌊N * r⌋₊ : ℝ) / N) (b' := (⌊N * t⌋₊ : ℝ) / N) (M := MF)
        (fun x y => intervalIntegrable_floor_comp
          (fun n => riccatiGen μ B (scalingField μ B lam N) N n s) hNpos x y)
        (fun x hx => hbd x (by
          rw [Set.uIcc_of_ge hr1] at hx
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩))
        (fun x hx => hbd x (by
          rw [Set.uIcc_of_ge ht1] at hx
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩))
      have h3 : |(⌊N * r⌋₊ : ℝ) / N - r| + |(⌊N * t⌋₊ : ℝ) / N - t| ≤ 2 / N := by
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        have : 2 / N = 1 / N + 1 / N := by ring
        linarith
      have h4 : MF * (|(⌊N * r⌋₊ : ℝ) / N - r| + |(⌊N * t⌋₊ : ℝ) / N - t|) ≤ MF * (2 / N) :=
        mul_le_mul_of_nonneg_left h3 hMF0
      have h5 : (Cr + 2 * MF) / N = Cr / N + MF * (2 / N) := by ring
      have a1 := abs_le.1 h1
      have a2 := abs_le.1 h2
      rw [abs_le]
      constructor <;> linarith
    have hlim0 : Tendsto (fun j => (Cr + 2 * MF) / Ns j) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hNs
    exact squeeze_zero_norm' (hbound.mono fun j hj => by rw [Real.norm_eq_abs]; exact hj) hlim0
  have hHt := hH t ⟨hr.trans_le hrt, htT⟩ s hs
  have hHr := hH r ⟨hr, hrt.trans htT⟩ s hs
  have hA : Tendsto (fun j => scaledCompensated μ B lam (Ns j) t s -
      scaledCompensated μ B lam (Ns j) r s) atTop (𝓝 (H t s - H r s)) := hHt.sub hHr
  have hB' : Tendsto (fun j => scaledCompensated μ B lam (Ns j) t s -
      scaledCompensated μ B lam (Ns j) r s) atTop
      (𝓝 (∫ τ in r..t, (S τ * H τ s + H τ s ^ 2 / 2 - s ^ 2 / 2))) := by
    have := hdiff.add hlimInt
    simp only [zero_add, sub_add_cancel] at this
    exact this
  exact tendsto_nhds_unique hA hB'

end Assembly

/-! ### The moment equations from the Riccati equation -/

theorem ii_of_bdd {f : ℝ → ℝ} {r t M : ℝ} (hrt : r ≤ t) (hf : Measurable f)
    (hb : ∀ τ ∈ Set.Icc r t, |f τ| ≤ M) : IntervalIntegrable f volume r t := by
  refine (intervalIntegrable_const (c := M)).mono_fun hf.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun τ hτ => ?_)
  rw [Set.uIoc_of_le hrt] at hτ
  have := hb τ ⟨hτ.1.le, hτ.2⟩
  show ‖f τ‖ ≤ ‖M‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact this.trans (le_abs_self M)

/-- Pointwise expansion of the Riccati right-hand side. -/
theorem riccati_poly_bound {S d K P H s MS MD MK MP C₇ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hS : |S| ≤ MS) (hd : |d| ≤ MD) (hK : |K| ≤ MK) (hP : |P| ≤ MP) (hC₇ : 0 ≤ C₇)
    (hH : |H - (-(s * d) + s ^ 2 * K / 2 - s ^ 3 * P / 6)| ≤ C₇ * (s ^ 3 * Real.sqrt s)) :
    |S * H + H ^ 2 / 2 - s ^ 2 / 2 - (-(s * (S * d)) + s ^ 2 * (S * K + d ^ 2 - 1) / 2 -
        s ^ 3 * (S * P + 3 * d * K) / 6)| ≤
      (MS * C₇ + (MD + MK + MP) * C₇ + C₇ ^ 2 + MK ^ 2 + MD * MP + MK * MP + MP ^ 2) *
        (s ^ 3 * Real.sqrt s) := by
  have hMS : 0 ≤ MS := (abs_nonneg _).trans hS
  have hMD : 0 ≤ MD := (abs_nonneg _).trans hd
  have hMK : 0 ≤ MK := (abs_nonneg _).trans hK
  have hMP : 0 ≤ MP := (abs_nonneg _).trans hP
  set p := -(s * d) + s ^ 2 * K / 2 - s ^ 3 * P / 6 with hp
  set ρ := H - p with hρ
  set X := s ^ 3 * Real.sqrt s with hX
  have hsq1 : Real.sqrt s ≤ 1 := by simpa using Real.sqrt_le_sqrt hs1
  have hssq : s ≤ Real.sqrt s := by
    rw [Real.le_sqrt hs0 hs0]
    calc s ^ 2 = s * s := by ring
      _ ≤ s * 1 := mul_le_mul_of_nonneg_left hs1 hs0
      _ = s := by ring
  have hs2 : s ^ 2 ≤ 1 := by
    calc s ^ 2 = s * s := by ring
      _ ≤ 1 * 1 := mul_le_mul hs1 hs1 hs0 zero_le_one
      _ = 1 := by ring
  have hs3 : s ^ 3 ≤ 1 := by
    calc s ^ 3 = s ^ 2 * s := by ring
      _ ≤ 1 * 1 := mul_le_mul hs2 hs1 hs0 zero_le_one
      _ = 1 := by ring
  have hX0 : 0 ≤ X := by positivity
  have hX1 : X ≤ 1 := by
    calc X = s ^ 3 * Real.sqrt s := rfl
      _ ≤ 1 * 1 := mul_le_mul hs3 hsq1 (Real.sqrt_nonneg _) zero_le_one
      _ = 1 := by ring
  have hs4 : s ^ 4 ≤ X := by
    calc s ^ 4 = s ^ 3 * s := by ring
      _ ≤ s ^ 3 * Real.sqrt s := mul_le_mul_of_nonneg_left hssq (by positivity)
  have hs5 : s ^ 5 ≤ s ^ 4 := by
    calc s ^ 5 = s ^ 4 * s := by ring
      _ ≤ s ^ 4 * 1 := mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = s ^ 4 := by ring
  have hs6 : s ^ 6 ≤ s ^ 4 := by
    calc s ^ 6 = s ^ 4 * s ^ 2 := by ring
      _ ≤ s ^ 4 * 1 := mul_le_mul_of_nonneg_left hs2 (by positivity)
      _ = s ^ 4 := by ring
  have hid : S * H + H ^ 2 / 2 - s ^ 2 / 2 - (-(s * (S * d)) + s ^ 2 * (S * K + d ^ 2 - 1) / 2 -
      s ^ 3 * (S * P + 3 * d * K) / 6) =
      S * ρ + p * ρ + ρ ^ 2 / 2 + (s ^ 4 * (K ^ 2 / 4 + d * P / 3) / 2 -
        s ^ 5 * (K * P) / 12 + s ^ 6 * P ^ 2 / 72) := by
    rw [hρ, hp]; ring
  rw [hid]
  have hρb : |ρ| ≤ C₇ * X := hH
  have b1 : |S * ρ| ≤ MS * (C₇ * X) := by
    rw [abs_mul]; exact mul_le_mul hS hρb (abs_nonneg _) hMS
  have hpb : |p| ≤ MD + MK + MP := by
    have e1 : |s * d| ≤ MD := by
      rw [abs_mul, abs_of_nonneg hs0]
      calc s * |d| ≤ 1 * MD := mul_le_mul hs1 hd (abs_nonneg _) zero_le_one
        _ = MD := one_mul _
    have e2 : |s ^ 2 * K / 2| ≤ MK := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg s), abs_two]
      have : s ^ 2 * |K| ≤ 1 * MK := mul_le_mul hs2 hK (abs_nonneg _) zero_le_one
      linarith
    have e3 : |s ^ 3 * P / 6| ≤ MP := by
      rw [abs_div, abs_mul, abs_of_nonneg (pow_nonneg hs0 3), show |(6 : ℝ)| = 6 by norm_num]
      have : s ^ 3 * |P| ≤ 1 * MP := mul_le_mul hs3 hP (abs_nonneg _) zero_le_one
      linarith
    have f1 := abs_sub (-(s * d) + s ^ 2 * K / 2) (s ^ 3 * P / 6)
    have f2 := abs_add_le (-(s * d)) (s ^ 2 * K / 2)
    have f3 : |-(s * d)| = |s * d| := abs_neg _
    rw [hp]
    linarith
  have b2 : |p * ρ| ≤ (MD + MK + MP) * (C₇ * X) := by
    rw [abs_mul]; exact mul_le_mul hpb hρb (abs_nonneg _) (by positivity)
  have b3 : |ρ ^ 2 / 2| ≤ C₇ ^ 2 * X := by
    rw [abs_div, abs_two, abs_pow]
    have : |ρ| ^ 2 ≤ (C₇ * X) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hρb 2
    have h2 : (C₇ * X) ^ 2 ≤ C₇ ^ 2 * X := by
      calc (C₇ * X) ^ 2 = C₇ ^ 2 * (X * X) := by ring
        _ ≤ C₇ ^ 2 * (X * 1) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left hX1 hX0
        _ = C₇ ^ 2 * X := by ring
    have : 0 ≤ C₇ ^ 2 * X := by positivity
    linarith
  have b4 : |s ^ 4 * (K ^ 2 / 4 + d * P / 3) / 2 - s ^ 5 * (K * P) / 12 + s ^ 6 * P ^ 2 / 72| ≤
      (MK ^ 2 + MD * MP + MK * MP + MP ^ 2) * X := by
    have hK2 : K ^ 2 ≤ MK ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hK 2
    have hP2 : P ^ 2 ≤ MP ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hP 2
    have hdP : |d * P| ≤ MD * MP := by
      rw [abs_mul]; exact mul_le_mul hd hP (abs_nonneg _) hMD
    have hKP : |K * P| ≤ MK * MP := by
      rw [abs_mul]; exact mul_le_mul hK hP (abs_nonneg _) hMK
    have c1 : |s ^ 4 * (K ^ 2 / 4 + d * P / 3) / 2| ≤ (MK ^ 2 + MD * MP) * X := by
      rw [abs_div, abs_two, abs_mul, abs_of_nonneg (pow_nonneg hs0 4)]
      have e1 : |K ^ 2 / 4 + d * P / 3| ≤ MK ^ 2 + MD * MP := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_div, abs_div, abs_of_nonneg (sq_nonneg K), show |(4 : ℝ)| = 4 by norm_num,
          show |(3 : ℝ)| = 3 by norm_num]
        have : 0 ≤ MK ^ 2 := sq_nonneg _
        have : 0 ≤ MD * MP := by positivity
        have : 0 ≤ |d * P| := abs_nonneg _
        linarith
      have e2 : s ^ 4 * |K ^ 2 / 4 + d * P / 3| ≤ X * (MK ^ 2 + MD * MP) :=
        mul_le_mul hs4 e1 (abs_nonneg _) hX0
      have : 0 ≤ X * (MK ^ 2 + MD * MP) := by positivity
      linarith
    have c2 : |s ^ 5 * (K * P) / 12| ≤ MK * MP * X := by
      rw [abs_div, abs_mul, abs_of_nonneg (pow_nonneg hs0 5), show |(12 : ℝ)| = 12 by norm_num]
      have e2 : s ^ 5 * |K * P| ≤ X * (MK * MP) := mul_le_mul (hs5.trans hs4) hKP (abs_nonneg _) hX0
      have : 0 ≤ X * (MK * MP) := by positivity
      linarith
    have c3 : |s ^ 6 * P ^ 2 / 72| ≤ MP ^ 2 * X := by
      rw [abs_div, abs_mul, abs_of_nonneg (pow_nonneg hs0 6), abs_of_nonneg (sq_nonneg P),
        show |(72 : ℝ)| = 72 by norm_num]
      have e2 : s ^ 6 * P ^ 2 ≤ X * MP ^ 2 := mul_le_mul (hs6.trans hs4) hP2 (sq_nonneg _) hX0
      have : 0 ≤ X * MP ^ 2 := by positivity
      linarith
    have f1 := abs_add_le (s ^ 4 * (K ^ 2 / 4 + d * P / 3) / 2 - s ^ 5 * (K * P) / 12)
      (s ^ 6 * P ^ 2 / 72)
    have f2 := abs_sub (s ^ 4 * (K ^ 2 / 4 + d * P / 3) / 2) (s ^ 5 * (K * P) / 12)
    linarith
  have f1 := abs_add_le (S * ρ + p * ρ + ρ ^ 2 / 2)
    (s ^ 4 * (K ^ 2 / 4 + d * P / 3) / 2 - s ^ 5 * (K * P) / 12 + s ^ 6 * P ^ 2 / 72)
  have f2 := abs_add_le (S * ρ + p * ρ) (ρ ^ 2 / 2)
  have f3 := abs_add_le (S * ρ) (p * ρ)
  have e : (MS * C₇ + (MD + MK + MP) * C₇ + C₇ ^ 2 + MK ^ 2 + MD * MP + MK * MP + MP ^ 2) * X =
      MS * (C₇ * X) + (MD + MK + MP) * (C₇ * X) + C₇ ^ 2 * X +
        (MK ^ 2 + MD * MP + MK * MP + MP ^ 2) * X := by ring
  linarith

/-- The moment equations `scaling:odes` from the Riccati equation and the Taylor expansion. -/
theorem odes_of_riccati_taylor {S d K P : ℝ → ℝ} {H : ℝ → ℝ → ℝ} {r t MS MD MK MP C₇ : ℝ}
    (hrt : r ≤ t) (hmS : Measurable S) (hmd : Measurable d) (hmK : Measurable K)
    (hmP : Measurable P) (hmH : ∀ s, Measurable fun τ => H τ s)
    (hbS : ∀ τ ∈ Set.Icc r t, |S τ| ≤ MS) (hbd : ∀ τ ∈ Set.Icc r t, |d τ| ≤ MD)
    (hbK : ∀ τ ∈ Set.Icc r t, |K τ| ≤ MK) (hbP : ∀ τ ∈ Set.Icc r t, |P τ| ≤ MP) (hC₇ : 0 ≤ C₇)
    (hric : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      H t s - H r s = ∫ τ in r..t, (S τ * H τ s + H τ s ^ 2 / 2 - s ^ 2 / 2))
    (htay : ∀ τ ∈ Set.Icc r t, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |H τ s - (-(s * d τ) + s ^ 2 * K τ / 2 - s ^ 3 * P τ / 6)| ≤ C₇ * (s ^ 3 * Real.sqrt s)) :
    d t - d r = ∫ τ in r..t, S τ * d τ ∧
      K t - K r = ∫ τ in r..t, (S τ * K τ + d τ ^ 2 - 1) ∧
      P t - P r = ∫ τ in r..t, (S τ * P τ + 3 * d τ * K τ) := by
  have hMS : 0 ≤ MS := (abs_nonneg _).trans (hbS r ⟨le_rfl, hrt⟩)
  have hMD : 0 ≤ MD := (abs_nonneg _).trans (hbd r ⟨le_rfl, hrt⟩)
  have hMK : 0 ≤ MK := (abs_nonneg _).trans (hbK r ⟨le_rfl, hrt⟩)
  have hMP : 0 ≤ MP := (abs_nonneg _).trans (hbP r ⟨le_rfl, hrt⟩)
  -- integrability
  have iSd : IntervalIntegrable (fun τ => S τ * d τ) volume r t :=
    ii_of_bdd hrt (hmS.mul hmd) fun τ hτ => by
      rw [abs_mul]; exact mul_le_mul (hbS τ hτ) (hbd τ hτ) (abs_nonneg _) hMS
  have iQ2 : IntervalIntegrable (fun τ => S τ * K τ + d τ ^ 2 - 1) volume r t :=
    ii_of_bdd (M := MS * MK + MD ^ 2 + 1) hrt (((hmS.mul hmK).add (hmd.pow_const 2)).sub_const 1)
      fun τ hτ => by
        have e1 : |S τ * K τ| ≤ MS * MK := by
          rw [abs_mul]; exact mul_le_mul (hbS τ hτ) (hbK τ hτ) (abs_nonneg _) hMS
        have e2 : d τ ^ 2 ≤ MD ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hbd τ hτ) 2
        have e3 : 0 ≤ d τ ^ 2 := sq_nonneg _
        have := abs_le.1 e1
        rw [abs_le]; constructor <;> linarith
  have iQ3 : IntervalIntegrable (fun τ => S τ * P τ + 3 * d τ * K τ) volume r t :=
    ii_of_bdd (M := MS * MP + 3 * (MD * MK)) hrt ((hmS.mul hmP).add
      ((hmd.const_mul 3).mul hmK)) fun τ hτ => by
        have e1 : |S τ * P τ| ≤ MS * MP := by
          rw [abs_mul]; exact mul_le_mul (hbS τ hτ) (hbP τ hτ) (abs_nonneg _) hMS
        have e2 : |3 * d τ * K τ| ≤ 3 * (MD * MK) := by
          rw [abs_mul, abs_mul, show |(3 : ℝ)| = 3 by norm_num, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul (hbd τ hτ) (hbK τ hτ) (abs_nonneg _) hMD)
            (by norm_num)
        exact (abs_add_le _ _).trans (add_le_add e1 e2)
  set I₁ := ∫ τ in r..t, S τ * d τ with hI₁
  set I₂ := ∫ τ in r..t, (S τ * K τ + d τ ^ 2 - 1) with hI₂
  set I₃ := ∫ τ in r..t, (S τ * P τ + 3 * d τ * K τ) with hI₃
  set C₈ := MS * C₇ + (MD + MK + MP) * C₇ + C₇ ^ 2 + MK ^ 2 + MD * MP + MK * MP + MP ^ 2
    with hC₈
  have hC₈0 : 0 ≤ C₈ := by positivity
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 →
      |(-(d t - d r) + I₁) * s + ((K t - K r) / 2 - I₂ / 2) * s ^ 2 +
        (-(P t - P r) / 6 + I₃ / 6) * s ^ 3| ≤ (C₈ * (t - r) + 2 * C₇) * s ^ 3 * Real.sqrt s := by
    intro s hs0 hs1
    have hsI : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs0.le, hs1⟩
    -- the remainder `G`
    set G : ℝ → ℝ := fun τ => S τ * H τ s + H τ s ^ 2 / 2 - s ^ 2 / 2 -
      (-(s * (S τ * d τ)) + s ^ 2 * (S τ * K τ + d τ ^ 2 - 1) / 2 -
        s ^ 3 * (S τ * P τ + 3 * d τ * K τ) / 6) with hG
    have hGb : ∀ τ ∈ Set.Icc r t, |G τ| ≤ C₈ * (s ^ 3 * Real.sqrt s) := fun τ hτ =>
      riccati_poly_bound hs0.le hs1 (hbS τ hτ) (hbd τ hτ) (hbK τ hτ) (hbP τ hτ) hC₇
        (htay τ hτ s hsI)
    have hmF : Measurable fun τ => S τ * H τ s + H τ s ^ 2 / 2 - s ^ 2 / 2 :=
      ((hmS.mul (hmH s)).add ((hmH s).pow_const 2 |>.div_const 2)).sub_const _
    have hmPoly : Measurable fun τ => -(s * (S τ * d τ)) + s ^ 2 * (S τ * K τ + d τ ^ 2 - 1) / 2 -
        s ^ 3 * (S τ * P τ + 3 * d τ * K τ) / 6 :=
      (((hmS.mul hmd).const_mul s).neg.add ((((hmS.mul hmK).add (hmd.pow_const 2)).sub_const 1
        |>.const_mul _).div_const 2)).sub ((((hmS.mul hmP).add ((hmd.const_mul 3).mul hmK))
          |>.const_mul _).div_const 6)
    have iG : IntervalIntegrable G volume r t :=
      ii_of_bdd hrt (hmF.sub hmPoly) hGb
    have iPoly : IntervalIntegrable (fun τ => -(s * (S τ * d τ)) +
        s ^ 2 * (S τ * K τ + d τ ^ 2 - 1) / 2 - s ^ 3 * (S τ * P τ + 3 * d τ * K τ) / 6)
        volume r t :=
      ((iSd.const_mul s).neg.add ((iQ2.const_mul _).div_const 2)).sub
        ((iQ3.const_mul _).div_const 6)
    have hsplit : (∫ τ in r..t, (S τ * H τ s + H τ s ^ 2 / 2 - s ^ 2 / 2)) =
        (-(s * I₁) + s ^ 2 * I₂ / 2 - s ^ 3 * I₃ / 6) + ∫ τ in r..t, G τ := by
      have h1 : (fun τ => S τ * H τ s + H τ s ^ 2 / 2 - s ^ 2 / 2) = fun τ =>
          (-(s * (S τ * d τ)) + s ^ 2 * (S τ * K τ + d τ ^ 2 - 1) / 2 -
            s ^ 3 * (S τ * P τ + 3 * d τ * K τ) / 6) + G τ := by
        funext τ; simp only [hG]; ring
      have iA : IntervalIntegrable (fun τ => -(s * (S τ * d τ)) +
          s ^ 2 * (S τ * K τ + d τ ^ 2 - 1) / 2) volume r t :=
        (iSd.const_mul s).neg.add ((iQ2.const_mul _).div_const 2)
      have iB : IntervalIntegrable (fun τ => s ^ 3 * (S τ * P τ + 3 * d τ * K τ) / 6)
          volume r t := (iQ3.const_mul _).div_const 6
      have iC : IntervalIntegrable (fun τ => -(s * (S τ * d τ))) volume r t :=
        (iSd.const_mul s).neg
      have iD : IntervalIntegrable (fun τ => s ^ 2 * (S τ * K τ + d τ ^ 2 - 1) / 2) volume r t :=
        (iQ2.const_mul _).div_const 2
      rw [h1, intervalIntegral.integral_add iPoly iG, intervalIntegral.integral_sub iA iB,
        intervalIntegral.integral_add iC iD,
        intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
    have hGint : |∫ τ in r..t, G τ| ≤ C₈ * (s ^ 3 * Real.sqrt s) * (t - r) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := r) (b := t)
        (C := C₈ * (s ^ 3 * Real.sqrt s)) (f := G) fun τ hτ => by
          rw [Set.uIoc_of_le hrt] at hτ
          rw [Real.norm_eq_abs]; exact hGb τ ⟨hτ.1.le, hτ.2⟩
      rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hrt)] at this
    have hρt := htay t ⟨hrt, le_rfl⟩ s hsI
    have hρr := htay r ⟨le_rfl, hrt⟩ s hsI
    have hric' := hric s hsI
    rw [hsplit] at hric'
    have hid : (-(d t - d r) + I₁) * s + ((K t - K r) / 2 - I₂ / 2) * s ^ 2 +
        (-(P t - P r) / 6 + I₃ / 6) * s ^ 3 =
        (∫ τ in r..t, G τ) - ((H t s - (-(s * d t) + s ^ 2 * K t / 2 - s ^ 3 * P t / 6)) -
          (H r s - (-(s * d r) + s ^ 2 * K r / 2 - s ^ 3 * P r / 6))) := by
      linarith
    rw [hid]
    have a1 := abs_le.1 hGint
    have a2 := abs_le.1 hρt
    have a3 := abs_le.1 hρr
    rw [abs_le]
    have e : (C₈ * (t - r) + 2 * C₇) * s ^ 3 * Real.sqrt s =
        C₈ * (s ^ 3 * Real.sqrt s) * (t - r) + C₇ * (s ^ 3 * Real.sqrt s) +
          C₇ * (s ^ 3 * Real.sqrt s) := by ring
    constructor <;> linarith
  obtain ⟨h1, h2, h3⟩ := coeff_eq_zero_of_taylor key
  refine ⟨by linarith, by linarith, by linarith⟩

/-! ### The extraction -/

/-- The grid point attached to `o : Option ℚ`: `T` for `none`, `q` for `some q`. -/
def gridPt (T : ℝ) (o : Option ℚ) : ℝ := o.elim T fun q => (q : ℝ)

theorem subseq_tendsto {f : ℕ → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h : ∃ L, Tendsto f atTop (𝓝 L)) : ∃ L, Tendsto (fun j => f (φ j)) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨L, hL.comp hφ.tendsto_atTop⟩

/-- The extraction of `scaling:compactness`: a common subsequence along which `S_N` converges
at every time of `(0, T]` and `ℋ_N` converges on the grid. -/
theorem extraction {T : ℝ} (hT : 0 < T) (f : ℕ → ℝ → ℝ) (g : ℕ → ℝ → ℝ → ℝ)
    (hfb : ∀ t ∈ Set.Ioc 0 T, ∃ M, ∀ᶠ j in atTop, |f j t| ≤ M)
    (hgb : ∀ t ∈ Set.Ioc 0 T, ∀ s : ℝ, 0 ≤ s → ∃ M, ∀ᶠ j in atTop, |g j t s| ≤ M)
    (hmono : ∀ r, 0 < r → r < T → ∃ C M : ℝ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      (∀ᶠ j in atTop, ∀ t ∈ Set.Icc r T, |f j t| ≤ M) ∧
      ∀ᶠ j in atTop, ∀ t₁ t₂ : ℝ, r ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
        f j t₂ - f j t₁ ≤ C * (t₂ - t₁) + ε j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ t ∈ Set.Ioc 0 T, ∃ L, Tendsto (fun j => f (φ j) t) atTop (𝓝 L)) ∧
      (∀ t ∈ timeGrid T, ∀ q : ℚ, (0 : ℝ) ≤ q →
        ∃ L, Tendsto (fun j => g (φ j) t q) atTop (𝓝 L)) := by
  classical
  -- first diagonal extraction
  let x₁ : ℕ → (Option ℚ ⊕ (Option ℚ × ℚ)) → ℝ := fun j i => match i with
    | Sum.inl o => if gridPt T o ∈ Set.Ioc 0 T then f j (gridPt T o) else 0
    | Sum.inr (o, q) => if gridPt T o ∈ Set.Ioc 0 T ∧ (0 : ℝ) ≤ q then g j (gridPt T o) q else 0
  obtain ⟨φ₁, hφ₁, hconv₁⟩ := exists_subseq_tendsto_of_countable x₁ (by
    rintro (o | ⟨o, q⟩)
    · by_cases h : gridPt T o ∈ Set.Ioc 0 T
      · obtain ⟨M, hM⟩ := hfb _ h
        exact ⟨M, hM.mono fun j hj => by simp only [x₁, if_pos h]; exact hj⟩
      · exact ⟨0, Eventually.of_forall fun j => by simp only [x₁, if_neg h, abs_zero, le_refl]⟩
    · by_cases h : gridPt T o ∈ Set.Ioc 0 T ∧ (0 : ℝ) ≤ q
      · obtain ⟨M, hM⟩ := hgb _ h.1 q h.2
        exact ⟨M, hM.mono fun j hj => by simp only [x₁, if_pos h]; exact hj⟩
      · exact ⟨0, Eventually.of_forall fun j => by simp only [x₁, if_neg h, abs_zero, le_refl]⟩)
  have hf₁ : ∀ o : Option ℚ, gridPt T o ∈ Set.Ioc 0 T →
      ∃ L, Tendsto (fun j => f (φ₁ j) (gridPt T o)) atTop (𝓝 L) := by
    intro o ho
    obtain ⟨L, hL⟩ := hconv₁ (Sum.inl o)
    exact ⟨L, hL.congr fun j => by simp only [x₁, if_pos ho]⟩
  have hg₁ : ∀ o : Option ℚ, gridPt T o ∈ Set.Ioc 0 T → ∀ q : ℚ, (0 : ℝ) ≤ q →
      ∃ L, Tendsto (fun j => g (φ₁ j) (gridPt T o) q) atTop (𝓝 L) := by
    intro o ho q hq
    obtain ⟨L, hL⟩ := hconv₁ (Sum.inr (o, q))
    exact ⟨L, hL.congr fun j => by simp only [x₁, if_pos (And.intro ho hq)]⟩
  -- the countable exceptional sets
  have hE : ∀ k : ℕ, Set.Countable {t | t ∈ Set.Ioo (T / ((k : ℝ) + 2)) T ∧
      ¬ ∃ L, Tendsto (fun j => f (φ₁ j) t) atTop (𝓝 L)} := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hak : 0 < T / ((k : ℝ) + 2) := div_pos hT hk
    have hakT : T / ((k : ℝ) + 2) < T := by
      rw [div_lt_iff₀ hk]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    obtain ⟨C, M, ε, hε, hM, hmo⟩ := hmono _ hak hakT
    refine countable_not_tendsto_of_almostMono (fun j => f (φ₁ j)) (ε ∘ φ₁)
      (hε.comp hφ₁.tendsto_atTop) (hφ₁.tendsto_atTop.eventually hM) (C := C)
      (hφ₁.tendsto_atTop.eventually hmo) (D := Set.range ((↑) : ℚ → ℝ)) ?_ ?_
    · intro x y _ hxy _
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hxy
      exact ⟨q, ⟨q, rfl⟩, hq1, hq2⟩
    · rintro _ ⟨q, rfl⟩ hq
      exact hf₁ (some q) ⟨lt_of_lt_of_le hak hq.1, hq.2⟩
  set E := ⋃ k : ℕ, {t | t ∈ Set.Ioo (T / ((k : ℝ) + 2)) T ∧
      ¬ ∃ L, Tendsto (fun j => f (φ₁ j) t) atTop (𝓝 L)} with hE_def
  have hEc : E.Countable := Set.countable_iUnion hE
  haveI : Countable E := hEc.to_subtype
  have hEsub : E ⊆ Set.Ioc 0 T := by
    intro t ht
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 ht
    have : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    exact ⟨lt_trans (div_pos hT this) hk.1.1, hk.1.2.le⟩
  -- second diagonal extraction on the exceptional set
  let x₂ : ℕ → E → ℝ := fun j e => f (φ₁ j) e
  obtain ⟨φ₂, hφ₂, hconv₂⟩ := exists_subseq_tendsto_of_countable x₂ (by
    intro e
    obtain ⟨M, hM⟩ := hfb e (hEsub e.2)
    exact ⟨M, hφ₁.tendsto_atTop.eventually hM⟩)
  refine ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, ?_, ?_⟩
  · intro t ht
    by_cases htT : t = T
    · subst htT
      exact subseq_tendsto hφ₂ (hf₁ none ht)
    by_cases htE : t ∈ E
    · exact hconv₂ ⟨t, htE⟩
    · have htT' : t < T := lt_of_le_of_ne ht.2 htT
      obtain ⟨k, hk⟩ := exists_nat_gt (T / t)
      have hk2 : T / ((k : ℝ) + 2) < t := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ ht.1] at hk
        nlinarith
      have hnot : ¬ (t ∈ Set.Ioo (T / ((k : ℝ) + 2)) T ∧
          ¬ ∃ L, Tendsto (fun j => f (φ₁ j) t) atTop (𝓝 L)) :=
        fun h => htE (Set.mem_iUnion.2 ⟨k, h⟩)
      push_neg at hnot
      exact subseq_tendsto hφ₂ (hnot ⟨hk2, htT'⟩)
  · intro t ht q hq
    rcases ht with ht | ⟨⟨q', rfl⟩, ht⟩
    · rw [Set.mem_singleton_iff.1 ht]
      exact subseq_tendsto hφ₂ (hg₁ none ⟨hT, le_rfl⟩ q hq)
    · exact subseq_tendsto hφ₂ (hg₁ (some q') ⟨ht.1, ht.2.le⟩ q hq)

/-! ### The limit measures -/

theorem tendsto_mul_pow_floor {ρ t : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (ht : 0 < t) :
    Tendsto (fun N : ℝ => N * ρ ^ ⌊N * t⌋₊) atTop (𝓝 0) := by
  have hfl : Tendsto (fun N : ℝ => ⌊N * t⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.atTop_mul_const ht)
  have hu : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * ρ ^ n / t) atTop (𝓝 0) := by
    have h1 := tendsto_self_mul_const_pow_of_lt_one hρ0 hρ1
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    have := (h1.add h2).div_const t
    rw [add_zero, zero_div] at this
    exact this.congr fun n => by ring
  refine squeeze_zero' ?_ ?_ (hu.comp hfl)
  · filter_upwards [eventually_ge_atTop 0] with N hN
    positivity
  · filter_upwards [eventually_gt_atTop 0] with N hN
    show N * ρ ^ ⌊N * t⌋₊ ≤ ((⌊N * t⌋₊ : ℝ) + 1) * ρ ^ ⌊N * t⌋₊ / t
    have h1 : N * t < ⌊N * t⌋₊ + 1 := Nat.lt_floor_add_one _
    have h2 : N ≤ ((⌊N * t⌋₊ : ℝ) + 1) / t := by rw [le_div_iff₀ ht]; linarith
    calc N * ρ ^ ⌊N * t⌋₊ ≤ ((⌊N * t⌋₊ : ℝ) + 1) / t * ρ ^ ⌊N * t⌋₊ :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = _ := by ring

section LimitMeasures

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem transformAt_eq_scaled (μ : Measure ℝ) (B lam N t s : ℝ) :
    transformAt μ B (scalingField μ B lam N) N ⌊N * t⌋₊ s =
      scaledCompensated μ B lam N t s - s + scaledMass μ B lam N t := by
  rw [scaledCompensated, scaledMass, ← transformAt_zero]
  ring

/-- The weak limit of `ν_N(t, ·)` along a sequence where `S_N(t)` and `ℋ_N(t, ·)` converge. -/
theorem nu_limit (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hlamT : lam * (2 * T) ^ 2 ≤ η) {Ns : ℕ → ℝ}
    (hNs : Tendsto Ns atTop atTop) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {S₀ : ℝ} {H₀ : ℝ → ℝ}
    (hS : Tendsto (fun j => scaledMass μ B lam (Ns j) t) atTop (𝓝 S₀))
    (hH : ∀ s : ℝ, 0 ≤ s →
      Tendsto (fun j => scaledCompensated μ B lam (Ns j) t s) atTop (𝓝 (H₀ s))) :
    ∃ ν' : FiniteMeasure ℝ, (ν' : Measure ℝ) (Set.Iio 0) = 0 ∧
      (∀ f : ℝ →ᵇ ℝ, Tendsto (fun j => ∫ x, f x ∂(scalingMeasure μ B lam (Ns j) t)) atTop
        (𝓝 (∫ x, f x ∂(ν' : Measure ℝ)))) ∧
      (∀ s : ℝ, 0 ≤ s → ∫ x, expBCF s x ∂(ν' : Measure ℝ) = H₀ s - s + S₀) ∧
      (∀ k : ℕ, ∫ x, sevenHalvesBCF k x ∂(ν' : Measure ℝ) ≤
        96 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (t ^ 2 * Real.sqrt t)) := by
  have ha := log_pos_of_two_lt hB
  have hθ0 := theta_pos hB
  have ht0 := ht.1
  set MS := (2 * C + c) / t + 2 * C * lam * T
  set MD := (C + 4 * C * lam * T ^ 2 + 16 * C * lam ^ 2 * T ^ 4) / Real.log B
  have hMS : 0 ≤ MS := by positivity
  have hMD : 0 ≤ MD := by positivity
  set β := -Real.log (floorSeq B 1)
  have hβ0 : 0 ≤ β := neg_nonneg.2 (Real.log_nonpos (floorSeq_one_pos hB).le (floorSeq_le_one hB 1))
  set ρ := 2 / B
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := (div_lt_one (by linarith)).2 hB
  -- eventual facts in `N`
  have hev := unif_bounds hB hC hc hW hlam hT hlamT ht0
  have hfact : ∀ᶠ N in atTop, 0 < N ∧ 1 ≤ ⌊N * t⌋₊ ∧ |scaledMass μ B lam N t| ≤ MS ∧
      |scaledDrift μ B lam N t| ≤ MD ∧
      absTiltedLogRpowMoment μ B (scalingField μ B lam N) (7 / 2) ⌊N * t⌋₊ ≤
        8 * C * (N ^ 2 * Real.sqrt N) * (t ^ 2 * Real.sqrt t) := by
    filter_upwards [hev] with N hN
    obtain ⟨-, -, hn1, hS', hd', -, -, h72⟩ := hN.2 t ⟨le_rfl, ht.2⟩
    exact ⟨hN.1, hn1, hS', hd', h72⟩
  have hfactj := hNs.eventually hfact
  set ν : ℕ → Measure ℝ := fun j => scalingMeasure μ B lam (Ns j) t with hν
  -- the Laplace transforms
  have hlap : ∀ s : ℝ, 0 ≤ s →
      Tendsto (fun j => ∫ x, expBCF s x ∂(ν j)) atTop (𝓝 (H₀ s - s + S₀)) := by
    intro s hs
    have hmain : Tendsto (fun j => scaledCompensated μ B lam (Ns j) t s - s +
        scaledMass μ B lam (Ns j) t) atTop (𝓝 (H₀ s - s + S₀)) :=
      ((hH s hs).sub tendsto_const_nhds).add hS
    have herr : Tendsto (fun j => Ns j * ρ ^ ⌊Ns j * t⌋₊ +
        s / (Real.log B * theta B) * (MS / Ns j + ρ ^ ⌊Ns j * t⌋₊)) atTop (𝓝 0) := by
      have h1 := (tendsto_mul_pow_floor hρ0 hρ1 ht0).comp hNs
      have h2 : Tendsto (fun j => MS / Ns j) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hNs
      have h3 : Tendsto (fun j => ρ ^ ⌊Ns j * t⌋₊) atTop (𝓝 0) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp
          ((tendsto_nat_floor_atTop.comp (tendsto_id.atTop_mul_const ht0)).comp hNs)
      have := h1.add ((h2.add h3).const_mul (s / (Real.log B * theta B)))
      simp only [add_zero, mul_zero] at this
      exact this
    have hθs : ∀ᶠ j in atTop, s / (Real.log B * Ns j) ≤ theta B := by
      have h1 : Tendsto (fun j => s / (Real.log B * Ns j)) atTop (𝓝 0) := by
        have := (tendsto_const_nhds (x := s / Real.log B)).mul (tendsto_inv_atTop_zero.comp hNs)
        rw [mul_zero] at this
        exact this.congr fun j => by simp only [Function.comp]; ring
      exact ((tendsto_order.1 h1).2 _ hθ0).mono fun j hj => hj.le
    have hbound : ∀ᶠ j in atTop, |∫ x, expBCF s x ∂(ν j) - (scaledCompensated μ B lam (Ns j) t s -
        s + scaledMass μ B lam (Ns j) t)| ≤ Ns j * ρ ^ ⌊Ns j * t⌋₊ +
          s / (Real.log B * theta B) * (MS / Ns j + ρ ^ ⌊Ns j * t⌋₊) := by
      filter_upwards [hfactj, hθs] with j ⟨hN, hn1, hSj, _, _⟩ hθj
      have hl := laplace_rescaled_bound hpos hmean hB (scalingField μ B lam (Ns j)) (Ns j) s hn1 hN
        hs hθj
      rw [transformAt_eq_scaled] at hl
      refine hl.trans ?_
      have hfl : 1 - floorSeq B ⌊Ns j * t⌋₊ ≤ ρ ^ ⌊Ns j * t⌋₊ := one_sub_floorSeq_le hB _
      have hA : tiltedMass μ B (scalingField μ B lam (Ns j)) ⌊Ns j * t⌋₊ - 1 ≤ MS / Ns j := by
        have : scaledMass μ B lam (Ns j) t = Ns j * (tiltedMass μ B (scalingField μ B lam (Ns j))
          ⌊Ns j * t⌋₊ - 1) := rfl
        rw [le_div_iff₀ hN, mul_comm, ← this]
        exact (le_abs_self _).trans hSj
      have k1 : Ns j * (1 - floorSeq B ⌊Ns j * t⌋₊) ≤ Ns j * ρ ^ ⌊Ns j * t⌋₊ :=
        mul_le_mul_of_nonneg_left hfl hN.le
      have k2 : s / (Real.log B * theta B) * ((tiltedMass μ B (scalingField μ B lam (Ns j))
          ⌊Ns j * t⌋₊ - 1) + (1 - floorSeq B ⌊Ns j * t⌋₊)) ≤
          s / (Real.log B * theta B) * (MS / Ns j + ρ ^ ⌊Ns j * t⌋₊) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hfl) (by positivity)
      linarith
    have := hmain.add (squeeze_zero_norm' (hbound.mono fun j hj => by
      rw [Real.norm_eq_abs]; exact hj) herr)
    rw [add_zero] at this
    exact this.congr fun j => by ring
  -- uniform mass and tail bounds for large `j`
  set Ct := (Real.log B * MD + (Real.log B + 2 * β) * (1 + MS)) / Real.log B with hCt
  have hCt0 : 0 ≤ Ct := by positivity
  have hmass0 : ∀ᶠ j in atTop, (ν j).real Set.univ ≤ H₀ 0 + S₀ + 1 := by
    have h1 := hlap 0 le_rfl
    have h2 : ∀ j, ∫ x, expBCF 0 x ∂(ν j) = (ν j).real Set.univ := by
      intro j
      have : (fun x => expBCF 0 x) = fun _ => (1 : ℝ) := by
        funext x; rw [expBCF_apply le_rfl, zero_mul, neg_zero, Real.exp_zero]
      rw [this, integral_const, smul_eq_mul, mul_one]
    simp only [h2, sub_zero] at h1
    exact ((tendsto_order.1 h1).2 _ (by linarith)).mono fun j hj => hj.le
  have htail0 : ∀ᶠ j in atTop, ∀ n : ℕ, (ν j).real (Set.Ioi ((n : ℝ) + 1)) ≤ Ct / ((n : ℝ) + 1) := by
    filter_upwards [hfactj, hNs.eventually (eventually_ge_atTop 1)] with j ⟨hN, hn1, hSj, hdj, _⟩ hN1
    intro n
    have htl := tail_rescaled_bound hpos hmean hB (scalingField μ B lam (Ns j)) (Ns j)
      ((n : ℝ) + 1) hn1 hN (by positivity)
    refine htl.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hH1 : tiltedLogMoment μ B (scalingField μ B lam (Ns j)) 1 ⌊Ns j * t⌋₊ ≤
        Real.log B * MD := by
      have : scaledDrift μ B lam (Ns j) t =
          tiltedLogMoment μ B (scalingField μ B lam (Ns j)) 1 ⌊Ns j * t⌋₊ / Real.log B := rfl
      have h2 := (le_abs_self _).trans hdj
      rw [this, div_le_iff₀ ha] at h2
      linarith
    have hA1 : tiltedMass μ B (scalingField μ B lam (Ns j)) ⌊Ns j * t⌋₊ ≤ 1 + MS := by
      have : scaledMass μ B lam (Ns j) t = Ns j * (tiltedMass μ B (scalingField μ B lam (Ns j))
        ⌊Ns j * t⌋₊ - 1) := rfl
      have h2 := (le_abs_self _).trans hSj
      rw [this] at h2
      have h3 : tiltedMass μ B (scalingField μ B lam (Ns j)) ⌊Ns j * t⌋₊ - 1 ≤
          Ns j * (tiltedMass μ B (scalingField μ B lam (Ns j)) ⌊Ns j * t⌋₊ - 1) ∨
          tiltedMass μ B (scalingField μ B lam (Ns j)) ⌊Ns j * t⌋₊ - 1 ≤ 0 := by
        rcases le_total 0 (tiltedMass μ B (scalingField μ B lam (Ns j)) ⌊Ns j * t⌋₊ - 1) with h | h
        · left; exact le_mul_of_one_le_left h hN1
        · right; exact h
      rcases h3 with h3 | h3 <;> linarith
    have hA0 := tiltedMass_nonneg hpos hB (scalingField μ B lam (Ns j)) ⌊Ns j * t⌋₊
    have e1 : (Real.log B + 2 * β) * tiltedMass μ B (scalingField μ B lam (Ns j)) ⌊Ns j * t⌋₊ ≤
        (Real.log B + 2 * β) * (1 + MS) := mul_le_mul_of_nonneg_left hA1 (by positivity)
    have e2 : Ct * (Real.log B * ((n : ℝ) + 1)) =
        (Real.log B * MD + (Real.log B + 2 * β) * (1 + MS)) * ((n : ℝ) + 1) := by
      rw [hCt]; field_simp
    rw [e2]
    have e3 : 0 ≤ ((n : ℝ) + 1) := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) e3
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hmass0.and (htail0.and hfactj))
  set Cm := max (H₀ 0 + S₀ + 1) Ct
  haveI hfin : ∀ j, IsFiniteMeasure (ν (j + j₀)) := fun j =>
    isFiniteMeasure_rescaledMeasure hpos hmean hB _ (hj₀ (j + j₀) (by omega)).2.2.1 _
  obtain ⟨ν', hν'supp, hν'conv⟩ := exists_weakLimit_of_laplace (fun j => ν (j + j₀))
    (fun j => (rescaledMeasure_finite_aux hpos hmean hB _ (hj₀ (j + j₀) (by omega)).2.2.1 _).2)
    (C := Cm) (fun j => ((hj₀ (j + j₀) (by omega)).1).trans (le_max_left _ _))
    (fun j n => ((hj₀ (j + j₀) (by omega)).2.1 n).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)))
    (fun k => ⟨_, by
      rw [laplaceBCF_eq_expBCF]
      exact (tendsto_add_atTop_iff_nat j₀).2 (hlap k (Nat.cast_nonneg k))⟩)
  have hconv : ∀ f : ℝ →ᵇ ℝ, Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop
      (𝓝 (∫ x, f x ∂(ν' : Measure ℝ))) :=
    fun f => (tendsto_add_atTop_iff_nat j₀).1 (hν'conv f)
  refine ⟨ν', hν'supp, hconv, fun s hs => tendsto_nhds_unique (hconv _) (hlap s hs), fun k => ?_⟩
  -- the `7/2` moment
  set C9 := 96 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (t ^ 2 * Real.sqrt t)
  have hbnd : ∀ᶠ j in atTop, ∫ x, sevenHalvesBCF k x ∂(ν j) ≤
      C9 + 12 * (1 + MS) / (Ns j ^ 2 * Real.sqrt (Ns j)) := by
    filter_upwards [hfactj, hNs.eventually (eventually_ge_atTop 1)] with j ⟨hN, hn1, hSj, _, h72⟩ hN1
    refine (sevenHalves_rescaled_bound hpos hmean hB (scalingField μ B lam (Ns j)) (Ns j) hN k).trans ?_
    have hA1 : tiltedMass μ B (scalingField μ B lam (Ns j)) ⌊Ns j * t⌋₊ ≤ 1 + MS := by
      have : scaledMass μ B lam (Ns j) t = Ns j * (tiltedMass μ B (scalingField μ B lam (Ns j))
        ⌊Ns j * t⌋₊ - 1) := rfl
      have h2 := (le_abs_self _).trans hSj
      rw [this] at h2
      rcases le_total 0 (tiltedMass μ B (scalingField μ B lam (Ns j)) ⌊Ns j * t⌋₊ - 1) with h | h
      · have := le_mul_of_one_le_left h hN1; linarith
      · linarith
    have hsa : 0 < Real.sqrt (Real.log B) := Real.sqrt_pos.2 ha
    have hsN : 0 < Real.sqrt (Ns j) := Real.sqrt_pos.2 hN
    have hden : 0 < Real.log B ^ 3 * Real.sqrt (Real.log B) * (Ns j ^ 2 * Real.sqrt (Ns j)) := by
      positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    have e1 : 12 * (absTiltedLogRpowMoment μ B (scalingField μ B lam (Ns j)) (7 / 2) ⌊Ns j * t⌋₊ +
        Real.log B ^ 3 * Real.sqrt (Real.log B) *
          tiltedMass μ B (scalingField μ B lam (Ns j)) ⌊Ns j * t⌋₊) ≤
        12 * (8 * C * (Ns j ^ 2 * Real.sqrt (Ns j)) * (t ^ 2 * Real.sqrt t) +
          Real.log B ^ 3 * Real.sqrt (Real.log B) * (1 + MS)) := by
      have := mul_le_mul_of_nonneg_left hA1 (by positivity :
        (0 : ℝ) ≤ Real.log B ^ 3 * Real.sqrt (Real.log B))
      linarith
    refine e1.trans (le_of_eq ?_)
    simp only [C9]
    field_simp
    ring
  have hlimb : Tendsto (fun j => 12 * (1 + MS) / (Ns j ^ 2 * Real.sqrt (Ns j))) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ ((tendsto_const_nhds (x := 12 * (1 + MS))).div_atTop hNs)
    · filter_upwards [hNs.eventually (eventually_gt_atTop 0)] with j hj
      positivity
    · filter_upwards [hNs.eventually (eventually_ge_atTop 1)] with j hj
      have h0 : 0 < Ns j := by linarith
      apply div_le_div_of_nonneg_left (by positivity) h0
      have hs1 : 1 ≤ Real.sqrt (Ns j) := by simpa using Real.sqrt_le_sqrt hj
      have h2 : Ns j ≤ Ns j ^ 2 := by nlinarith
      calc Ns j ≤ Ns j ^ 2 * 1 := by linarith
        _ ≤ Ns j ^ 2 * Real.sqrt (Ns j) := mul_le_mul_of_nonneg_left hs1 (by positivity)
  have hlim2 := (tendsto_const_nhds (x := C9)).add hlimb
  rw [add_zero] at hlim2
  exact le_of_tendsto_of_tendsto (hconv _) hlim2 hbnd

end LimitMeasures

/-! ### Moments of the limit measures -/

/-- Bounded truncated `7/2` moments give an integrable `(x⁺)^{7/2}`. -/
theorem sevenHalves_integrable {ν : Measure ℝ} [IsFiniteMeasure ν] {M : ℝ}
    (h : ∀ k : ℕ, ∫ x, sevenHalvesBCF k x ∂ν ≤ M) :
    Integrable (fun x => max x 0 ^ 3 * Real.sqrt (max x 0)) ν ∧
      ∫ x, max x 0 ^ 3 * Real.sqrt (max x 0) ∂ν ≤ M := by
  set G := fun x : ℝ => max x 0 ^ 3 * Real.sqrt (max x 0) with hG
  have hG0 : ∀ x, 0 ≤ G x := fun x => by
    have := le_max_right x 0
    simp only [hG]
    positivity
  have hGm : Measurable G :=
    (((continuous_id.max continuous_const).pow 3).mul
      (continuous_id.max continuous_const).sqrt).measurable
  have hmono : ∀ x, Monotone fun k : ℕ => ENNReal.ofReal (sevenHalvesBCF k x) := by
    intro x k l hkl
    apply ENNReal.ofReal_le_ofReal
    rw [sevenHalvesBCF_apply, sevenHalvesBCF_apply]
    have h0 : 0 ≤ min (max x 0) (k : ℝ) := le_min (le_max_right _ _) (Nat.cast_nonneg k)
    have h1 : min (max x 0) (k : ℝ) ≤ min (max x 0) (l : ℝ) :=
      min_le_min_left _ (Nat.cast_le.2 hkl)
    exact mul_le_mul (pow_le_pow_left₀ h0 h1 3) (Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg _)
      (by positivity)
  have hlim : ∀ x, Tendsto (fun k : ℕ => ENNReal.ofReal (sevenHalvesBCF k x)) atTop
      (𝓝 (ENNReal.ofReal (G x))) := by
    intro x
    obtain ⟨k₀, hk₀⟩ := exists_nat_ge (max x 0)
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨k₀, fun k hk => ?_⟩)
    show ENNReal.ofReal (G x) = ENNReal.ofReal (sevenHalvesBCF k x)
    rw [sevenHalvesBCF_apply, min_eq_left (hk₀.trans (Nat.cast_le.2 hk))]
  have hT := lintegral_tendsto_of_tendsto_of_monotone (μ := ν)
    (fun k => (ENNReal.measurable_ofReal.comp (sevenHalvesBCF k).continuous.measurable).aemeasurable)
    (ae_of_all _ hmono) (ae_of_all _ hlim)
  have hle : ∀ k : ℕ, ∫⁻ x, ENNReal.ofReal (sevenHalvesBCF k x) ∂ν ≤ ENNReal.ofReal M := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal ((sevenHalvesBCF k).integrable ν)
      (ae_of_all _ (sevenHalvesBCF_nonneg k))]
    exact ENNReal.ofReal_le_ofReal (h k)
  have hGle : ∫⁻ x, ENNReal.ofReal (G x) ∂ν ≤ ENNReal.ofReal M := le_of_tendsto' hT hle
  have hint : Integrable G ν :=
    ⟨hGm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hG0)).2
      (hGle.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hG0) hGm.aestronglyMeasurable]
  have hM0 : 0 ≤ M := (integral_nonneg (sevenHalvesBCF_nonneg 0)).trans (h 0)
  exact ENNReal.toReal_le_of_le_ofReal hM0 hGle

theorem pow_le_one_add_sevenHalves {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : k ≤ 3) :
    |x ^ k| ≤ 1 + max x 0 ^ 3 * Real.sqrt (max x 0) := by
  rw [max_eq_left hx, abs_of_nonneg (pow_nonneg hx k)]
  have hG : 0 ≤ x ^ 3 * Real.sqrt x := by positivity
  rcases le_total x 1 with h1 | h1
  · have : x ^ k ≤ 1 := pow_le_one₀ hx h1
    linarith
  · have h2 : x ^ k ≤ x ^ 3 := pow_le_pow_right₀ h1 hk
    have h3 : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt h1
    have h4 : x ^ 3 ≤ x ^ 3 * Real.sqrt x := le_mul_of_one_le_right (by positivity) h3
    linarith

/-- The moments of a limit measure are read off from the Taylor expansion of its compensated
Laplace transform. -/
theorem moments_of_taylor {ν : Measure ℝ} [IsFiniteMeasure ν] (hsupp : ν (Set.Iio 0) = 0)
    {M C d₀ K₀ P₀ : ℝ} (h72 : ∀ k : ℕ, ∫ x, sevenHalvesBCF k x ∂ν ≤ M) {H₀ : ℝ → ℝ}
    (hrep : ∀ s : ℝ, 0 ≤ s → H₀ s = s + compensatedLaplace ν s)
    (htay : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |H₀ s - (-(s * d₀) + s ^ 2 * K₀ / 2 - s ^ 3 * P₀ / 6)| ≤ C * (s ^ 3 * Real.sqrt s)) :
    measureMoment ν 1 = 1 + d₀ ∧ measureMoment ν 2 = K₀ ∧ measureMoment ν 3 = P₀ ∧
      Integrable (fun x : ℝ => x ^ 3) ν := by
  have hpos : ∀ᵐ x ∂ν, 0 ≤ x := by
    rw [ae_iff]; simp only [not_le]; exact hsupp
  obtain ⟨hGi, hGle⟩ := sevenHalves_integrable h72
  have hM0 : 0 ≤ M := (integral_nonneg (sevenHalvesBCF_nonneg 0)).trans (h72 0)
  have hpow : ∀ k : ℕ, k ≤ 3 → Integrable (fun x : ℝ => x ^ k) ν := by
    intro k hk
    refine ((integrable_const (1 : ℝ)).add hGi).mono' (measurable_id.pow_const k).aestronglyMeasurable ?_
    filter_upwards [hpos] with x hx
    rw [Real.norm_eq_abs]
    exact pow_le_one_add_sevenHalves hx hk
  have i1 := hpow 1 (by norm_num)
  have i2 := hpow 2 (by norm_num)
  have i3 := hpow 3 le_rfl
  simp only [pow_one] at i1
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 →
      |(1 - measureMoment ν 1 + d₀) * s + ((measureMoment ν 2 - K₀) / 2) * s ^ 2 +
        (-(measureMoment ν 3 - P₀) / 6) * s ^ 3| ≤ (C + 4 * M) * s ^ 3 * Real.sqrt s := by
    intro s hs0 hs1
    have hR : Integrable (fun x : ℝ => taylorRem (s * x)) ν := by
      refine (hGi.const_mul (4 * (s ^ 3 * Real.sqrt s))).mono'
        (continuous_taylorRem.measurable.comp (measurable_const.mul measurable_id)).aestronglyMeasurable ?_
      filter_upwards [hpos] with x hx
      rw [Real.norm_eq_abs, max_eq_left hx]
      have hsx : -1 ≤ s * x := by nlinarith
      refine (abs_taylorRem_le hsx).trans (le_of_eq ?_)
      rw [abs_of_nonneg (by positivity), Real.sqrt_mul hs0.le]
      ring
    have hRb : |∫ x, taylorRem (s * x) ∂ν| ≤ 4 * (s ^ 3 * Real.sqrt s) * M := by
      have := norm_integral_le_of_norm_le (hGi.const_mul (4 * (s ^ 3 * Real.sqrt s))) (by
        filter_upwards [hpos] with x hx
        rw [Real.norm_eq_abs, max_eq_left hx]
        have hsx : -1 ≤ s * x := by nlinarith
        refine (abs_taylorRem_le hsx).trans (le_of_eq ?_)
        rw [abs_of_nonneg (by positivity), Real.sqrt_mul hs0.le]
        ring)
      rw [Real.norm_eq_abs, integral_const_mul] at this
      exact this.trans (mul_le_mul_of_nonneg_left hGle (by positivity))
    have hlap : compensatedLaplace ν s = -(s * measureMoment ν 1) +
        s ^ 2 * measureMoment ν 2 / 2 - s ^ 3 * measureMoment ν 3 / 6 +
          ∫ x, taylorRem (s * x) ∂ν := by
      have hfun : (fun x : ℝ => Real.exp (-(s * x)) - 1) = fun x =>
          -(s * x) + s ^ 2 * x ^ 2 / 2 - s ^ 3 * x ^ 3 / 6 + taylorRem (s * x) := by
        funext x; simp only [taylorRem]; ring
      have ia : Integrable (fun x : ℝ => -(s * x)) ν := (i1.const_mul s).neg
      have ib : Integrable (fun x : ℝ => s ^ 2 * x ^ 2 / 2) ν := (i2.const_mul _).div_const 2
      have ic : Integrable (fun x : ℝ => s ^ 3 * x ^ 3 / 6) ν := (i3.const_mul _).div_const 6
      have iab : Integrable (fun x : ℝ => -(s * x) + s ^ 2 * x ^ 2 / 2) ν := ia.add ib
      have iabc : Integrable (fun x : ℝ => -(s * x) + s ^ 2 * x ^ 2 / 2 - s ^ 3 * x ^ 3 / 6) ν :=
        iab.sub ic
      rw [compensatedLaplace, hfun, integral_add iabc hR, integral_sub iab ic,
        integral_add ia ib, integral_neg, integral_const_mul, integral_div, integral_const_mul,
        integral_div, integral_const_mul]
      simp only [measureMoment, pow_one]
    have h1 := htay s ⟨hs0.le, hs1⟩
    rw [hrep s hs0.le, hlap] at h1
    have hid : (1 - measureMoment ν 1 + d₀) * s + ((measureMoment ν 2 - K₀) / 2) * s ^ 2 +
        (-(measureMoment ν 3 - P₀) / 6) * s ^ 3 =
        (s + (-(s * measureMoment ν 1) + s ^ 2 * measureMoment ν 2 / 2 -
          s ^ 3 * measureMoment ν 3 / 6 + ∫ x, taylorRem (s * x) ∂ν) -
          (-(s * d₀) + s ^ 2 * K₀ / 2 - s ^ 3 * P₀ / 6)) - ∫ x, taylorRem (s * x) ∂ν := by ring
    rw [hid]
    have a1 := abs_le.1 h1
    have a2 := abs_le.1 hRb
    rw [abs_le]
    have e : (C + 4 * M) * s ^ 3 * Real.sqrt s =
        C * (s ^ 3 * Real.sqrt s) + 4 * (s ^ 3 * Real.sqrt s) * M := by ring
    constructor <;> linarith
  obtain ⟨k1, k2, k3⟩ := coeff_eq_zero_of_taylor key
  refine ⟨by linarith, by linarith, by linarith, i3⟩

/-! ### No atom at the origin -/

theorem laplace_split {ν : Measure ℝ} [IsFiniteMeasure ν] (hsupp : ν (Set.Iio 0) = 0) {s : ℝ}
    (hs : 0 ≤ s) :
    compensatedLaplace ν s = (∫ x, Real.exp (-(s * x)) ∂ν) - ν.real Set.univ ∧
      0 ≤ ∫ x, Real.exp (-(s * x)) ∂ν ∧ ∫ x, Real.exp (-(s * x)) ∂ν ≤ ν.real Set.univ := by
  have hpos : ∀ᵐ x ∂ν, 0 ≤ x := by
    rw [ae_iff]; simp only [not_le]; exact hsupp
  have hb : ∀ᵐ x ∂ν, ‖Real.exp (-(s * x))‖ ≤ 1 := by
    filter_upwards [hpos] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hs hx))
  have hi : Integrable (fun x : ℝ => Real.exp (-(s * x))) ν :=
    (integrable_const (1 : ℝ)).mono' (by fun_prop) hb
  refine ⟨?_, integral_nonneg fun x => (Real.exp_pos _).le, ?_⟩
  · rw [compensatedLaplace, integral_sub hi (integrable_const 1), integral_const, smul_eq_mul,
      mul_one]
  · calc ∫ x, Real.exp (-(s * x)) ∂ν ≤ ∫ _, (1 : ℝ) ∂ν :=
          integral_mono_ae hi (integrable_const 1) (hb.mono fun x hx => by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hx; exact hx)
      _ = ν.real Set.univ := by rw [integral_const, smul_eq_mul, mul_one]

theorem tendsto_laplace_atom {ν : Measure ℝ} [IsFiniteMeasure ν] (hsupp : ν (Set.Iio 0) = 0) :
    Tendsto (fun n : ℕ => ∫ x, Real.exp (-((n : ℝ) * x)) ∂ν) atTop (𝓝 (ν.real {0})) := by
  have hpos : ∀ᵐ x ∂ν, 0 ≤ x := by
    rw [ae_iff]; simp only [not_le]; exact hsupp
  have := tendsto_integral_of_dominated_convergence (μ := ν)
    (F := fun (n : ℕ) (x : ℝ) => Real.exp (-((n : ℝ) * x)))
    (f := fun x => ({0} : Set ℝ).indicator (fun _ => (1 : ℝ)) x) (fun _ => (1 : ℝ))
    (fun n => (by fun_prop : Continuous fun x : ℝ => Real.exp (-((n : ℝ) * x))).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => by
      filter_upwards [hpos] with x hx
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (Nat.cast_nonneg n) hx)))
    (by
      filter_upwards [hpos] with x hx
      rcases eq_or_lt_of_le hx with h | h
      · rw [← h, Set.indicator_of_mem (Set.mem_singleton 0)]
        simp
      · rw [Set.indicator_of_notMem (by simpa using h.ne')]
        have h1 : Tendsto (fun n : ℕ => -((n : ℝ) * x)) atTop atBot :=
          tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_mul_const h)
        exact Real.tendsto_exp_atBot.comp h1)
  rwa [integral_indicator_const _ (measurableSet_singleton 0), smul_eq_mul, mul_one] at this

/-- `scaling:noatom`: the Riccati equation as `s → ∞` forces `ν_t({0}) = 0` for almost every
`t ∈ (0, T]`. -/
theorem noatom_of_riccati {T : ℝ} (hT : 0 < T) {S : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    {ν : ℝ → Measure ℝ} (hνm : Measurable ν) (hfin : ∀ τ, IsFiniteMeasure (ν τ))
    (hsupp : ∀ τ ∈ Set.Ioc 0 T, ν τ (Set.Iio 0) = 0)
    (hmass : ∀ τ ∈ Set.Ioc 0 T, (ν τ).real Set.univ = S τ)
    (hrep : ∀ τ ∈ Set.Ioc 0 T, ∀ s : ℝ, 0 ≤ s → H τ s = s + compensatedLaplace (ν τ) s)
    (hric : ∀ s : ℝ, 0 ≤ s → ∀ r t : ℝ, 0 < r → r ≤ t → t ≤ T →
      H t s - H r s = ∫ τ in r..t, (S τ * H τ s + H τ s ^ 2 / 2 - s ^ 2 / 2))
    (hSb : ∀ r : ℝ, 0 < r → ∃ M : ℝ, ∀ τ ∈ Set.Icc r T, |S τ| ≤ M)
    (hSm : Measurable S) (hHm : ∀ s, Measurable fun τ => H τ s) :
    ∀ᵐ τ, τ ∈ Set.Ioc 0 T → ν τ {0} = 0 := by
  -- the Laplace transform at weight `s`
  have hg : ∀ τ ∈ Set.Ioc 0 T, ∀ s : ℝ, 0 ≤ s →
      H τ s - s + S τ = ∫ x, Real.exp (-(s * x)) ∂(ν τ) ∧
        0 ≤ H τ s - s + S τ ∧ H τ s - s + S τ ≤ S τ := by
    intro τ hτ s hs
    haveI := hfin τ
    obtain ⟨e1, e2, e3⟩ := laplace_split (hsupp τ hτ) hs
    have hm := hmass τ hτ
    rw [hrep τ hτ s hs, e1, hm]
    refine ⟨by ring, by linarith, by linarith⟩
  have hk : ∀ k : ℕ, ∀ᵐ τ, τ ∈ Set.Icc (T / ((k : ℝ) + 2)) T → ν τ {0} = 0 := by
    intro k
    set r := T / ((k : ℝ) + 2) with hr_def
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hr : 0 < r := div_pos hT hk2
    have hrT : r < T := by rw [div_lt_iff₀ hk2]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    obtain ⟨M, hM⟩ := hSb r hr
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM T ⟨hrT.le, le_rfl⟩)
    have hIcc : ∀ τ ∈ Set.Icc r T, τ ∈ Set.Ioc 0 T := fun τ hτ => ⟨hr.trans_le hτ.1, hτ.2⟩
    -- measurability
    have hatomm : Measurable fun τ => (ν τ).real {0} :=
      (Measure.measurable_coe (measurableSet_singleton 0)).comp hνm |>.ennreal_toReal
    have hgm : ∀ s : ℝ, Measurable fun τ => H τ s - s + S τ := fun s =>
      ((hHm s).sub_const s).add hSm
    -- integral bound
    have hint : ∀ n : ℕ, 1 ≤ n → |∫ τ in r..T, (H τ n - n + S τ)| ≤
        (4 * M + 2 * M ^ 2 * (T - r)) / n := by
      intro n hn
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < n := by linarith
      have hric' := hric n (Nat.cast_nonneg n) r T hr hrT.le le_rfl
      set g : ℝ → ℝ := fun τ => H τ n - n + S τ with hg_def
      set Q : ℝ → ℝ := fun τ => S τ * (g τ - S τ) + (g τ - S τ) ^ 2 / 2 with hQ_def
      have hF : ∀ τ, S τ * H τ n + H τ n ^ 2 / 2 - (n : ℝ) ^ 2 / 2 = n * g τ + Q τ := by
        intro τ; simp only [hg_def, hQ_def]; ring
      have hgb : ∀ τ ∈ Set.Icc r T, |g τ| ≤ M := fun τ hτ => by
        obtain ⟨-, h1, h2⟩ := hg τ (hIcc τ hτ) n (Nat.cast_nonneg n)
        rw [abs_of_nonneg h1]; exact h2.trans ((le_abs_self _).trans (hM τ hτ))
      have hQb : ∀ τ ∈ Set.Icc r T, |Q τ| ≤ 2 * M ^ 2 := fun τ hτ => by
        obtain ⟨-, h1, h2⟩ := hg τ (hIcc τ hτ) n (Nat.cast_nonneg n)
        have hS := hM τ hτ
        have hS0 : 0 ≤ S τ := le_trans h1 h2
        have e1 : |g τ - S τ| ≤ M := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
          linarith [le_abs_self (S τ)]
        have e2 : |S τ * (g τ - S τ)| ≤ M * M := by
          rw [abs_mul]; exact mul_le_mul hS e1 (abs_nonneg _) hM0
        have e3 : (g τ - S τ) ^ 2 ≤ M ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) e1 2
        have e4 : 0 ≤ (g τ - S τ) ^ 2 := sq_nonneg _
        refine (abs_add_le _ _).trans ?_
        rw [abs_div, abs_two, abs_of_nonneg e4]
        nlinarith
      have ig : IntervalIntegrable g volume r T := ii_of_bdd hrT.le (hgm n) hgb
      have iQ : IntervalIntegrable Q volume r T :=
        ii_of_bdd hrT.le ((hSm.mul ((hgm n).sub hSm)).add (((hgm n).sub hSm).pow_const 2
          |>.div_const 2)) hQb
      have hsplit : (∫ τ in r..T, (S τ * H τ n + H τ n ^ 2 / 2 - (n : ℝ) ^ 2 / 2)) =
          n * (∫ τ in r..T, g τ) + ∫ τ in r..T, Q τ := by
        simp_rw [hF]
        rw [intervalIntegral.integral_add (ig.const_mul _) iQ, intervalIntegral.integral_const_mul]
      rw [hsplit] at hric'
      have hQi : |∫ τ in r..T, Q τ| ≤ 2 * M ^ 2 * (T - r) := by
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := r) (b := T)
          (C := 2 * M ^ 2) (f := Q) fun τ hτ => by
            rw [Set.uIoc_of_le hrT.le] at hτ
            rw [Real.norm_eq_abs]; exact hQb τ ⟨hτ.1.le, hτ.2⟩
        rwa [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ T - r by linarith)] at this
      have hLHS : |H T n - H r n| ≤ 4 * M := by
        have hT' := hg T ⟨hT, le_rfl⟩ n (Nat.cast_nonneg n)
        have hr' := hg r (hIcc r ⟨le_rfl, hrT.le⟩) n (Nat.cast_nonneg n)
        have hST := hM T ⟨hrT.le, le_rfl⟩
        have hSr := hM r ⟨le_rfl, hrT.le⟩
        have a1 := abs_le.1 hST
        have a2 := abs_le.1 hSr
        rw [abs_le]
        constructor <;> linarith [hT'.2.1, hT'.2.2, hr'.2.1, hr'.2.2]
      have hnI : (n : ℝ) * ∫ τ in r..T, g τ = (H T n - H r n) - ∫ τ in r..T, Q τ := by linarith
      have hmul : |(n : ℝ) * ∫ τ in r..T, g τ| ≤ 4 * M + 2 * M ^ 2 * (T - r) := by
        rw [hnI]; exact (abs_sub _ _).trans (add_le_add hLHS hQi)
      rw [abs_mul, abs_of_pos hn0] at hmul
      rw [le_div_iff₀ hn0, mul_comm]
      exact hmul
    -- dominated convergence in time
    have hlim : Tendsto (fun n : ℕ => ∫ τ in r..T, (H τ n - n + S τ)) atTop
        (𝓝 (∫ τ in r..T, (ν τ).real {0})) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
        (Eventually.of_forall fun n => (hgm n).aestronglyMeasurable) ?_
        intervalIntegrable_const ?_
      · refine Eventually.of_forall fun n => Eventually.of_forall fun τ hτ => ?_
        rw [Set.uIoc_of_le hrT.le] at hτ
        have hτ' : τ ∈ Set.Icc r T := ⟨hτ.1.le, hτ.2⟩
        obtain ⟨-, h1, h2⟩ := hg τ (hIcc τ hτ') n (Nat.cast_nonneg n)
        rw [Real.norm_eq_abs, abs_of_nonneg h1]
        exact h2.trans ((le_abs_self _).trans (hM τ hτ'))
      · refine Eventually.of_forall fun τ hτ => ?_
        rw [Set.uIoc_of_le hrT.le] at hτ
        have hτ' : τ ∈ Set.Ioc 0 T := hIcc τ ⟨hτ.1.le, hτ.2⟩
        haveI := hfin τ
        refine (tendsto_laplace_atom (hsupp τ hτ')).congr fun n => ?_
        exact ((hg τ hτ' n (Nat.cast_nonneg n)).1).symm
    have hzero : ∫ τ in r..T, (ν τ).real {0} = 0 := by
      have h0 : Tendsto (fun n : ℕ => ∫ τ in r..T, (H τ n - n + S τ)) atTop (𝓝 0) := by
        refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := 4 * M + 2 * M ^ 2 * (T - r))).div_atTop
          tendsto_natCast_atTop_atTop)
        filter_upwards [eventually_ge_atTop 1] with n hn
        rw [Real.norm_eq_abs]; exact hint n hn
      exact tendsto_nhds_unique hlim h0
    -- the atom vanishes almost everywhere on `[r, T]`
    have hnn : ∀ τ, 0 ≤ (ν τ).real {0} := fun τ => measureReal_nonneg
    rw [intervalIntegral.integral_of_le hrT.le] at hzero
    have hint' : IntegrableOn (fun τ => (ν τ).real {0}) (Set.Ioc r T) := by
      refine (integrableOn_const (C := M) (by simp)).mono' hatomm.aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ => ?_)
      have hτ' : τ ∈ Set.Ioc 0 T := hIcc τ ⟨hτ.1.le, hτ.2⟩
      haveI := hfin τ
      obtain ⟨e1, e2, e3⟩ := laplace_split (hsupp τ hτ') (le_refl (0 : ℝ))
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn τ)]
      calc (ν τ).real {0} ≤ (ν τ).real Set.univ := measureReal_mono (Set.subset_univ _)
        _ = S τ := hmass τ hτ'
        _ ≤ M := (le_abs_self _).trans (hM τ ⟨hτ.1.le, hτ.2⟩)
    have hae := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hnn) hint').1 hzero
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hae
    have hTnull : ∀ᵐ τ : ℝ, τ ≠ r := by
      rw [ae_iff]; simp
    filter_upwards [hae, hTnull] with τ hτ hτr hτI
    have hτ' : τ ∈ Set.Ioc r T := ⟨lt_of_le_of_ne hτI.1 (Ne.symm hτr), hτI.2⟩
    have hτv := hτ hτ'
    haveI := hfin τ
    rwa [Pi.zero_apply, measureReal_def, ENNReal.toReal_eq_zero_iff,
      or_iff_left (measure_ne_top _ _)] at hτv
  rw [← ae_all_iff] at hk
  filter_upwards [hk] with τ hτ hτI
  obtain ⟨k, hk'⟩ := exists_nat_gt (T / τ)
  apply hτ k
  refine ⟨?_, hτI.2⟩
  rw [div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ hτI.1] at hk'
  nlinarith [hτI.1]

/-! ### Bounded variation from a one-sided bound -/

theorem eVariationOn_le_of_oneSided {f : ℝ → ℝ} {s : Set ℝ} {C M a b : ℝ} (hC : 0 ≤ C)
    (hs : s ⊆ Set.Icc a b) (hb : ∀ x ∈ s, |f x| ≤ M)
    (hone : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → f y - f x ≤ C * (y - x)) :
    eVariationOn f s ≤ ENNReal.ofReal (2 * M + 2 * C * (b - a)) := by
  refine iSup_le fun p => ?_
  rcases p with ⟨n, u, hu, hus⟩
  dsimp only
  have hterm : ∀ i, edist (f (u (i + 1))) (f (u i)) =
      ENNReal.ofReal |f (u (i + 1)) - f (u i)| := fun i => by rw [edist_dist, Real.dist_eq]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hstep : ∀ i, |f (u (i + 1)) - f (u i)| ≤
      2 * C * (u (i + 1) - u i) - (f (u (i + 1)) - f (u i)) := by
    intro i
    have hmono : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    have h1 := hone (u i) (hus i) (u (i + 1)) (hus (i + 1)) hmono
    have h2 : 0 ≤ C * (u (i + 1) - u i) := mul_nonneg hC (by linarith)
    rcases le_total 0 (f (u (i + 1)) - f (u i)) with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_nonpos h]; linarith
  have t1 : ∑ i ∈ Finset.range n, (u (i + 1) - u i) = u n - u 0 := Finset.sum_range_sub u n
  have t2 : ∑ i ∈ Finset.range n, (f (u (i + 1)) - f (u i)) = f (u n) - f (u 0) :=
    Finset.sum_range_sub (fun i => f (u i)) n
  calc ∑ i ∈ Finset.range n, |f (u (i + 1)) - f (u i)|
      ≤ ∑ i ∈ Finset.range n, (2 * C * (u (i + 1) - u i) - (f (u (i + 1)) - f (u i))) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = 2 * C * (u n - u 0) - (f (u n) - f (u 0)) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, t1, t2]
    _ ≤ 2 * M + 2 * C * (b - a) := by
        have h1 := hs (hus n)
        have h2 := hs (hus 0)
        have h3 := abs_le.1 (hb _ (hus n))
        have h4 := abs_le.1 (hb _ (hus 0))
        have : 2 * C * (u n - u 0) ≤ 2 * C * (b - a) :=
          mul_le_mul_of_nonneg_left (by linarith [h1.2, h2.1]) (by positivity)
        linarith

/-! ### Limits of the scaled estimates -/

section LimitEstimates

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem eventually_small_div {x y : ℝ} (hy : 0 < y) :
    ∀ᶠ N in atTop, x / (Real.log 2 * N) * Real.log 2 ≤ y ∧ x / N ≤ y := by
  have h1 : Tendsto (fun N : ℝ => x / N) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 := (tendsto_order.1 h1).2 y hy
  filter_upwards [h2, eventually_gt_atTop 0] with N hN hN0
  refine ⟨le_of_eq_of_le ?_ hN.le, hN.le⟩
  have : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp

/-- The one-sided bound for `S` in the limit, with the uniform bound on `[r, T]`. -/
theorem oneSided_limit (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hlamT : lam * (2 * T) ^ 2 ≤ η) {Ns : ℕ → ℝ}
    (hNs : Tendsto Ns atTop atTop) {S : ℝ → ℝ}
    (hS : ∀ t ∈ Set.Ioc 0 T, Tendsto (fun j => scaledMass μ B lam (Ns j) t) atTop (𝓝 (S t)))
    {r : ℝ} (hr : 0 < r) (hrT : r < T) :
    ∃ CS : ℝ, 0 ≤ CS ∧ (∃ M : ℝ, ∀ t ∈ Set.Icc r T, |S t| ≤ M) ∧
      ∀ t₁ t₂ : ℝ, r ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T → S t₂ - S t₁ ≤ CS * (t₂ - t₁) := by
  set M := (2 * C + c) / r + 2 * C * lam * T
  have hev := unif_bounds hB hC hc hW hlam hT hlamT hr
  obtain ⟨N₁, CS, ε, hε, hone⟩ := scaled_oneSided (μ := μ) hpos hmean hB (M := M) hr hrT
  have hev' := hNs.eventually (hev.and (eventually_ge_atTop N₁))
  refine ⟨max CS 0, le_max_right _ _, ⟨M, fun t ht => ?_⟩, fun t₁ t₂ h1 h12 h2 => ?_⟩
  · refine le_of_tendsto (hS t ⟨hr.trans_le ht.1, ht.2⟩).abs ?_
    filter_upwards [hev'] with j hj
    exact (hj.1.2 t ht).2.2.2.1
  · have hlim1 := (hS t₂ ⟨by linarith, h2⟩).sub (hS t₁ ⟨by linarith, by linarith⟩)
    have hlim2 : Tendsto (fun j => max CS 0 * (t₂ - t₁) + ε (Ns j)) atTop
        (𝓝 (max CS 0 * (t₂ - t₁) + 0)) := tendsto_const_nhds.add (hε.comp hNs)
    rw [add_zero] at hlim2
    refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
    filter_upwards [hev'] with j hj
    have hb : ∀ t ∈ Set.Icc r T, |scaledMass μ B lam (Ns j) t| ≤ M := fun t ht =>
      (hj.1.2 t ht).2.2.2.1
    have := hone (Ns j) hj.2 lam hb t₁ t₂ h1 h12 h2
    have : CS * (t₂ - t₁) ≤ max CS 0 * (t₂ - t₁) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    linarith

/-- The Taylor bound `scaling:taylor` in the limit. -/
theorem taylor_limit (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hlamT : lam * (2 * T) ^ 2 ≤ η) {Ns : ℕ → ℝ}
    (hNs : Tendsto Ns atTop atTop) {t s : ℝ} (ht : t ∈ Set.Ioc 0 T) (hs : 0 ≤ s)
    {Sv Hv dv Kv Pv : ℝ}
    (hS : Tendsto (fun j => scaledMass μ B lam (Ns j) t) atTop (𝓝 Sv))
    (hH : Tendsto (fun j => scaledCompensated μ B lam (Ns j) t s) atTop (𝓝 Hv))
    (hd : Tendsto (fun j => scaledDrift μ B lam (Ns j) t) atTop (𝓝 dv))
    (hK : Tendsto (fun j => scaledSecond μ B lam (Ns j) t) atTop (𝓝 Kv))
    (hP : Tendsto (fun j => scaledThird μ B lam (Ns j) t) atTop (𝓝 Pv)) :
    |Hv - (-(s * dv) + s ^ 2 * Kv / 2 - s ^ 3 * Pv / 6)| ≤
      32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (s ^ 3 * Real.sqrt s) *
        (t ^ 2 * Real.sqrt t) := by
  have ha := log_pos_of_two_lt hB
  set K7 := 32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (s ^ 3 * Real.sqrt s) *
    (t ^ 2 * Real.sqrt t)
  have hp : Tendsto (fun j => -(s * scaledDrift μ B lam (Ns j) t) +
      s ^ 2 * scaledSecond μ B lam (Ns j) t / 2 - s ^ 3 * scaledThird μ B lam (Ns j) t / 6) atTop
      (𝓝 (-(s * dv) + s ^ 2 * Kv / 2 - s ^ 3 * Pv / 6)) :=
    (((hd.const_mul s).neg).add ((hK.const_mul _).div_const 2)).sub ((hP.const_mul _).div_const 6)
  have hlim1 := (hH.sub hp).abs
  have hinv : Tendsto (fun j => 1 / Ns j) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hNs
  have hlim2 : Tendsto (fun j => s ^ 2 * (1 / Ns j) + s * (1 / Ns j) * |scaledMass μ B lam (Ns j) t| +
      s * (1 / Ns j) * |-(s * scaledDrift μ B lam (Ns j) t) +
        s ^ 2 * scaledSecond μ B lam (Ns j) t / 2 - s ^ 3 * scaledThird μ B lam (Ns j) t / 6| + K7)
      atTop (𝓝 (s ^ 2 * 0 + s * 0 * |Sv| + s * 0 * |-(s * dv) + s ^ 2 * Kv / 2 - s ^ 3 * Pv / 6| +
        K7)) :=
    ((((hinv.const_mul _)).add (((hinv.const_mul s)).mul hS.abs)).add
      (((hinv.const_mul s)).mul hp.abs)).add tendsto_const_nhds
  simp only [mul_zero, zero_mul, zero_add] at hlim2
  refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
  have hlb : 0 ≤ Real.log B - Real.log (floorSeq B 1) := by
    have := Real.log_nonpos (floorSeq_one_pos hB).le (floorSeq_le_one hB 1); linarith
  have hsm : ∀ᶠ N in atTop, s / (Real.log B * N) * (Real.log B - Real.log (floorSeq B 1)) ≤ 1 := by
    have h1 : Tendsto (fun N : ℝ => s / (Real.log B * N) * (Real.log B - Real.log (floorSeq B 1)))
        atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := s / Real.log B *
        (Real.log B - Real.log (floorSeq B 1)))).mul (tendsto_inv_atTop_zero (𝕜 := ℝ))
      rw [mul_zero] at this
      refine this.congr fun N => ?_
      ring
    exact ((tendsto_order.1 h1).2 _ one_pos).mono fun N hN => hN.le
  filter_upwards [hNs.eventually ((unif_bounds hB hC hc hW hlam hT hlamT ht.1).and
    ((eventually_ge_atTop s).and hsm))] with j ⟨⟨hN, hb⟩, hsN, hsmall⟩
  obtain ⟨hNt2, hNt0, -⟩ := hb t ⟨le_rfl, ht.2⟩
  have hwin : lam * (2 * t) ^ 2 ≤ η := by
    have : (2 * t) ^ 2 ≤ (2 * T) ^ 2 := pow_le_pow_left₀ (by linarith [ht.1]) (by linarith [ht.2]) 2
    exact (mul_le_mul_of_nonneg_left this hlam).trans hlamT
  have := scaled_taylor hpos hmean hB hC hc hW hlam hN ht.1 hNt2 hNt0 hwin hs hsN hsmall
  have e1 : s ^ 2 / Ns j = s ^ 2 * (1 / Ns j) := by ring
  have e2 : s / Ns j = s * (1 / Ns j) := by ring
  rw [e1, e2] at this
  exact this

/-- The scaled window bounds in the limit. -/
theorem limit_bounds {B : ℝ} (hB : 2 < B) {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hW : WinBounds μ B n₀ η C c) {lam T : ℝ} (hlam : 0 ≤ lam) (hT : 0 < T)
    (hlamT : lam * (2 * T) ^ 2 ≤ η) {Ns : ℕ → ℝ} (hNs : Tendsto Ns atTop atTop) {t : ℝ}
    (ht : t ∈ Set.Ioc 0 T) {Sv dv Kv Pv : ℝ}
    (hS : Tendsto (fun j => scaledMass μ B lam (Ns j) t) atTop (𝓝 Sv))
    (hd : Tendsto (fun j => scaledDrift μ B lam (Ns j) t) atTop (𝓝 dv))
    (hK : Tendsto (fun j => scaledSecond μ B lam (Ns j) t) atTop (𝓝 Kv))
    (hP : Tendsto (fun j => scaledThird μ B lam (Ns j) t) atTop (𝓝 Pv)) :
    c / t - 2 * C * lam * t ≤ Sv ∧ Sv ≤ 2 * C / t + 2 * C * lam * t ∧
    |dv| ≤ (4 * C * lam * t ^ 2 + 16 * C * lam ^ 2 * t ^ 4) / Real.log B ∧
    (c * t / 2 - 8 * C * lam * t ^ 3) / Real.log B ^ 2 ≤ Kv ∧
    Kv ≤ (C * t + 8 * C * lam * t ^ 3) / Real.log B ^ 2 ∧
    (c * t ^ 2 - 16 * C * lam * t ^ 4) / Real.log B ^ 3 ≤ Pv ∧
    Pv ≤ (4 * C * t ^ 2 + 16 * C * lam * t ^ 4) / Real.log B ^ 3 := by
  have hwin : lam * (2 * t) ^ 2 ≤ η := by
    have : (2 * t) ^ 2 ≤ (2 * T) ^ 2 := pow_le_pow_left₀ (by linarith [ht.1]) (by linarith [ht.2]) 2
    exact (mul_le_mul_of_nonneg_left this hlam).trans hlamT
  have hev : ∀ᶠ j in atTop, 0 < Ns j ∧ 2 ≤ Ns j * t ∧ (n₀ : ℝ) + 1 ≤ Ns j * t := by
    filter_upwards [hNs.eventually (unif_bounds hB hC hc hW hlam hT hlamT ht.1)] with j hj
    obtain ⟨h1, h2, -⟩ := hj.2 t ⟨le_rfl, ht.2⟩
    exact ⟨hj.1, h1, h2⟩
  have hw : ∀ᶠ j in atTop, _ := hev.mono fun j hj =>
    scaled_window hB hC hc hW hlam hj.1 ht.1 hj.2.1 hj.2.2 hwin
  refine ⟨ge_of_tendsto hS (hw.mono fun j hj => hj.2.2.1),
    le_of_tendsto hS (hw.mono fun j hj => hj.2.2.2.1), ?_,
    ge_of_tendsto hK (hw.mono fun j hj => hj.2.2.2.2.2.1),
    le_of_tendsto hK (hw.mono fun j hj => hj.2.2.2.2.2.2.1),
    ge_of_tendsto hP (hw.mono fun j hj => hj.2.2.2.2.2.2.2.1),
    le_of_tendsto hP (hw.mono fun j hj => hj.2.2.2.2.2.2.2.2.1)⟩
  have hlim : Tendsto (fun j => (2 * C / (Ns j * t) + 4 * C * lam * t ^ 2 +
      16 * C * lam ^ 2 * t ^ 4) / Real.log B) atTop
      (𝓝 ((0 + 4 * C * lam * t ^ 2 + 16 * C * lam ^ 2 * t ^ 4) / Real.log B)) := by
    refine (((tendsto_const_nhds.div_atTop (hNs.atTop_mul_const ht.1)).add tendsto_const_nhds).add
      tendsto_const_nhds).div_const _
  rw [zero_add] at hlim
  exact le_of_tendsto_of_tendsto hd.abs hlim (hw.mono fun j hj => hj.2.2.2.2.1)

/-- The matching estimate in the limit: `|d - α P| ≤ 16 C λ² t⁴ / a`. -/
theorem limit_matching {B : ℝ} (hB : 2 < B) {κ ℓ₃ η C : ℝ} (hC : 0 < C)
    (hM : WinMatching μ B κ ℓ₃ η C) {lam T : ℝ} (hlam : 0 ≤ lam) (hT : 0 < T)
    (hlamT : lam * (2 * T) ^ 2 ≤ η) {Ns : ℕ → ℝ} (hNs : Tendsto Ns atTop atTop) {t : ℝ}
    (ht : t ∈ Set.Ioc 0 T) {dv Pv : ℝ}
    (hd : Tendsto (fun j => scaledDrift μ B lam (Ns j) t) atTop (𝓝 dv))
    (hP : Tendsto (fun j => scaledThird μ B lam (Ns j) t) atTop (𝓝 Pv)) :
    |dv - lam * κ * Real.log B ^ 2 / ℓ₃ * Pv| ≤ 16 * C * lam ^ 2 * t ^ 4 / Real.log B := by
  have ha := log_pos_of_two_lt hB
  have ht0 := ht.1
  have hwin : lam * (2 * t) ^ 2 ≤ η := by
    have : (2 * t) ^ 2 ≤ (2 * T) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith [ht.2]) 2
    exact (mul_le_mul_of_nonneg_left this hlam).trans hlamT
  have hε : ∀ ε > 0, |dv - lam * κ * Real.log B ^ 2 / ℓ₃ * Pv| ≤
      (4 * ε * lam * t ^ 2 + 16 * C * lam ^ 2 * t ^ 4) / Real.log B := by
    intro ε hε
    obtain ⟨n₁, hn₁⟩ := hM ε hε
    have hev : ∀ᶠ j in atTop, 0 < Ns j ∧ 2 ≤ Ns j * t ∧ (n₁ : ℝ) + 1 ≤ Ns j * t := by
      have hmul := hNs.atTop_mul_const ht0
      filter_upwards [hNs.eventually (eventually_gt_atTop 0), hmul.eventually (eventually_ge_atTop 2),
        hmul.eventually (eventually_ge_atTop ((n₁ : ℝ) + 1))] with j h1 h2 h3
      exact ⟨h1, h2, h3⟩
    have hlim1 := (hd.sub (hP.const_mul (lam * κ * Real.log B ^ 2 / ℓ₃))).abs
    have hlim2 : Tendsto (fun j => (2 * C / (Ns j * t) + 4 * ε * lam * t ^ 2 +
        16 * C * lam ^ 2 * t ^ 4) / Real.log B) atTop
        (𝓝 ((0 + 4 * ε * lam * t ^ 2 + 16 * C * lam ^ 2 * t ^ 4) / Real.log B)) :=
      (((tendsto_const_nhds.div_atTop (hNs.atTop_mul_const ht0)).add tendsto_const_nhds).add
        tendsto_const_nhds).div_const _
    rw [zero_add] at hlim2
    refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
    filter_upwards [hev] with j hj
    exact scaled_matching hB hC hε hn₁ hlam hj.1 ht0 hj.2.1 hj.2.2 hwin
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hden : 0 < 4 * lam * t ^ 2 + 1 := by positivity
  have := hε (δ * Real.log B / (4 * lam * t ^ 2 + 1)) (by positivity)
  refine this.trans ?_
  rw [div_le_iff₀ ha, add_mul, div_mul_cancel₀ _ ha.ne', add_comm]
  have : 4 * (δ * Real.log B / (4 * lam * t ^ 2 + 1)) * lam * t ^ 2 ≤ δ * Real.log B := by
    rw [show 4 * (δ * Real.log B / (4 * lam * t ^ 2 + 1)) * lam * t ^ 2 =
      δ * Real.log B * (4 * lam * t ^ 2 / (4 * lam * t ^ 2 + 1)) by ring]
    have h1 : 4 * lam * t ^ 2 / (4 * lam * t ^ 2 + 1) ≤ 1 := by
      rw [div_le_one hden]; linarith
    calc δ * Real.log B * (4 * lam * t ^ 2 / (4 * lam * t ^ 2 + 1)) ≤ δ * Real.log B * 1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = δ * Real.log B := mul_one _
  linarith

end LimitEstimates

/-! ### The complex Taylor bound -/

/-- `scaling:taylor` after the analytic extension: for `Re s ≥ 0`,
`‖s + ∫ (e^{-sx} - 1) dν - (-s d + s² K/2 - s³ P/6)‖ ≤ 4 M |s|^{7/2}`. -/
theorem taylor_complex_of {ν : Measure ℝ} [IsFiniteMeasure ν] (hsupp : ν (Set.Iio 0) = 0)
    {M d K P : ℝ} (hint : Integrable (fun x => max x 0 ^ 3 * Real.sqrt (max x 0)) ν)
    (hM : ∫ x, max x 0 ^ 3 * Real.sqrt (max x 0) ∂ν ≤ M)
    (h1 : measureMoment ν 1 = 1 + d) (h2 : measureMoment ν 2 = K) (h3 : measureMoment ν 3 = P)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖s + complexCompensatedLaplace ν s - (-(s * (d : ℂ)) + s ^ 2 * (K : ℂ) / 2 -
      s ^ 3 * (P : ℂ) / 6)‖ ≤ 4 * M * (‖s‖ ^ 3 * Real.sqrt ‖s‖) := by
  have hpos : ∀ᵐ x ∂ν, 0 ≤ x := by
    rw [ae_iff]; simp only [not_le]; exact hsupp
  have hpow : ∀ k : ℕ, k ≤ 3 → Integrable (fun x : ℝ => x ^ k) ν := by
    intro k hk
    refine ((integrable_const (1 : ℝ)).add hint).mono'
      (measurable_id.pow_const k).aestronglyMeasurable ?_
    filter_upwards [hpos] with x hx
    rw [Real.norm_eq_abs]
    exact pow_le_one_add_sevenHalves hx hk
  have i1 : Integrable (fun x : ℝ => ((x : ℂ))) ν := by
    have := (hpow 1 (by norm_num)).ofReal (𝕜 := ℂ)
    simpa using this
  have i2 : Integrable (fun x : ℝ => ((x : ℂ)) ^ 2) ν := by
    have := (hpow 2 (by norm_num)).ofReal (𝕜 := ℂ)
    simpa using this
  have i3 : Integrable (fun x : ℝ => ((x : ℂ)) ^ 3) ν := by
    have := (hpow 3 le_rfl).ofReal (𝕜 := ℂ)
    simpa using this
  set rC : ℝ → ℂ := fun x => Complex.exp (-(s * x)) - (1 - s * x + (s * x) ^ 2 / 2 - (s * x) ^ 3 / 6)
    with hrC
  have hrCb : ∀ᵐ x ∂ν, ‖rC x‖ ≤ 4 * (‖s‖ ^ 3 * Real.sqrt ‖s‖) *
      (max x 0 ^ 3 * Real.sqrt (max x 0)) := by
    filter_upwards [hpos] with x hx
    have hre : 0 ≤ (s * (x : ℂ)).re := by
      rw [Complex.re_mul_ofReal]; exact mul_nonneg hs hx
    have := norm_cexp_neg_sub_taylor_le (s * (x : ℂ)) (Or.inr hre)
    rw [max_eq_left hx]
    refine this.trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx,
      Real.sqrt_mul (norm_nonneg _)]
    ring
  have irC : Integrable rC ν :=
    (hint.const_mul (4 * (‖s‖ ^ 3 * Real.sqrt ‖s‖))).mono' (by
      simp only [hrC]; fun_prop) hrCb
  have hid : (fun x : ℝ => Complex.exp (-(s * x)) - 1) = fun x : ℝ =>
      -(s * (x : ℂ)) + s ^ 2 * (x : ℂ) ^ 2 / 2 - s ^ 3 * (x : ℂ) ^ 3 / 6 + rC x := by
    funext x; simp only [hrC]; ring
  have ia : Integrable (fun x : ℝ => -(s * (x : ℂ))) ν := (i1.const_mul s).neg
  have ib : Integrable (fun x : ℝ => s ^ 2 * (x : ℂ) ^ 2 / 2) ν := (i2.const_mul _).div_const 2
  have ic : Integrable (fun x : ℝ => s ^ 3 * (x : ℂ) ^ 3 / 6) ν := (i3.const_mul _).div_const 6
  have iab : Integrable (fun x : ℝ => -(s * (x : ℂ)) + s ^ 2 * (x : ℂ) ^ 2 / 2) ν := ia.add ib
  have iabc : Integrable (fun x : ℝ => -(s * (x : ℂ)) + s ^ 2 * (x : ℂ) ^ 2 / 2 -
      s ^ 3 * (x : ℂ) ^ 3 / 6) ν := iab.sub ic
  have hm1 : ∫ x, ((x : ℂ)) ∂ν = ((1 + d : ℝ) : ℂ) := by
    rw [← h1, measureMoment, ← integral_complex_ofReal]; simp
  have hm2 : ∫ x, ((x : ℂ)) ^ 2 ∂ν = (K : ℂ) := by
    rw [← h2, measureMoment, ← integral_complex_ofReal]; simp
  have hm3 : ∫ x, ((x : ℂ)) ^ 3 ∂ν = (P : ℂ) := by
    rw [← h3, measureMoment, ← integral_complex_ofReal]; simp
  have hlap : complexCompensatedLaplace ν s =
      -(s * ((1 + d : ℝ) : ℂ)) + s ^ 2 * (K : ℂ) / 2 - s ^ 3 * (P : ℂ) / 6 + ∫ x : ℝ, rC x ∂ν := by
    rw [complexCompensatedLaplace, hid, integral_add iabc irC, integral_sub iab ic,
      integral_add ia ib, integral_neg, integral_const_mul, integral_div, integral_const_mul,
      integral_div, integral_const_mul, hm1, hm2, hm3]
  rw [hlap]
  have hsimp : s + (-(s * ((1 + d : ℝ) : ℂ)) + s ^ 2 * (K : ℂ) / 2 - s ^ 3 * (P : ℂ) / 6 +
      ∫ x : ℝ, rC x ∂ν) - (-(s * (d : ℂ)) + s ^ 2 * (K : ℂ) / 2 - s ^ 3 * (P : ℂ) / 6) =
      ∫ x : ℝ, rC x ∂ν := by push_cast; ring
  rw [hsimp]
  calc ‖∫ x : ℝ, rC x ∂ν‖ ≤ ∫ x, 4 * (‖s‖ ^ 3 * Real.sqrt ‖s‖) *
        (max x 0 ^ 3 * Real.sqrt (max x 0)) ∂ν := norm_integral_le_of_norm_le
          (hint.const_mul _) hrCb
    _ = 4 * (‖s‖ ^ 3 * Real.sqrt ‖s‖) * ∫ x, max x 0 ^ 3 * Real.sqrt (max x 0) ∂ν :=
        integral_const_mul _ _
    _ ≤ 4 * (‖s‖ ^ 3 * Real.sqrt ‖s‖) * M := mul_le_mul_of_nonneg_left hM (by positivity)
    _ = 4 * M * (‖s‖ ^ 3 * Real.sqrt ‖s‖) := by ring

/-! ## Assembly -/

/-- The entrance constant of `scaling:entrancebounds`, from the window constants. -/
noncomputable def entranceConst (a C c : ℝ) : ℝ :=
  2 / c + 4 * a ^ 2 / c + 2 * a ^ 3 / c + 2 * C + c + (4 * C + c) / a + (C + c) / a ^ 2 +
    (4 * C + c) / a ^ 3

theorem entranceConst_pos {a C c : ℝ} (ha : 0 < a) (hC : 0 < C) (hc : 0 < c) :
    0 < entranceConst a C c := by
  unfold entranceConst; positivity

set_option maxHeartbeats 400000 in
-- seven entrance bounds share one elaboration
/-- The arithmetic of `scaling:entrancebounds`. -/
theorem entrance_arith {a C c lam t Sv dv Kv Pv : ℝ} (ha : 0 < a) (hC : 0 < C) (hc : 0 < c)
    (hlam : 0 ≤ lam) (ht : 0 < t) (hsmall : lam * t ^ 2 ≤ c / (32 * C))
    (hS1 : c / t - 2 * C * lam * t ≤ Sv) (hS2 : Sv ≤ 2 * C / t + 2 * C * lam * t)
    (hd : |dv| ≤ (4 * C * lam * t ^ 2 + 16 * C * lam ^ 2 * t ^ 4) / a)
    (hK1 : (c * t / 2 - 8 * C * lam * t ^ 3) / a ^ 2 ≤ Kv)
    (hK2 : Kv ≤ (C * t + 8 * C * lam * t ^ 3) / a ^ 2)
    (hP1 : (c * t ^ 2 - 16 * C * lam * t ^ 4) / a ^ 3 ≤ Pv)
    (hP2 : Pv ≤ (4 * C * t ^ 2 + 16 * C * lam * t ^ 4) / a ^ 3) :
    (entranceConst a C c)⁻¹ * t⁻¹ ≤ Sv ∧ Sv ≤ entranceConst a C c * t⁻¹ ∧
    |dv| ≤ entranceConst a C c * lam * t ^ 2 ∧ (entranceConst a C c)⁻¹ * t ≤ Kv ∧
    Kv ≤ entranceConst a C c * t ∧ (entranceConst a C c)⁻¹ * t ^ 2 ≤ Pv ∧
    Pv ≤ entranceConst a C c * t ^ 2 := by
  set E := entranceConst a C c with hEdef
  have hE : 0 < E := entranceConst_pos ha hC hc
  have hEexp : E = 2 / c + 4 * a ^ 2 / c + 2 * a ^ 3 / c + 2 * C + c + (4 * C + c) / a +
      (C + c) / a ^ 2 + (4 * C + c) / a ^ 3 := rfl
  have p1 : 0 < 2 / c := by positivity
  have p2 : 0 < 4 * a ^ 2 / c := by positivity
  have p3 : 0 < 2 * a ^ 3 / c := by positivity
  have p5 : 0 < (4 * C + c) / a := by positivity
  have p6 : 0 < (C + c) / a ^ 2 := by positivity
  have p7 : 0 < (4 * C + c) / a ^ 3 := by positivity
  have e1 : 2 / c ≤ E := by rw [hEexp]; linarith
  have e2 : 4 * a ^ 2 / c ≤ E := by rw [hEexp]; linarith
  have e3 : 2 * a ^ 3 / c ≤ E := by rw [hEexp]; linarith
  have e4 : 2 * C + c ≤ E := by rw [hEexp]; linarith
  have e5 : (4 * C + c) / a ≤ E := by rw [hEexp]; linarith
  have e6 : (C + c) / a ^ 2 ≤ E := by rw [hEexp]; linarith
  have e7 : (4 * C + c) / a ^ 3 ≤ E := by rw [hEexp]; linarith
  have i1 : E⁻¹ ≤ c / 2 := by
    have := inv_anti₀ p1 e1; rwa [inv_div] at this
  have i2 : E⁻¹ ≤ c / (4 * a ^ 2) := by
    have := inv_anti₀ p2 e2; rwa [inv_div] at this
  have i3 : E⁻¹ ≤ c / (2 * a ^ 3) := by
    have := inv_anti₀ p3 e3; rwa [inv_div] at this
  have hlt0 : 0 ≤ lam * t ^ 2 := by positivity
  have hCl : C * (lam * t ^ 2) ≤ c / 32 := by
    calc C * (lam * t ^ 2) ≤ C * (c / (32 * C)) := mul_le_mul_of_nonneg_left hsmall hC.le
      _ = c / 32 := by field_simp
  have ht' : 0 < t⁻¹ := inv_pos.2 ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : c / t - 2 * C * lam * t = (c - 2 * (C * (lam * t ^ 2))) * t⁻¹ := by
      field_simp
    have h2 : c / 2 * t⁻¹ ≤ (c - 2 * (C * (lam * t ^ 2))) * t⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) ht'.le
    have h3 : E⁻¹ * t⁻¹ ≤ c / 2 * t⁻¹ := mul_le_mul_of_nonneg_right i1 ht'.le
    linarith
  · have h1 : 2 * C / t + 2 * C * lam * t = (2 * C + 2 * (C * (lam * t ^ 2))) * t⁻¹ := by
      field_simp
    have h2 : (2 * C + 2 * (C * (lam * t ^ 2))) * t⁻¹ ≤ E * t⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) ht'.le
    linarith
  · have h1 : 16 * C * lam ^ 2 * t ^ 4 = 16 * (C * (lam * t ^ 2)) * (lam * t ^ 2) := by ring
    have h2 : 16 * (C * (lam * t ^ 2)) * (lam * t ^ 2) ≤ 16 * (c / 32) * (lam * t ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) hlt0
    have h3 : 4 * C * lam * t ^ 2 + 16 * C * lam ^ 2 * t ^ 4 ≤ (4 * C + c) * (lam * t ^ 2) := by
      have : 0 ≤ c * (lam * t ^ 2) := by positivity
      linarith
    have h4 : (4 * C * lam * t ^ 2 + 16 * C * lam ^ 2 * t ^ 4) / a ≤
        (4 * C + c) / a * (lam * t ^ 2) := by
      rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right h3 ha.le
    have h5 : (4 * C + c) / a * (lam * t ^ 2) ≤ E * (lam * t ^ 2) :=
      mul_le_mul_of_nonneg_right e5 hlt0
    have h6 : E * (lam * t ^ 2) = E * lam * t ^ 2 := by ring
    linarith
  · have h1 : 8 * C * lam * t ^ 3 = 8 * (C * (lam * t ^ 2)) * t := by ring
    have h2 : 8 * (C * (lam * t ^ 2)) * t ≤ 8 * (c / 32) * t :=
      mul_le_mul_of_nonneg_right (by linarith) ht.le
    have h3 : c / (4 * a ^ 2) * t ≤ (c * t / 2 - 8 * C * lam * t ^ 3) / a ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : c / (4 * a ^ 2) * t * a ^ 2 = c * t / 4 := by field_simp
      rw [this]; linarith
    have h4 : E⁻¹ * t ≤ c / (4 * a ^ 2) * t := mul_le_mul_of_nonneg_right i2 ht.le
    linarith
  · have h1 : 8 * C * lam * t ^ 3 = 8 * (C * (lam * t ^ 2)) * t := by ring
    have h2 : 8 * (C * (lam * t ^ 2)) * t ≤ 8 * (c / 32) * t :=
      mul_le_mul_of_nonneg_right (by linarith) ht.le
    have h3 : (C * t + 8 * C * lam * t ^ 3) / a ^ 2 ≤ (C + c) / a ^ 2 * t := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ c * t := by positivity
      linarith
    have h4 : (C + c) / a ^ 2 * t ≤ E * t := mul_le_mul_of_nonneg_right e6 ht.le
    linarith
  · have h1 : 16 * C * lam * t ^ 4 = 16 * (C * (lam * t ^ 2)) * t ^ 2 := by ring
    have h2 : 16 * (C * (lam * t ^ 2)) * t ^ 2 ≤ 16 * (c / 32) * t ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg t)
    have h3 : c / (2 * a ^ 3) * t ^ 2 ≤ (c * t ^ 2 - 16 * C * lam * t ^ 4) / a ^ 3 := by
      rw [le_div_iff₀ (by positivity)]
      have : c / (2 * a ^ 3) * t ^ 2 * a ^ 3 = c * t ^ 2 / 2 := by field_simp
      rw [this]; linarith
    have h4 : E⁻¹ * t ^ 2 ≤ c / (2 * a ^ 3) * t ^ 2 := mul_le_mul_of_nonneg_right i3 (sq_nonneg t)
    linarith
  · have h1 : 16 * C * lam * t ^ 4 = 16 * (C * (lam * t ^ 2)) * t ^ 2 := by ring
    have h2 : 16 * (C * (lam * t ^ 2)) * t ^ 2 ≤ 16 * (c / 32) * t ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg t)
    have h3 : (4 * C * t ^ 2 + 16 * C * lam * t ^ 4) / a ^ 3 ≤ (4 * C + c) / a ^ 3 * t ^ 2 := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ c * t ^ 2 := by positivity
      linarith
    have h4 : (4 * C + c) / a ^ 3 * t ^ 2 ≤ E * t ^ 2 := mul_le_mul_of_nonneg_right e7 (sq_nonneg t)
    linarith

/-- The limit objects of the extraction and their convergence and measurability. -/
structure LimData (μ : Measure ℝ) (B lam T : ℝ) (Ns : ℕ → ℝ) (S d K P : ℝ → ℝ)
    (H : ℝ → ℝ → ℝ) : Prop where
  tendsto_Ns : Tendsto Ns atTop atTop
  conv_S : ∀ t ∈ Set.Ioc 0 T, Tendsto (fun j => scaledMass μ B lam (Ns j) t) atTop (𝓝 (S t))
  unif_d : ∀ r, 0 < r → r ≤ T →
    TendstoUniformlyOn (fun j t => scaledDrift μ B lam (Ns j) t) d atTop (Set.Icc r T)
  unif_K : ∀ r, 0 < r → r ≤ T →
    TendstoUniformlyOn (fun j t => scaledSecond μ B lam (Ns j) t) K atTop (Set.Icc r T)
  unif_P : ∀ r, 0 < r → r ≤ T →
    TendstoUniformlyOn (fun j t => scaledThird μ B lam (Ns j) t) P atTop (Set.Icc r T)
  unif_H : ∀ r M, 0 < r → r ≤ T → 0 ≤ M →
    TendstoUniformlyOn (fun j (p : ℝ × ℝ) => scaledCompensated μ B lam (Ns j) p.1 p.2)
      (fun p => H p.1 p.2) atTop (Set.Icc r T ×ˢ Set.Icc 0 M)
  meas_S : Measurable S
  meas_d : Measurable d
  meas_K : Measurable K
  meas_P : Measurable P
  meas_H : ∀ s, Measurable fun t => H t s

namespace LimData

variable {μ : Measure ℝ} {B lam T : ℝ} {Ns : ℕ → ℝ} {S d K P : ℝ → ℝ} {H : ℝ → ℝ → ℝ}

theorem conv_d (L : LimData μ B lam T Ns S d K P H) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) :
    Tendsto (fun j => scaledDrift μ B lam (Ns j) t) atTop (𝓝 (d t)) :=
  (L.unif_d t ht.1 ht.2).tendsto_at ⟨le_rfl, ht.2⟩

theorem conv_K (L : LimData μ B lam T Ns S d K P H) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) :
    Tendsto (fun j => scaledSecond μ B lam (Ns j) t) atTop (𝓝 (K t)) :=
  (L.unif_K t ht.1 ht.2).tendsto_at ⟨le_rfl, ht.2⟩

theorem conv_P (L : LimData μ B lam T Ns S d K P H) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) :
    Tendsto (fun j => scaledThird μ B lam (Ns j) t) atTop (𝓝 (P t)) :=
  (L.unif_P t ht.1 ht.2).tendsto_at ⟨le_rfl, ht.2⟩

theorem conv_H (L : LimData μ B lam T Ns S d K P H) {t s : ℝ} (ht : t ∈ Set.Ioc 0 T)
    (hs : 0 ≤ s) :
    Tendsto (fun j => scaledCompensated μ B lam (Ns j) t s) atTop (𝓝 (H t s)) :=
  (L.unif_H t s ht.1 ht.2 hs).tendsto_at (x := (t, s)) ⟨⟨le_rfl, ht.2⟩, ⟨hs, le_rfl⟩⟩

end LimData

section Fields

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- Uniform bounds for the limits on `[r, T]`. -/
theorem LimData.bounds_on {B : ℝ} (hB : 2 < B) {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hW : WinBounds μ B n₀ η C c) {lam T : ℝ} (hlam : 0 ≤ lam) (hT : 0 < T)
    (hlamT : lam * (2 * T) ^ 2 ≤ η) {Ns : ℕ → ℝ} {S d K P : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LimData μ B lam T Ns S d K P H) {r : ℝ} (hr : 0 < r) :
    ∀ τ ∈ Set.Icc r T, |S τ| ≤ (2 * C + c) / r + 2 * C * lam * T ∧
      |d τ| ≤ (C + 4 * C * lam * T ^ 2 + 16 * C * lam ^ 2 * T ^ 4) / Real.log B ∧
      |K τ| ≤ (C * T + 8 * C * lam * T ^ 3) / Real.log B ^ 2 ∧
      |P τ| ≤ (4 * C * T ^ 2 + 16 * C * lam * T ^ 4) / Real.log B ^ 3 := by
  intro τ hτ
  have hτ' : τ ∈ Set.Ioc 0 T := ⟨hr.trans_le hτ.1, hτ.2⟩
  have hev := L.tendsto_Ns.eventually (unif_bounds hB hC hc hW hlam hT hlamT hr)
  refine ⟨le_of_tendsto (L.conv_S τ hτ').abs (hev.mono fun j hj => (hj.2 τ hτ).2.2.2.1),
    le_of_tendsto (L.conv_d hτ').abs (hev.mono fun j hj => (hj.2 τ hτ).2.2.2.2.1),
    le_of_tendsto (L.conv_K hτ').abs (hev.mono fun j hj => (hj.2 τ hτ).2.2.2.2.2.1),
    le_of_tendsto (L.conv_P hτ').abs (hev.mono fun j hj => (hj.2 τ hτ).2.2.2.2.2.2.1)⟩

/-- The Taylor bound for the limits. -/
theorem LimData.taylor (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hlamT : lam * (2 * T) ^ 2 ≤ η) {Ns : ℕ → ℝ}
    {S d K P : ℝ → ℝ} {H : ℝ → ℝ → ℝ} (L : LimData μ B lam T Ns S d K P H) {t s : ℝ}
    (ht : t ∈ Set.Ioc 0 T) (hs : 0 ≤ s) :
    |H t s - (-(s * d t) + s ^ 2 * K t / 2 - s ^ 3 * P t / 6)| ≤
      32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (s ^ 3 * Real.sqrt s) *
        (t ^ 2 * Real.sqrt t) :=
  taylor_limit hpos hmean hB hC hc hW hlam hT hlamT L.tendsto_Ns ht hs (L.conv_S t ht)
    (L.conv_H ht hs) (L.conv_d ht) (L.conv_K ht) (L.conv_P ht)

/-- The Riccati equation for the limits. -/
theorem LimData.riccati (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hlamT : lam * (2 * T) ^ 2 ≤ η) {Ns : ℕ → ℝ}
    {S d K P : ℝ → ℝ} {H : ℝ → ℝ → ℝ} (L : LimData μ B lam T Ns S d K P H) :
    ∀ s : ℝ, 0 ≤ s → ∀ r t : ℝ, 0 < r → r ≤ t → t ≤ T →
      H t s - H r s = timeIntegral (fun τ => S τ * H τ s + H τ s ^ 2 / 2 - s ^ 2 / 2) r t :=
  fun _ hs _ _ hr hrt htT => riccati_limit hpos hmean hB hC hc hW hlam hT hlamT L.tendsto_Ns
    L.conv_S (fun _ hτ _ hσ => L.conv_H hτ hσ) hs hr hrt htT

/-- The moment equations for the limits. -/
theorem LimData.odes (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hlamT : lam * (2 * T) ^ 2 ≤ η) {Ns : ℕ → ℝ}
    {S d K P : ℝ → ℝ} {H : ℝ → ℝ → ℝ} (L : LimData μ B lam T Ns S d K P H) {r t : ℝ}
    (hr : 0 < r) (hrt : r ≤ t) (htT : t ≤ T) :
    d t - d r = ∫ τ in r..t, S τ * d τ ∧
      K t - K r = ∫ τ in r..t, (S τ * K τ + d τ ^ 2 - 1) ∧
      P t - P r = ∫ τ in r..t, (S τ * P τ + 3 * d τ * K τ) := by
  have ha := log_pos_of_two_lt hB
  have hb := L.bounds_on hB hC hc hW hlam hT hlamT hr
  have hsub : ∀ τ ∈ Set.Icc r t, τ ∈ Set.Icc r T := fun τ hτ => ⟨hτ.1, hτ.2.trans htT⟩
  refine odes_of_riccati_taylor hrt L.meas_S L.meas_d L.meas_K L.meas_P L.meas_H
    (fun τ hτ => (hb τ (hsub τ hτ)).1) (fun τ hτ => (hb τ (hsub τ hτ)).2.1)
    (fun τ hτ => (hb τ (hsub τ hτ)).2.2.1) (fun τ hτ => (hb τ (hsub τ hτ)).2.2.2)
    (C₇ := 32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (T ^ 2 * Real.sqrt T))
    (by positivity)
    (fun s hs => L.riccati hpos hmean hB hC hc hW hlam hT hlamT s hs.1 r t hr hrt htT)
    (fun τ hτ s hs => ?_)
  have hτ' : τ ∈ Set.Ioc 0 T := ⟨hr.trans_le hτ.1, hτ.2.trans htT⟩
  refine (L.taylor hpos hmean hB hC hc hW hlam hT hlamT hτ' hs.1).trans ?_
  have h1 : τ ^ 2 * Real.sqrt τ ≤ T ^ 2 * Real.sqrt T :=
    mul_le_mul (pow_le_pow_left₀ hτ'.1.le hτ'.2 2) (Real.sqrt_le_sqrt hτ'.2)
      (Real.sqrt_nonneg _) (by positivity)
  have h2 : 0 ≤ 32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (s ^ 3 * Real.sqrt s) := by
    have := hs.1; positivity
  calc _ ≤ 32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (s ^ 3 * Real.sqrt s) *
        (T ^ 2 * Real.sqrt T) := mul_le_mul_of_nonneg_left h1 h2
    _ = _ := by ring

/-- Local Lipschitz bounds for `d, K, P`. -/
theorem LimData.lipschitz (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hlamT : lam * (2 * T) ^ 2 ≤ η) {Ns : ℕ → ℝ}
    {S d K P : ℝ → ℝ} {H : ℝ → ℝ → ℝ} (L : LimData μ B lam T Ns S d K P H) :
    ∀ r : ℝ, 0 < r → ∃ Lc : NNReal,
      LipschitzOnWith Lc d (Set.Icc r T) ∧ LipschitzOnWith Lc K (Set.Icc r T) ∧
        LipschitzOnWith Lc P (Set.Icc r T) := by
  intro r hr
  have hb := L.bounds_on hB hC hc hW hlam hT hlamT hr
  set MS := (2 * C + c) / r + 2 * C * lam * T
  set MD := (C + 4 * C * lam * T ^ 2 + 16 * C * lam ^ 2 * T ^ 4) / Real.log B
  set MK := (C * T + 8 * C * lam * T ^ 3) / Real.log B ^ 2
  set MP := (4 * C * T ^ 2 + 16 * C * lam * T ^ 4) / Real.log B ^ 3
  have ha := log_pos_of_two_lt hB
  have hMS : 0 ≤ MS := by positivity
  have hMD : 0 ≤ MD := by positivity
  have hMK : 0 ≤ MK := by positivity
  have hMP : 0 ≤ MP := by positivity
  set Lr := MS * MD + (MS * MK + MD ^ 2 + 1) + (MS * MP + 3 * (MD * MK))
  have hLr : 0 ≤ Lr := by positivity
  -- a general Lipschitz estimate from an integral identity
  have key : ∀ (f g : ℝ → ℝ) (M : ℝ), 0 ≤ M → M ≤ Lr →
      (∀ x y, r ≤ x → x ≤ y → y ≤ T → f y - f x = ∫ τ in x..y, g τ) →
      (∀ τ ∈ Set.Icc r T, |g τ| ≤ M) →
      LipschitzOnWith (Real.toNNReal Lr) f (Set.Icc r T) := by
    intro f g M hM hML hid hg
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.coe_toNNReal _ hLr, Real.dist_eq, Real.dist_eq]
    have hint : ∀ x y, r ≤ x → x ≤ y → y ≤ T → |f y - f x| ≤ Lr * (y - x) := by
      intro x y hx hxy hy
      rw [hid x y hx hxy hy]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := y) (C := M)
        (f := g) fun τ hτ => by
          rw [Set.uIoc_of_le hxy] at hτ
          rw [Real.norm_eq_abs]; exact hg τ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ y - x by linarith)] at this
      exact this.trans (mul_le_mul_of_nonneg_right hML (by linarith))
    rcases le_total x y with h | h
    · rw [abs_sub_comm (f x), abs_sub_comm x y, abs_of_nonneg (show (0 : ℝ) ≤ y - x by linarith)]
      exact hint x y hx.1 h hy.2
    · rw [abs_of_nonneg (show (0 : ℝ) ≤ x - y by linarith)]
      exact hint y x hy.1 h hx.2
  have hodes := fun x y (hx : r ≤ x) (hxy : x ≤ y) (hy : y ≤ T) =>
    L.odes hpos hmean hB hC hc hW hlam hT hlamT (hr.trans_le hx) hxy hy
  refine ⟨Real.toNNReal Lr, ?_, ?_, ?_⟩
  · refine key d (fun τ => S τ * d τ) (MS * MD) (by positivity) (by
      have : 0 ≤ MS * MK + MD ^ 2 + 1 := by positivity
      have : 0 ≤ MS * MP + 3 * (MD * MK) := by positivity
      linarith) (fun x y hx hxy hy => (hodes x y hx hxy hy).1) fun τ hτ => ?_
    rw [abs_mul]; exact mul_le_mul (hb τ hτ).1 (hb τ hτ).2.1 (abs_nonneg _) hMS
  · refine key K (fun τ => S τ * K τ + d τ ^ 2 - 1) (MS * MK + MD ^ 2 + 1) (by positivity) (by
      have : 0 ≤ MS * MD := by positivity
      have : 0 ≤ MS * MP + 3 * (MD * MK) := by positivity
      linarith) (fun x y hx hxy hy => (hodes x y hx hxy hy).2.1) fun τ hτ => ?_
    have e1 : |S τ * K τ| ≤ MS * MK := by
      rw [abs_mul]; exact mul_le_mul (hb τ hτ).1 (hb τ hτ).2.2.1 (abs_nonneg _) hMS
    have e2 : d τ ^ 2 ≤ MD ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb τ hτ).2.1 2
    have e3 : 0 ≤ d τ ^ 2 := sq_nonneg _
    have := abs_le.1 e1
    rw [abs_le]; constructor <;> linarith
  · refine key P (fun τ => S τ * P τ + 3 * d τ * K τ) (MS * MP + 3 * (MD * MK)) (by positivity)
      (by
        have : 0 ≤ MS * MD := by positivity
        have : 0 ≤ MS * MK + MD ^ 2 + 1 := by positivity
        linarith) (fun x y hx hxy hy => (hodes x y hx hxy hy).2.2) fun τ hτ => ?_
    have e1 : |S τ * P τ| ≤ MS * MP := by
      rw [abs_mul]; exact mul_le_mul (hb τ hτ).1 (hb τ hτ).2.2.2 (abs_nonneg _) hMS
    have e2 : |3 * d τ * K τ| ≤ 3 * (MD * MK) := by
      rw [abs_mul, abs_mul, show |(3 : ℝ)| = 3 by norm_num, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hb τ hτ).2.1 (hb τ hτ).2.2.1 (abs_nonneg _)
        hMD) (by norm_num)
    exact (abs_add_le _ _).trans (add_le_add e1 e2)

/-- `S` is locally of bounded variation on `(0, T]`. -/
theorem LimData.bv (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hlamT : lam * (2 * T) ^ 2 ≤ η) {Ns : ℕ → ℝ}
    {S d K P : ℝ → ℝ} {H : ℝ → ℝ → ℝ} (L : LimData μ B lam T Ns S d K P H) :
    LocallyBoundedVariationOn S (Set.Ioc 0 T) := by
  intro a b ha hb
  by_cases haT : a < T
  · obtain ⟨CS, hCS, ⟨M, hM⟩, hone⟩ :=
      oneSided_limit hpos hmean hB hC hc hW hlam hT hlamT L.tendsto_Ns L.conv_S ha.1 haT
    have hsub : Set.Ioc 0 T ∩ Set.Icc a b ⊆ Set.Icc a T := fun x hx => ⟨hx.2.1, hx.1.2⟩
    have := eVariationOn_le_of_oneSided hCS hsub (fun x hx => hM x (hsub hx))
      (fun x hx y hy hxy => hone x y (hsub hx).1 hxy (hsub hy).2)
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this
  · have haT' : a = T := le_antisymm ha.2 (not_lt.1 haT)
    refine BoundedVariationOn.of_subsingleton fun x hx y hy => ?_
    have h1 : x = T := le_antisymm hx.1.2 (haT' ▸ hx.2.1)
    have h2 : y = T := le_antisymm hy.1.2 (haT' ▸ hy.2.1)
    rw [h1, h2]

/-- `scaling:matching` for the limits. -/
theorem LimData.matching {B : ℝ} (hB : 2 < B) {n₀ : ℕ} {κ ℓ₃ η C c : ℝ} (hC : 0 < C)
    (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) (hWM : WinMatching μ B κ ℓ₃ η C) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hlamT : lam * (2 * T) ^ 2 ≤ η)
    (hsmall : lam * T ^ 2 ≤ c / (32 * C)) {Ns : ℕ → ℝ}
    {S d K P : ℝ → ℝ} {H : ℝ → ℝ → ℝ} (L : LimData μ B lam T Ns S d K P H) :
    Tendsto (fun t => d t / P t) (𝓝[>] 0) (𝓝 (lam * κ * Real.log B ^ 2 / ℓ₃)) := by
  have ha := log_pos_of_two_lt hB
  set α := lam * κ * Real.log B ^ 2 / ℓ₃
  set Kc := 16 * C * lam ^ 2 / Real.log B * (2 * Real.log B ^ 3 / c)
  have hbound : ∀ t ∈ Set.Ioc 0 T, |d t / P t - α| ≤ Kc * t ^ 2 := by
    intro t ht
    have hm := limit_matching hB hC hWM hlam hT hlamT L.tendsto_Ns ht (L.conv_d ht) (L.conv_P ht)
    obtain ⟨-, -, -, -, -, hP1, -⟩ := limit_bounds hB hC hc hW hlam hT hlamT L.tendsto_Ns ht
      (L.conv_S t ht) (L.conv_d ht) (L.conv_K ht) (L.conv_P ht)
    have ht0 := ht.1
    have hlt : lam * t ^ 2 ≤ c / (32 * C) :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0.le ht.2 2) hlam).trans hsmall
    have hCl : C * (lam * t ^ 2) ≤ c / 32 := by
      calc C * (lam * t ^ 2) ≤ C * (c / (32 * C)) := mul_le_mul_of_nonneg_left hlt hC.le
        _ = c / 32 := by field_simp
    have hPlow : c * t ^ 2 / (2 * Real.log B ^ 3) ≤ P t := by
      refine le_trans ?_ hP1
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 16 * C * lam * t ^ 4 = 16 * (C * (lam * t ^ 2)) * t ^ 2 := by ring
      have h2 : 16 * (C * (lam * t ^ 2)) * t ^ 2 ≤ 16 * (c / 32) * t ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg t)
      have h3 : 0 ≤ c * t ^ 2 := by positivity
      nlinarith [pow_pos ha 3]
    have hPpos : 0 < P t := lt_of_lt_of_le (by positivity) hPlow
    have heq : d t / P t - α = (d t - α * P t) / P t := by field_simp
    rw [heq, abs_div, abs_of_pos hPpos, div_le_iff₀ hPpos]
    calc |d t - α * P t| ≤ 16 * C * lam ^ 2 * t ^ 4 / Real.log B := hm
      _ = Kc * t ^ 2 * (c * t ^ 2 / (2 * Real.log B ^ 3)) := by
          simp only [Kc]; field_simp
      _ ≤ Kc * t ^ 2 * P t := mul_le_mul_of_nonneg_left hPlow (by positivity)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun t : ℝ => Kc * t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => Kc * t ^ 2) (𝓝 0) (𝓝 (Kc * 0 ^ 2)) :=
      ((continuous_const.mul (continuous_pow 2)).tendsto 0)
    rw [show Kc * (0 : ℝ) ^ 2 = 0 by ring] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [Ioo_mem_nhdsGT hT] with t ht
  rw [norm_norm, Real.norm_eq_abs]
  exact hbound t ⟨ht.1, ht.2.le⟩

end Fields

/-! ### Measurability of the scaled objects -/

theorem measurable_lim_indicator {f : ℕ → ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hf : ∀ j, Measurable (f j)) {g : ℝ → ℝ}
    (hg : ∀ t ∈ s, Tendsto (fun j => f j t) atTop (𝓝 (g t))) (hg0 : ∀ t ∉ s, g t = 0) :
    Measurable g := by
  refine measurable_of_tendsto_metrizable (f := fun j => s.indicator (f j))
    (fun j => (hf j).indicator hs) (tendsto_pi_nhds.2 fun t => ?_)
  by_cases ht : t ∈ s
  · simp only [Set.indicator_of_mem ht]; exact hg t ht
  · simp only [Set.indicator_of_notMem ht, hg0 t ht]; exact tendsto_const_nhds

theorem measurable_scaledMass (μ : Measure ℝ) (B lam N : ℝ) :
    Measurable fun t => scaledMass μ B lam N t :=
  measurable_floor_comp (fun n => N * (tiltedMass μ B (scalingField μ B lam N) n - 1)) N

theorem measurable_scaledDrift (μ : Measure ℝ) (B lam N : ℝ) :
    Measurable fun t => scaledDrift μ B lam N t :=
  measurable_floor_comp (fun n => tiltedLogMoment μ B (scalingField μ B lam N) 1 n / Real.log B) N

theorem measurable_scaledSecond (μ : Measure ℝ) (B lam N : ℝ) :
    Measurable fun t => scaledSecond μ B lam N t :=
  measurable_floor_comp
    (fun n => tiltedLogMoment μ B (scalingField μ B lam N) 2 n / (Real.log B ^ 2 * N)) N

theorem measurable_scaledThird (μ : Measure ℝ) (B lam N : ℝ) :
    Measurable fun t => scaledThird μ B lam N t :=
  measurable_floor_comp
    (fun n => tiltedLogMoment μ B (scalingField μ B lam N) 3 n / (Real.log B ^ 3 * N ^ 2)) N

theorem measurable_scaledCompensated (μ : Measure ℝ) (B lam N s : ℝ) :
    Measurable fun t => scaledCompensated μ B lam N t s :=
  measurable_floor_comp (fun n => s + transformAt μ B (scalingField μ B lam N) N n s -
    transformAt μ B (scalingField μ B lam N) N n 0) N

theorem measurable_integral_scalingMeasure (μ : Measure ℝ) (B lam N : ℝ) (f : ℝ → ℝ) :
    Measurable fun t => ∫ x, f x ∂(scalingMeasure μ B lam N t) :=
  measurable_floor_comp (fun n => ∫ x, f x ∂(rescaledMeasure μ B (scalingField μ B lam N) N n)) N

/-! ### The limit data -/

section Construction

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- The extraction produces a subsequence and limit objects with the properties of
`LimData`. -/
theorem exists_limData (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hW : WinBounds μ B n₀ η C c) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hwT : lam * (2 * T) ^ 2 ≤ η) {Nseq : ℕ → ℝ}
    (hNseq : Tendsto Nseq atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (S d K P : ℝ → ℝ) (H : ℝ → ℝ → ℝ),
      LimData μ B lam T (fun j => Nseq (φ j)) S d K P H := by
  obtain ⟨φ, hφ, hSφ, hHφ⟩ := extraction hT (fun j t => scaledMass μ B lam (Nseq j) t)
    (fun j t s => scaledCompensated μ B lam (Nseq j) t s)
    (fun t ht => ⟨_, (hNseq.eventually (unif_bounds hB hC hc hW hlam hT hwT ht.1)).mono
      fun j hj => (hj.2 t ⟨le_rfl, ht.2⟩).2.2.2.1⟩)
    (fun t ht s hs => by
      obtain ⟨MF, -, hev⟩ := riccati_bounds hpos hmean hB hC hc hW hlam hT hwT ht.1 hs
      exact ⟨MF, (hNseq.eventually hev).mono fun j hj =>
        (hj.2 t ⟨le_rfl, ht.2⟩ s ⟨hs, le_rfl⟩).2.1⟩)
    (fun r hr hrT => by
      obtain ⟨N₁, CS, ε, hε, hone⟩ := scaled_oneSided (μ := μ) hpos hmean hB
        (M := (2 * C + c) / r + 2 * C * lam * T) hr hrT
      have hev := hNseq.eventually (unif_bounds hB hC hc hW hlam hT hwT hr)
      refine ⟨CS, (2 * C + c) / r + 2 * C * lam * T, fun j => ε (Nseq j), hε.comp hNseq,
        hev.mono fun j hj t ht => (hj.2 t ht).2.2.2.1, ?_⟩
      filter_upwards [hev, hNseq.eventually (eventually_ge_atTop N₁)] with j hj hjN
      exact hone (Nseq j) hjN lam fun t ht => (hj.2 t ht).2.2.2.1)
  set Ns : ℕ → ℝ := fun j => Nseq (φ j) with hNs_def
  have hNs : Tendsto Ns atTop atTop := hNseq.comp hφ.tendsto_atTop
  have hHucs := fun r M (hr : 0 < r) (hrT : r ≤ T) (hM : 0 ≤ M) =>
    ucs_H hpos hmean hB hC hc hW hlam hT hwT hNs hHφ hr hrT hM
  have hdKP := fun r (hr : 0 < r) (hrT : r ≤ T) =>
    ucs_dKP hpos hmean hB hC hc hW hlam hT hwT hNs hr (hHucs r 3 hr hrT (by norm_num))
  let S : ℝ → ℝ := fun t =>
    if t ∈ Set.Ioc 0 T then limUnder atTop (fun j => scaledMass μ B lam (Ns j) t) else 0
  let d : ℝ → ℝ := fun t =>
    if t ∈ Set.Ioc 0 T then limUnder atTop (fun j => scaledDrift μ B lam (Ns j) t) else 0
  let K : ℝ → ℝ := fun t =>
    if t ∈ Set.Ioc 0 T then limUnder atTop (fun j => scaledSecond μ B lam (Ns j) t) else 0
  let P : ℝ → ℝ := fun t =>
    if t ∈ Set.Ioc 0 T then limUnder atTop (fun j => scaledThird μ B lam (Ns j) t) else 0
  let H : ℝ → ℝ → ℝ := fun t s => if t ∈ Set.Ioc 0 T ∧ 0 ≤ s then
    limUnder atTop (fun j => scaledCompensated μ B lam (Ns j) t s) else 0
  have hS : ∀ t ∈ Set.Ioc 0 T, Tendsto (fun j => scaledMass μ B lam (Ns j) t) atTop (𝓝 (S t)) :=
    fun t ht => by simp only [S, if_pos ht]; exact tendsto_nhds_limUnder (hSφ t ht)
  have hud : ∀ r, 0 < r → r ≤ T →
      TendstoUniformlyOn (fun j t => scaledDrift μ B lam (Ns j) t) d atTop (Set.Icc r T) :=
    fun r hr hrT => (tendstoUniformlyOn_limUnder (hdKP r hr hrT).1).congr_right fun t ht => by
      simp only [d, if_pos (show t ∈ Set.Ioc 0 T from ⟨hr.trans_le ht.1, ht.2⟩)]
  have huK : ∀ r, 0 < r → r ≤ T →
      TendstoUniformlyOn (fun j t => scaledSecond μ B lam (Ns j) t) K atTop (Set.Icc r T) :=
    fun r hr hrT => (tendstoUniformlyOn_limUnder (hdKP r hr hrT).2.1).congr_right fun t ht => by
      simp only [K, if_pos (show t ∈ Set.Ioc 0 T from ⟨hr.trans_le ht.1, ht.2⟩)]
  have huP : ∀ r, 0 < r → r ≤ T →
      TendstoUniformlyOn (fun j t => scaledThird μ B lam (Ns j) t) P atTop (Set.Icc r T) :=
    fun r hr hrT => (tendstoUniformlyOn_limUnder (hdKP r hr hrT).2.2).congr_right fun t ht => by
      simp only [P, if_pos (show t ∈ Set.Ioc 0 T from ⟨hr.trans_le ht.1, ht.2⟩)]
  have huH : ∀ r M, 0 < r → r ≤ T → 0 ≤ M →
      TendstoUniformlyOn (fun j (p : ℝ × ℝ) => scaledCompensated μ B lam (Ns j) p.1 p.2)
        (fun p => H p.1 p.2) atTop (Set.Icc r T ×ˢ Set.Icc 0 M) :=
    fun r M hr hrT hM => (tendstoUniformlyOn_limUnder (hHucs r M hr hrT hM)).congr_right
      fun p hp => by
        simp only [H, if_pos (show p.1 ∈ Set.Ioc 0 T ∧ 0 ≤ p.2 from
          ⟨⟨hr.trans_le hp.1.1, hp.1.2⟩, hp.2.1⟩)]
  have hpt : ∀ {F : ℕ → ℝ → ℝ} {g : ℝ → ℝ}, (∀ r, 0 < r → r ≤ T →
      TendstoUniformlyOn F g atTop (Set.Icc r T)) →
      ∀ t ∈ Set.Ioc 0 T, Tendsto (fun j => F j t) atTop (𝓝 (g t)) :=
    fun h t ht => (h t ht.1 ht.2).tendsto_at ⟨le_rfl, ht.2⟩
  refine ⟨φ, hφ, S, d, K, P, H, ⟨hNs, hS, hud, huK, huP, huH, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact measurable_lim_indicator measurableSet_Ioc
      (fun j => measurable_scaledMass μ B lam (Ns j)) hS fun t ht => if_neg ht
  · exact measurable_lim_indicator measurableSet_Ioc
      (fun j => measurable_scaledDrift μ B lam (Ns j)) (hpt hud) fun t ht => if_neg ht
  · exact measurable_lim_indicator measurableSet_Ioc
      (fun j => measurable_scaledSecond μ B lam (Ns j)) (hpt huK) fun t ht => if_neg ht
  · exact measurable_lim_indicator measurableSet_Ioc
      (fun j => measurable_scaledThird μ B lam (Ns j)) (hpt huP) fun t ht => if_neg ht
  · intro s
    by_cases hs : 0 ≤ s
    · refine measurable_lim_indicator measurableSet_Ioc
        (fun j => measurable_scaledCompensated μ B lam (Ns j) s) (fun t ht => ?_)
        fun t ht => if_neg fun h => ht h.1
      exact (huH t s ht.1 ht.2 hs).tendsto_at (x := (t, s)) ⟨⟨le_rfl, ht.2⟩, ⟨hs, le_rfl⟩⟩
    · have : (fun t => H t s) = fun _ => 0 := funext fun t => if_neg fun h => hs h.2
      rw [this]; exact measurable_const

set_option maxHeartbeats 400000 in
-- the entrance data collects all the limit properties
/-- The entrance data and the convergence statements, from the limit data. -/
theorem entrance_of_limData (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ}
    (hB : 2 < B) {κ ℓ₃ : ℝ} {n₀ : ℕ} {η C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hW : WinBounds μ B n₀ η C c) (hWM : WinMatching μ B κ ℓ₃ η C) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 0 < T) (hwT : lam * (2 * T) ^ 2 ≤ η)
    (hsmall : lam * T ^ 2 ≤ c / (32 * C)) {Ns : ℕ → ℝ} {S d K P : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LimData μ B lam T Ns S d K P H) :
    ∃ E : EntranceData T lam (lam * κ * Real.log B ^ 2 / ℓ₃) (entranceConst (Real.log B) C c),
      (∀ r : ℝ, 0 < r → r < T →
        Tendsto (fun j => timeIntegral
          (fun t => |scaledMass μ B lam (Ns j) t - E.S t|) r T) atTop (𝓝 0)) ∧
      (∀ r : ℝ, 0 < r →
        TendstoUniformlyOn (fun j t => scaledDrift μ B lam (Ns j) t) E.d atTop
          (Set.Icc r T)) ∧
      (∀ r : ℝ, 0 < r →
        TendstoUniformlyOn (fun j t => scaledSecond μ B lam (Ns j) t) E.K atTop
          (Set.Icc r T)) ∧
      (∀ r : ℝ, 0 < r →
        TendstoUniformlyOn (fun j t => scaledThird μ B lam (Ns j) t) E.P atTop
          (Set.Icc r T)) ∧
      (∀ r M : ℝ, 0 < r →
        TendstoUniformlyOn
          (fun j (p : ℝ × ℝ) => scaledCompensated μ B lam (Ns j) p.1 p.2)
          (fun p => E.H p.1 p.2) atTop (Set.Icc r T ×ˢ Set.Icc 0 M)) ∧
      (∀ᵐ t, t ∈ Set.Ioc 0 T →
        WeakConvergence (fun j => scalingMeasure μ B lam (Ns j) t) atTop (E.ν t)) := by
  have ha := log_pos_of_two_lt hB
  -- the limit measures
  have hex : ∀ t : ℝ, ∃ ν' : FiniteMeasure ℝ, (t ∈ Set.Ioc 0 T →
      (ν' : Measure ℝ) (Set.Iio 0) = 0 ∧
      (∀ f : ℝ →ᵇ ℝ, Tendsto (fun j => ∫ x, f x ∂(scalingMeasure μ B lam (Ns j) t)) atTop
        (𝓝 (∫ x, f x ∂(ν' : Measure ℝ)))) ∧
      (∀ s : ℝ, 0 ≤ s → ∫ x, expBCF s x ∂(ν' : Measure ℝ) = H t s - s + S t) ∧
      (∀ k : ℕ, ∫ x, sevenHalvesBCF k x ∂(ν' : Measure ℝ) ≤
        96 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (t ^ 2 * Real.sqrt t))) ∧
      (t ∉ Set.Ioc 0 T → ν' = 0) := by
    intro t
    by_cases ht : t ∈ Set.Ioc 0 T
    · obtain ⟨ν', h1, h2, h3, h4⟩ := nu_limit hpos hmean hB hC hc hW hlam hT hwT L.tendsto_Ns ht
        (L.conv_S t ht) (fun s hs => L.conv_H ht hs)
      exact ⟨ν', fun _ => ⟨h1, h2, h3, h4⟩, fun h => absurd ht h⟩
    · exact ⟨0, fun h => absurd h ht, fun _ => rfl⟩
  choose νF hνF using hex
  have hsupp : ∀ t ∈ Set.Ioc 0 T, (νF t : Measure ℝ) (Set.Iio 0) = 0 :=
    fun t ht => ((hνF t).1 ht).1
  have hH0 : ∀ t ∈ Set.Ioc 0 T, H t 0 = 0 := by
    intro t ht
    have h0 : (fun j => scaledCompensated μ B lam (Ns j) t 0) = fun _ => (0 : ℝ) :=
      funext fun j => by simp [scaledCompensated]
    have := L.conv_H ht le_rfl
    rw [h0] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hmass : ∀ t ∈ Set.Ioc 0 T, (νF t : Measure ℝ).real Set.univ = S t := by
    intro t ht
    have h1 := ((hνF t).1 ht).2.2.1 0 le_rfl
    have h2 : (fun x => expBCF 0 x) = fun _ => (1 : ℝ) := funext fun x => by
      rw [expBCF_apply le_rfl, zero_mul, neg_zero, Real.exp_zero]
    rw [h2, integral_const, smul_eq_mul, mul_one, hH0 t ht] at h1
    linarith
  have hexp : ∀ t ∈ Set.Ioc 0 T, ∀ s : ℝ, 0 ≤ s →
      ∫ x, Real.exp (-(s * x)) ∂(νF t : Measure ℝ) = H t s - s + S t := by
    intro t ht s hs
    rw [← ((hνF t).1 ht).2.2.1 s hs]
    refine integral_congr_ae ?_
    have hpos' : ∀ᵐ x ∂(νF t : Measure ℝ), 0 ≤ x := by
      rw [ae_iff]; simp only [not_le]; exact hsupp t ht
    filter_upwards [hpos'] with x hx
    rw [expBCF_apply hs, max_eq_left hx]
  have hrep : ∀ t ∈ Set.Ioc 0 T, ∀ s : ℝ, 0 ≤ s →
      H t s = s + compensatedLaplace (νF t : Measure ℝ) s := by
    intro t ht s hs
    rw [(laplace_split (hsupp t ht) hs).1, hexp t ht s hs, hmass t ht]
    ring
  have htay' : ∀ t ∈ Set.Ioc 0 T, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |H t s - (-(s * d t) + s ^ 2 * K t / 2 - s ^ 3 * P t / 6)| ≤
        32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)) * (t ^ 2 * Real.sqrt t) *
          (s ^ 3 * Real.sqrt s) := by
    intro t ht s hs
    refine (L.taylor hpos hmean hB hC hc hW hlam hT hwT ht hs.1).trans (le_of_eq ?_)
    ring
  have hmom : ∀ t ∈ Set.Ioc 0 T, measureMoment (νF t : Measure ℝ) 1 = 1 + d t ∧
      measureMoment (νF t : Measure ℝ) 2 = K t ∧ measureMoment (νF t : Measure ℝ) 3 = P t ∧
      Integrable (fun x : ℝ => x ^ 3) (νF t : Measure ℝ) := fun t ht =>
    moments_of_taylor (hsupp t ht) ((hνF t).1 ht).2.2.2 (hrep t ht) (htay' t ht)
  have hνm : Measurable fun t => (νF t : Measure ℝ) := by
    refine measurable_toMeasure_of_integral fun f => ?_
    refine measurable_lim_indicator measurableSet_Ioc
      (fun j => measurable_integral_scalingMeasure μ B lam (Ns j) f)
      (fun t ht => ((hνF t).1 ht).2.1 f) fun t ht => ?_
    rw [(hνF t).2 ht, FiniteMeasure.toMeasure_zero, integral_zero_measure]
  have hric := L.riccati hpos hmean hB hC hc hW hlam hT hwT
  have hnoatom : ∀ᵐ t, t ∈ Set.Ioc 0 T → (νF t : Measure ℝ) {0} = 0 :=
    noatom_of_riccati hT hνm (fun τ => inferInstance) hsupp hmass hrep
      (fun s hs r t hr hrt htT => hric s hs r t hr hrt htT)
      (fun r hr => ⟨_, fun τ hτ => (L.bounds_on hB hC hc hW hlam hT hwT hr τ hτ).1⟩)
      L.meas_S L.meas_H
  have hEA : ∀ t ∈ Set.Ioc 0 T, _ := fun t (ht : t ∈ Set.Ioc 0 T) => by
    obtain ⟨hS1, hS2, hd, hK1, hK2, hP1, hP2⟩ := limit_bounds hB hC hc hW hlam hT hwT L.tendsto_Ns
      ht (L.conv_S t ht) (L.conv_d ht) (L.conv_K ht) (L.conv_P ht)
    have hst : lam * t ^ 2 ≤ c / (32 * C) :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1.le ht.2 2) hlam).trans hsmall
    exact entrance_arith ha hC hc hlam ht.1 hst hS1 hS2 hd hK1 hK2 hP1 hP2
  have hodes := fun r t (hr : 0 < r) (hrt : r ≤ t) (htT : t ≤ T) =>
    L.odes hpos hmean hB hC hc hW hlam hT hwT hr hrt htT
  refine ⟨⟨S, d, K, P, H, fun t => (νF t : Measure ℝ),
      L.bv hpos hmean hB hC hc hW hlam hT hwT,
      L.lipschitz hpos hmean hB hC hc hW hlam hT hwT,
      fun r t hr hrt htT => (hodes r t hr hrt htT).1,
      fun r t hr hrt htT => (hodes r t hr hrt htT).2.1,
      fun r t hr hrt htT => (hodes r t hr hrt htT).2.2,
      hric, hνm, ?_,
      Eventually.of_forall fun t ht => ⟨(hEA t ht).1, (hEA t ht).2.1⟩,
      fun t ht => (hEA t ht).2.2,
      fun _ => ⟨32 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B)), fun t ht s hs => by
        rw [rpow_seven_halves_mul_sqrt hs.1, rpow_five_halves ht.1.le]
        exact L.taylor hpos hmean hB hC hc hW hlam hT hwT ht hs.1⟩,
      Eventually.of_forall fun t ht => complexCompensatedLaplace_extension (hsupp t ht),
      fun Kc _ hKc => ⟨4 * (96 * C / (Real.log B ^ 3 * Real.sqrt (Real.log B))),
          Eventually.of_forall fun t ht s hs => ?_⟩,
      L.matching hB hC hc hW hWM hlam hT hwT hsmall⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the representation of `ℋ` by the measures
    filter_upwards [hnoatom] with t hna ht
    refine ⟨inferInstance, hsupp t ht, (hmom t ht).2.2.2, hrep t ht, ?_, (hmom t ht).1,
      (hmom t ht).2.1, (hmom t ht).2.2.1, hna ht⟩
    simp only [measureMoment, pow_zero, integral_const, smul_eq_mul, mul_one]
    exact hmass t ht
  · -- the complex Taylor bound
    obtain ⟨hGi, hGle⟩ := sevenHalves_integrable ((hνF t).1 ht).2.2.2
    obtain ⟨h1, h2, h3, -⟩ := hmom t ht
    have := taylor_complex_of (hsupp t ht) hGi hGle h1 h2 h3 (hKc hs)
    rw [rpow_seven_halves_mul_sqrt (norm_nonneg s), rpow_five_halves ht.1.le]
    refine this.trans (le_of_eq ?_)
    ring
  · -- `L¹` convergence of `S_N`
    intro r hr hrT
    set MS := (2 * C + c) / r + 2 * C * lam * T
    have hbS := L.bounds_on hB hC hc hW hlam hT hwT hr
    have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := r) (b := T) (l := atTop)
      (F := fun j t => |scaledMass μ B lam (Ns j) t - S t|) (f := fun _ => (0 : ℝ))
      (fun _ => 2 * MS)
      (Eventually.of_forall fun j => (continuous_abs.measurable.comp
        ((measurable_scaledMass μ B lam (Ns j)).sub L.meas_S)).aestronglyMeasurable)
      ((L.tendsto_Ns.eventually (unif_bounds hB hC hc hW hlam hT hwT hr)).mono fun j hj =>
        Eventually.of_forall fun τ hτ => by
          rw [Set.uIoc_of_le hrT.le] at hτ
          have hτ' : τ ∈ Set.Icc r T := ⟨hτ.1.le, hτ.2⟩
          have e1 := (hj.2 τ hτ').2.2.2.1
          have e2 := (hbS τ hτ').1
          rw [Real.norm_eq_abs, abs_abs]
          refine (abs_sub _ _).trans ?_
          linarith)
      intervalIntegrable_const
      (Eventually.of_forall fun τ hτ => by
        rw [Set.uIoc_of_le hrT.le] at hτ
        have hτ' : τ ∈ Set.Ioc 0 T := ⟨hr.trans hτ.1, hτ.2⟩
        have := ((L.conv_S τ hτ').sub (tendsto_const_nhds (x := S τ))).abs
        rwa [sub_self, abs_zero] at this)
    rw [intervalIntegral.integral_zero] at hDCT
    exact hDCT
  · intro r hr
    by_cases hrT : r ≤ T
    · exact L.unif_d r hr hrT
    · rw [Set.Icc_eq_empty hrT]; exact tendstoUniformlyOn_empty
  · intro r hr
    by_cases hrT : r ≤ T
    · exact L.unif_K r hr hrT
    · rw [Set.Icc_eq_empty hrT]; exact tendstoUniformlyOn_empty
  · intro r hr
    by_cases hrT : r ≤ T
    · exact L.unif_P r hr hrT
    · rw [Set.Icc_eq_empty hrT]; exact tendstoUniformlyOn_empty
  · intro r M hr
    by_cases hrT : r ≤ T
    · by_cases hM : 0 ≤ M
      · exact L.unif_H r M hr hrT hM
      · rw [Set.Icc_eq_empty hM, Set.prod_empty]; exact tendstoUniformlyOn_empty
    · rw [Set.Icc_eq_empty hrT, Set.empty_prod]; exact tendstoUniformlyOn_empty
  · refine Eventually.of_forall fun t ht => ⟨inferInstance, ?_, ((hνF t).1 ht).2.1⟩
    exact (L.tendsto_Ns.eventually (eventually_gt_atTop 0)).mono fun j hj =>
      isFiniteMeasure_rescaledMeasure hpos hmean hB _ hj _

end Construction

/-! ## The theorem -/

/-- `scaling:compactness` (`scaling.tex` lines 56–118), conditional on the conclusions of
`th:product` (`criticalProduct`), `th:response` (`response_transversality`) and
`prop:window-moments` (`windowMoments`, `window_derivBounds`). The binders through `hκ` and
the conclusion are those of `scaling_compactness` in `DiamondPinning.Statements.Scaling`;
`hProd`, `hTransv`, `hWindow`, `hDeriv` are the conclusions of the four cited statements. -/
theorem scaling_compactness_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hProd : ∃ C : ℝ, 0 < C ∧
      (∀ n : ℕ, 1 ≤ n →
        ((n : ℝ) + 1) ^ 2 / C ≤ tiltedProduct μ B (criticalPoint μ B) n ∧
        tiltedProduct μ B (criticalPoint μ B) n ≤ C * ((n : ℝ) + 1) ^ 2 ∧
        tiltedLogMoment μ B (criticalPoint μ B) 2 n ^ 2 ≤
          C * tiltedProduct μ B (criticalPoint μ B) n ∧
        tiltedLogMoment μ B (criticalPoint μ B) 4 n ≤ C * ((n : ℝ) + 1) ^ 3) ∧
      Summable (fun n : ℕ => (tiltedProduct μ B (criticalPoint μ B) n)⁻¹) ∧
      (∃ ℓ₃ : ℝ, 0 < ℓ₃ ∧
        Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
          tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃)) ∧
      (∀ᶠ n : ℕ in atTop, 1 < tiltedMass μ B (criticalPoint μ B) n) ∧
      ((fun n : ℕ => tiltedMass μ B (criticalPoint μ B) n - 1) =Θ[atTop]
        fun n : ℕ => ((n : ℝ))⁻¹) ∧
      ((fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 2 n) =Θ[atTop]
        fun n : ℕ => (n : ℝ)) ∧
      ((fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 1 n) =O[atTop]
        fun n : ℕ => ((n : ℝ))⁻¹) ∧
      ∀ ε > 0, Tendsto (fun n : ℕ => lawR μ B (criticalPoint μ B) n {x | ε < |x - 1|})
        atTop (𝓝 0))
    (hTransv : ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
        tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ) ∧
      (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B)) =Θ[atTop]
        fun n : ℕ => (n : ℝ) ^ 2)
    (hWindow : ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ u : ℝ, 0 ≤ u →
      u * ((n : ℝ) + 1) ^ 2 ≤ η →
      |tiltedMass μ B (criticalPoint μ B + u) n - tiltedMass μ B (criticalPoint μ B) n| ≤
          C * u * ((n : ℝ) + 1) ∧
        |tiltedLogMoment μ B (criticalPoint μ B + u) 1 n -
            tiltedLogMoment μ B (criticalPoint μ B) 1 n -
            u * deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B)| ≤
          C * u ^ 2 * ((n : ℝ) + 1) ^ 4 ∧
        |tiltedLogMoment μ B (criticalPoint μ B + u) 2 n -
            tiltedLogMoment μ B (criticalPoint μ B) 2 n| ≤ C * u * ((n : ℝ) + 1) ^ 3 ∧
        |tiltedLogMoment μ B (criticalPoint μ B + u) 3 n -
            tiltedLogMoment μ B (criticalPoint μ B) 3 n| ≤ C * u * ((n : ℝ) + 1) ^ 4 ∧
        absTiltedLogRpowMoment μ B (criticalPoint μ B + u) (7 / 2) n ≤
          C * ((n : ℝ) + 1) ^ ((5 : ℝ) / 2) ∧
        |tiltedProduct μ B (criticalPoint μ B + u) n /
            tiltedProduct μ B (criticalPoint μ B) n - 1| ≤ C * u * ((n : ℝ) + 1) ^ 2)
    (hDeriv : ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ v : ℝ, 0 ≤ v →
      v * ((n : ℝ) + 1) ^ 2 ≤ η →
      |deriv (fun h => tiltedMass μ B h n) (criticalPoint μ B + v)| ≤ C * ((n : ℝ) + 1) ∧
        |deriv (deriv fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B + v)| ≤
          C * ((n : ℝ) + 1) ^ 4 ∧
        |deriv (fun h => tiltedLogMoment μ B h 2 n) (criticalPoint μ B + v)| ≤
          C * ((n : ℝ) + 1) ^ 3 ∧
        |deriv (fun h => tiltedLogMoment μ B h 3 n) (criticalPoint μ B + v)| ≤
          C * ((n : ℝ) + 1) ^ 4) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ lam T : ℝ, 0 ≤ lam → 0 < T → lam * T ^ 2 ≤ η₀ →
      ∃ C : ℝ, 0 < C ∧ ∀ Nseq : ℕ → ℝ, Tendsto Nseq atTop atTop →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ E : EntranceData T lam (lam * κ * Real.log B ^ 2 / ℓ₃) C,
            (∀ r : ℝ, 0 < r → r < T →
              Tendsto (fun j => timeIntegral
                (fun t => |scaledMass μ B lam (Nseq (φ j)) t - E.S t|) r T) atTop (𝓝 0)) ∧
            (∀ r : ℝ, 0 < r →
              TendstoUniformlyOn (fun j t => scaledDrift μ B lam (Nseq (φ j)) t) E.d atTop
                (Set.Icc r T)) ∧
            (∀ r : ℝ, 0 < r →
              TendstoUniformlyOn (fun j t => scaledSecond μ B lam (Nseq (φ j)) t) E.K atTop
                (Set.Icc r T)) ∧
            (∀ r : ℝ, 0 < r →
              TendstoUniformlyOn (fun j t => scaledThird μ B lam (Nseq (φ j)) t) E.P atTop
                (Set.Icc r T)) ∧
            (∀ r M : ℝ, 0 < r →
              TendstoUniformlyOn
                (fun j (p : ℝ × ℝ) => scaledCompensated μ B lam (Nseq (φ j)) p.1 p.2)
                (fun p => E.H p.1 p.2) atTop (Set.Icc r T ×ˢ Set.Icc 0 M)) ∧
            (∀ᵐ t, t ∈ Set.Ioc 0 T →
              WeakConvergence (fun j => scalingMeasure μ B lam (Nseq (φ j)) t) atTop (E.ν t)) := by
  obtain ⟨-, n₀, η, C, c, -, hη, hC, hc, hW, hWM⟩ := gen_window hpos hB hℓ₃ hκ hProd hWindow
  refine ⟨min (η / 4) (c / (32 * C)), lt_min (by positivity) (by positivity),
    fun lam T hlam hT hlamT => ?_⟩
  have hwT : lam * (2 * T) ^ 2 ≤ η := by
    have := hlamT.trans (min_le_left _ _)
    have e : lam * (2 * T) ^ 2 = 4 * (lam * T ^ 2) := by ring
    rw [e]; linarith
  have hsmall : lam * T ^ 2 ≤ c / (32 * C) := hlamT.trans (min_le_right _ _)
  refine ⟨entranceConst (Real.log B) C c, entranceConst_pos (log_pos_of_two_lt hB) hC hc,
    fun Nseq hNseq => ?_⟩
  obtain ⟨φ, hφ, S, d, K, P, H, L⟩ := exists_limData hpos hmean hB hC hc hW hlam hT hwT hNseq
  obtain ⟨E, h1, h2, h3, h4, h5, h6⟩ :=
    entrance_of_limData hpos hmean hB hC hc hW hWM hlam hT hwT hsmall L
  exact ⟨φ, hφ, E, h1, h2, h3, h4, h5, h6⟩

end DiamondPinning
