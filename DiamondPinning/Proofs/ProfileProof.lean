module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Model.Basic
public import DiamondPinning.Model.Profile
public import DiamondPinning.Model.Scaling
public import DiamondPinning.Proofs.EntireBoundsProof
public import DiamondPinning.Proofs.EntireOdeProof
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

namespace DiamondPinning

open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal

/-- A polynomial bound on the closed right half-plane extends to the whole plane
if the entire function has minimal exponential type on the left. -/
theorem profile_entire_global_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C : ℝ} (hC : 0 < C) (k : ℕ)
    (hr : ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ C * (1 + ‖z‖) ^ k)
    (hl : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ z : ℂ, z.re ≤ 0 →
      ‖f z‖ ≤ A * Real.exp (ε * ‖z‖)) :
    ∀ z : ℂ, ‖f z‖ ≤ (C * 2 ^ k) * (1 + ‖z‖) ^ k := by
  have hshift (z : ℂ) (hz : z.re ≤ 0) : 1 ≤ ‖1 - z‖ := by
    have h := Complex.re_le_norm (1 - z)
    simp only [Complex.sub_re, Complex.one_re] at h
    linarith
  have himag (z : ℂ) (hz : z.re = 0) : ‖z‖ ≤ ‖1 - z‖ := by
    suffices h : ‖z‖ ^ 2 ≤ ‖1 - z‖ ^ 2 by
      nlinarith [norm_nonneg z, norm_nonneg (1 - z)]
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, hz]
    nlinarith
  let g : ℂ → ℂ := fun z => f z / ((C * 2 ^ k : ℝ) : ℂ) / (1 - z) ^ k
  have hg (z : ℂ) (hz : z.re ≤ 0) : DifferentiableAt ℂ g z := by
    apply ((hf z).div_const _).div (by fun_prop)
    exact pow_ne_zero k (norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (hshift z hz)))
  have hnorm (z : ℂ) : ‖g z‖ = ‖f z‖ / (C * 2 ^ k) / ‖1 - z‖ ^ k := by
    simp [g, norm_pow, Complex.norm_real, abs_of_pos hC]
  have hd (z : ℂ) (hz : z.re ≤ 0) : 0 < ‖1 - z‖ ^ k :=
    pow_pos (zero_lt_one.trans_le (hshift z hz)) _
  have hb : ∀ z : ℂ, z.re = 0 → ‖g z‖ ≤ 1 := by
    intro z hz
    rw [hnorm, div_le_iff₀ (hd z hz.le), one_mul, div_le_iff₀ (by positivity : 0 < C * 2 ^ k)]
    calc
      ‖f z‖ ≤ C * (1 + ‖z‖) ^ k := hr z hz.ge
      _ ≤ C * (2 * ‖1 - z‖) ^ k := by
        gcongr
        linarith [hshift z hz.le, himag z hz]
      _ = ‖1 - z‖ ^ k * (C * 2 ^ k) := by rw [mul_pow]; ring
  have hgl : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ z : ℂ, z.re ≤ 0 →
      ‖g z‖ ≤ A * Real.exp (ε * ‖z‖) := by
    intro ε hε
    obtain ⟨A, ha⟩ := hl ε hε
    refine ⟨A / (C * 2 ^ k), fun z hz => ?_⟩
    rw [hnorm]
    calc
      _ ≤ ‖f z‖ / (C * 2 ^ k) := div_le_self (by positivity) (one_le_pow₀ (hshift z hz))
      _ ≤ (A * Real.exp (ε * ‖z‖)) / (C * 2 ^ k) := by gcongr; exact ha z hz
      _ = _ := by ring
  have hleft := leftHalfPlane_bounded_of_minimal_exponential_type_aux g
    (fun z hz => (hg z hz.le).differentiableWithinAt)
    (fun z hz => (hg z hz).continuousAt.continuousWithinAt) hb hgl
  intro z
  rcases le_total 0 z.re with hz | hz
  · apply (hr z hz).trans
    have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg (mul_nonneg hC.le (sub_nonneg.mpr hp))
      (pow_nonneg (show 0 ≤ 1 + ‖z‖ by positivity) k)]
  · have h := hleft z hz
    rw [hnorm, div_le_iff₀ (hd z hz), one_mul, div_le_iff₀ (by positivity : 0 < C * 2 ^ k)] at h
    calc
      ‖f z‖ ≤ ‖1 - z‖ ^ k * (C * 2 ^ k) := h
      _ = (C * 2 ^ k) * ‖1 - z‖ ^ k := mul_comm _ _
      _ ≤ _ := by gcongr; simpa using norm_sub_le (1 : ℂ) z

/-- Polynomial growth of an entire function kills all Taylor coefficients
above the degree of the growth bound. -/
theorem profile_iteratedDeriv_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C : ℝ} (hC : 0 ≤ C) {k n : ℕ} (hkn : k < n)
    (h : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖) ^ k) :
    iteratedDeriv n f 0 = 0 := by
  apply norm_le_zero_iff.mp
  apply le_of_forall_gt_imp_ge_of_dense
  intro ε hε
  let D : ℝ := n.factorial * (C * 2 ^ k)
  let R : ℝ := max 1 (D / ε)
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hRD : D ≤ ε * R := by
    simpa only [mul_comm ε R] using (div_le_iff₀ hε).mp
      (le_max_right 1 (D / ε))
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (c := 0) n hR hf.diffContOnCl
    (C := C * (2 * R) ^ k) (fun z hz => by
      have hzn : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hz
      apply (h z).trans
      rw [hzn]
      gcongr
      linarith)
  refine hcauchy.trans ((div_le_iff₀ (pow_pos hR n)).2 ?_)
  calc
    (n.factorial : ℝ) * (C * (2 * R) ^ k) = D * R ^ k := by
      simp only [D, mul_pow]
      ring
    _ ≤ (ε * R) * R ^ k := by gcongr
    _ = ε * R ^ (k + 1) := by rw [pow_succ]; ring
    _ ≤ ε * R ^ n := by
      gcongr
      omega

/-- The half-plane estimates imply a finite Taylor expansion of degree at most
the degree of the right half-plane bound. -/
theorem profile_entire_polynomial {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C : ℝ} (hC : 0 < C) (k : ℕ)
    (hr : ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ C * (1 + ‖z‖) ^ k)
    (hl : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ z : ℂ, z.re ≤ 0 →
      ‖f z‖ ≤ A * Real.exp (ε * ‖z‖)) :
    ∀ z : ℂ, f z = ∑ n ∈ Finset.range (k + 1),
      (iteratedDeriv n f 0 / (n.factorial : ℂ)) * z ^ n := by
  intro z
  have hseries := hf.hasFPowerSeriesOnBall 0 (R := 1) zero_lt_one
  have hsum := hseries.hasSum_iteratedFDeriv (show z ∈ Metric.eball (0 : ℂ) ∞ by simp)
  simp only [zero_add, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hg := profile_entire_global_bound hf hC k hr hl
  rw [← hsum.tsum_eq, tsum_eq_sum (s := Finset.range (k + 1))]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [div_eq_mul_inv]
    ring
  · intro n hn
    have hkn : k < n := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hn
    rw [profile_iteratedDeriv_eq_zero hf (by positivity) hkn hg, mul_zero, mul_zero]

/-- On times where the exponential rate is positive the profile has finite
mass, and its Laplace transform is the stated rational function. -/
theorem profileMeasure_laplace {v t : ℝ} (hb : 0 < profileB v t) :
    IsFiniteMeasure (profileMeasure v t) ∧
      ∀ s : ℝ, 0 ≤ s →
        (∫ x, Real.exp (-(s * x)) ∂profileMeasure v t) = profileTransform v t s := by
  have ha : 0 ≤ profileA v t := by unfold profileA; positivity
  have hd : ∀ x, 0 ≤ profileDensity v t x := fun x => mul_nonneg ha (Real.exp_pos _).le
  have hmeas : Measurable (profileDensity v t) := by unfold profileDensity; fun_prop
  refine ⟨?_, ?_⟩
  · apply isFiniteMeasure_withDensity_ofReal
    have hi := integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) 0
    have hi' := (integrableOn_Ici_iff_integrableOn_Ioi).2 hi
    change HasFiniteIntegral (fun x : ℝ => profileA v t * Real.exp (-(profileB v t * x)))
      (volume.restrict (Ici 0))
    simpa only [neg_mul] using (hi'.const_mul (profileA v t)).hasFiniteIntegral
  · intro s hs
    have hrate : 0 < s + profileB v t := add_pos_of_nonneg_of_pos hs hb
    unfold profileMeasure profileTransform
    rw [integral_withDensity_eq_integral_toReal_smul hmeas.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal (hd _), smul_eq_mul, profileDensity, mul_assoc,
      ← Real.exp_add]
    simp_rw [show ∀ x : ℝ, -(profileB v t * x) + -(s * x) = -(s + profileB v t) * x
      from fun x => by ring]
    rw [integral_const_mul, ← restrict_Ioi_eq_restrict_Ici,
      integral_exp_mul_Ioi (neg_neg_of_pos hrate)]
    rw [mul_zero, Real.exp_zero, neg_div_neg_eq, mul_one_div]

/-- The profile rate is positive on an initial interval chosen solely from
the parameter and the time horizon. -/
theorem profileB_pos_initial (v : ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ Tstar : ℝ, 0 < Tstar ∧ Tstar ≤ T ∧
      ∀ t ∈ Ioc 0 Tstar, IsPrePoleTime v t ∧ 0 < profileB v t := by
  by_cases hv : 0 < v
  · have hrs : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
    refine ⟨min T (Real.pi / (4 * Real.sqrt v)), lt_min hT (by positivity),
      min_le_left _ _, ?_⟩
    intro t ht
    have hb : Real.sqrt v * t < Real.pi / 2 := by
      have hj := (le_div_iff₀ (show 0 < 4 * Real.sqrt v by positivity)).mp
        (ht.2.trans (min_le_right _ _))
      nlinarith [Real.pi_pos]
    have harg : 0 < Real.sqrt v * t := mul_pos hrs ht.1
    have hsin := Real.sin_pos_of_pos_of_lt_pi harg (by linarith)
    have hcos := Real.cos_pos_of_mem_Ioo (show Real.sqrt v * t ∈
        Ioo (-(Real.pi / 2)) (Real.pi / 2) from ⟨by linarith [Real.pi_pos], hb⟩)
    have hderiv : HasDerivAt (profileU v) (Real.cos (Real.sqrt v * t)) t := by
      have hU : profileU v = fun x => Real.sin (Real.sqrt v * x) / Real.sqrt v := by
        funext x
        exact ite_eq_left hv
      rw [hU]
      have hlin : HasDerivAt (fun x : ℝ => Real.sqrt v * x) (Real.sqrt v) t := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (Real.sqrt v)
      simpa only [mul_div_cancel_right₀ _ hrs.ne'] using hlin.sin.div_const (Real.sqrt v)
    refine ⟨⟨ht.1, fun _ => (lt_div_iff₀ hrs).2 (by nlinarith [Real.pi_pos])⟩, ?_⟩
    simp only [profileB, hderiv.deriv, profileU, ite_eq_left hv]
    positivity
  · refine ⟨T, hT, le_rfl, fun t ht => ⟨⟨ht.1, fun hv' => (hv hv').elim⟩, ?_⟩⟩
    have hU : profileU v = id := by
      funext x
      exact ite_eq_right hv
    have hderiv : deriv (profileU v) t = 1 := by rw [hU]; exact (hasDerivAt_id t).deriv
    rw [profileB, hderiv, profileU, ite_eq_right hv, mul_one]
    exact div_pos (by norm_num) ht.1

/-- Equal compensated transforms on the imaginary axis, with equal total
mass, identify finite measures through their characteristic functions. -/
theorem profile_measure_eq_of_imaginary_transform {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : measureMoment μ 0 = measureMoment ν 0)
    (h : ∀ y : ℝ, complexCompensatedLaplace μ ((y : ℂ) * Complex.I) =
      complexCompensatedLaplace ν ((y : ℂ) * Complex.I)) :
    μ = ν := by
  have hchar (ρ : Measure ℝ) [IsFiniteMeasure ρ] (y : ℝ) :
      complexCompensatedLaplace ρ ((- (y : ℂ)) * Complex.I) =
        charFun ρ y - (measureMoment ρ 0 : ℂ) := by
    have hi : Integrable (fun x : ℝ => Complex.exp ((y : ℂ) * x * Complex.I)) ρ := by
      apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
      exact Eventually.of_forall fun x => by simp [Complex.norm_exp]
    unfold complexCompensatedLaplace
    have hexp (x : ℝ) : -(- (y : ℂ) * Complex.I * (x : ℂ)) =
        (y : ℂ) * (x : ℂ) * Complex.I := by ring
    simp_rw [hexp]
    rw [integral_sub hi (integrable_const _), charFun_apply_real]
    simp [measureMoment, measureReal_def]
  apply Measure.ext_of_charFun
  funext y
  have hy := h (-y)
  rw [Complex.ofReal_neg, hchar μ, hchar ν, hm] at hy
  exact sub_left_inj.mp hy

/-- Regularized second moment in the entrance equation. -/
noncomputable def entranceQ {T lam α C : ℝ} (E : EntranceData T lam α C) (t : ℝ) : ℝ :=
  E.K t - E.d t * timeIntegral E.d 0 t

/-- Regularized third moment in the entrance equation. -/
noncomputable def entranceR {T lam α C : ℝ} (E : EntranceData T lam α C) (t : ℝ) : ℝ :=
  E.P t - 3 * E.d t * timeIntegral E.K 0 t

/-- The regularization errors vanish faster than either entrance moment. -/
theorem entrance_regularization_error {T lam α C : ℝ} (E : EntranceData T lam α C)
    (hlam : 0 ≤ lam) (hC : 0 < C) {t : ℝ} (ht : t ∈ Ioc 0 T) :
    |E.K t - entranceQ E t| ≤ (C * lam) ^ 2 * t ^ 5 ∧
      |E.P t - entranceR E t| ≤ 3 * C ^ 2 * lam * t ^ 4 := by
  have hnorm_d : |timeIntegral E.d 0 t| ≤ C * lam * t ^ 2 * t := by
    rw [← Real.norm_eq_abs, timeIntegral]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := E.d) (a := 0) (b := t) (C := C * lam * t ^ 2) (by
        rw [uIoc_of_le ht.1.le]
        intro x hx
        rw [Real.norm_eq_abs]
        exact (E.bounds x ⟨hx.1, hx.2.trans ht.2⟩).1.trans
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hx.1.le hx.2 2) (mul_nonneg hC.le hlam)))
    simpa [abs_of_nonneg ht.1.le] using h
  have hnorm_K : |timeIntegral E.K 0 t| ≤ C * t * t := by
    rw [← Real.norm_eq_abs, timeIntegral]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := E.K) (a := 0) (b := t) (C := C * t) (by
        rw [uIoc_of_le ht.1.le]
        intro x hx
        obtain ⟨_, hlo, hhi, _⟩ := E.bounds x ⟨hx.1, hx.2.trans ht.2⟩
        have hx0 : 0 < x := hx.1
        rw [Real.norm_eq_abs, abs_of_nonneg ((by positivity : 0 ≤ C⁻¹ * x).trans hlo)]
        exact hhi.trans (mul_le_mul_of_nonneg_left hx.2 hC.le))
    simpa [abs_of_nonneg ht.1.le] using h
  constructor
  · rw [entranceQ, sub_sub_cancel, abs_mul]
    calc
      _ ≤ (C * lam * t ^ 2) * (C * lam * t ^ 2 * t) :=
        mul_le_mul (E.bounds t ht).1 hnorm_d (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [entranceR, sub_sub_cancel, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      _ ≤ (3 * (C * lam * t ^ 2)) * (C * t * t) := by
        gcongr
        exact (E.bounds t ht).1
      _ = _ := by ring

/-- One initial time interval works for all entrance data with the same bounds.
On it the regularized moments are positive and comparable to `t` and `t²`. -/
theorem entrance_regularization_bounds {T lam C : ℝ}
    (hT : 0 < T) (hlam : 0 ≤ lam) (hC : 0 < C) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ T ∧
      ∀ {α : ℝ} (E : EntranceData T lam α C) {t : ℝ}, t ∈ Ioc 0 δ →
        C⁻¹ / 2 * t ≤ entranceQ E t ∧ entranceQ E t ≤ (C + C⁻¹ / 2) * t ∧
        C⁻¹ / 2 * t ^ 2 ≤ entranceR E t ∧ entranceR E t ≤ (C + C⁻¹ / 2) * t ^ 2 := by
  let A : ℝ := (C * lam) ^ 2 + 3 * C ^ 2 * lam
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let δ : ℝ := min T (min 1 (C⁻¹ / 2 / (A + 1)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδT : δ ≤ T := min_le_left _ _
  refine ⟨δ, hδ, hδT, ?_⟩
  intro α E t ht
  have htT : t ∈ Ioc 0 T := ⟨ht.1, ht.2.trans hδT⟩
  have ht0 := ht.1
  have ht1 : t ≤ 1 := ht.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htA : A * t ≤ C⁻¹ / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < A + 1)).mp
      (ht.2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [h, ht0]
  obtain ⟨hdQ, hdR⟩ := entrance_regularization_error E hlam hC htT
  have hQ : |E.K t - entranceQ E t| ≤ (C⁻¹ / 2) * t := by
    have ht4 : t ^ 4 ≤ t := by simpa using pow_le_pow_of_le_one ht0.le ht1 (show 1 ≤ 4 by omega)
    calc
      _ ≤ (C * lam) ^ 2 * t ^ 5 := hdQ
      _ ≤ (A * t) * t := by
        rw [show t ^ 5 = t ^ 4 * t by ring, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (le_add_of_nonneg_right (by positivity)) ht4 (by positivity) hA) ht0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right htA ht0.le
  have hR : |E.P t - entranceR E t| ≤ (C⁻¹ / 2) * t ^ 2 := by
    have ht2 : t ^ 2 ≤ t := by nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht1)]
    calc
      _ ≤ 3 * C ^ 2 * lam * t ^ 4 := hdR
      _ ≤ (A * t) * t ^ 2 := by
        rw [show t ^ 4 = t ^ 2 * t ^ 2 by ring, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (le_add_of_nonneg_left (sq_nonneg (C * lam))) ht2 (by positivity) hA) (sq_nonneg t)
      _ ≤ _ := mul_le_mul_of_nonneg_right htA (sq_nonneg t)
  obtain ⟨_, hklo, hkhi, hplo, hphi⟩ := E.bounds t htT
  obtain ⟨hqlo, hqhi⟩ := abs_le.mp hQ
  obtain ⟨hrlo, hrhi⟩ := abs_le.mp hR
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem entrance_ae_hasDerivAt_of_integral_eq {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a ≤ b) (hg : IntervalIntegrable g volume a b)
    (hfg : ∀ t ∈ Icc a b, f t - f a = timeIntegral g a t) :
    ∀ᵐ t : ℝ, t ∈ Ioo a b → HasDerivAt f (g t) t := by
  filter_upwards [hg.ae_hasDerivAt_integral] with t ht ht'
  rw [uIcc_of_le hab] at ht
  apply ((ht (Ioo_subset_Icc_self ht') a ⟨le_rfl, hab⟩).const_add
    (f a)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht'.1 ht'.2] with x hx
  have h := hfg x (Ioo_subset_Icc_self hx)
  exact eq_add_of_sub_eq' h

private theorem entrance_integrableOn_S {T lam α C : ℝ} (E : EntranceData T lam α C)
    (hC : 0 < C) {a b : ℝ} (ha : 0 < a) (hb : b ≤ T) :
    IntegrableOn E.S (Icc a b) := by
  let μ := (volume : Measure ℝ).restrict (Icc a b)
  have hmem : ∀ᵐ t ∂μ, t ∈ Icc a b := ae_restrict_mem measurableSet_Icc
  have hrep := ae_restrict_of_ae (μ := volume) (s := Icc a b) E.representation
  have hbound := ae_restrict_of_ae (μ := volume) (s := Icc a b) E.bounds_S
  refine (integrable_const (C * a⁻¹)).mono' ?_ ?_
  · have hmeas : Measurable (fun t => (E.ν t Set.univ).toReal) :=
      ((Measure.measurable_coe MeasurableSet.univ).comp E.measurable_ν).ennreal_toReal
    apply hmeas.aestronglyMeasurable.congr
    filter_upwards [hmem, hrep] with t ht hr
    have h := (hr ⟨ha.trans_le ht.1, ht.2.trans hb⟩).2.2.2.2.1
    simpa [measureMoment, measureReal_def] using h
  · filter_upwards [hmem, hbound] with t ht h
    have ht0 := ha.trans_le ht.1
    obtain ⟨hl, hu⟩ := h ⟨ht0, ht.2.trans hb⟩
    rw [Real.norm_eq_abs, abs_of_nonneg ((by positivity : 0 ≤ C⁻¹ * t⁻¹).trans hl)]
    exact hu.trans (mul_le_mul_of_nonneg_left (inv_anti₀ ha ht.1) hC.le)

private theorem entrance_moment_integrable {T lam α C : ℝ} (E : EntranceData T lam α C)
    (hlam : 0 ≤ lam) (hC : 0 < C) (hT : 0 < T) :
    IntervalIntegrable E.d volume 0 T ∧ IntervalIntegrable E.K volume 0 T := by
  have h_loc (f : ℝ → ℝ)
      (hc : ∀ a > 0, ContinuousOn f (Icc a T)) (M : ℝ)
      (hf : ∀ t ∈ Ioo 0 T, ‖f t‖ ≤ M) : IntervalIntegrable f volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le]
    refine (integrable_const M).mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioo hf)
    have hcont : ContinuousOn f (Ioo 0 T) := by
      intro t ht
      have ha := half_pos ht.1
      have hn : Icc (t / 2) T ∈ 𝓝 t :=
        mem_of_superset (Ioo_mem_nhds (half_lt_self ht.1) ht.2) Ioo_subset_Icc_self
      exact ((hc _ ha) t ⟨(half_lt_self ht.1).le, ht.2.le⟩).continuousAt hn
        |>.continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  refine ⟨h_loc E.d (fun a ha => ?_) (C * lam * T ^ 2) ?_,
    h_loc E.K (fun a ha => ?_) (C * T) ?_⟩
  · obtain ⟨_, hd, _⟩ := E.lipschitz a ha
    exact hd.continuousOn
  · intro t ht
    rw [Real.norm_eq_abs]
    exact (E.bounds t ⟨ht.1, ht.2.le⟩).1.trans <|
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1.le ht.2.le 2) (mul_nonneg hC.le hlam)
  · obtain ⟨_, _, hK, _⟩ := E.lipschitz a ha
    exact hK.continuousOn
  · intro t ht
    obtain ⟨_, hl, hu, _⟩ := E.bounds t ⟨ht.1, ht.2.le⟩
    have ht0 := ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg ((by positivity : 0 ≤ C⁻¹ * t).trans hl)]
    exact hu.trans (mul_le_mul_of_nonneg_left ht.2.le hC.le)

/-- The regularized moments obey the entrance ODEs almost everywhere on each
positive-time interval, by the local Lebesgue differentiation theorem. -/
theorem entrance_regularized_ode_ae {T lam α C : ℝ} (E : EntranceData T lam α C)
    (hlam : 0 ≤ lam) (hC : 0 < C) {a : ℝ} (ha : 0 < a) (haT : a ≤ T) :
    ∀ᵐ t : ℝ, t ∈ Ioo a T →
      HasDerivAt (entranceQ E) (E.S t * entranceQ E t - 1) t ∧
        HasDerivAt (entranceR E) (E.S t * entranceR E t) t ∧
        HasDerivAt E.d (E.S t * E.d t) t := by
  have hSi := entrance_integrableOn_S E hC ha le_rfl
  obtain ⟨_, hd, hK, hP⟩ := E.lipschitz a ha
  have hi (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a T)) :
      IntervalIntegrable (fun t => E.S t * f t) volume a T := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le haT]
    exact hSi.mul_bdd (hf.aestronglyMeasurable measurableSet_Icc)
      (ae_restrict_of_forall_mem measurableSet_Icc hM)
  have hdk {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a T)) :
      IntervalIntegrable f volume a T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le haT]
    exact hf.integrableOn_compact isCompact_Icc
  obtain ⟨hd0, hK0⟩ := entrance_moment_integrable E hlam hC (ha.trans_le haT)
  have hd' := entrance_ae_hasDerivAt_of_integral_eq haT (hi E.d hd.continuousOn)
    (fun t ht => E.ode_d a t ha ht.1 ht.2)
  have hK' := entrance_ae_hasDerivAt_of_integral_eq haT
    (((hi E.K hK.continuousOn).add (hdk (hd.continuousOn.pow 2))).sub intervalIntegrable_const)
    (fun t ht => E.ode_K a t ha ht.1 ht.2)
  have hP' := entrance_ae_hasDerivAt_of_integral_eq haT
    ((hi E.P hP.continuousOn).add
      (hdk ((continuousOn_const.mul hd.continuousOn).mul hK.continuousOn)))
    (fun t ht => E.ode_P a t ha ht.1 ht.2)
  have hd0' := hd0.ae_hasDerivAt_integral
  have hK0' := hK0.ae_hasDerivAt_integral
  rw [uIcc_of_le (ha.trans_le haT).le] at hd0' hK0'
  filter_upwards [hd', hK', hP', hd0', hK0'] with t hdt hKt hPt hdint hKint ht
  have htT : t ∈ Icc 0 T := ⟨(ha.trans ht.1).le, ht.2.le⟩
  have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ha.le.trans haT⟩
  refine ⟨?_, ?_, hdt ht⟩
  · convert (hKt ht).sub ((hdt ht).mul (hdint htT 0 hz)) using 1
    · rfl
    · simp only [entranceQ, timeIntegral, Pi.pow_apply]
      ring
  · convert (hPt ht).sub (((hdt ht).const_mul 3).mul (hKint htT 0 hz)) using 1
    · funext x
      simp only [entranceR, timeIntegral, Pi.sub_apply, Pi.mul_apply]
    · simp only [entranceR, timeIntegral, Pi.mul_apply]
      ring

/-- The matching limit is invariant under regularization of the third moment. -/
theorem entrance_regularized_matching {T lam α C : ℝ} (E : EntranceData T lam α C)
    (hlam : 0 ≤ lam) (hC : 0 < C) (hT : 0 < T) :
    Tendsto (fun t => E.d t / entranceR E t) (𝓝[>] 0) (𝓝 α) := by
  obtain ⟨δ, hδ, hδT, hb⟩ := entrance_regularization_bounds hT hlam hC
  have hlim : Tendsto (fun t => (E.P t - entranceR E t) / entranceR E t)
      (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hcont : Continuous (fun t : ℝ => (3 * C ^ 2 * lam / (C⁻¹ / 2)) * t ^ 2) :=
      continuous_const.mul (continuous_id.pow 2)
    have hsmall : Tendsto (fun t : ℝ => (3 * C ^ 2 * lam / (C⁻¹ / 2)) * t ^ 2)
        (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using hcont.tendsto 0)
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsmall
    filter_upwards [Ioc_mem_nhdsGT hδ] with t ht
    have ht0 := ht.1
    have hr := (hb E ht).2.2.1
    have hr0 : 0 < entranceR E t := (by positivity : 0 < C⁻¹ / 2 * t ^ 2).trans_le hr
    have herr := (entrance_regularization_error E hlam hC ⟨ht0, ht.2.trans hδT⟩).2
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hr0]
    calc
      _ ≤ (3 * C ^ 2 * lam * t ^ 4) / entranceR E t :=
        div_le_div_of_nonneg_right herr hr0.le
      _ ≤ (3 * C ^ 2 * lam * t ^ 4) / (C⁻¹ / 2 * t ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hr
      _ = _ := by field_simp
  have hratio : Tendsto (fun t => 1 + (E.P t - entranceR E t) / entranceR E t)
      (𝓝[>] 0) (𝓝 1) := by
    simpa only [add_zero] using hlim.const_add (1 : ℝ)
  have hh := E.matching.mul hratio
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [Ioc_mem_nhdsGT hδ] with t ht
  have ht0 := ht.1
  have hr : 0 < entranceR E t := (by positivity : 0 < C⁻¹ / 2 * t ^ 2).trans_le
    (hb E ht).2.2.1
  have hp : 0 < E.P t := (by positivity : 0 < C⁻¹ * t ^ 2).trans_le
    (E.bounds t ⟨ht0, ht.2.trans hδT⟩).2.2.2.1
  field_simp [hr.ne', hp.ne']
  ring

/-- On the common initial interval, the regularized third moment carries
the drift exactly, with proportionality constant given by matching. -/
theorem entrance_regularized_ratio {T lam C : ℝ}
    (hT : 0 < T) (hlam : 0 ≤ lam) (hC : 0 < C) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ T ∧
      ∀ {α : ℝ} (E : EntranceData T lam α C) {t : ℝ}, t ∈ Ioc 0 δ →
        E.d t / entranceR E t = α := by
  obtain ⟨δ, hδ, hδT, hbounds⟩ := entrance_regularization_bounds hT hlam hC
  refine ⟨δ, hδ, hδT, ?_⟩
  intro α E t ht
  have hconstant (a : ℝ) (ha : 0 < a) (hat : a ≤ t) :
      E.d a / entranceR E a = E.d t / entranceR E t := by
    have haT : a ≤ T := hat.trans (ht.2.trans hδT)
    obtain ⟨_, hdl, _, hPl⟩ := E.lipschitz a ha
    have huv : uIcc a t ⊆ Icc a T := by
      rw [uIcc_of_le hat]
      exact Icc_subset_Icc_right (ht.2.trans hδT)
    have hdac := (hdl.mono huv).absolutelyContinuousOnInterval
    have hPac := (hPl.mono huv).absolutelyContinuousOnInterval
    have hprim := (entrance_moment_integrable E hlam hC hT).2
      |>.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (left_mem_uIcc)
    have hprim' := hprim.mono (show uIcc a t ⊆ uIcc 0 T by
      rw [uIcc_of_le hat, uIcc_of_le hT.le]
      exact Icc_subset_Icc (ha.le) (ht.2.trans hδT))
    have hRac : AbsolutelyContinuousOnInterval (entranceR E) a t :=
      hPac.sub ((hdac.const_mul 3).mul hprim')
    let m := C⁻¹ / 2 * a ^ 2
    let M := (C + C⁻¹ / 2) * δ ^ 2
    have hm : 0 < m := by dsimp [m]; positivity
    have hmaps : MapsTo (entranceR E) (uIcc a t) (Icc m M) := by
      rw [uIcc_of_le hat]
      intro x hx
      have hx0 := ha.trans_le hx.1
      have h := (hbounds E ⟨hx0, hx.2.trans ht.2⟩).2.2
      exact ⟨(mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hx.1 _) (by positivity)).trans h.1,
        h.2.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hx0.le (hx.2.trans ht.2) _) (by positivity))⟩
    have hInv : ContDiffOn ℝ 1 (Inv.inv : ℝ → ℝ) (Icc m M) :=
      contDiffOn_id.inv fun x hx => ne_of_gt (hm.trans_le hx.1)
    obtain ⟨L, hLip⟩ := hInv.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
    have hratio : AbsolutelyContinuousOnInterval (fun x => E.d x / entranceR E x) a t := by
      simpa [div_eq_mul_inv, Function.comp_def] using hdac.fun_mul
        (hLip.comp_absolutelyContinuousOnInterval hmaps hRac)
    have hder : ∀ᵐ x : ℝ, x ∈ uIcc a t → HasDerivAt (fun x => E.d x / entranceR E x) 0 x := by
      filter_upwards [entrance_regularized_ode_ae E hlam hC ha haT, volume.ae_ne a, volume.ae_ne T]
        with x hx hxa hxT hxt
      have hx' : x ∈ Icc a T := huv hxt
      have h := hx ⟨lt_of_le_of_ne hx'.1 hxa.symm, lt_of_le_of_ne hx'.2 hxT⟩
      have hz : entranceR E x ≠ 0 := ne_of_gt (hm.trans_le (hmaps hxt).1)
      convert h.2.2.div h.2.1 hz using 1
      ring_nf
    obtain ⟨k, hk⟩ := hratio.const_of_ae_hasDerivAt_zero hder
    exact (hk a left_mem_uIcc).trans (hk t right_mem_uIcc).symm
  apply tendsto_nhds_unique _ (entrance_regularized_matching E hlam hC hT)
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioc_mem_nhdsGT ht.1] with a ha
  exact (hconstant a ha.1 ha.2).symm

private theorem profile_first_moment_integrable {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (h3 : Integrable (fun x : ℝ => x ^ 3) ρ) : Integrable (fun x : ℝ => x) ρ := by
  refine ((integrable_const (1 : ℝ)).add h3.norm).mono' (by fun_prop) ?_
  exact Eventually.of_forall fun x => by
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_pow]
    rcases le_total |x| 1 with h | h
    · nlinarith only [h, pow_nonneg (abs_nonneg x) 3]
    · have h' : |x| ≤ |x| ^ 3 := by
        simpa using pow_le_pow_right₀ h (show 1 ≤ 3 by omega)
      linarith

private theorem profile_realLaplace_bound {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ : ρ (Iio 0) = 0) (h3 : Integrable (fun x : ℝ => x ^ 3) ρ)
    {s : ℝ} (hs : 0 ≤ s) :
    -compensatedLaplace ρ s =
        (∫⁻ x, ENNReal.ofReal (1 - Real.exp (-(s * x))) ∂ρ).toReal ∧
      0 ≤ -compensatedLaplace ρ s ∧
      -compensatedLaplace ρ s ≤ s * measureMoment ρ 1 := by
  have hx : ∀ᵐ x ∂ρ, 0 ≤ x := by simpa [ae_iff, not_le, Iio] using hρ
  have hi := profile_first_moment_integrable h3
  have hfn : ∀ᵐ x ∂ρ, 0 ≤ 1 - Real.exp (-(s * x)) := by
    filter_upwards [hx] with x hx
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs hx)))
  have hfl : ∀ᵐ x ∂ρ, 1 - Real.exp (-(s * x)) ≤ s * x :=
    Eventually.of_forall fun x => by linarith [Real.add_one_le_exp (-(s * x))]
  have hfi : Integrable (fun x : ℝ => 1 - Real.exp (-(s * x))) ρ := by
    refine (hi.const_mul s).mono' (by fun_prop) ?_
    filter_upwards [hfn, hfl] with x hn hl
    rwa [Real.norm_eq_abs, abs_of_nonneg hn]
  have heq : -compensatedLaplace ρ s = ∫ x, (1 - Real.exp (-(s * x))) ∂ρ := by
    unfold compensatedLaplace
    rw [← integral_neg]
    simp only [neg_sub]
  rw [heq]
  refine ⟨integral_eq_lintegral_of_nonneg_ae hfn hfi.aestronglyMeasurable,
    integral_nonneg_of_ae hfn, ?_⟩
  simp only [measureMoment, pow_one, ← integral_const_mul]
  exact integral_mono_ae hfi (hi.const_mul s) hfl

private theorem entrance_riccati_integrable {T lam α C : ℝ} (E : EntranceData T lam α C)
    (hlam : 0 ≤ lam) (hC : 0 < C) {a s : ℝ} (ha : 0 < a) (haT : a ≤ T) (hs : 0 ≤ s) :
    IntervalIntegrable (fun t => E.H t s) volume 0 T ∧
      IntervalIntegrable (fun t => E.S t * E.H t s + E.H t s ^ 2 / 2 - s ^ 2 / 2)
        volume a T := by
  let F : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (1 - Real.exp (-(s * x)))
  let M : ℝ := s + s * (1 + C * lam * T ^ 2)
  have hF : Measurable F := by unfold F; fun_prop
  have hml : Measurable (fun t => s - (∫⁻ x, F x ∂E.ν t).toReal) :=
    measurable_const.sub (((Measure.measurable_lintegral hF).comp E.measurable_ν).ennreal_toReal)
  have hrepr : ∀ᵐ t : ℝ, t ∈ Ioc 0 T →
      E.H t s = s - (∫⁻ x, F x ∂E.ν t).toReal ∧ ‖E.H t s‖ ≤ M := by
    filter_upwards [E.representation] with t ht hmem
    obtain ⟨hfin, hsupport, h3, hH, _, hm1, _⟩ := ht hmem
    let _ : IsFiniteMeasure (E.ν t) := hfin
    obtain ⟨heq, hlo, hhi⟩ := profile_realLaplace_bound hsupport h3 hs
    rw [hm1] at hhi
    rw [hH s hs]
    constructor
    · linarith only [heq]
    · have hdt : E.d t ≤ C * lam * T ^ 2 :=
        (le_abs_self _).trans (((E.bounds t hmem).1).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hmem.1.le hmem.2 2) (mul_nonneg hC.le hlam)))
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      have hmul : s * E.d t ≤ s * (C * lam * T ^ 2) := mul_le_mul_of_nonneg_left hdt hs
      dsimp [M]
      constructor <;> nlinarith only [hhi, hlo, hmul, hs, mul_nonneg (mul_nonneg hC.le hlam) (sq_nonneg T)]
  have hH_on {D : Set ℝ} (hD : MeasurableSet D) (hsub : D ⊆ Ioc 0 T) :
      AEStronglyMeasurable (fun t => E.H t s) (volume.restrict D) ∧
      ∀ᵐ t ∂volume.restrict D, ‖E.H t s‖ ≤ M := by
    have h := (ae_restrict_of_ae (s := D) hrepr).and (ae_restrict_mem hD)
    have hh := h.mono fun t ht => ht.1 (hsub ht.2)
    exact ⟨hml.aestronglyMeasurable.congr (hh.mono fun t ht => ht.1.symm),
      hh.mono fun t ht => ht.2⟩
  have hHi0 := hH_on measurableSet_Ioc (Subset.rfl : Ioc 0 T ⊆ Ioc 0 T)
  have hT := ha.trans_le haT
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).2
    ((integrable_const M).mono' hHi0.1 hHi0.2), ?_⟩
  have hHi := hH_on measurableSet_Icc
    (show Icc a T ⊆ Ioc 0 T from fun t ht => ⟨ha.trans_le ht.1, ht.2⟩)
  have hHintegrable : IntegrableOn (fun t => E.H t s) (Icc a T) :=
    (integrable_const M).mono' hHi.1 hHi.2
  have h₁ := (entrance_integrableOn_S E hC ha le_rfl).mul_bdd hHi.1 hHi.2
  have h₂ := hHintegrable.mul_bdd hHi.1 hHi.2
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le haT]
  rw [show (fun t => E.S t * E.H t s + E.H t s ^ 2 / 2 - s ^ 2 / 2) =
      (fun t => E.S t * E.H t s) + (fun t => E.H t s * E.H t s / 2) -
        (fun _ => s ^ 2 / 2) by funext t; simp [pow_two]]
  exact (h₁.add (h₂.div_const 2)).sub (integrable_const (s ^ 2 / 2))

/-- For a real Laplace parameter the entrance Riccati equation holds almost
everywhere on every positive-time interval. The transform is also integrable
from time zero. -/
theorem entrance_riccati_ae {T lam α C : ℝ} (E : EntranceData T lam α C)
    (hlam : 0 ≤ lam) (hC : 0 < C) {a s : ℝ} (ha : 0 < a) (haT : a ≤ T) (hs : 0 ≤ s) :
    IntervalIntegrable (fun t => E.H t s) volume 0 T ∧
      ∀ᵐ t : ℝ, t ∈ Ioo a T → HasDerivAt (fun u => E.H u s)
        (E.S t * E.H t s + E.H t s ^ 2 / 2 - s ^ 2 / 2) t := by
  obtain ⟨hH, hg⟩ := entrance_riccati_integrable E hlam hC ha haT hs
  exact ⟨hH, entrance_ae_hasDerivAt_of_integral_eq haT hg
    (fun t ht => E.riccati s hs a t ha ht.1 ht.2)⟩

/-- Weight of the manuscript's regularized first-order system. -/
noncomputable def entranceW {T lam α C : ℝ} (E : EntranceData T lam α C) (t : ℝ) : ℝ :=
  entranceQ E t ^ 2 / entranceR E t

/-- The integrating factor for the entrance Riccati equation. -/
noncomputable def entranceY {T lam α C : ℝ} (E : EntranceData T lam α C) (t s : ℝ) : ℝ :=
  Real.exp (-timeIntegral (fun u => E.H u s) 0 t / 2)

/-- Value coordinate of the regularized system, scaled by `s²`. -/
noncomputable def entranceCanonicalValue {T lam α C : ℝ}
    (E : EntranceData T lam α C) (t s : ℝ) : ℝ :=
  2 * E.H t s * entranceY E t s / entranceQ E t

/-- Flux coordinate of the regularized system, scaled by `-2s`. -/
noncomputable def entranceCanonicalFlux {T lam α C : ℝ}
    (E : EntranceData T lam α C) (t s : ℝ) : ℝ :=
  2 * s * entranceY E t s * (entranceQ E t - 2 * E.H t s / s ^ 2) / entranceR E t

/-- The entrance regularization gives the two differential equations of the
fundamental-matrix system for positive real Laplace parameters. -/
theorem entrance_canonical_ode_ae {T lam C : ℝ} (hT : 0 < T) (hlam : 0 ≤ lam) (hC : 0 < C) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ T ∧
      ∀ {α : ℝ} (E : EntranceData T lam α C) {a s : ℝ}, 0 < a → a ≤ δ → 0 < s →
        ∀ᵐ t : ℝ, t ∈ Ioo a δ →
          HasDerivAt (fun t => entranceCanonicalValue E t s)
            (-(s / 2) * (entranceW E t)⁻¹ * entranceCanonicalFlux E t s) t ∧
          HasDerivAt (fun t => entranceCanonicalFlux E t s)
            (-(s / 2) * entranceW E t * entranceCanonicalValue E t s) t := by
  obtain ⟨δ, hδ, hδT, hb⟩ := entrance_regularization_bounds hT hlam hC
  refine ⟨δ, hδ, hδT, ?_⟩
  intro α E a s ha haδ hs
  have haT := haδ.trans hδT
  obtain ⟨hint, hder⟩ := entrance_riccati_ae E hlam hC ha haT hs.le
  have hp := hint.ae_hasDerivAt_integral
  rw [uIcc_of_le hT.le] at hp
  filter_upwards [hder, entrance_regularized_ode_ae E hlam hC ha haT, hp]
    with t hdH hdMom hdInt ht
  have htT : t ∈ Ioo a T := ⟨ht.1, ht.2.trans_le hδT⟩
  have htδ : t ∈ Ioc 0 δ := ⟨(ha.trans ht.1), ht.2.le⟩
  have ht0 := htδ.1
  have hb' := hb E htδ
  have hQ : 0 < entranceQ E t := (by positivity : 0 < C⁻¹ / 2 * t).trans_le hb'.1
  have hR : 0 < entranceR E t := (by positivity : 0 < C⁻¹ / 2 * t ^ 2).trans_le hb'.2.2.1
  have hH := hdH htT
  have hQ' := (hdMom htT).1
  have hR' := (hdMom htT).2.1
  have hprimitive : HasDerivAt (fun t => timeIntegral (fun u => E.H u s) 0 t)
      (E.H t s) t := hdInt ⟨ht0.le, htT.2.le⟩ 0 ⟨le_rfl, hT.le⟩
  have hy : HasDerivAt (fun t => entranceY E t s)
      (entranceY E t s * (-(E.H t s) / 2)) t :=
    (hprimitive.neg.div_const 2).exp
  have hconstant := hasDerivAt_const t (2 * s)
  constructor
  · convert (((hH.const_mul 2).mul hy).div hQ' hQ.ne') using 1
    · funext u
      rfl
    · simp only [entranceW, entranceCanonicalFlux, Pi.mul_apply]
      field_simp [hs.ne', hQ.ne', hR.ne']
      ring
  · convert (((hconstant.mul hy).mul
        (hQ'.sub ((hH.const_mul 2).div_const (s ^ 2)))).div hR' hR.ne') using 1
    · funext u
      rfl
    · simp only [entranceW, entranceCanonicalValue, Pi.mul_apply, Pi.sub_apply]
      field_simp [hs.ne', hQ.ne', hR.ne']
      ring

private theorem entrance_div_tendsto_zero
    {f g : ℝ → ℝ} {δ L A p : ℝ} {q : ℕ} (hδ : 0 < δ) (hL : 0 < L) (hA : 0 ≤ A)
    (hp : 0 < p)
    (hf : ∀ t ∈ Ioc 0 δ, |f t| ≤ A * (t ^ q * t ^ p))
    (hg : ∀ t ∈ Ioc 0 δ, L * t ^ q ≤ g t) :
    Tendsto (fun t => f t / g t) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun t : ℝ => A / L * t ^ p) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by
      simpa [Real.zero_rpow hp.ne'] using
        ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).const_mul (A / L)).tendsto)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [Ioc_mem_nhdsGT hδ] with t ht
  have ht0 := ht.1
  have hl : 0 < L * t ^ q := mul_pos hL (pow_pos ht0 _)
  have hgt : 0 < g t := hl.trans_le (hg t ht)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hgt]
  calc
    _ ≤ (A * (t ^ q * t ^ p)) / g t :=
      div_le_div_of_nonneg_right (hf t ht) hgt.le
    _ ≤ (A * (t ^ q * t ^ p)) / (L * t ^ q) :=
      div_le_div_of_nonneg_left (by positivity) hl (hg t ht)
    _ = _ := by field_simp

/-- The real value and flux coordinates extend to the entrance with polynomial
initial values in the Laplace parameter. -/
theorem entrance_canonical_traces {T lam α C : ℝ} (E : EntranceData T lam α C)
    (hT : 0 < T) (hlam : 0 ≤ lam) (hC : 0 < C) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun t => entranceCanonicalValue E t s) (𝓝[>] 0) (𝓝 (s ^ 2)) ∧
      Tendsto (fun t => entranceCanonicalFlux E t s) (𝓝[>] 0) (𝓝 (2 * s ^ 2 / 3 + 4 * α)) := by
  obtain ⟨δ, hδ, hδT, hb⟩ := entrance_regularization_bounds hT hlam hC
  have hq t (ht : t ∈ Ioc 0 δ) : C⁻¹ / 2 * t ^ (1 : ℕ) ≤ entranceQ E t := by
    simpa using (hb E ht).1
  have hr t (ht : t ∈ Ioc 0 δ) : C⁻¹ / 2 * t ^ (2 : ℕ) ≤ entranceR E t := (hb E ht).2.2.1
  have hden : 0 < C⁻¹ / 2 := by positivity
  have hsub {t : ℝ} (ht : t ∈ Ioc 0 δ) : t ∈ Ioc 0 T := ⟨ht.1, ht.2.trans hδT⟩
  have hKQ := entrance_div_tendsto_zero hδ hden (sq_nonneg (C * lam))
    (p := 3) (by norm_num) (f := fun t => E.K t - entranceQ E t) (g := entranceR E)
    (q := 2) (fun t ht => by
      simpa only [Real.rpow_natCast, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ← pow_add]
        using (entrance_regularization_error E hlam hC (hsub ht)).1) hr
  have hPR0 := entrance_div_tendsto_zero hδ hden (by positivity : 0 ≤ 3 * C ^ 2 * lam)
    (p := 2) (by norm_num) (f := fun t => E.P t - entranceR E t) (g := entranceR E)
    (q := 2) (fun t ht => by
      simpa only [Real.rpow_natCast, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ← pow_add]
        using (entrance_regularization_error E hlam hC (hsub ht)).2) hr
  have hPR : Tendsto (fun t => E.P t / entranceR E t) (𝓝[>] 0) (𝓝 1) := by
    have hh := hPR0.const_add (1 : ℝ)
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [Ioc_mem_nhdsGT hδ] with t ht
    have ht0 := ht.1
    have hr0 := ne_of_gt ((by positivity : 0 < C⁻¹ / 2 * t ^ 2).trans_le (hr t ht))
    field_simp [hr0]
    ring
  have hRQ := entrance_div_tendsto_zero hδ hden
    (by positivity : 0 ≤ C + C⁻¹ / 2) (p := 1) (by norm_num)
    (f := entranceR E) (g := entranceQ E) (q := 1) (fun t ht => by
      have ht0 := ht.1
      have hr0 := (by positivity : 0 < C⁻¹ / 2 * t ^ 2).trans_le (hr t ht)
      simp only [abs_of_pos hr0, pow_one, Real.rpow_one, ← pow_two]
      exact (hb E ht).2.2.2) hq
  let rem : ℝ → ℝ := fun t => E.H t s -
    (-(s * E.d t) + s ^ 2 * E.K t / 2 - s ^ 3 * E.P t / 6)
  obtain ⟨K, hK⟩ := E.taylor s
  have hre := entrance_div_tendsto_zero hδ hden
    (by positivity : 0 ≤ |K| * s ^ ((7 : ℝ) / 2)) (p := 1 / 2) (by norm_num)
    (f := rem) (g := entranceR E) (q := 2) (fun t ht => by
      have ht0 := ht.1
      have hpow : t ^ ((5 : ℝ) / 2) = t ^ (2 : ℕ) * t ^ ((1 : ℝ) / 2) := by
        rw [show (5 : ℝ) / 2 = ((2 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.rpow_add ht0,
          Real.rpow_natCast]
      have h := hK t (hsub ht) s ⟨hs.le, le_rfl⟩
      rw [hpow] at h
      exact h.trans (by gcongr; exact le_abs_self _)) hr
  let G : ℝ → ℝ := fun t => (2 * E.H t s / s ^ 2 - entranceQ E t) / entranceR E t
  have hG : Tendsto G (𝓝[>] 0) (𝓝 (-(2 / s * α) - s / 3)) := by
    have h := (((hre.const_mul (2 / s ^ 2)).sub
      ((entrance_regularized_matching E hlam hC hT).const_mul (2 / s))).add hKQ).sub
      (hPR.const_mul (s / 3))
    simp only [mul_zero, zero_sub, add_zero, mul_one] at h
    apply h.congr'
    filter_upwards [Ioc_mem_nhdsGT hδ] with t ht
    have ht0 := ht.1
    have hr0 := ne_of_gt ((by positivity : 0 < C⁻¹ / 2 * t ^ 2).trans_le (hr t ht))
    unfold rem G
    field_simp [hr0, hs.ne']
    ring
  have hi := (entrance_riccati_ae E hlam hC hT le_rfl hs.le).1
  have hcont := intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  rw [uIcc_of_le hT.le] at hcont
  have hI := (hcont 0 ⟨le_rfl, hT.le⟩).tendsto.mono_left
    (nhdsWithin_le_of_mem (mem_of_superset (Ioc_mem_nhdsGT hT) Ioc_subset_Icc_self))
  have hY : Tendsto (fun t => entranceY E t s) (𝓝[>] 0) (𝓝 1) := by
    have hh : Tendsto (fun t => ∫ u in (0 : ℝ)..t, E.H u s) (𝓝[>] 0) (𝓝 0) := by
      simpa only [intervalIntegral.integral_same] using hI
    have he := Real.continuous_exp.continuousAt.tendsto.comp (hh.neg.div_const 2)
    simpa only [entranceY, timeIntegral, Function.comp_def, neg_zero, zero_div, Real.exp_zero] using he
  constructor
  · have hh := (hY.mul ((hG.mul hRQ).const_add 1)).const_mul (s ^ 2)
    simp only [mul_zero, add_zero, mul_one] at hh
    apply hh.congr'
    filter_upwards [Ioc_mem_nhdsGT hδ] with t ht
    have ht0 := ht.1
    have hq0 := ne_of_gt ((by positivity : 0 < C⁻¹ / 2 * t).trans_le (hb E ht).1)
    have hr0 := ne_of_gt ((by positivity : 0 < C⁻¹ / 2 * t ^ 2).trans_le (hr t ht))
    unfold G entranceCanonicalValue
    field_simp [hq0, hr0, hs.ne']
    ring
  · have hh := (hY.mul hG).const_mul (-2 * s)
    simp only [one_mul] at hh
    rw [show -2 * s * (-(2 / s * α) - s / 3) = 2 * s ^ 2 / 3 + 4 * α by
      field_simp [hs.ne']; ring] at hh
    apply hh.congr'
    filter_upwards with t
    unfold G entranceCanonicalFlux
    ring

private theorem profile_compensated_cast (ρ : Measure ℝ) (s : ℝ) :
      complexCompensatedLaplace ρ (s : ℂ) = (compensatedLaplace ρ s : ℂ) := by
  rw [complexCompensatedLaplace, compensatedLaplace, ← integral_complex_ofReal]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    push_cast
    rfl

private theorem profile_eqOn_right_of_eq_positive {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0 < z.re})
    (hg : DifferentiableOn ℂ g {z | 0 < z.re})
    (hcf : ContinuousOn f {z | 0 ≤ z.re}) (hcg : ContinuousOn g {z | 0 ≤ z.re})
    (h : ∀ s : ℝ, 0 < s → f (s : ℂ) = g (s : ℂ)) : EqOn f g {z | 0 ≤ z.re} := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_Ioi.preimage Complex.continuous_re
  have hc : (1 : ℝ) ∈ closure (Ioo 1 2) := by
    rw [closure_Ioo (by norm_num : (1 : ℝ) ≠ 2)]
    exact ⟨le_rfl, by norm_num⟩
  have hmem : (1 : ℂ) ∈ closure (Complex.ofReal '' Ioo (1 : ℝ) 2) := by
    simpa only [Complex.ofReal_one] using mem_closure_image Complex.continuous_ofReal.continuousAt hc
  have hsub : Complex.ofReal '' Ioo (1 : ℝ) 2 ⊆
      {z | f z = g z} \ {(1 : ℂ)} := by
    rintro z ⟨s, hs, rfl⟩
    constructor
    · exact h s (zero_lt_one.trans hs.1)
    · have hs' : s ≠ 1 := ne_of_gt hs.1
      simpa only [mem_singleton_iff, ← Complex.ofReal_one, Complex.ofReal_inj] using hs'
  have heq :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2 hf |>.eqOn_of_preconnected_of_mem_closure
      ((Complex.analyticOnNhd_iff_differentiableOn hopen).2 hg)
      (convex_halfSpace_re_gt 0).isPreconnected
      (show (1 : ℂ) ∈ {z : ℂ | 0 < z.re} by simp) (closure_mono hsub hmem)
  have heq' : EqOn f g {z : ℂ | 0 ≤ z.re} := by
    apply heq.of_subset_closure hcf hcg (fun z hz =>
      show 0 ≤ z.re from (show 0 < z.re from hz).le)
    rw [Complex.closure_setOfPred_lt_re]
  exact heq'

/-- Real compensated Laplace data determine a finite measure when the
transforms extend continuously to the imaginary axis and the masses agree. -/
theorem profile_measure_eq_of_real_transform {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : measureMoment μ 0 = measureMoment ν 0)
    (hμ : DifferentiableOn ℂ (complexCompensatedLaplace μ) {z : ℂ | 0 < z.re})
    (hν : DifferentiableOn ℂ (complexCompensatedLaplace ν) {z : ℂ | 0 < z.re})
    (hcμ : ContinuousOn (complexCompensatedLaplace μ) {z : ℂ | 0 ≤ z.re})
    (hcν : ContinuousOn (complexCompensatedLaplace ν) {z : ℂ | 0 ≤ z.re})
    (h : ∀ s > 0, compensatedLaplace μ s = compensatedLaplace ν s) :
    μ = ν := by

  have heq := profile_eqOn_right_of_eq_positive hμ hν hcμ hcν (fun s hs => by
    rw [profile_compensated_cast, profile_compensated_cast, h s hs])
  exact profile_measure_eq_of_imaginary_transform hm (fun y => heq (by simp))


/-- The canonical coefficient has a measurable representative bounded above
and away from zero on a common initial interval. -/
theorem entrance_canonical_weight {T lam C : ℝ} (hT : 0 < T) (hlam : 0 ≤ lam) (hC : 0 < C) :
    ∃ δ m M : ℝ, 0 < δ ∧ δ ≤ T ∧ 0 < m ∧
      ∀ {α : ℝ} (E : EntranceData T lam α C), ∃ w : ℝ → ℝ,
        Measurable w ∧ EqOn w (entranceW E) (Ioo 0 δ) ∧
          ∀ t ∈ Ioo 0 δ, m ≤ w t ∧ w t ≤ M := by
  classical
  obtain ⟨δ, hδ, hδT, hb⟩ := entrance_regularization_bounds hT hlam hC
  let L := C⁻¹ / 2
  let U := C + C⁻¹ / 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  refine ⟨δ, L ^ 2 / U, U ^ 2 / L, hδ, hδT, by positivity, ?_⟩
  intro α E
  have hposR (t : ℝ) (ht : t ∈ Ioo 0 δ) : 0 < entranceR E t :=
    (mul_pos hL (pow_pos ht.1 2)).trans_le (hb E ⟨ht.1, ht.2.le⟩).2.2.1
  obtain ⟨hdi, hKi⟩ := entrance_moment_integrable E hlam hC hT
  have hDc := intervalIntegral.continuousOn_primitive_interval' hdi left_mem_uIcc
  have hKc := intervalIntegral.continuousOn_primitive_interval' hKi left_mem_uIcc
  rw [uIcc_of_le hT.le] at hDc hKc
  have hmom {f : ℝ → ℝ} (hc : ∀ r > 0, ContinuousOn f (Icc r T)) :
      ContinuousOn f (Ioo 0 δ) := by
    intro t ht
    have hlt : t < T := ht.2.trans_le hδT
    have hra := half_lt_self ht.1
    have hloc : Icc (t / 2) T ∈ 𝓝 t :=
      mem_of_superset (Ioo_mem_nhds hra hlt) Ioo_subset_Icc_self
    exact ((hc _ (half_pos ht.1)) t ⟨hra.le, hlt.le⟩).continuousAt hloc
      |>.continuousWithinAt
  have hd := hmom fun r hr => by
    obtain ⟨_, h, _, _⟩ := E.lipschitz r hr
    exact h.continuousOn
  have hK := hmom fun r hr => by
    obtain ⟨_, _, h, _⟩ := E.lipschitz r hr
    exact h.continuousOn
  have hP := hmom fun r hr => by
    obtain ⟨_, _, _, h⟩ := E.lipschitz r hr
    exact h.continuousOn
  have hsub : Ioo 0 δ ⊆ Icc 0 T := fun _ ht => ⟨ht.1.le, ht.2.le.trans hδT⟩
  have hQ : ContinuousOn (entranceQ E) (Ioo 0 δ) :=
    hK.sub (hd.mul (hDc.mono hsub))
  have hR : ContinuousOn (entranceR E) (Ioo 0 δ) :=
    hP.sub ((continuousOn_const.mul hd).mul (hKc.mono hsub))
  have hW : ContinuousOn (entranceW E) (Ioo 0 δ) :=
    (hQ.pow 2).div hR (fun t ht => (hposR t ht).ne')
  let w := (Ioo 0 δ).piecewise (entranceW E) (fun _ => 1)
  have hw : EqOn w (entranceW E) (Ioo 0 δ) := fun t ht => piecewise_eq_of_mem _ _ _ ht
  refine ⟨w, hW.measurable_piecewise continuousOn_const measurableSet_Ioo, hw, ?_⟩
  intro t ht
  obtain ⟨hql, hqu, hrl, hru⟩ := hb E ⟨ht.1, ht.2.le⟩
  have ht0 := ht.1
  have hql' : L * t ≤ entranceQ E t := hql
  have hqu' : entranceQ E t ≤ U * t := hqu
  have hrl' : L * t ^ 2 ≤ entranceR E t := hrl
  have hru' : entranceR E t ≤ U * t ^ 2 := hru
  rw [hw ht, entranceW]
  refine ⟨(le_div_iff₀ (hposR t ht)).2 ?_, (div_le_iff₀ (hposR t ht)).2 ?_⟩
  · calc
      L ^ 2 / U * entranceR E t ≤ L ^ 2 / U * (U * t ^ 2) := by gcongr
      _ = (L * t) ^ 2 := by field_simp
      _ ≤ entranceQ E t ^ 2 := pow_le_pow_left₀ (by positivity) hql' _
  · calc
      entranceQ E t ^ 2 ≤ (U * t) ^ 2 :=
        pow_le_pow_left₀ ((by positivity : 0 ≤ L * t).trans hql') hqu' _
      _ = U ^ 2 / L * (L * t ^ 2) := by field_simp
      _ ≤ U ^ 2 / L * entranceR E t := by gcongr

section Volterra

open intervalIntegral

/-- The Picard series gives an entire family of solutions to a Volterra equation
with a uniformly bounded time-dependent linear coefficient. The factorial estimate
is in the uniform norm on the time interval. -/
theorem profile_volterra_entire
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (A : ℝ → X →L[ℂ] X)
    (hAint : ∀ f : ℝ → X, ContinuousOn f (Icc 0 T) →
      IntervalIntegrable (fun u => A u (f u)) volume 0 T)
    (hA : ∀ u ∈ Ioo 0 T, ∀ x : X, ‖A u x‖ ≤ K * ‖x‖)
    (x₀ : X) :
    ∃ Y : ℂ → ℝ → X, (∀ z, ContinuousOn (Y z) (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, Differentiable ℂ (fun z => Y z t)) ∧
      ∀ z t, t ∈ Icc 0 T → Y z t = x₀ + ∫ u in (0 : ℝ)..t, (-z) • A u (Y z u) := by
  let I := Icc (0 : ℝ) T
  let _ : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let p : ℝ → I := projIcc 0 T hT
  have hp : Continuous p := continuous_projIcc
  have hproj {u : ℝ} (hu : u ∈ I) : (p u : ℝ) = u := by
    change (projIcc 0 T hT u : ℝ) = u
    rw [projIcc_of_mem hT hu]
  have hint (f : C(I, X)) :
      IntervalIntegrable (fun u => A u (f (p u))) volume 0 T :=
    hAint _ (f.continuous.comp hp).continuousOn
  have hsub (t : I) : uIcc 0 (t : ℝ) ⊆ uIcc 0 T := by
    rw [uIcc_of_le t.property.1, uIcc_of_le hT]
    exact Icc_subset_Icc_right t.property.2
  have hae {t : I} {P : ℝ → Prop} (h : ∀ u ∈ Ioo 0 (t : ℝ), P u) :
      ∀ᵐ u : ℝ, u ∈ Ioc 0 (t : ℝ) → P u := by
    rw [← ae_restrict_iff' measurableSet_Ioc, ← restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_of_forall_mem measurableSet_Ioo h
  let Vₗ : C(I, X) →ₗ[ℂ] C(I, X) :=
    { toFun := fun f =>
        ⟨fun t => ∫ u in (0 : ℝ)..t, A u (f (p u)), by
          have hc := continuousOn_primitive_interval' (hint f) left_mem_uIcc
          rw [uIcc_of_le hT] at hc
          exact hc.domRestrict⟩
      map_add' := fun f g => by
        ext t
        change (∫ u in (0 : ℝ)..t, A u (f (p u) + g (p u))) =
          (∫ u in (0 : ℝ)..t, A u (f (p u))) + ∫ u in (0 : ℝ)..t, A u (g (p u))
        simp_rw [map_add]
        exact integral_add ((hint f).mono_set (hsub t)) ((hint g).mono_set (hsub t))
      map_smul' := fun c f => by
        ext t
        change (∫ u in (0 : ℝ)..t, A u (c • f (p u))) =
          c • ∫ u in (0 : ℝ)..t, A u (f (p u))
        simp_rw [map_smul]
        exact integral_smul c _ }
  let V : C(I, X) →L[ℂ] C(I, X) := Vₗ.mkContinuous (K * T) (fun f => by
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro t
    change ‖∫ u in (0 : ℝ)..t, A u (f (p u))‖ ≤ K * T * ‖f‖
    calc
      _ ≤ (K * ‖f‖) * |(t : ℝ) - 0| := norm_integral_le_of_norm_le_const_ae (by
        rw [uIoc_of_le t.property.1]
        exact hae fun u hu => (hA u ⟨hu.1, hu.2.trans_le t.property.2⟩ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm f (p u)) hK))
      _ ≤ _ := by
        rw [sub_zero, abs_of_nonneg t.property.1, mul_right_comm K T]
        exact mul_le_mul_of_nonneg_left t.property.2 (mul_nonneg hK (norm_nonneg _)))
  let coeff : ℕ → C(I, X) := Nat.rec (ContinuousMap.const I x₀) (fun _ f => V f)
  have hcoeff (n : ℕ) (t : I) :
      ‖coeff n t‖ ≤ ‖x₀‖ * (K ^ n / n.factorial) * (t : ℝ) ^ n := by
    induction n generalizing t with
    | zero => simp [coeff]
    | succ n ih =>
      let c : ℝ := K * (‖x₀‖ * (K ^ n / n.factorial))
      change ‖∫ u in (0 : ℝ)..t, A u (coeff n (p u))‖ ≤ _
      calc
        _ ≤ ∫ u in (0 : ℝ)..t, c * u ^ n := by
          apply norm_integral_le_of_norm_le t.property.1
          · apply hae
            intro u hu
            have huT : u ∈ I := ⟨hu.1.le, hu.2.le.trans t.property.2⟩
            have h := ih (p u)
            rw [hproj huT] at h
            exact (hA u ⟨hu.1, hu.2.trans_le t.property.2⟩ _).trans (by
              simpa only [c, mul_assoc] using mul_le_mul_of_nonneg_left h hK)
          · exact (continuous_const.mul (continuous_id.pow n)).intervalIntegrable _ _
        _ = _ := by
          rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero n), sub_zero,
            Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ K]
          dsimp [c]
          have hf : (n.factorial : ℝ) ≠ 0 := by positivity
          have hn : (n : ℝ) + 1 ≠ 0 := by positivity
          field_simp
  have hbound (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) (n : ℕ) :
      ‖(-z) ^ n • coeff n‖ ≤ ‖x₀‖ * ((R * K * T) ^ n / n.factorial) := by
    rw [norm_smul, norm_pow, norm_neg]
    have hc : ‖coeff n‖ ≤ ‖x₀‖ * (K ^ n / n.factorial) * T ^ n := by
      apply (ContinuousMap.norm_le _ (by positivity)).2
      intro t
      exact (hcoeff n t).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ t.property.1 t.property.2 _) (by positivity))
    calc
      _ ≤ R ^ n * (‖x₀‖ * (K ^ n / n.factorial) * T ^ n) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz _) hc (norm_nonneg _) (by positivity)
      _ = _ := by simp only [mul_pow, div_eq_mul_inv]; ring
  have hmaj (R : ℝ) : Summable (fun n : ℕ => ‖x₀‖ * ((R * K * T) ^ n / n.factorial)) :=
    (Real.summable_pow_div_factorial (R * K * T)).mul_left _
  have hsum (z : ℂ) : Summable (fun n : ℕ => (-z) ^ n • coeff n) :=
    Summable.of_norm_bounded (hmaj ‖z‖) (fun n => hbound ‖z‖ (norm_nonneg _) z le_rfl n)
  let F (z : ℂ) : C(I, X) := ∑' n : ℕ, (-z) ^ n • coeff n
  have hF : Differentiable ℂ F := by
    intro z
    let r := ‖z‖ + 1
    have hR : 0 ≤ r := by dsimp [r]; positivity
    have hdiff := Complex.differentiableOn_tsum_of_summable_norm (hmaj r)
      (F := fun (n : ℕ) (z : ℂ) => (-z) ^ n • coeff n)
      (U := Metric.ball (0 : ℂ) r)
      (fun n => (((differentiable_id.neg).pow n).smul_const (coeff n)).differentiableOn)
      Metric.isOpen_ball (fun n w hw => hbound r hR w (by
        have := Metric.mem_ball.mp hw
        simpa only [dist_zero_right] using this.le) n)
    apply hdiff.differentiableAt
    apply Metric.isOpen_ball.mem_nhds
    apply Metric.mem_ball.mpr
    rw [dist_zero_right]
    dsimp [r]
    linarith
  refine ⟨fun z t => F z (p t), fun z => ((F z).continuous.comp hp).continuousOn,
    ?_, ?_⟩
  · intro t _
    let ev : C(I, X) →L[ℂ] X := ContinuousMap.evalCLM ℂ (p t)
    exact ev.differentiable.comp hF
  · intro z t ht
    have hfix : F z = (ContinuousMap.const I x₀) + (-z) • V (F z) := by
      have htail : (∑' n : ℕ, (-z) ^ (n + 1) • coeff (n + 1)) = (-z) • V (F z) := by
        change _ = (-z) • V (∑' n : ℕ, (-z) ^ n • coeff n)
        rw [V.map_tsum (hsum z), ← tsum_const_smul'']
        apply tsum_congr
        intro n
        rw [map_smul, pow_succ', mul_smul]
      calc
        F z = (ContinuousMap.const I x₀) + (∑' n : ℕ, (-z) ^ (n + 1) • coeff (n + 1)) := by
          simpa only [F, coeff, pow_zero, one_smul, Nat.rec_zero] using (hsum z).tsum_eq_zero_add
        _ = _ := congrArg (fun y => (ContinuousMap.const I x₀) + y) htail
    have h := congrArg (fun f : C(I, X) => f (p t)) hfix
    change F z (p t) = x₀ + (-z) • ∫ u in (0 : ℝ)..(p t : ℝ), A u (F z (p u)) at h
    rw [hproj ht, ← intervalIntegral.integral_smul] at h
    exact h

end Volterra

section FundamentalMatrix

noncomputable section

open scoped Matrix.Norms.Elementwise

local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ

private noncomputable def profileWeightMatrix (b : ℝ) : Mat :=
  !![0, (b : ℂ)⁻¹; (b : ℂ), 0]

private theorem profile_weightMatrix_measurable : Measurable profileWeightMatrix := by
  apply Measurable.of_eval_matrix
  intro i j
  fin_cases i <;> fin_cases j
  · exact measurable_const
  · exact Complex.measurable_ofReal.inv
  · exact Complex.measurable_ofReal
  · exact measurable_const

private theorem profile_weightMatrix_norm (b : ℝ) (X : Mat) :
    ‖profileWeightMatrix b * X‖ ≤ max ‖(b : ℂ)⁻¹‖ ‖(b : ℂ)‖ * ‖X‖ := by
  apply (Matrix.norm_le_iff (by positivity)).2
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i
  · change ‖0 * X 0 j + (b : ℂ)⁻¹ * X 1 j‖ ≤ _
    rw [zero_mul, zero_add, norm_mul]
    exact mul_le_mul (le_max_left _ _) (Matrix.norm_entry_le_entrywise_sup_norm X)
      (norm_nonneg _) (by positivity)
  · change ‖(b : ℂ) * X 0 j + 0 * X 1 j‖ ≤ _
    rw [zero_mul, add_zero, norm_mul]
    exact mul_le_mul (le_max_right _ _) (Matrix.norm_entry_le_entrywise_sup_norm X)
      (norm_nonneg _) (by positivity)

private theorem profile_weightMatrix_norm_of_bounds {m M b : ℝ}
    (hm : 0 < m) (hl : m ≤ b) (hu : b ≤ M) (X : Mat) :
    ‖profileWeightMatrix b * X‖ ≤ max M m⁻¹ * ‖X‖ := by
  have hb := hm.trans_le hl
  apply (profile_weightMatrix_norm b X).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
  exact max_le (le_max_right M m⁻¹ |>.trans' (inv_anti₀ hm hl)) (hu.trans (le_max_left _ _))

private noncomputable def profileMatrixOp (b : ℝ) : Mat →L[ℂ] Mat :=
  (show Mat →ₗ[ℂ] Mat from
    { toFun := fun X => profileWeightMatrix b * X
      map_add' := fun X Y => Matrix.mul_add _ X Y
      map_smul' := fun c X => Matrix.mul_smul _ c X }).mkContinuous
    (max ‖(b : ℂ)⁻¹‖ ‖(b : ℂ)‖) (profile_weightMatrix_norm b)

private theorem profileMatrixOp_apply (b : ℝ) (X : Mat) :
    profileMatrixOp b X = profileWeightMatrix b * X := rfl

local instance : ContinuousENorm Mat :=
  inferInstanceAs (ContinuousENorm (Fin 2 → Fin 2 → ℂ))

local instance : ENormedAddMonoid Mat :=
  inferInstanceAs (ENormedAddMonoid (Fin 2 → Fin 2 → ℂ))

local instance : TopologicalSpace.PseudoMetrizableSpace Mat :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

local instance : SecondCountableTopology Mat :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))

private theorem profile_matrix_intervalIntegrable
    {T m M : ℝ} (hT : 0 < T) {w : ℝ → ℝ} (hw : Measurable w) (hm : 0 < m)
    (hl : ∀ t ∈ Ioo 0 T, m ≤ w t) (hu : ∀ t ∈ Ioo 0 T, w t ≤ M)
    (f : ℝ → Mat) (hf : ContinuousOn f (Icc 0 T)) :
    IntervalIntegrable (fun t => profileMatrixOp (w t) (f t)) volume 0 T := by
  have hK : 0 ≤ max M m⁻¹ := (inv_nonneg.mpr hm.le).trans (le_max_right _ _)
  simp only [profileMatrixOp_apply]
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le]
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  apply (integrable_const (max M m⁻¹ * B)).mono'
  · have hmul : Continuous (fun X : Mat × Mat => X.1 * X.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hmul.comp_aestronglyMeasurable
      (((profile_weightMatrix_measurable.comp hw).aestronglyMeasurable).prodMk
        ((hf.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo))
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (profile_weightMatrix_norm_of_bounds hm (hl t ht) (hu t ht) (f t)).trans
      (mul_le_mul_of_nonneg_left (hB t (Ioo_subset_Icc_self ht)) hK)

/-- The fundamental matrix in the entrance argument is entire in its spectral
parameter. Its normalization and integral equation are those of
`matrix_integral_solution_exists_unique_aux`. -/
theorem profile_fundamental_matrix_entire
    {T m M : ℝ} (hT : 0 < T) (w : ℝ → ℝ) (hw : Measurable w) (hm : 0 < m)
    (hl : ∀ t ∈ Ioo 0 T, m ≤ w t) (hu : ∀ t ∈ Ioo 0 T, w t ≤ M) :
    ∃ Y : ℂ → ℝ → Mat, (∀ z, ContinuousOn (Y z) (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, Differentiable ℂ (fun z => Y z t)) ∧
      ∀ z t, t ∈ Icc 0 T → Y z t = 1 + ∫ u in (0 : ℝ)..t,
        (-z) • ((!![0, (w u : ℂ)⁻¹; (w u : ℂ), 0] : Mat) * Y z u) := by
  have hK : 0 ≤ max M m⁻¹ := (inv_nonneg.mpr hm.le).trans (le_max_right _ _)
  have hA (t : ℝ) (ht : t ∈ Ioo 0 T) (X : Mat) :
      ‖profileMatrixOp (w t) X‖ ≤ max M m⁻¹ * ‖X‖ := by
    rw [profileMatrixOp_apply]
    exact profile_weightMatrix_norm_of_bounds hm (hl t ht) (hu t ht) X
  obtain ⟨Y, hY, hd, he⟩ := profile_volterra_entire hT.le hK
    (fun t => profileMatrixOp (w t)) (profile_matrix_intervalIntegrable hT hw hm hl hu) hA (1 : Mat)
  refine ⟨Y, hY, hd, fun z t ht => ?_⟩
  have hh := he z t ht
  change Y z t = 1 + ∫ u in (0 : ℝ)..t, (-z) • profileMatrixOp (w u) (Y z u) at hh
  simp only [profileMatrixOp_apply, profileWeightMatrix] at hh
  exact hh

private noncomputable def profileMatrixEntry (i j : Fin 2) : Mat →L[ℂ] ℂ :=
  (show Mat →ₗ[ℂ] ℂ from
    { toFun := fun X => X i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).mkContinuous 1 (fun X => by
        rw [one_mul]
        exact Matrix.norm_entry_le_entrywise_sup_norm X)

private theorem profileMatrixEntry_apply (i j : Fin 2) (X : Mat) :
    profileMatrixEntry i j X = X i j := rfl

private noncomputable def profileMatrixRight (J : Mat) : Mat →L[ℂ] Mat :=
  LinearMap.toContinuousLinearMap
    (show Mat →ₗ[ℂ] Mat from
      { toFun := fun X => X * J
        map_add' := fun X Y => Matrix.add_mul X Y J
        map_smul' := fun c X => Matrix.smul_mul c X J })

private theorem profileMatrixRight_apply (J X : Mat) : profileMatrixRight J X = X * J := rfl

private theorem profile_matrix_initial_transport
    {D m M : ℝ} (hD : 0 < D) {w : ℝ → ℝ} (hw : Measurable w) (hm : 0 < m)
    (hl : ∀ t ∈ Ioo 0 D, m ≤ w t) (hu : ∀ t ∈ Ioo 0 D, w t ≤ M)
    (z : ℂ) (J : Mat) {Y F : ℝ → Mat}
    (hY : ContinuousOn Y (Icc 0 D)) (hF : ContinuousOn F (Icc 0 D))
    (hYe : ∀ t ∈ Icc 0 D, Y t = 1 + ∫ u in (0 : ℝ)..t, (-z) • (profileWeightMatrix (w u) * Y u))
    (hFe : ∀ t ∈ Icc 0 D, F t = J + ∫ u in (0 : ℝ)..t, (-z) • (profileWeightMatrix (w u) * F u)) :
    ∀ t ∈ Icc 0 D, F t = Y t * J := by
  let G : ℝ → Mat := fun t => Y t * J
  have hG : ContinuousOn G (Icc 0 D) :=
    (profileMatrixRight J).continuous.comp_continuousOn hY
  let V (f : ℝ → Mat) (u : ℝ) := (-z) • (profileWeightMatrix (w u) * f u)
  have hint {f : ℝ → Mat} (hf : ContinuousOn f (Icc 0 D)) {t : ℝ} (ht : t ∈ Icc 0 D) :
      IntervalIntegrable (V f) volume 0 t := by
    have h := profile_matrix_intervalIntegrable hD hw hm hl hu f hf
    simp only [profileMatrixOp_apply] at h
    have hsub : uIcc 0 t ⊆ uIcc 0 D := by
      rw [uIcc_of_le ht.1, uIcc_of_le hD.le]
      exact Icc_subset_Icc_right ht.2
    exact (h.mono_set hsub).smul (-z)
  have hGe (t : ℝ) (ht : t ∈ Icc 0 D) :
      G t = J + ∫ u in (0 : ℝ)..t, V G u := by
    have h := congrArg (profileMatrixRight J) (hYe t ht)
    change profileMatrixRight J (Y t) =
      profileMatrixRight J (1 + ∫ u in (0 : ℝ)..t, V Y u) at h
    rw [map_add] at h
    erw [← (profileMatrixRight J).intervalIntegral_comp_comm (hint hY ht)] at h
    calc
      G t = profileMatrixRight J (Y t) := rfl
      _ = profileMatrixRight J 1 + ∫ u in (0 : ℝ)..t, profileMatrixRight J (V Y u) := h
      _ = _ := by
        rw [profileMatrixRight_apply, one_mul]
        congr 1
        apply intervalIntegral.integral_congr
        intro u hu
        change ((-z) • (profileWeightMatrix (w u) * Y u)) * J =
          (-z) • (profileWeightMatrix (w u) * (Y u * J))
        rw [Matrix.smul_mul, Matrix.mul_assoc]
  let W : ℝ → Mat := fun t => Y t + (F t - G t)
  have hW : ContinuousOn W (Icc 0 D) := hY.add (hF.sub hG)
  have hWe (t : ℝ) (ht : t ∈ Icc 0 D) :
      W t = 1 + ∫ u in (0 : ℝ)..t, V W u := by
    have hi : (∫ u in (0 : ℝ)..t, V W u) = (∫ u in (0 : ℝ)..t, V Y u) +
        ((∫ u in (0 : ℝ)..t, V F u) - (∫ u in (0 : ℝ)..t, V G u)) := by
      rw [← intervalIntegral.integral_sub (hint hF ht) (hint hG ht),
        ← intervalIntegral.integral_add (hint hY ht) ((hint hF ht).sub (hint hG ht))]
      simp only [W, V, Matrix.mul_add, Matrix.mul_sub, smul_add, smul_sub]
    rw [hi]
    dsimp only [W]
    rw [hYe t ht, hFe t ht, hGe t ht]
    change _ + (_ + (∫ u in (0 : ℝ)..t, V F u) - (_ + (∫ u in (0 : ℝ)..t, V G u))) = _
    abel
  have huniq := (matrix_integral_solution_exists_unique_aux D m M hD w hw hm hl hu z).2
  intro t ht
  have h := huniq W Y hW hY (by simpa only [V, profileWeightMatrix] using hWe)
    (by simpa only [profileWeightMatrix] using hYe) t ht
  have hz : F t - G t = 0 := by
    have h' : Y t + (F t - G t) = Y t + 0 := by simpa only [W, add_zero] using h
    exact add_left_cancel h'
  exact sub_eq_zero.mp hz


private noncomputable def profileColumn (x y : ℂ) : Mat := !![x, 0; y, 0]

private theorem profile_fundamental_real_agreement
    {D m M α : ℝ} (hD : 0 < D) {w : ℝ → ℝ} (hw : Measurable w) (hm : 0 < m)
    (hl : ∀ t ∈ Ioo 0 D, m ≤ w t) (hu : ∀ t ∈ Ioo 0 D, w t ≤ M)
    {s : ℝ} {Y : ℝ → Mat} (hY : ContinuousOn Y (Icc 0 D))
    (hYe : ∀ t ∈ Icc 0 D, Y t = 1 + ∫ u in (0 : ℝ)..t,
      (-((s : ℂ) / 2)) • (profileWeightMatrix (w u) * Y u))
    {X Z : ℝ → ℝ} (hX : ContinuousOn X (Icc 0 D)) (hZ : ContinuousOn Z (Icc 0 D))
    (he : ∀ t ∈ Icc 0 D,
      X t = s ^ 2 + ∫ u in (0 : ℝ)..t, -(s / 2) * (w u)⁻¹ * Z u ∧
      Z t = (2 * s ^ 2 / 3 + 4 * α) + ∫ u in (0 : ℝ)..t, -(s / 2) * w u * X u) :
    ∀ t ∈ Icc 0 D, profileColumn (X t) (Z t) =
      Y t * profileColumn ((s : ℂ) ^ 2) (2 * (s : ℂ) ^ 2 / 3 + 4 * (α : ℂ)) := by
  let F : ℝ → Mat := fun t => profileColumn (X t) (Z t)
  let J : Mat := profileColumn ((s : ℂ) ^ 2) (2 * (s : ℂ) ^ 2 / 3 + 4 * (α : ℂ))
  have hF : ContinuousOn F (Icc 0 D) := by
    change ContinuousOn (fun t (i : Fin 2) (j : Fin 2) => F t i j) (Icc 0 D)
    apply continuousOn_pi.2
    intro i
    apply continuousOn_pi.2
    intro j
    fin_cases i <;> fin_cases j
    · exact Complex.continuous_ofReal.comp_continuousOn hX
    · exact continuousOn_const
    · exact Complex.continuous_ofReal.comp_continuousOn hZ
    · exact continuousOn_const
  apply profile_matrix_initial_transport hD hw hm hl hu ((s : ℂ) / 2) J hY hF hYe
  intro t ht
  let g : ℝ → Mat := fun u => (-((s : ℂ) / 2)) • (profileWeightMatrix (w u) * F u)
  have hgi : IntervalIntegrable g volume 0 t := by
    have hi := profile_matrix_intervalIntegrable hD hw hm hl hu F hF
    simp only [profileMatrixOp_apply] at hi
    have hsub : uIcc 0 t ⊆ uIcc 0 D := by
      rw [uIcc_of_le ht.1, uIcc_of_le hD.le]
      exact Icc_subset_Icc_right ht.2
    exact (hi.mono_set hsub).smul (-((s : ℂ) / 2))
  change F t = J + ∫ u in (0 : ℝ)..t, g u
  apply Matrix.ext
  intro i j
  rw [Matrix.add_apply]
  change F t i j = J i j + profileMatrixEntry i j (∫ u in (0 : ℝ)..t, g u)
  erw [← (profileMatrixEntry i j).intervalIntegral_comp_comm hgi]
  change F t i j = J i j + ∫ u in (0 : ℝ)..t, g u i j
  have hx := congrArg Complex.ofReal (he t ht).1
  have hz := congrArg Complex.ofReal (he t ht).2
  push_cast [← intervalIntegral.integral_ofReal] at hx hz
  fin_cases i <;> fin_cases j
  · simpa [F, J, g, profileColumn, profileWeightMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, mul_assoc] using hx
  · simp [F, J, g, profileColumn, profileWeightMatrix]
  · simpa [F, J, g, profileColumn, profileWeightMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, mul_assoc] using hz
  · simp [F, J, g, profileColumn, profileWeightMatrix]


end

end FundamentalMatrix

section IntegralEntrance

open intervalIntegral

private theorem profile_ac_contDiffOn_comp {f g : ℝ → ℝ} {a b m M : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : ContDiffOn ℝ 1 g (Icc m M)) (hmap : MapsTo f (uIcc a b) (Icc m M)) :
    AbsolutelyContinuousOnInterval (g ∘ f) a b := by
  obtain ⟨L, hL⟩ := hg.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  exact hL.comp_absolutelyContinuousOnInterval hmap hf

private theorem profile_ac_inv {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hpos : ∀ t ∈ uIcc a b, 0 < f t) :
    AbsolutelyContinuousOnInterval (fun t => (f t)⁻¹) a b := by
  obtain ⟨x, hx, hlo⟩ := isCompact_uIcc.exists_isMinOn ⟨a, left_mem_uIcc⟩ hf.continuousOn
  obtain ⟨y, hy, hhi⟩ := isCompact_uIcc.exists_isMaxOn ⟨a, left_mem_uIcc⟩ hf.continuousOn
  exact profile_ac_contDiffOn_comp hf
    (contDiffOn_id.inv fun _ hz => (hpos x hx |>.trans_le hz.1).ne')
    (fun _ ht => ⟨hlo ht, hhi ht⟩)

private theorem profile_ac_exp {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => Real.exp (f t)) a b := by
  obtain ⟨D, hD⟩ := isCompact_uIcc.exists_bound_of_continuousOn hf.continuousOn
  have hmaps : MapsTo f (uIcc a b) (Icc (-D) D) := by
    intro t ht
    have hb := hD t ht
    rw [Real.norm_eq_abs] at hb
    exact abs_le.mp hb
  exact profile_ac_contDiffOn_comp (g := Real.exp) hf Real.contDiff_exp.contDiffOn hmaps

/-- Away from the entrance, both regularized coordinates are absolutely
continuous. The positivity assumptions on the two denominators hold on
the common interval of `entrance_regularization_bounds`. -/
theorem entrance_canonical_ac {T lam α C : ℝ} (E : EntranceData T lam α C)
    (hlam : 0 ≤ lam) (hC : 0 < C) {a b s : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T) (hs : 0 ≤ s)
    (hposQ : ∀ t ∈ Icc a b, 0 < entranceQ E t)
    (hposR : ∀ t ∈ Icc a b, 0 < entranceR E t) :
    AbsolutelyContinuousOnInterval (fun t => entranceCanonicalValue E t s) a b ∧
      AbsolutelyContinuousOnInterval (fun t => entranceCanonicalFlux E t s) a b := by
  have haT := hab.trans hbT
  have hT := ha.trans_le haT
  have hsub : uIcc a b ⊆ uIcc a T := by
    rw [uIcc_of_le hab, uIcc_of_le haT]
    exact Icc_subset_Icc_right hbT
  have hsub₀ : uIcc a b ⊆ uIcc 0 T := by
    rw [uIcc_of_le hab, uIcc_of_le hT.le]
    exact Icc_subset_Icc ha.le hbT
  obtain ⟨L, hdl, hKl, hPl⟩ := E.lipschitz a ha
  have hsub' : uIcc a b ⊆ Icc a T := uIcc_of_le haT ▸ hsub
  have hd := (hdl.mono hsub').absolutelyContinuousOnInterval
  have hK := (hKl.mono hsub').absolutelyContinuousOnInterval
  have hP := (hPl.mono hsub').absolutelyContinuousOnInterval
  obtain ⟨hdi, hKi⟩ := entrance_moment_integrable E hlam hC hT
  have hdprim := (hdi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).mono hsub₀
  have hKprim := (hKi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).mono hsub₀
  have hQ : AbsolutelyContinuousOnInterval (entranceQ E) a b := hK.sub (hd.mul hdprim)
  have hR : AbsolutelyContinuousOnInterval (entranceR E) a b :=
    hP.sub ((hd.const_mul 3).mul hKprim)
  have hQi := profile_ac_inv hQ (by rwa [uIcc_of_le hab])
  have hRi := profile_ac_inv hR (by rwa [uIcc_of_le hab])
  obtain ⟨hHi, hGi⟩ := entrance_riccati_integrable E hlam hC ha haT hs
  have hH : AbsolutelyContinuousOnInterval (fun t => E.H t s) a b := by
    have hG := (hGi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).mono hsub
    have hconst := ((LipschitzWith.const (α := ℝ) (E.H a s)).lipschitzOnWith
      (s := uIcc a b)).absolutelyContinuousOnInterval
    apply (hconst.fun_add hG).congr
    intro t ht
    have h := hsub' ht
    exact (eq_add_of_sub_eq' (E.riccati s hs a t ha h.1 h.2)).symm
  have hp := (hHi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).mono hsub₀
  have hY : AbsolutelyContinuousOnInterval (fun t => entranceY E t s) a b := by
    have hx : AbsolutelyContinuousOnInterval
        (fun t => -timeIntegral (fun u => E.H u s) 0 t / 2) a b := by
      apply (hp.const_mul (-(2 : ℝ)⁻¹)).congr
      intro t ht
      simp only [timeIntegral, div_eq_mul_inv]
      ring
    exact profile_ac_exp hx
  constructor
  · apply (((hH.const_mul 2).mul hY).mul hQi).congr
    intro t ht
    simp only [entranceCanonicalValue, Pi.mul_apply, div_eq_mul_inv]
  · have hf := (((hY.const_mul (2 * s)).mul
      (hQ.sub (hH.const_mul (2 / s ^ 2)))).mul hRi)
    apply hf.congr
    intro t ht
    simp only [entranceCanonicalFlux, Pi.mul_apply, Pi.sub_apply, div_eq_mul_inv]
    ring

private theorem profile_integral_eq_at_entrance {D x₀ : ℝ} (hD : 0 < D) {f g : ℝ → ℝ}
    (hac : ∀ a, 0 < a → a ≤ D → AbsolutelyContinuousOnInterval f a D)
    (hder : ∀ a, 0 < a → a ≤ D → ∀ᵐ t : ℝ, t ∈ Ioo a D → HasDerivAt f (g t) t)
    (hg : IntervalIntegrable g volume 0 D) (htrace : Tendsto f (𝓝[>] 0) (𝓝 x₀)) :
    ∀ t ∈ Ioc 0 D, f t = x₀ + ∫ u in (0 : ℝ)..t, g u := by
  let P : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, g u
  have hPac : AbsolutelyContinuousOnInterval P 0 D :=
    hg.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hpder := hg.ae_hasDerivAt_integral
  rw [uIcc_of_le hD.le] at hpder
  have hconstant (a : ℝ) (ha : 0 < a) (haD : a ≤ D) : f a - P a = f D - P D := by
    have hsub : uIcc a D ⊆ uIcc 0 D := by
      rw [uIcc_of_le haD, uIcc_of_le hD.le]
      exact Icc_subset_Icc_left ha.le
    have hdif := (hac a ha haD).sub (hPac.mono hsub)
    have hh : ∀ᵐ t : ℝ, t ∈ uIcc a D → HasDerivAt (fun u => f u - P u) 0 t := by
      filter_upwards [hder a ha haD, hpder, volume.ae_ne a, volume.ae_ne D]
        with t ht hp hta htD hmem
      have hm : t ∈ Icc a D := uIcc_of_le haD ▸ hmem
      have hpos : t ∈ Ioo a D := ⟨lt_of_le_of_ne hm.1 hta.symm, lt_of_le_of_ne hm.2 htD⟩
      have hP := hp ⟨ha.le.trans hm.1, hm.2⟩ 0 ⟨le_rfl, hD.le⟩
      simpa only [sub_self, Pi.sub_apply, P] using (ht hpos).fun_sub hP
    obtain ⟨k, hk⟩ := hdif.const_of_ae_hasDerivAt_zero hh
    exact (hk a left_mem_uIcc).trans (hk D right_mem_uIcc).symm
  have hPc := hPac.continuousOn
  rw [uIcc_of_le hD.le] at hPc
  have hP0 : Tendsto P (𝓝[>] 0) (𝓝 0) := by
    have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc 0 D] 0 :=
      nhdsWithin_le_of_mem (mem_of_superset (Ioc_mem_nhdsGT hD) Ioc_subset_Icc_self)
    simpa only [P, intervalIntegral.integral_same] using
      (hPc 0 ⟨le_rfl, hD.le⟩).tendsto.mono_left hle
  have hc : Tendsto (fun t => f t - P t) (𝓝[>] 0) (𝓝 (f D - P D)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioc_mem_nhdsGT hD] with t ht
    exact (hconstant t ht.1 ht.2).symm
  have he := tendsto_nhds_unique hc (htrace.sub hP0)
  intro t ht
  have he' := hconstant t ht.1 ht.2
  change f t = x₀ + P t
  linarith

end IntegralEntrance

section RealEntranceVolterra

open intervalIntegral

private theorem profile_continuousOn_of_trace {D f₀ : ℝ} {f : ℝ → ℝ}
    (_hD : 0 < D) (ht : Tendsto f (𝓝[>] 0) (𝓝 f₀))
    (hc : ∀ a, 0 < a → a ≤ D → ContinuousOn f (Icc a D)) :
    ContinuousOn (fun t => if t = 0 then f₀ else f t) (Icc 0 D) := by
  let F : ℝ → ℝ := fun t => if t = 0 then f₀ else f t
  change ContinuousOn F (Icc 0 D)
  intro t ht'
  by_cases hzero : t = 0
  · subst t
    have hFt : Tendsto F (𝓝[>] 0) (𝓝 f₀) := by
      apply ht.congr'
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu' : 0 < u := hu
      simp [F, hu'.ne']
    have hF : ContinuousWithinAt F (Ioi 0) 0 := by
      simpa [ContinuousWithinAt, F] using hFt
    apply hF.insert.mono
    intro u hu
    rcases eq_or_lt_of_le hu.1 with he | he
    · exact mem_insert_iff.mpr (Or.inl he.symm)
    · exact mem_insert_of_mem _ he
  · have hpos : 0 < t := lt_of_le_of_ne ht'.1 (Ne.symm hzero)
    let a := t / 2
    have ha : 0 < a := half_pos hpos
    have hat : a < t := half_lt_self hpos
    have haD := hat.le.trans ht'.2
    have hca : ContinuousOn F (Icc a D) :=
      (hc a ha haD).congr fun u hu => by simp [F, (ha.trans_le hu.1).ne']
    apply (hca t ⟨hat.le, ht'.2⟩).mono_left
    apply nhdsWithin_le_of_mem
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hat)] with u hu ha'
    exact ⟨ha'.le, hu.2⟩

private theorem profile_scalar_intervalIntegrable {D L : ℝ} (hD : 0 < D)
    {w f : ℝ → ℝ} (hw : Measurable w) (hL : 0 ≤ L)
    (hb : ∀ t ∈ Ioo 0 D, ‖w t‖ ≤ L) (hf : ContinuousOn f (Icc 0 D)) :
    IntervalIntegrable (fun t => w t * f t) volume 0 D := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hD.le]
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine (integrable_const (L * B)).mono'
    (hw.aestronglyMeasurable.mul ((hf.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo))
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [norm_mul]
  exact mul_le_mul (hb t ht) (hB t (Ioo_subset_Icc_self ht)) (norm_nonneg _) hL

/-- The real entrance coordinates extend continuously by their traces and
satisfy the canonical integral equation starting at time zero. -/
theorem entrance_canonical_integral {T lam C : ℝ}
    (hT : 0 < T) (hlam : 0 ≤ lam) (hC : 0 < C) :
    ∃ D m M : ℝ, 0 < D ∧ D ≤ T ∧ 0 < m ∧
      ∀ {α : ℝ} (E : EntranceData T lam α C), ∃ w : ℝ → ℝ, Measurable w ∧ (∀ t ∈ Ioo 0 D, m ≤ w t ∧ w t ≤ M) ∧
      ∀ s : ℝ, 0 < s → ∃ X Z : ℝ → ℝ,
        ContinuousOn X (Icc 0 D) ∧ ContinuousOn Z (Icc 0 D) ∧
        (∀ t ∈ Ioc 0 D, X t = entranceCanonicalValue E t s ∧
          Z t = entranceCanonicalFlux E t s) ∧
        ∀ t ∈ Icc 0 D,
          X t = s ^ 2 + ∫ u in (0 : ℝ)..t, -(s / 2) * (w u)⁻¹ * Z u ∧
          Z t = (2 * s ^ 2 / 3 + 4 * α) + ∫ u in (0 : ℝ)..t, -(s / 2) * w u * X u := by
  obtain ⟨D₁, hD₁, hD₁T, hode⟩ := entrance_canonical_ode_ae hT hlam hC
  obtain ⟨D₂, m, M, hD₂, hD₂T, hm, hw⟩ := entrance_canonical_weight hT hlam hC
  obtain ⟨D₃, hD₃, hD₃T, hb⟩ := entrance_regularization_bounds hT hlam hC
  let D := min D₁ (min D₂ D₃)
  have hD : 0 < D := lt_min hD₁ (lt_min hD₂ hD₃)
  have hDle₁ : D ≤ D₁ := min_le_left _ _
  have hDle₂ : D ≤ D₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hDle₃ : D ≤ D₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hDT := hDle₁.trans hD₁T
  refine ⟨D, m, M, hD, hDT, hm, ?_⟩
  intro α E
  obtain ⟨w, hwm, hweq, hwb⟩ := hw E
  have hwi (t : ℝ) (ht : t ∈ Ioo 0 D) : m ≤ w t ∧ w t ≤ M :=
    hwb t ⟨ht.1, ht.2.trans_le hDle₂⟩
  have hM : 0 ≤ M :=
    hm.le.trans ((hwi (D / 2) ⟨half_pos hD, half_lt_self hD⟩).1.trans
      (hwi (D / 2) ⟨half_pos hD, half_lt_self hD⟩).2)
  refine ⟨w, hwm, hwi, ?_⟩
  intro s hs
  obtain ⟨hx, hz⟩ := entrance_canonical_traces E hT hlam hC hs
  let X : ℝ → ℝ := fun t => if t = 0 then s ^ 2 else entranceCanonicalValue E t s
  let Z : ℝ → ℝ := fun t => if t = 0 then 2 * s ^ 2 / 3 + 4 * α else entranceCanonicalFlux E t s
  have hXZ (t : ℝ) (ht : 0 < t) :
      X t = entranceCanonicalValue E t s ∧ Z t = entranceCanonicalFlux E t s := by
    simp [X, Z, ht.ne']
  have hac (a : ℝ) (ha : 0 < a) (haD : a ≤ D) :=
    entrance_canonical_ac E hlam hC ha haD hDT hs.le
      (fun t ht => by
        have ht0 := ha.trans_le ht.1
        exact (by positivity : 0 < C⁻¹ / 2 * t).trans_le
          (hb E ⟨ht0, ht.2.trans hDle₃⟩).1)
      (fun t ht => by
        have ht0 := ha.trans_le ht.1
        exact (by positivity : 0 < C⁻¹ / 2 * t ^ 2).trans_le
          (hb E ⟨ht0, ht.2.trans hDle₃⟩).2.2.1)
  have hXc : ContinuousOn X (Icc 0 D) := profile_continuousOn_of_trace hD hx
    (fun a ha haD => uIcc_of_le haD ▸ (hac a ha haD).1.continuousOn)
  have hZc : ContinuousOn Z (Icc 0 D) := profile_continuousOn_of_trace hD hz
    (fun a ha haD => uIcc_of_le haD ▸ (hac a ha haD).2.continuousOn)
  let gx : ℝ → ℝ := fun u => -(s / 2) * (w u)⁻¹ * Z u
  let gz : ℝ → ℝ := fun u => -(s / 2) * w u * X u
  have hgi : IntervalIntegrable gx volume 0 D := by
    apply profile_scalar_intervalIntegrable hD (measurable_const.mul hwm.inv)
      (L := s / 2 * m⁻¹) (by positivity) _ hZc
    intro t ht
    have hp := hm.trans_le (hwi t ht).1
    change ‖-(s / 2) * (w t)⁻¹‖ ≤ s / 2 * m⁻¹
    rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (half_pos hs), abs_of_pos (inv_pos.mpr hp)]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hm (hwi t ht).1) (half_pos hs).le
  have hgj : IntervalIntegrable gz volume 0 D := by
    apply profile_scalar_intervalIntegrable hD (measurable_const.mul hwm)
      (L := s / 2 * M) (by positivity) _ hXc
    intro t ht
    have hp := hm.trans_le (hwi t ht).1
    change ‖-(s / 2) * w t‖ ≤ s / 2 * M
    rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (half_pos hs), abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left (hwi t ht).2 (half_pos hs).le
  have hder (a : ℝ) (ha : 0 < a) (haD : a ≤ D) :
      ∀ᵐ t : ℝ, t ∈ Ioo a D →
        HasDerivAt (fun t => entranceCanonicalValue E t s) (gx t) t ∧
          HasDerivAt (fun t => entranceCanonicalFlux E t s) (gz t) t := by
    filter_upwards [hode E ha (haD.trans hDle₁) hs] with t ht ht'
    have ht0 := ha.trans ht'.1
    have hw' : w t = entranceW E t := hweq ⟨ht0, ht'.2.trans_le hDle₂⟩
    simpa only [gx, gz, hw', (hXZ t ht0).1, (hXZ t ht0).2] using
      ht ⟨ht'.1, ht'.2.trans_le hDle₁⟩
  have hxInt := profile_integral_eq_at_entrance hD (fun a ha haD => (hac a ha haD).1)
    (fun a ha haD => (hder a ha haD).mono fun t ht hu => (ht hu).1) hgi hx
  have hzInt := profile_integral_eq_at_entrance hD (fun a ha haD => (hac a ha haD).2)
    (fun a ha haD => (hder a ha haD).mono fun t ht hu => (ht hu).2) hgj hz
  refine ⟨X, Z, hXc, hZc, fun t ht => hXZ t ht.1, ?_⟩
  intro t ht
  rcases eq_or_lt_of_le ht.1 with hzero | hpos
  · subst t
    simp [X, Z]
  · exact ⟨(hXZ t hpos).1.trans (hxInt t ⟨hpos, ht.2⟩),
      (hXZ t hpos).2.trans (hzInt t ⟨hpos, ht.2⟩)⟩

end RealEntranceVolterra

section EntireEntrance

open scoped Matrix.Norms.Elementwise
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ

/-- The regularized entrance value extends to an entire function after
multiplication by the exponential factor in the profile argument. The
quadratic scaling gives a polynomial initial vector for the Volterra equation. -/
theorem entrance_canonical_entire {T lam C : ℝ}
    (hT : 0 < T) (hlam : 0 ≤ lam) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ D ≤ T ∧
      ∀ {α : ℝ} (E : EntranceData T lam α C) (t : ℝ), t ∈ Ioc 0 D → ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 0 = 0 ∧
        (∀ s : ℝ, 0 < s → F (s : ℂ) =
          Complex.exp ((s : ℂ) * (t : ℂ) / 2) * (entranceCanonicalValue E t s : ℂ)) ∧
        ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ z : ℂ, z.re ≤ 0 →
          ‖F z‖ ≤ A * Real.exp (ε * ‖z‖) := by
  obtain ⟨D, m, M, hD, hDT, hm, hcanon⟩ := entrance_canonical_integral hT hlam hC
  refine ⟨D, hD, hDT, ?_⟩
  intro α E
  obtain ⟨w, hw, hwb, hint⟩ := hcanon E
  have hl (t : ℝ) (ht : t ∈ Ioo 0 D) := (hwb t ht).1
  have hu (t : ℝ) (ht : t ∈ Ioo 0 D) := (hwb t ht).2
  obtain ⟨Y, hY, hd, he⟩ := profile_fundamental_matrix_entire hD w hw hm hl hu
  intro t ht
  have ht' : t ∈ Icc 0 D := ⟨ht.1.le, ht.2⟩
  let P : ℂ → Mat := fun z => Y (z / 2) t
  let J : ℂ → Mat := fun z => profileColumn (z ^ 2) (2 * z ^ 2 / 3 + 4 * (α : ℂ))
  let F : ℂ → ℂ := fun z => Complex.exp (z * (t : ℂ) / 2) * (P z * J z) 0 0
  have hp : Differentiable ℂ P := (hd t ht').comp (differentiable_id.div_const _)
  have helem (i j : Fin 2) : Differentiable ℂ (fun z => P z i j) :=
    (profileMatrixEntry i j).differentiable.comp hp
  have h00 (z : ℂ) : (P z * J z) 0 0 =
      P z 0 0 * z ^ 2 + P z 0 1 * (2 * z ^ 2 / 3 + 4 * (α : ℂ)) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    rfl
  have hzero : P 0 = 1 := by
    simpa [P] using he 0 t ht'
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · simp only [F, h00]
    apply Differentiable.mul (by fun_prop)
    apply Differentiable.add
    · exact (helem 0 0).mul (differentiable_pow 2)
    · apply Differentiable.mul (helem 0 1)
      fun_prop
  · simp [F, hzero, h00]
  · intro s hs
    obtain ⟨X, Z, hX, hZ, hXZ, he'⟩ := hint s hs
    have ha := profile_fundamental_real_agreement hD hw hm hl hu (hY ((s : ℂ) / 2))
      (by simpa only [profileWeightMatrix] using he ((s : ℂ) / 2)) hX hZ he' t ht'
    have hentry := congrArg (fun M : Mat => M 0 0) ha
    change (X t : ℂ) = (P (s : ℂ) * J (s : ℂ)) 0 0 at hentry
    change Complex.exp _ * (P (s : ℂ) * J (s : ℂ)) 0 0 = _
    rw [← hentry, (hXZ t ht).1]
  · intro ε hε
    have hsub : Icc 0 t ⊆ Icc 0 D := Icc_subset_Icc_right ht.2
    obtain ⟨A, hA⟩ := matrix_integral_growth_bound_aux t m M ht.1 w hw hm
      (fun u hu' => hl u ⟨hu'.1, hu'.2.trans_le ht.2⟩)
      (fun u hu' => hu u ⟨hu'.1, hu'.2.trans_le ht.2⟩) ε hε
    let L := 3 + 4 * |α|
    have hL : 0 ≤ L := by dsimp [L]; positivity
    let B := max A 1
    have hB : 0 ≤ B := zero_le_one.trans (le_max_right _ _)
    let d := ε / 2
    have hδ : 0 < d := half_pos hε
    refine ⟨B * L * (1 + 2 / d ^ 2), ?_⟩
    intro z hz
    let r := ‖z‖
    have hr : 0 ≤ r := norm_nonneg _
    have hnorm : ‖z / 2‖ = r / 2 := by rw [norm_div]; simp [r]
    have hreal : (z / 2).re = z.re / 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re]
    have hA' := hA (z / 2) (Y (z / 2)) ((hY (z / 2)).mono hsub)
      (fun u hu' => he (z / 2) u (hsub hu'))
    have hnormP : ‖P z‖ ≤ B * Real.exp (-(t * z.re / 2) + d * r) := by
      change ‖Y (z / 2) t‖ ≤ _
      rw [hnorm, hreal, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hz (by norm_num))] at hA'
      apply hA'.trans
      have heq : t * -(z.re / 2) + ε * (r / 2) = -(t * z.re / 2) + d * r := by
        dsimp [d]
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    have hPoly : ‖(P z * J z) 0 0‖ ≤ ‖P z‖ * (L * (1 + r ^ 2)) := by
      rw [h00]
      have hCoef : ‖2 * z ^ 2 / 3 + 4 * (α : ℂ)‖ ≤ 2 * r ^ 2 / 3 + 4 * |α| := by
        apply (norm_add_le _ _).trans
        simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, r]
      calc
        _ ≤ ‖P z 0 0 * z ^ 2‖ + ‖P z 0 1 * (2 * z ^ 2 / 3 + 4 * (α : ℂ))‖ :=
          norm_add_le _ _
        _ ≤ ‖P z‖ * r ^ 2 + ‖P z‖ * (2 * r ^ 2 / 3 + 4 * |α|) := by
          simp only [norm_mul, norm_pow]
          exact add_le_add
            (mul_le_mul_of_nonneg_right (Matrix.norm_entry_le_entrywise_sup_norm _) (sq_nonneg _))
            (mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm _) hCoef (norm_nonneg _) (norm_nonneg _))
        _ ≤ _ := by
          rw [← mul_add]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          dsimp [L]
          nlinarith [sq_nonneg r, mul_nonneg (abs_nonneg α) (sq_nonneg r)]
    have hExp : 1 + r ^ 2 ≤ (1 + 2 / d ^ 2) * Real.exp (d * r) := by
      have hpow := Real.pow_div_factorial_le_exp (d * r) (mul_nonneg hδ.le hr) 2
      norm_num at hpow
      have h := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2 / d ^ 2 by positivity)
      have heq : (2 / d ^ 2) * ((d * r) ^ 2 / 2) = r ^ 2 := by field_simp
      rw [heq] at h
      have h1 : 1 ≤ Real.exp (d * r) := Real.one_le_exp_iff.mpr (mul_nonneg hδ.le hr)
      nlinarith only [h, h1]
    have hnE : ‖Complex.exp (z * (t : ℂ) / 2)‖ = Real.exp (t * z.re / 2) := by
      rw [Complex.norm_exp, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.div_ofReal_re, Complex.mul_re]
      simp [mul_comm]
    change ‖Complex.exp (z * (t : ℂ) / 2) * (P z * J z) 0 0‖ ≤ _
    rw [norm_mul, hnE]
    calc
      _ ≤ Real.exp (t * z.re / 2) *
          ((B * Real.exp (-(t * z.re / 2) + d * r)) * (L * ((1 + 2 / d ^ 2) * Real.exp (d * r)))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact hPoly.trans (mul_le_mul hnormP (mul_le_mul_of_nonneg_left hExp hL)
          (by positivity) (by positivity))
      _ = _ := by
        have heq : (t * z.re / 2) + (-(t * z.re / 2) + d * r) + d * r = ε * ‖z‖ := by
          dsimp [d, r]
          ring
        conv_rhs => rw [← heq, Real.exp_add, Real.exp_add]
        ring

end EntireEntrance

section ComplexEntranceLaplace

private noncomputable def profileLaplaceKernel (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(z * (x : ℂ))) - 1

private noncomputable def profileLaplaceDerivative (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(z * (x : ℂ))) * -(x : ℂ)

private theorem profile_kernel_exp_norm {z : ℂ} (hz : 0 ≤ z.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖Complex.exp (-(z * (x : ℂ)))‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff, Complex.neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact neg_nonpos.mpr (mul_nonneg hz hx)

private theorem profile_kernel_norm {z : ℂ} (hz : 0 ≤ z.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖profileLaplaceKernel z x‖ ≤ 2 ∧ ‖profileLaplaceKernel z x‖ ≤ 2 * ‖z‖ * x := by
  have h₂ : ‖profileLaplaceKernel z x‖ ≤ 2 := by
    have h := profile_kernel_exp_norm hz hx
    unfold profileLaplaceKernel
    apply (norm_sub_le _ _).trans
    rw [norm_one]
    linarith
  refine ⟨h₂, ?_⟩
  have hnorm : ‖-(z * (x : ℂ))‖ = ‖z‖ * x := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
  by_cases h : ‖z‖ * x ≤ 1
  · rw [profileLaplaceKernel, mul_assoc]
    simpa only [hnorm] using Complex.norm_exp_sub_one_le (hnorm.trans_le h)
  · apply h₂.trans
    have hh : 1 ≤ ‖z‖ * x := (lt_of_not_ge h).le
    calc
      (2 : ℝ) = 2 * 1 := by ring
      _ ≤ 2 * (‖z‖ * x) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring

/-- A finite measure on the nonnegative half-line controls its compensated
Laplace transform by both mass and first moment on the closed right half-plane. -/
private theorem profile_complexLaplace_bounds {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ : ρ (Iio 0) = 0) (hi : Integrable (fun x : ℝ => x) ρ)
    {z : ℂ} (hz : 0 ≤ z.re) :
    Integrable (profileLaplaceKernel z) ρ ∧
      ‖complexCompensatedLaplace ρ z‖ ≤ 2 * measureMoment ρ 0 ∧
      ‖complexCompensatedLaplace ρ z‖ ≤ 2 * ‖z‖ * measureMoment ρ 1 := by
  have hx : ∀ᵐ x ∂ρ, 0 ≤ x := by simpa [ae_iff, not_le, Iio] using hρ
  have hB := hx.mono fun x hx' => (profile_kernel_norm hz hx').1
  have hL := hx.mono fun x hx' => (profile_kernel_norm hz hx').2
  refine ⟨(integrable_const (2 : ℝ)).mono' (by unfold profileLaplaceKernel; fun_prop) hB, ?_, ?_⟩
  · have h := norm_integral_le_of_norm_le (integrable_const (2 : ℝ)) hB
    simpa [profileLaplaceKernel, complexCompensatedLaplace, measureMoment, integral_const,
      smul_eq_mul, mul_comm] using h
  · have h := norm_integral_le_of_norm_le (hi.const_mul (2 * ‖z‖)) hL
    rw [MeasureTheory.integral_const_mul] at h
    simpa [profileLaplaceKernel, complexCompensatedLaplace, measureMoment] using h

/-- The spectral derivative of the compensated Laplace transform on the
open right half-plane. Its integrand is dominated by the first moment. -/
private theorem profile_complexLaplace_hasDerivAt {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ : ρ (Iio 0) = 0) (hi : Integrable (fun x : ℝ => x) ρ)
    {z : ℂ} (hz : 0 < z.re) :
    Integrable (profileLaplaceDerivative z) ρ ∧
      HasDerivAt (complexCompensatedLaplace ρ) (∫ x, profileLaplaceDerivative z x ∂ρ) z := by
  have hx : ∀ᵐ x ∂ρ, 0 ≤ x := by simpa [ae_iff, not_le, Iio] using hρ
  let S : Set ℂ := {w : ℂ | 0 < w.re}
  have hS : S ∈ 𝓝 z := (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hz
  have hmeas (w : ℂ) : AEStronglyMeasurable (profileLaplaceKernel w) ρ := by
    unfold profileLaplaceKernel
    fun_prop
  have hmeas' : AEStronglyMeasurable (profileLaplaceDerivative z) ρ := by
    unfold profileLaplaceDerivative
    fun_prop
  have hb : ∀ᵐ x ∂ρ, ∀ w ∈ S, ‖profileLaplaceDerivative w x‖ ≤ x := by
    filter_upwards [hx] with x hx' w hw
    have hw' : 0 < w.re := hw
    rw [profileLaplaceDerivative, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hx']
    exact (mul_le_mul_of_nonneg_right (profile_kernel_exp_norm hw'.le hx') hx').trans_eq
      (one_mul x)
  have hd : ∀ᵐ x ∂ρ, ∀ w ∈ S, HasDerivAt (fun u => profileLaplaceKernel u x)
      (profileLaplaceDerivative w x) w := by
    filter_upwards with x w hw
    have h := (((hasDerivAt_id w).mul_const (x : ℂ)).neg.cexp).sub_const 1
    simpa [profileLaplaceKernel, profileLaplaceDerivative, id_eq] using h
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    (Eventually.of_forall hmeas) (profile_complexLaplace_bounds hρ hi hz.le).1 hmeas' hb hi hd

end ComplexEntranceLaplace

section ComplexEntrancePrimitive

private theorem profile_integral_aestronglyMeasurable
    {ν : ℝ → Measure ℝ} (hν : Measurable ν) {σ : Measure ℝ}
    {g : ℝ → ℂ} (hg : Measurable g) (hi : ∀ᵐ t ∂σ, Integrable g (ν t)) :
    AEStronglyMeasurable (fun t => ∫ x, g x ∂ν t) σ := by
  let h (f : ℝ → ℝ) (t : ℝ) :=
    (∫⁻ x, ENNReal.ofReal (f x) ∂ν t).toReal -
      (∫⁻ x, ENNReal.ofReal (-f x) ∂ν t).toReal
  have hm (f : ℝ → ℝ) (hf : Measurable f) : Measurable (h f) :=
    ((Measure.measurable_lintegral hf.ennreal_ofReal).comp hν).ennreal_toReal.sub
      ((Measure.measurable_lintegral hf.neg.ennreal_ofReal).comp hν).ennreal_toReal
  have hmr := hm (fun x => (g x).re) (Complex.continuous_re.measurable.comp hg)
  have hmi := hm (fun x => (g x).im) (Complex.continuous_im.measurable.comp hg)
  have hG : Measurable (fun t =>
      (h (fun x => (g x).re) t : ℂ) + (h (fun x => (g x).im) t : ℂ) * Complex.I) :=
    (Complex.measurable_ofReal.comp hmr).add ((Complex.measurable_ofReal.comp hmi).mul measurable_const)
  apply hG.aestronglyMeasurable.congr
  filter_upwards [hi] with t ht
  have hr := integral_eq_lintegral_pos_part_sub_lintegral_neg_part (Complex.reCLM.integrable_comp ht)
  have hm' := integral_eq_lintegral_pos_part_sub_lintegral_neg_part (Complex.imCLM.integrable_comp ht)
  have hre := integral_re ht
  have him := integral_im ht
  have h₁ : h (fun x => (g x).re) t = (∫ x, g x ∂ν t).re := hr.symm.trans hre
  have h₂ : h (fun x => (g x).im) t = (∫ x, g x ∂ν t).im := hm'.symm.trans him
  rw [h₁, h₂]
  exact Complex.re_add_im _

/-- Complex form of the compensated entrance transform supplied by the
measure representation. -/
noncomputable def entranceComplexH {T lam α C : ℝ} (E : EntranceData T lam α C)
    (t : ℝ) (z : ℂ) : ℂ := z + complexCompensatedLaplace (E.ν t) z

private noncomputable def entranceComplexHDerivative {T lam α C : ℝ}
    (E : EntranceData T lam α C) (t : ℝ) (z : ℂ) : ℂ :=
  1 + ∫ x, profileLaplaceDerivative z x ∂E.ν t

/-- The time primitive of the complex entrance transform is holomorphic in
the open right half-plane and continuous on its closure. -/
theorem entrance_complex_primitive {T lam α C : ℝ} (E : EntranceData T lam α C)
    (hlam : 0 ≤ lam) (hC : 0 < C) {t : ℝ} (ht : t ∈ Ioc 0 T) :
    DifferentiableOn ℂ (fun z => ∫ u in (0 : ℝ)..t, entranceComplexH E u z) {z | 0 < z.re} ∧
      ContinuousOn (fun z => ∫ u in (0 : ℝ)..t, entranceComplexH E u z) {z | 0 ≤ z.re} := by
  let σ : Measure ℝ := volume.restrict (Ioc 0 t)
  let L : ℝ := 1 + C * lam * T ^ 2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hgood : ∀ᵐ u ∂σ, IsFiniteMeasure (E.ν u) ∧ E.ν u (Iio 0) = 0 ∧
      Integrable (fun x : ℝ => x) (E.ν u) ∧ measureMoment (E.ν u) 1 ≤ L := by
    filter_upwards [ae_restrict_of_ae (s := Ioc 0 t) E.representation,
      ae_restrict_mem (μ := volume) (s := Ioc 0 t) measurableSet_Ioc] with u hu hm
    have hmem : u ∈ Ioc 0 T := ⟨hm.1, hm.2.trans ht.2⟩
    obtain ⟨hfin, hp, h3, _, _, hd, _⟩ := hu hmem
    let _ : IsFiniteMeasure (E.ν u) := hfin
    refine ⟨hfin, hp, profile_first_moment_integrable h3, ?_⟩
    rw [hd]
    apply add_le_add_right
    exact (le_abs_self _).trans ((E.bounds u hmem).1.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmem.1.le hmem.2 _) (mul_nonneg hC.le hlam)) )
  have hmeas (z : ℂ) (hz : 0 ≤ z.re) :
      AEStronglyMeasurable (fun u => entranceComplexH E u z) σ := by
    apply aestronglyMeasurable_const.add
    apply profile_integral_aestronglyMeasurable E.measurable_ν (g := profileLaplaceKernel z)
    · unfold profileLaplaceKernel
      fun_prop
    · filter_upwards [hgood] with u hu
      let _ : IsFiniteMeasure (E.ν u) := hu.1
      exact (profile_complexLaplace_bounds hu.2.1 hu.2.2.1 hz).1
  have hb : ∀ᵐ u ∂σ, ∀ z : ℂ, 0 ≤ z.re →
      ‖entranceComplexH E u z‖ ≤ (1 + 2 * L) * ‖z‖ := by
    filter_upwards [hgood] with u hu z hz
    let _ : IsFiniteMeasure (E.ν u) := hu.1
    apply (norm_add_le _ _).trans
    have h := (profile_complexLaplace_bounds hu.2.1 hu.2.2.1 hz).2.2
    have h' := mul_le_mul_of_nonneg_left hu.2.2.2 (by positivity : 0 ≤ 2 * ‖z‖)
    linarith
  have hder : ∀ᵐ u ∂σ, ∀ z : ℂ, 0 < z.re →
      HasDerivAt (fun w => entranceComplexH E u w) (entranceComplexHDerivative E u z) z ∧
        ‖entranceComplexHDerivative E u z‖ ≤ 1 + L := by
    filter_upwards [hgood] with u hu z hz
    let _ : IsFiniteMeasure (E.ν u) := hu.1
    refine ⟨(hasDerivAt_id z).add (profile_complexLaplace_hasDerivAt hu.2.1 hu.2.2.1 hz).2, ?_⟩
    apply (norm_add_le _ _).trans
    have hx : ∀ᵐ x ∂E.ν u, 0 ≤ x := by simpa [ae_iff, not_le, Iio] using hu.2.1
    have hx' : ∀ᵐ x ∂E.ν u, ‖profileLaplaceDerivative z x‖ ≤ x := by
      filter_upwards [hx] with x hx
      rw [profileLaplaceDerivative, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hx]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (profile_kernel_exp_norm hz.le hx) hx
    rw [norm_one]
    apply add_le_add_right
    exact (norm_integral_le_of_norm_le hu.2.2.1 hx').trans (by simpa [measureMoment] using hu.2.2.2)
  have hmder (z : ℂ) (hz : 0 < z.re) :
      AEStronglyMeasurable (fun u => entranceComplexHDerivative E u z) σ := by
    apply aestronglyMeasurable_const.add
    apply profile_integral_aestronglyMeasurable E.measurable_ν (g := profileLaplaceDerivative z)
    · unfold profileLaplaceDerivative
      fun_prop
    · filter_upwards [hgood] with u hu
      let _ : IsFiniteMeasure (E.ν u) := hu.1
      exact (profile_complexLaplace_hasDerivAt hu.2.1 hu.2.2.1 hz).1
  have hS : IsOpen {z : ℂ | 0 < z.re} := isOpen_Ioi.preimage Complex.continuous_re
  simp_rw [intervalIntegral.integral_of_le ht.1.le]
  constructor
  · intro z hz
    have hz' : 0 < z.re := hz
    have hneigh : ∀ᶠ w : ℂ in 𝓝 z, 0 < w.re := hS.mem_nhds hz
    have hF_int : Integrable (fun u => entranceComplexH E u z) σ :=
      (integrable_const ((1 + 2 * L) * ‖z‖)).mono' (hmeas z hz'.le)
        (hb.mono fun u hu => hu z hz'.le)
    obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun z u => entranceComplexH E u z)
      (F' := fun z u => entranceComplexHDerivative E u z)
      (bound := fun _ => 1 + L) hneigh (hneigh.mono fun w hw => hmeas w (show 0 < w.re from hw).le)
      hF_int (hmder z hz')
      (hder.mono fun _ hu w hw => (hu w hw).2) (integrable_const _)
      (hder.mono fun _ hu w hw => (hu w hw).1)
    exact hd.differentiableAt.differentiableWithinAt
  · intro z hz
    let R : Set ℂ := {w : ℂ | 0 ≤ w.re}
    have hc : ContinuousAt (fun _ : ℂ => ‖z‖ + 1) z := continuousAt_const
    have hnorm : ∀ᶠ w : ℂ in 𝓝[R] z, ‖w‖ < ‖z‖ + 1 :=
      (continuous_norm.continuousAt.eventually_lt hc (by linarith)).filter_mono nhdsWithin_le_nhds
    have hmem : ∀ᶠ w : ℂ in 𝓝[R] z, 0 ≤ w.re := self_mem_nhdsWithin
    apply continuousWithinAt_of_dominated (μ := σ)
      (bound := fun _ => (1 + 2 * L) * (‖z‖ + 1))
      (hmem.mono hmeas) ?_ (integrable_const _) ?_
    · filter_upwards [hmem, hnorm] with w hw hwn
      exact hb.mono fun u hu => (hu w hw).trans (mul_le_mul_of_nonneg_left hwn.le (by positivity))
    · filter_upwards [ae_restrict_of_ae (s := Ioc 0 t) E.laplace_extension,
        ae_restrict_mem (μ := volume) (s := Ioc 0 t) measurableSet_Ioc] with u hu humem
      exact (continuousOn_id.add (hu ⟨humem.1, humem.2.trans ht.2⟩).2) z hz

end ComplexEntrancePrimitive

section RightGrowth

open intervalIntegral

private theorem entrance_complex_time_bounds {T lam α C : ℝ} (E : EntranceData T lam α C)
    (hlam : 0 ≤ lam) (hC : 0 < C) {t : ℝ} (ht : t ∈ Ioc 0 T)
    {z : ℂ} (hz : 0 ≤ z.re) :
    let L := 1 + C * lam * T ^ 2
    let A := max (2 * C) (2 * L)
    IntervalIntegrable (fun u => entranceComplexH E u z) volume 0 t ∧
      ∀ᵐ u : ℝ, u ∈ Ioc 0 t →
        ‖complexCompensatedLaplace (E.ν u) z‖ ≤ A * u⁻¹ ∧
        ‖complexCompensatedLaplace (E.ν u) z‖ ≤ A * ‖z‖ := by
  let L : ℝ := 1 + C * lam * T ^ 2
  let A := max (2 * C) (2 * L)
  let σ : Measure ℝ := volume.restrict (Ioc 0 t)
  change IntervalIntegrable (fun u => entranceComplexH E u z) volume 0 t ∧ _
  have he : ∀ᵐ u : ℝ, u ∈ Ioc 0 t →
      Integrable (profileLaplaceKernel z) (E.ν u) ∧
      ‖complexCompensatedLaplace (E.ν u) z‖ ≤ A * u⁻¹ ∧
      ‖complexCompensatedLaplace (E.ν u) z‖ ≤ A * ‖z‖ := by
    filter_upwards [E.representation, E.bounds_S] with u hrep hS hu
    have huT : u ∈ Ioc 0 T := ⟨hu.1, hu.2.trans ht.2⟩
    obtain ⟨hf, hs, h3, _, hm, hd, _⟩ := hrep huT
    let _ : IsFiniteMeasure (E.ν u) := hf
    have h := profile_complexLaplace_bounds hs (profile_first_moment_integrable h3) hz
    have hd' : measureMoment (E.ν u) 1 ≤ L := by
      rw [hd]
      apply add_le_add_right
      exact (le_abs_self _).trans ((E.bounds u huT).1.trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.1.le huT.2 _) (mul_nonneg hC.le hlam)))
    have hu0 := hu.1
    refine ⟨h.1, ?_, ?_⟩
    · calc
        _ ≤ 2 * measureMoment (E.ν u) 0 := h.2.1
        _ ≤ 2 * (C * u⁻¹) := by rw [hm]; gcongr; exact (hS huT).2
        _ = 2 * C * u⁻¹ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · calc
        _ ≤ 2 * ‖z‖ * measureMoment (E.ν u) 1 := h.2.2
        _ ≤ 2 * ‖z‖ * L := mul_le_mul_of_nonneg_left hd' (by positivity)
        _ = 2 * L * ‖z‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le]
    have he' : ∀ᵐ u ∂σ, Integrable (profileLaplaceKernel z) (E.ν u) ∧
        ‖complexCompensatedLaplace (E.ν u) z‖ ≤ A * ‖z‖ := by
      filter_upwards [ae_restrict_of_ae (s := Ioc 0 t) he, ae_restrict_mem (μ := volume)
        (s := Ioc 0 t) measurableSet_Ioc] with u h hu
      exact ⟨(h hu).1, (h hu).2.2⟩
    have hm : AEStronglyMeasurable (fun u => entranceComplexH E u z) σ := by
      apply aestronglyMeasurable_const.add
      apply profile_integral_aestronglyMeasurable E.measurable_ν (g := profileLaplaceKernel z)
      · unfold profileLaplaceKernel
        fun_prop
      · exact he'.mono fun u hu => hu.1
    refine (integrable_const (‖z‖ + A * ‖z‖)).mono' hm ?_
    filter_upwards [he'] with u hu
    exact (norm_add_le _ _).trans (add_le_add_right hu.2 _)
  · exact he.mono fun u hu hm => (hu hm).2

private theorem profile_min_bound {A r u f : ℝ} (hA : 0 ≤ A) (hr : 0 ≤ r) (hu : 0 < u)
    (h₁ : f ≤ A * u⁻¹) (h₂ : f ≤ A * r) :
    f ≤ 2 * A * r / (1 + u * r) := by
  have hp : 0 < 1 + u * r := by positivity
  by_cases h : u * r ≤ 1
  · apply h₂.trans
    apply (le_div_iff₀ hp).2
    nlinarith only [mul_nonneg (mul_nonneg hA hr) (sub_nonneg.mpr h)]
  · apply h₁.trans
    apply (le_div_iff₀ hp).2
    rw [← div_eq_mul_inv, div_mul_eq_mul_div, div_le_iff₀ hu]
    have h' : 1 ≤ u * r := (lt_of_not_ge h).le
    nlinarith only [mul_nonneg hA (sub_nonneg.mpr h')]

private theorem profile_log_integral {A r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, 2 * A * r / (1 + u * r)) = 2 * A * Real.log (1 + t * r) := by
  have hp (u : ℝ) (hu : u ∈ Icc 0 t) : 0 < 1 + u * r :=
    zero_lt_one.trans_le (le_add_of_nonneg_right (mul_nonneg hu.1 hr))
  have hcont : ContinuousOn (fun u => 2 * A * r / (1 + u * r)) (Icc 0 t) :=
    continuousOn_const.div (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
      (fun u hu => (hp u hu).ne')
  have hi : IntervalIntegrable (fun u => 2 * A * r / (1 + u * r)) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht]
    exact hcont.integrableOn_compact isCompact_Icc
  have hd (u : ℝ) (hu : u ∈ uIcc 0 t) :
      HasDerivAt (fun u => 2 * A * Real.log (1 + u * r)) (2 * A * r / (1 + u * r)) u := by
    have hu' : u ∈ Icc 0 t := uIcc_of_le ht ▸ hu
    have hlin : HasDerivAt (fun v => 1 + v * r) r u := by
      simpa [id_eq] using ((hasDerivAt_id u).mul_const r).const_add 1
    have h := ((Real.hasDerivAt_log (hp u hu').ne').comp u hlin).const_mul (2 * A)
    convert h using 1
    · rfl
    · ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp

/-- Bounds on the entrance measure imply logarithmic growth for the real
part of the exponent used to regularize its transform. -/
theorem entrance_complex_primitive_growth {T lam α C : ℝ} (E : EntranceData T lam α C)
    (hlam : 0 ≤ lam) (hC : 0 < C) {t : ℝ} (ht : t ∈ Ioc 0 T)
    {z : ℂ} (hz : 0 ≤ z.re) :
    ((z * (t : ℂ) - ∫ u in (0 : ℝ)..t, entranceComplexH E u z) / 2).re ≤
      max (2 * C) (2 * (1 + C * lam * T ^ 2)) * Real.log (1 + t * ‖z‖) := by
  let A := max (2 * C) (2 * (1 + C * lam * T ^ 2))
  have hA : 0 ≤ A := (by positivity : 0 ≤ 2 * C).trans (le_max_left _ _)
  have hz0 := norm_nonneg z
  obtain ⟨hi, hb⟩ := entrance_complex_time_bounds E hlam hC ht hz
  let f : ℝ → ℝ := fun u => z.re - (entranceComplexH E u z).re
  have hiRe : IntervalIntegrable (fun u => (entranceComplexH E u z).re) volume 0 t :=
    ⟨Complex.reCLM.integrable_comp hi.1, Complex.reCLM.integrable_comp hi.2⟩
  have hif : IntervalIntegrable f volume 0 t := intervalIntegrable_const.sub hiRe
  have hbf : ∀ᵐ u : ℝ, u ∈ Ioc 0 t → f u ≤ 2 * A * ‖z‖ / (1 + u * ‖z‖) := by
    filter_upwards [hb] with u hu hmem
    have hf : f u ≤ ‖complexCompensatedLaplace (E.ν u) z‖ := by
      have hh := (abs_le.mp (Complex.abs_re_le_norm (complexCompensatedLaplace (E.ν u) z))).1
      change z.re - (z + complexCompensatedLaplace (E.ν u) z).re ≤ _
      rw [Complex.add_re]
      linarith
    exact profile_min_bound hA hz0 hmem.1 (hf.trans (hu hmem).1) (hf.trans (hu hmem).2)
  have hcont : ContinuousOn (fun u => 2 * A * ‖z‖ / (1 + u * ‖z‖)) (Icc 0 t) :=
    continuousOn_const.div (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
      (fun u hu => ne_of_gt (zero_lt_one.trans_le
        (le_add_of_nonneg_right (mul_nonneg hu.1 hz0))))
  have him : IntervalIntegrable (fun u => 2 * A * ‖z‖ / (1 + u * ‖z‖)) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1.le]
    exact hcont.integrableOn_compact isCompact_Icc
  have h := intervalIntegral.integral_mono_ae_restrict ht.1.le hif him
    (by rw [← restrict_Ioc_eq_restrict_Icc]; exact (ae_restrict_iff' measurableSet_Ioc).2 hbf)
  rw [profile_log_integral hz0 ht.1.le] at h
  have hf : (∫ u in (0 : ℝ)..t, f u) =
      z.re * t - (∫ u in (0 : ℝ)..t, entranceComplexH E u z).re := by
    change (∫ u in (0 : ℝ)..t, z.re - (entranceComplexH E u z).re) = _
    rw [intervalIntegral.integral_sub intervalIntegrable_const hiRe,
      intervalIntegral.integral_const, show (∫ u in (0 : ℝ)..t, (entranceComplexH E u z).re) =
        (∫ u in (0 : ℝ)..t, entranceComplexH E u z).re from
        Complex.reCLM.intervalIntegral_comp_comm hi]
    simp [smul_eq_mul, mul_comm]
  rw [hf] at h
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re, Complex.sub_re, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  linarith

end RightGrowth

section EntrancePolynomial

open intervalIntegral

private theorem entranceComplexH_real_ae {T lam α C : ℝ} (E : EntranceData T lam α C) :
    ∀ᵐ t : ℝ, t ∈ Ioc 0 T → ∀ s : ℝ, 0 ≤ s →
      entranceComplexH E t (s : ℂ) = (E.H t s : ℂ) := by
  filter_upwards [E.representation] with t ht htmem s hs
  rw [(ht htmem).2.2.2.1 s hs, Complex.ofReal_add, entranceComplexH, profile_compensated_cast]

/-- At almost every time on a common initial interval, the exponentially
regularized value is a polynomial on the positive real axis. Its degree
bound is independent of the entrance data and time. -/
theorem entrance_canonical_polynomial {T lam C : ℝ}
    (hT : 0 < T) (hlam : 0 ≤ lam) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ D ≤ T ∧ ∃ k : ℕ,
      ∀ {α : ℝ} (E : EntranceData T lam α C), ∀ᵐ t : ℝ, t ∈ Ioc 0 D →
        ∃ b : ℕ → ℂ, ∀ s : ℝ, 0 < s →
          Complex.exp ((s : ℂ) * (t : ℂ) / 2) * (entranceCanonicalValue E t s : ℂ) =
            ∑ n ∈ Finset.range (k + 1), b n * (s : ℂ) ^ n := by
  obtain ⟨D₁, hD₁, hD₁T, he⟩ := entrance_canonical_entire hT hlam hC
  obtain ⟨D₂, hD₂, hD₂T, hb⟩ := entrance_regularization_bounds hT hlam hC
  let D := min D₁ D₂
  have hD : 0 < D := lt_min hD₁ hD₂
  have hDle₁ : D ≤ D₁ := min_le_left _ _
  have hDle₂ : D ≤ D₂ := min_le_right _ _
  have hDT := hDle₁.trans hD₁T
  let A := max (2 * C) (2 * (1 + C * lam * T ^ 2))
  let L := 1 + 2 * (1 + C * lam * T ^ 2)
  let k := ⌈A⌉₊ + 1
  have hA : 0 ≤ A := (by positivity : 0 ≤ 2 * C).trans (le_max_left _ _)
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨D, hD, hDT, k, ?_⟩
  intro α E
  filter_upwards [E.representation, E.laplace_extension, entranceComplexH_real_ae E]
    with t hrep hlap hreal ht
  have htT : t ∈ Ioc 0 T := ⟨ht.1, ht.2.trans hDT⟩
  have ht0 := ht.1
  have hQ : 0 < entranceQ E t :=
    (by positivity : 0 < C⁻¹ / 2 * t).trans_le (hb E ⟨ht.1, ht.2.trans hDle₂⟩).1
  obtain ⟨F, hF, _, hFe, hFleft⟩ := he E t ⟨ht.1, ht.2.trans hDle₁⟩
  let I : ℂ → ℂ := fun z => ∫ u in (0 : ℝ)..t, entranceComplexH E u z
  let G : ℂ → ℂ := fun z =>
    2 * entranceComplexH E t z * Complex.exp ((z * (t : ℂ) - I z) / 2) / (entranceQ E t : ℂ)
  obtain ⟨hdI, hcI⟩ := entrance_complex_primitive E hlam hC htT
  obtain ⟨hd, hc⟩ := hlap htT
  have hGH : DifferentiableOn ℂ G {z | 0 < z.re} := by
    have hH : DifferentiableOn ℂ (entranceComplexH E t) {z | 0 < z.re} :=
      differentiableOn_id.add hd
    have hArg := (((differentiableOn_id.mul_const (t : ℂ)).sub hdI).div_const (2 : ℂ))
    exact ((hH.const_mul 2).mul hArg.cexp).div_const _
  have hGC : ContinuousOn G {z | 0 ≤ z.re} := by
    have hH : ContinuousOn (entranceComplexH E t) {z | 0 ≤ z.re} :=
      continuousOn_id.add hc
    have hZ : ContinuousOn (fun z : ℂ => z * (t : ℂ)) {z | 0 ≤ z.re} :=
      (continuous_id.mul continuous_const).continuousOn
    have hArg := ((hZ.sub hcI).div_const (2 : ℂ))
    exact ((continuousOn_const.mul hH).mul hArg.cexp).div_const _
  have hFG : EqOn F G {z | 0 ≤ z.re} := by
    apply profile_eqOn_right_of_eq_positive hF.differentiableOn hGH hF.continuous.continuousOn hGC
    intro s hs
    have hI : I (s : ℂ) = (timeIntegral (fun u => E.H u s) 0 t : ℂ) := by
      change (∫ u in (0 : ℝ)..t, entranceComplexH E u (s : ℂ)) = _
      rw [timeIntegral, ← intervalIntegral.integral_ofReal]
      apply intervalIntegral.integral_congr_ae
      rw [uIoc_of_le ht.1.le]
      filter_upwards [entranceComplexH_real_ae E] with u hu humem
      exact hu ⟨humem.1, humem.2.trans htT.2⟩ s hs.le
    rw [hFe s hs]
    change _ = 2 * entranceComplexH E t (s : ℂ) *
      Complex.exp (((s : ℂ) * (t : ℂ) - I (s : ℂ)) / 2) / (entranceQ E t : ℂ)
    rw [hreal htT s hs.le, hI, sub_div, sub_eq_add_neg, Complex.exp_add]
    simp only [entranceCanonicalValue, entranceY, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_exp, Complex.ofReal_neg, neg_div]
    ring
  let C_t := (2 * L / entranceQ E t) * (max 1 T) ^ A
  have hCt : 0 < C_t := by dsimp [C_t]; positivity
  have hright (z : ℂ) (hz : 0 ≤ z.re) : ‖F z‖ ≤ C_t * (1 + ‖z‖) ^ k := by
    have he' := entrance_complex_primitive_growth E hlam hC htT hz
    have hH : ‖entranceComplexH E t z‖ ≤ L * ‖z‖ := by
      obtain ⟨hfin, hsup, h3, _, _, hd1, _⟩ := hrep htT
      let _ : IsFiniteMeasure (E.ν t) := hfin
      have hb' := (profile_complexLaplace_bounds hsup (profile_first_moment_integrable h3) hz).2.2
      have hdt : E.d t ≤ C * lam * T ^ 2 :=
        (le_abs_self _).trans ((E.bounds t htT).1.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ ht.1.le htT.2 _) (mul_nonneg hC.le hlam)))
      apply (norm_add_le _ _).trans
      rw [hd1] at hb'
      have h := mul_le_mul_of_nonneg_left hdt (by positivity : 0 ≤ 2 * ‖z‖)
      dsimp [L]
      linarith only [hb', h]
    have hbase : 1 + t * ‖z‖ ≤ max 1 T * (1 + ‖z‖) := by
      have hl : (1 : ℝ) ≤ max 1 T := le_max_left _ _
      have hmul := mul_le_mul_of_nonneg_right (htT.2.trans (le_max_right 1 T)) (norm_nonneg z)
      linarith only [hl, hmul]
    have hn : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
    have hpow : Real.exp (A * Real.log (1 + t * ‖z‖)) ≤
        (max 1 T) ^ A * (1 + ‖z‖) ^ ⌈A⌉₊ := by
      rw [mul_comm A, ← Real.rpow_def_of_pos (by positivity : 0 < 1 + t * ‖z‖)]
      calc
        _ ≤ (max 1 T * (1 + ‖z‖)) ^ A := Real.rpow_le_rpow (by positivity) hbase hA
        _ = (max 1 T) ^ A * (1 + ‖z‖) ^ A :=
          Real.mul_rpow (by positivity) (by positivity)
        _ ≤ _ := by
          rw [← Real.rpow_natCast]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (norm_nonneg _)) hn)
            (by positivity)
    rw [hFG hz]
    change ‖2 * entranceComplexH E t z * Complex.exp ((z * (t : ℂ) - I z) / 2) /
      (entranceQ E t : ℂ)‖ ≤ _
    rw [norm_div, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hQ]
    have hn2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hn2]
    have hPexp := (Real.exp_le_exp.mpr he').trans hpow
    calc
      _ ≤ 2 * (L * (1 + ‖z‖)) * ((max 1 T) ^ A * (1 + ‖z‖) ^ ⌈A⌉₊) /
          entranceQ E t := by
        gcongr
        · exact hH.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hL.le)
      _ = _ := by
        dsimp [C_t, k]
        rw [pow_succ]
        ring
  refine ⟨fun n => iteratedDeriv n F 0 / (n.factorial : ℂ), fun s hs => ?_⟩
  rw [← hFe s hs]
  exact profile_entire_polynomial hF hCt k hright hFleft (s : ℂ)

end EntrancePolynomial

/-- The highest coefficient vanishes when the two polynomial equations
give `d = w * b` and `d' = -w * b'`. The product `b*d` is constant,
which avoids differentiating the weight or taking its square root. -/
theorem profile_top_coefficient_zero {D M : ℝ} (hD : 0 < D)
    {w b d : ℝ → ℝ}
    (hw : ∀ t ∈ Ioc 0 D, 0 < w t ∧ w t ≤ M)
    (hrelation : ∀ t ∈ Ioc 0 D, d t = w t * b t)
    (htrace : Tendsto b (𝓝[>] 0) (𝓝 0))
    (hac : ∀ a, 0 < a → a ≤ D →
      AbsolutelyContinuousOnInterval b a D ∧ AbsolutelyContinuousOnInterval d a D)
    (hder : ∀ a, 0 < a → a ≤ D →
      ∀ᵐ t : ℝ, t ∈ Ioo a D → deriv d t = -(w t * deriv b t)) :
    ∀ t ∈ Ioc 0 D, b t = 0 ∧ d t = 0 := by
  have hconst (a : ℝ) (ha : 0 < a) (haD : a ≤ D) : b a * d a = b D * d D := by
    obtain ⟨hba, hda⟩ := hac a ha haD
    have hp : AbsolutelyContinuousOnInterval (fun t => b t * d t) a D := hba.fun_mul hda
    have hn : ∀ᵐ t : ℝ, t ∈ uIcc a D → HasDerivAt (fun t => b t * d t) 0 t := by
      filter_upwards [hba.ae_differentiableAt, hda.ae_differentiableAt, hder a ha haD,
        volume.ae_ne a, volume.ae_ne D] with t hb hd hode haa hDD ht
      have ht' : t ∈ Icc a D := uIcc_of_le haD ▸ ht
      have ht'' : t ∈ Ioo a D := ⟨lt_of_le_of_ne ht'.1 haa.symm, lt_of_le_of_ne ht'.2 hDD⟩
      have h := ((hb ht).hasDerivAt.mul (hd ht).hasDerivAt)
      have he : deriv b t * d t + b t * deriv d t = 0 := by
        rw [hode ht'', hrelation t ⟨ha.trans_le ht'.1, ht'.2⟩]
        ring
      rwa [he] at h
    obtain ⟨c, hc⟩ := hp.const_of_ae_hasDerivAt_zero hn
    exact (hc a left_mem_uIcc).trans (hc D right_mem_uIcc).symm
  have hprod_trace : Tendsto (fun t => b t * d t) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hh := (htrace.norm.pow 2).const_mul M
    simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] at hh
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hh
    filter_upwards [Ioc_mem_nhdsGT hD] with t ht
    obtain ⟨hw0, hwM⟩ := hw t ht
    rw [hrelation t ht, norm_mul, norm_mul, Real.norm_eq_abs (w t), abs_of_pos hw0]
    calc
      _ = w t * ‖b t‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hwM (sq_nonneg _)
  have hh : Tendsto (fun t => b t * d t) (𝓝[>] 0) (𝓝 (b D * d D)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioc_mem_nhdsGT hD] with t ht
    exact (hconst t ht.1 ht.2).symm
  have hzero : b D * d D = 0 := tendsto_nhds_unique hh hprod_trace
  intro t ht
  have hz := (hconst t ht.1 ht.2).trans hzero
  rw [hrelation t ht] at hz
  have hb : b t = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact (mul_eq_zero.mp h).resolve_left (hw t ht).1.ne'
  exact ⟨hb, by rw [hrelation t ht, hb, mul_zero]⟩

section TimeInterpolation

private theorem profile_ac_finsetSum {ι : Type*} {a b : ℝ} (S : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ S, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => ∑ i ∈ S, f i t) a b := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        ((LipschitzWith.const (α := ℝ) (0 : ℝ)).lipschitzOnWith
          (s := uIcc a b)).absolutelyContinuousOnInterval
  | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self _ _)).fun_add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

private theorem profile_interpolate_time_on {D : ℝ} {k : ℕ} {B : ℝ → ℝ → ℝ}
    {S₀ : Set ℝ} (hpos : ∀ i : ℕ, (i : ℝ) + 1 ∈ S₀)
    (hpoly : ∀ᵐ t : ℝ, t ∈ Ioc 0 D →
      ∃ p : Polynomial ℝ, p.degree < (k + 1 : ℕ) ∧ ∀ s ∈ S₀, p.eval s = B t s)
    (hB : ∀ s ∈ S₀, ContinuousOn (fun t => B t s) (Ioc 0 D))
    (hBac : ∀ s ∈ S₀, ∀ a, 0 < a → a ≤ D →
      AbsolutelyContinuousOnInterval (fun t => B t s) a D) :
    ∃ P : ℝ → Polynomial ℝ, (∀ t, (P t).degree < (k + 1 : ℕ)) ∧
      (∀ t ∈ Ioc 0 D, ∀ s ∈ S₀, (P t).eval s = B t s) ∧
      (∀ n a, 0 < a → a ≤ D →
        AbsolutelyContinuousOnInterval (fun t => (P t).coeff n) a D) ∧
      ∀ P₀ : Polynomial ℝ, P₀.degree < (k + 1 : ℕ) →
        (∀ s ∈ S₀, Tendsto (fun t => B t s) (𝓝[>] 0) (𝓝 (P₀.eval s))) →
        ∀ n, Tendsto (fun t => (P t).coeff n) (𝓝[>] 0) (𝓝 (P₀.coeff n)) := by
  classical
  let S := Finset.range (k + 1)
  let v : ℕ → ℝ := fun n => n + 1
  have hv : InjOn v (↑S : Set ℕ) := by
    intro i hi j hj hij
    apply Nat.cast_injective (R := ℝ)
    exact add_right_cancel hij
  have hnode (i : ℕ) : v i ∈ S₀ := hpos i
  let P : ℝ → Polynomial ℝ := fun t => Lagrange.interpolate S v (fun i => B t (v i))
  have hP t : P t = ∑ i ∈ S, Polynomial.C (B t (v i)) * Lagrange.basis S v i :=
    Lagrange.interpolate_apply _ _ _
  have hc (s : ℝ) : ContinuousOn (fun t => (P t).eval s) (Ioc 0 D) := by
    have he (t : ℝ) : (P t).eval s =
        ∑ i ∈ S, B t (v i) * (Lagrange.basis S v i).eval s := by
      rw [hP t]
      change Polynomial.evalRingHom s _ = _
      simp only [map_sum, map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C]
    simp_rw [he]
    exact continuousOn_finsetSum _ fun i _ => (hB _ (hnode i)).mul continuousOn_const
  have hp' : ∀ᵐ t : ℝ, t ∈ Ioc 0 D → ∀ s ∈ S₀, (P t).eval s = B t s := by
    filter_upwards [hpoly] with t ht hu
    obtain ⟨p, hpd, hpe⟩ := ht hu
    have hdeg : p.degree < (S.card : ℕ) := by simpa [S] using hpd
    have h := Lagrange.eq_interpolate_of_eval_eq (fun i => B t (v i)) hv hdeg
      (fun i _ => hpe _ (hnode i))
    change p = P t at h
    exact fun s hs => h ▸ hpe s hs
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro t
    simpa [P, S] using Lagrange.degree_interpolate_lt (fun i => B t (v i)) hv
  · intro t ht s hs
    have he : (fun u => (P u).eval s) =ᵐ[volume.restrict (Ioc 0 D)] (fun u => B u s) :=
      (ae_restrict_iff' measurableSet_Ioc).2 (hp'.mono fun u hu hm => hu hm s hs)
    exact (Measure.eqOn_Ioc_of_ae_eq volume he (hc s) (hB s hs)) ht
  · intro n a ha haD
    have he (t : ℝ) : (P t).coeff n =
        ∑ i ∈ S, B t (v i) * (Lagrange.basis S v i).coeff n := by
      rw [hP t, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul]
    simp_rw [he]
    exact profile_ac_finsetSum _ _ fun i _ => by
      simpa only [mul_comm] using
        (hBac (v i) (hnode i) a ha haD).const_mul ((Lagrange.basis S v i).coeff n)
  · intro P₀ hdeg hlim n
    have he (t : ℝ) : (P t).coeff n =
        ∑ i ∈ S, B t (v i) * (Lagrange.basis S v i).coeff n := by
      rw [hP t, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul]
    have he₀ : P₀.coeff n = ∑ i ∈ S, P₀.eval (v i) * (Lagrange.basis S v i).coeff n := by
      conv_lhs => rw [Lagrange.eq_interpolate (f := P₀) hv (by simpa [S] using hdeg)]
      simp only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
    simp_rw [he, he₀]
    exact tendsto_finsetSum S fun i _ => (hlim (v i) (hnode i)).mul_const _

/-- Interpolation at fixed positive arguments turns an almost-everywhere
degree bound into a polynomial family whose coefficients inherit absolute
continuity in time. -/
theorem profile_interpolate_time {D : ℝ} {k : ℕ} {B : ℝ → ℝ → ℝ}
    (hpoly : ∀ᵐ t : ℝ, t ∈ Ioc 0 D →
      ∃ p : Polynomial ℝ, p.degree < (k + 1 : ℕ) ∧ ∀ s > 0, p.eval s = B t s)
    (hB : ∀ s > 0, ContinuousOn (fun t => B t s) (Ioc 0 D))
    (hBac : ∀ s > 0, ∀ a, 0 < a → a ≤ D →
      AbsolutelyContinuousOnInterval (fun t => B t s) a D) :
    ∃ P : ℝ → Polynomial ℝ, (∀ t, (P t).degree < (k + 1 : ℕ)) ∧
      (∀ t ∈ Ioc 0 D, ∀ s > 0, (P t).eval s = B t s) ∧
      ∀ n a, 0 < a → a ≤ D →
        AbsolutelyContinuousOnInterval (fun t => (P t).coeff n) a D := by
  obtain ⟨P, hdeg, heq, hac, _⟩ := profile_interpolate_time_on (S₀ := Ioi 0)
    (fun i => show 0 < (i : ℝ) + 1 by positivity) hpoly hB hBac
  exact ⟨P, hdeg, heq, hac⟩

end TimeInterpolation

/-- The coefficient equations of the exponentially regularized canonical
system lower any finite degree bound to the degree of the entrance trace. -/
theorem profile_canonical_coefficients_reduce {D M : ℝ} {k₀ : ℕ} (hD : 0 < D)
    {w : ℝ → ℝ} {B J : ℕ → ℝ → ℝ}
    (hw : ∀ t ∈ Ioc 0 D, 0 < w t ∧ w t ≤ M)
    (hwc : ContinuousOn w (Ioc 0 D))
    (hac : ∀ n a, 0 < a → a ≤ D →
      AbsolutelyContinuousOnInterval (B n) a D ∧ AbsolutelyContinuousOnInterval (J n) a D)
    (htrace : ∀ n : ℕ, k₀ < n → Tendsto (B n) (𝓝[>] 0) (𝓝 0))
    (hode : ∀ a, 0 < a → a ≤ D → ∀ᵐ t : ℝ, t ∈ Ioo a D → ∀ n : ℕ,
      deriv (B (n + 1)) t = (B n t - J n t / w t) / 2 ∧
      deriv (J (n + 1)) t = (J n t - w t * B n t) / 2)
    (k : ℕ) (hk : ∀ n : ℕ, k < n → ∀ t ∈ Ioc 0 D, B n t = 0 ∧ J n t = 0) :
    ∀ n : ℕ, k₀ < n → ∀ t ∈ Ioc 0 D, B n t = 0 ∧ J n t = 0 := by
  induction k with
  | zero => exact fun n hn => hk n (by omega)
  | succ k ih =>
    by_cases htop : k₀ < k + 1
    · have hzeroDeriv (t : ℝ) (ht : t ∈ Ioo 0 D) : deriv (B (k + 1 + 1)) t = 0 := by
        apply HasDerivAt.deriv
        apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
        exact (hk _ (by omega) u ⟨hu.1, hu.2.le⟩).1
      have hrel : ∀ t ∈ Ioc 0 D, J (k + 1) t = w t * B (k + 1) t := by
        intro t ht
        let a := t / 2
        have ha : 0 < a := half_pos ht.1
        have hat : a < t := half_lt_self ht.1
        have haD := hat.le.trans ht.2
        have hae : J (k + 1) =ᵐ[volume.restrict (Ioc a D)] (fun u => w u * B (k + 1) u) := by
          rw [← restrict_Ioo_eq_restrict_Ioc]
          apply (ae_restrict_iff' measurableSet_Ioo).2
          filter_upwards [hode a ha haD] with u hu humem
          have hu0 := ha.trans humem.1
          have hh := (hu humem (k + 1)).1
          rw [hzeroDeriv u ⟨hu0, humem.2⟩] at hh
          have hpos := (hw u ⟨hu0, humem.2.le⟩).1
          have h := (sub_eq_zero.mp (by linarith only [hh] : B (k + 1) u - J (k + 1) u / w u = 0)).symm
          exact (div_eq_iff hpos.ne').mp h |>.trans (mul_comm _ _)
        have hh := hac (k + 1) a ha haD
        have h1 : ContinuousOn (B (k + 1)) (Ioc a D) :=
          (uIcc_of_le haD ▸ hh.1.continuousOn).mono Ioc_subset_Icc_self
        have h2 : ContinuousOn (J (k + 1)) (Ioc a D) :=
          (uIcc_of_le haD ▸ hh.2.continuousOn).mono Ioc_subset_Icc_self
        have h3 : ContinuousOn w (Ioc a D) :=
          hwc.mono fun u hu => ⟨ha.trans hu.1, hu.2⟩
        exact (Measure.eqOn_Ioc_of_ae_eq volume hae h2 (h3.mul h1)) ⟨hat, ht.2⟩
      have htopzero := profile_top_coefficient_zero hD hw hrel (htrace _ htop) (hac (k + 1))
        (fun a ha haD => by
          filter_upwards [hode a ha haD] with t ht hm
          have h := ht hm k
          have hpos := (hw t ⟨ha.trans hm.1, hm.2.le⟩).1
          rw [h.1, h.2]
          field_simp
          ring)
      apply ih
      intro n hn t ht
      rcases eq_or_lt_of_le (show k + 1 ≤ n by omega) with h | h
      · subst n
        exact htopzero t ht
      · exact hk n h t ht
    · exact fun n hn => hk n (by omega)

section CoefficientEquations

private noncomputable def profileTimeDerivative (k : ℕ) (P : ℝ → Polynomial ℝ) (t : ℝ) :
    Polynomial ℝ :=
  ∑ n ∈ Finset.range (k + 1), Polynomial.monomial n (deriv (fun u => (P u).coeff n) t)

private theorem profile_deriv_coeff_above_degree {a D t : ℝ} {k n : ℕ}
    {P : ℝ → Polynomial ℝ} (ht : t ∈ Ioo a D) (ha : 0 ≤ a)
    (hP : ∀ u ∈ Ioc 0 D, (P u).natDegree ≤ k) (hn : k < n) :
    deriv (fun u => (P u).coeff n) t = 0 := by
  apply HasDerivAt.deriv
  apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    ((hP u ⟨ha.trans_lt hu.1, hu.2.le⟩).trans_lt hn)

private theorem profileTimeDerivative_coeff {a D t : ℝ} {k : ℕ}
    {P : ℝ → Polynomial ℝ} (ht : t ∈ Ioo a D) (ha : 0 ≤ a)
    (hP : ∀ u ∈ Ioc 0 D, (P u).natDegree ≤ k) (n : ℕ) :
    (profileTimeDerivative k P t).coeff n = deriv (fun u => (P u).coeff n) t := by
  have hs : (profileTimeDerivative k P t).coeff n =
      if n ∈ Finset.range (k + 1) then deriv (fun u => (P u).coeff n) t else 0 := by
    classical
    simp [profileTimeDerivative, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [hs]
  split
  · rfl
  · rename_i hn
    exact (profile_deriv_coeff_above_degree ht ha hP (by simpa using hn)).symm

private theorem profileTimeDerivative_eval {a D t : ℝ} {k : ℕ}
    {P : ℝ → Polynomial ℝ} (ht : t ∈ Ioo a D) (ha : 0 ≤ a)
    (hP : ∀ u ∈ Ioc 0 D, (P u).natDegree ≤ k)
    (hd : ∀ n, DifferentiableAt ℝ (fun u => (P u).coeff n) t) (s : ℝ) :
    HasDerivAt (fun u => (P u).eval s) ((profileTimeDerivative k P t).eval s) t := by
  have hev : (profileTimeDerivative k P t).eval s =
      ∑ n ∈ Finset.range (k + 1), deriv (fun u => (P u).coeff n) t * s ^ n := by
    change Polynomial.evalRingHom s _ = _
    simp only [profileTimeDerivative, map_sum, Polynomial.coe_evalRingHom, Polynomial.eval_monomial]
  rw [hev]
  have hd' := HasDerivAt.fun_sum (u := Finset.range (k + 1))
    (fun n _ => ((hd n).hasDerivAt).mul_const (s ^ n))
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
  exact Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hP u ⟨ha.trans_lt hu.1, hu.2.le⟩)) s

/-- Time differentiation of polynomial entrance values can be done on their
coefficients. The canonical equations at the positive integers suffice
to identify both polynomial identities. -/
theorem profile_canonical_polynomial_equations {a D : ℝ} {k : ℕ} (ha : 0 ≤ a)
    {w : ℝ → ℝ} {P Q : ℝ → Polynomial ℝ}
    (hP : ∀ t ∈ Ioc 0 D, (P t).natDegree ≤ k)
    (hQ : ∀ t ∈ Ioc 0 D, (Q t).natDegree ≤ k)
    (hPac : ∀ n, AbsolutelyContinuousOnInterval (fun t => (P t).coeff n) a D)
    (hQac : ∀ n, AbsolutelyContinuousOnInterval (fun t => (Q t).coeff n) a D)
    (hspec : ∀ n : ℕ, ∀ᵐ t : ℝ, t ∈ Ioo a D →
      let s : ℝ := n + 1
      HasDerivAt (fun u => (P u).eval s) (s / 2 * ((P t).eval s - (Q t).eval s / w t)) t ∧
      HasDerivAt (fun u => (Q u).eval s) (s / 2 * ((Q t).eval s - w t * (P t).eval s)) t) :
    ∀ᵐ t : ℝ, t ∈ Ioo a D → ∀ n : ℕ,
      deriv (fun u => (P u).coeff (n + 1)) t = ((P t).coeff n - (Q t).coeff n / w t) / 2 ∧
      deriv (fun u => (Q u).coeff (n + 1)) t = ((Q t).coeff n - w t * (P t).coeff n) / 2 := by
  have hspec' := ae_all_iff.mpr hspec
  have hdP := ae_all_iff.mpr (fun n => (hPac n).ae_differentiableAt)
  have hdQ := ae_all_iff.mpr (fun n => (hQac n).ae_differentiableAt)
  filter_upwards [hspec', hdP, hdQ] with t hspec' hdP hdQ ht n
  have hu : t ∈ uIcc a D := uIcc_of_le (ht.1.le.trans ht.2.le) ▸ Ioo_subset_Icc_self ht
  let v : ℕ → ℝ := fun j => j + 1
  have hv : Function.Injective v := fun _ _ h => Nat.cast_injective (R := ℝ) (add_right_cancel h)
  have hP' : profileTimeDerivative k P t =
      Polynomial.C (1 / 2) * (Polynomial.X * (P t - Polynomial.C (w t)⁻¹ * Q t)) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective hv).mono
    rintro s ⟨j, rfl⟩
    have h := (profileTimeDerivative_eval ht ha hP (fun n => hdP n hu) (v j)).unique
      (hspec' j ht).1
    change (profileTimeDerivative k P t).eval (v j) = _
    rw [h]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_sub]
    ring
  have hQ' : profileTimeDerivative k Q t =
      Polynomial.C (1 / 2) * (Polynomial.X * (Q t - Polynomial.C (w t) * P t)) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective hv).mono
    rintro s ⟨j, rfl⟩
    have h := (profileTimeDerivative_eval ht ha hQ (fun n => hdQ n hu) (v j)).unique
      (hspec' j ht).2
    change (profileTimeDerivative k Q t).eval (v j) = _
    rw [h]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_sub]
    ring
  constructor
  · rw [← profileTimeDerivative_coeff ht ha hP, hP', Polynomial.coeff_C_mul,
      Polynomial.coeff_X_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    ring
  · rw [← profileTimeDerivative_coeff ht ha hQ, hQ', Polynomial.coeff_C_mul,
      Polynomial.coeff_X_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    ring

end CoefficientEquations

section AbstractRigidity

private theorem profile_ae_Ioo_of_local {D : ℝ} (hD : 0 < D) {p : ℝ → Prop}
    (h : ∀ a, 0 < a → a ≤ D → ∀ᵐ t : ℝ, t ∈ Ioo a D → p t) :
    ∀ᵐ t : ℝ, t ∈ Ioo 0 D → p t := by
  let a : ℕ → ℝ := fun n => min (D / 2) (1 / (n + 1 : ℝ))
  have ha (n : ℕ) : 0 < a n := lt_min (half_pos hD) (by positivity)
  have haD (n : ℕ) : a n ≤ D := (min_le_left _ _).trans (half_lt_self hD).le
  have hae := ae_all_iff.mpr (fun n => h (a n) (ha n) (haD n))
  filter_upwards [hae] with t ht ht'
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht'.1
  exact ht n ⟨(min_le_right _ _).trans_lt hn, ht'.2⟩

private theorem profile_natDegree_le_of_degree_lt {k : ℕ} {p : Polynomial ℝ}
    (h : p.degree < (k + 1 : ℕ)) : p.natDegree ≤ k := by
  by_cases hp : p = 0
  · simp [hp]
  · exact Nat.lt_succ_iff.mp ((Polynomial.natDegree_lt_iff_degree_lt hp).mpr h)

/-- A finite polynomial bound for the regularized value becomes a quadratic
bound under the canonical equations and the quadratic entrance trace.
For the degree argument one extra spectral factor makes the flux polynomial
without a division at spectral parameter zero. -/
theorem profile_regularized_degree_two {D M : ℝ} {k : ℕ} (hD : 0 < D) (hk : 2 ≤ k)
    {w : ℝ → ℝ} {B J : ℝ → ℝ → ℝ}
    (hw : ∀ t ∈ Ioc 0 D, 0 < w t ∧ w t ≤ M) (hwc : ContinuousOn w (Ioc 0 D))
    (hpoly : ∀ᵐ t : ℝ, t ∈ Ioc 0 D →
      ∃ p : Polynomial ℝ, p.degree < (k + 1 : ℕ) ∧ ∀ s > 0, p.eval s = B t s)
    (hBc : ∀ s > 0, ContinuousOn (fun t => B t s) (Ioc 0 D))
    (hJc : ∀ s > 0, ContinuousOn (fun t => J t s) (Ioc 0 D))
    (hBac : ∀ s > 0, ∀ a, 0 < a → a ≤ D →
      AbsolutelyContinuousOnInterval (fun t => B t s) a D)
    (hJac : ∀ s > 0, ∀ a, 0 < a → a ≤ D →
      AbsolutelyContinuousOnInterval (fun t => J t s) a D)
    (htrace : ∀ s > 0, Tendsto (fun t => B t s) (𝓝[>] 0) (𝓝 (s ^ 2)))
    (hode : ∀ s > 0, ∀ a, 0 < a → a ≤ D → ∀ᵐ t : ℝ, t ∈ Ioo a D →
      HasDerivAt (fun u => B u s) (s / 2 * (B t s - J t s / w t)) t ∧
      HasDerivAt (fun u => J u s) (s / 2 * (J t s - w t * B t s)) t) :
    ∃ P : ℝ → Polynomial ℝ, (∀ t ∈ Ioc 0 D, (P t).natDegree ≤ 2) ∧
      (∀ t ∈ Ioc 0 D, ∀ s > 0, (P t).eval s = B t s) ∧
      ∀ n a, 0 < a → a ≤ D →
        AbsolutelyContinuousOnInterval (fun t => (P t).coeff n) a D := by
  classical
  obtain ⟨P, hPdeg, hPeq, hPac, hPtrace⟩ := profile_interpolate_time_on (S₀ := Ioi 0)
    (fun i => show 0 < (i : ℝ) + 1 by positivity) hpoly hBc hBac
  have hPndeg (t : ℝ) (_ : t ∈ Ioc 0 D) : (P t).natDegree ≤ k :=
    profile_natDegree_le_of_degree_lt (hPdeg t)
  let U : ℝ → Polynomial ℝ := fun t => Polynomial.X * P t
  have hUdeg (t : ℝ) (ht : t ∈ Ioc 0 D) : (U t).natDegree ≤ k + 1 := by
    by_cases hz : P t = 0
    · simp [U, hz]
    · simpa only [U, Polynomial.natDegree_X_mul hz] using Nat.succ_le_succ (hPndeg t ht)
  have hUac (n : ℕ) (a : ℝ) (ha : 0 < a) (haD : a ≤ D) :
      AbsolutelyContinuousOnInterval (fun t => (U t).coeff n) a D := by
    cases n with
    | zero =>
        simpa only [U, Polynomial.coeff_X_mul_zero] using
          ((LipschitzWith.const (α := ℝ) (0 : ℝ)).lipschitzOnWith
            (s := uIcc a D)).absolutelyContinuousOnInterval
    | succ n => simpa only [U, Polynomial.coeff_X_mul] using hPac n a ha haD
  have hUtrace (n : ℕ) (hn : 3 < n) :
      Tendsto (fun t => (U t).coeff n) (𝓝[>] 0) (𝓝 0) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hdegree : ((Polynomial.X : Polynomial ℝ) ^ 2).degree < (k + 1 : ℕ) := by
      rw [Polynomial.degree_X_pow]
      exact_mod_cast (show 2 < k + 1 by omega)
    have hlim := hPtrace ((Polynomial.X : Polynomial ℝ) ^ 2) hdegree
      (fun s hs => by simpa only [Polynomial.eval_pow, Polynomial.eval_X] using htrace s hs) j
    simpa [U, Polynomial.coeff_X_mul, Polynomial.coeff_X_pow,
      show j ≠ 2 by omega, show 2 ≠ j by omega] using hlim
  let S₀ : Set ℝ := range (fun n : ℕ => (n : ℝ) + 1)
  have hnode (n : ℕ) : (n : ℝ) + 1 ∈ S₀ := ⟨n, rfl⟩
  have hSpos {s : ℝ} (hs : s ∈ S₀) : 0 < s := by
    obtain ⟨n, rfl⟩ := hs
    positivity
  have hdiff : ∀ᵐ t : ℝ, t ∈ Ioo 0 D → ∀ n,
      DifferentiableAt ℝ (fun u => (P u).coeff n) t := by
    apply profile_ae_Ioo_of_local hD
    intro a ha haD
    have hh := ae_all_iff.mpr (fun n => (hPac n a ha haD).ae_differentiableAt)
    filter_upwards [hh] with t ht hmem n
    exact ht n (uIcc_of_le haD ▸ Ioo_subset_Icc_self hmem)
  have hodes : ∀ᵐ t : ℝ, t ∈ Ioo 0 D → ∀ n : ℕ,
      let s : ℝ := n + 1
      HasDerivAt (fun u => B u s) (s / 2 * (B t s - J t s / w t)) t := by
    apply profile_ae_Ioo_of_local hD
    intro a ha haD
    have hh := ae_all_iff.mpr (fun n : ℕ => hode ((n : ℝ) + 1) (by positivity) a ha haD)
    filter_upwards [hh] with t ht hm n
    exact (ht n hm).1
  have hpolyJ : ∀ᵐ t : ℝ, t ∈ Ioc 0 D →
      ∃ p : Polynomial ℝ, p.degree < ((k + 1) + 1 : ℕ) ∧
        ∀ s ∈ S₀, p.eval s = s * J t s := by
    filter_upwards [hdiff, hodes, volume.ae_ne D] with t hdt hod htD ht
    have ht' : t ∈ Ioo 0 D := ⟨ht.1, lt_of_le_of_ne ht.2 htD⟩
    let R := profileTimeDerivative k P t
    have hR : R.natDegree ≤ k := by
      apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      rw [profileTimeDerivative_coeff ht' le_rfl hPndeg]
      exact profile_deriv_coeff_above_degree ht' le_rfl hPndeg hn
    let V := Polynomial.C (w t) * (U t - Polynomial.C 2 * R)
    have hVdeg : V.natDegree ≤ k + 1 := by
      apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      simp only [V, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
        Polynomial.coeff_eq_zero_of_natDegree_lt ((hUdeg t ht).trans_lt hn),
        Polynomial.coeff_eq_zero_of_natDegree_lt (hR.trans_lt (by omega : k < n)),
        mul_zero, sub_zero]
    refine ⟨V, (Polynomial.natDegree_le_iff_degree_le.mp hVdeg).trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _)), ?_⟩
    rintro s ⟨j, rfl⟩
    let s : ℝ := j + 1
    have hs : 0 < s := by dsimp [s]; positivity
    have he := profileTimeDerivative_eval ht' le_rfl hPndeg (hdt ht') s
    have he' : HasDerivAt (fun u => B u s) (R.eval s) t := by
      apply he.congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds ht'.1 ht'.2] with u hu
      exact (hPeq u ⟨hu.1, hu.2.le⟩ s hs).symm
    have heval := he'.unique (hod ht' j)
    change V.eval s = s * J t s
    simp only [V, U, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_sub]
    rw [hPeq t ht s hs, heval]
    have hw0 := (hw t ht).1.ne'
    field_simp
    ring
  obtain ⟨V, hVdeg, hVeq, hVac, _⟩ := profile_interpolate_time_on hnode hpolyJ
    (fun s hs => continuousOn_const.mul (hJc s (hSpos hs)))
    (fun s hs a ha haD => (hJac s (hSpos hs) a ha haD).const_mul s)
  have hVndeg (t : ℝ) (_ : t ∈ Ioc 0 D) : (V t).natDegree ≤ k + 1 :=
    profile_natDegree_le_of_degree_lt (hVdeg t)
  have hUeq (t : ℝ) (ht : t ∈ Ioc 0 D) (s : ℝ) (hs : 0 < s) :
      (U t).eval s = s * B t s := by
    simp [U, hPeq t ht s hs]
  have hod' (a : ℝ) (ha : 0 < a) (haD : a ≤ D) :=
    profile_canonical_polynomial_equations ha.le hUdeg hVndeg (fun n => hUac n a ha haD)
      (fun n => hVac n a ha haD) (fun n => by
        let s : ℝ := n + 1
        have hs : 0 < s := by dsimp [s]; positivity
        filter_upwards [hode s hs a ha haD] with t ht hmem
        have htt : t ∈ Ioc 0 D := ⟨ha.trans hmem.1, hmem.2.le⟩
        have hUev : (fun u => (U u).eval s) =ᶠ[𝓝 t] (fun u => s * B u s) := by
          filter_upwards [Ioo_mem_nhds htt.1 hmem.2] with u hu
          exact hUeq u ⟨hu.1, hu.2.le⟩ s hs
        have hVev : (fun u => (V u).eval s) =ᶠ[𝓝 t] (fun u => s * J u s) := by
          filter_upwards [Ioo_mem_nhds htt.1 hmem.2] with u hu
          exact hVeq u ⟨hu.1, hu.2.le⟩ s (hnode n)
        change HasDerivAt (fun u => (U u).eval s)
            (s / 2 * ((U t).eval s - (V t).eval s / w t)) t ∧
          HasDerivAt (fun u => (V u).eval s)
            (s / 2 * ((V t).eval s - w t * (U t).eval s)) t
        rw [hUeq t htt s hs, hVeq t htt s (hnode n)]
        refine ⟨?_, ?_⟩
        · convert (((ht hmem).1.const_mul s).congr_of_eventuallyEq hUev) using 1
          ring
        · convert (((ht hmem).2.const_mul s).congr_of_eventuallyEq hVev) using 1
          ring)
  have hz := profile_canonical_coefficients_reduce hD hw hwc
    (fun n a ha haD => ⟨hUac n a ha haD, hVac n a ha haD⟩) hUtrace hod' (k + 1)
    (fun n hn t ht => ⟨Polynomial.coeff_eq_zero_of_natDegree_lt ((hUdeg t ht).trans_lt hn),
      Polynomial.coeff_eq_zero_of_natDegree_lt ((hVndeg t ht).trans_lt hn)⟩)
  refine ⟨P, ?_, hPeq, hPac⟩
  intro t ht
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have h := (hz (n + 1) (by omega) t ht).1
  simpa only [U, Polynomial.coeff_X_mul] using h

end AbstractRigidity

section EntranceQuadratic

private theorem profile_positive_time_continuousOn {D : ℝ} {f : ℝ → ℝ}
    (h : ∀ a, 0 < a → a ≤ D → AbsolutelyContinuousOnInterval f a D) :
    ContinuousOn f (Ioc 0 D) := by
  intro t ht
  let a := t / 2
  have ha : 0 < a := half_pos ht.1
  have hat : a < t := half_lt_self ht.1
  have haD := hat.le.trans ht.2
  have hc : ContinuousOn f (Icc a D) := uIcc_of_le haD ▸ (h a ha haD).continuousOn
  apply (hc t ⟨hat.le, ht.2⟩).mono_left
  apply nhdsWithin_le_of_mem
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hat)] with u hu hu'
  exact ⟨hu'.le, hu.2⟩

private theorem entrance_regularized_moments_ac {T lam α C : ℝ} (E : EntranceData T lam α C)
    (hlam : 0 ≤ lam) (hC : 0 < C) {a D : ℝ}
    (ha : 0 < a) (haD : a ≤ D) (hDT : D ≤ T) :
    AbsolutelyContinuousOnInterval (entranceQ E) a D ∧
      AbsolutelyContinuousOnInterval (entranceR E) a D := by
  have hT := ha.trans_le (haD.trans hDT)
  have hsub : uIcc a D ⊆ Icc a T := by
    rw [uIcc_of_le haD]
    exact Icc_subset_Icc_right hDT
  have hsub₀ : uIcc a D ⊆ uIcc 0 T := by
    rw [uIcc_of_le haD, uIcc_of_le hT.le]
    exact Icc_subset_Icc ha.le hDT
  obtain ⟨_, hd, hK, hP⟩ := E.lipschitz a ha
  have hd := (hd.mono hsub).absolutelyContinuousOnInterval
  have hK := (hK.mono hsub).absolutelyContinuousOnInterval
  have hP := (hP.mono hsub).absolutelyContinuousOnInterval
  obtain ⟨hdint, hKint⟩ := entrance_moment_integrable E hlam hC hT
  have hI := (hdint.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).mono hsub₀
  have hJ := (hKint.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).mono hsub₀
  exact ⟨hK.sub (hd.mul hI), hP.sub ((hd.const_mul 3).mul hJ)⟩

/-- The real exponentially regularized entrance value. -/
noncomputable def entranceExpValue {T lam α C : ℝ}
    (E : EntranceData T lam α C) (t s : ℝ) : ℝ :=
  Real.exp (s * t / 2) * entranceCanonicalValue E t s

private noncomputable def entranceExpFlux {T lam α C : ℝ}
    (E : EntranceData T lam α C) (t s : ℝ) : ℝ :=
  Real.exp (s * t / 2) * entranceCanonicalFlux E t s

private theorem entrance_exp_ode_ae {T lam C : ℝ}
    (hT : 0 < T) (hlam : 0 ≤ lam) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ D ≤ T ∧
      ∀ {α : ℝ} (E : EntranceData T lam α C) (s : ℝ), 0 < s →
        ∀ a : ℝ, 0 < a → a ≤ D → ∀ᵐ t : ℝ, t ∈ Ioo a D →
          HasDerivAt (fun u => entranceExpValue E u s)
            (s / 2 * (entranceExpValue E t s - entranceExpFlux E t s / entranceW E t)) t ∧
          HasDerivAt (fun u => entranceExpFlux E u s)
            (s / 2 * (entranceExpFlux E t s - entranceW E t * entranceExpValue E t s)) t := by
  obtain ⟨D, hD, hDT, hode⟩ := entrance_canonical_ode_ae hT hlam hC
  refine ⟨D, hD, hDT, ?_⟩
  intro α E s hs a ha haD
  filter_upwards [hode E ha haD hs] with t ht hu
  obtain ⟨hx, hz⟩ := ht hu
  have hlin : HasDerivAt (fun u => s * u / 2) (s / 2) t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul s).div_const 2
  refine ⟨?_, ?_⟩
  · convert hlin.exp.mul hx using 1
    · rfl
    · unfold entranceExpValue entranceExpFlux
      ring
  · convert hlin.exp.mul hz using 1
    · rfl
    · unfold entranceExpValue entranceExpFlux
      ring

private theorem entrance_expValue_cast {T lam α C : ℝ}
    (E : EntranceData T lam α C) (t s : ℝ) :
    (entranceExpValue E t s : ℂ) =
      Complex.exp ((s : ℂ) * (t : ℂ) / 2) * (entranceCanonicalValue E t s : ℂ) := by
  simp only [entranceExpValue, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_div, Complex.ofReal_ofNat]

private theorem profile_real_polynomial_of_complex_sum {k : ℕ} {f : ℝ → ℝ} {b : ℕ → ℂ}
    (h : ∀ s : ℝ, 0 < s → (f s : ℂ) = ∑ n ∈ Finset.range (k + 1), b n * (s : ℂ) ^ n) :
    ∃ P : Polynomial ℝ, P.degree < (k + 1 : ℕ) ∧ ∀ s > 0, P.eval s = f s := by
  classical
  let P := ∑ n ∈ Finset.range (k + 1), Polynomial.monomial n (b n).re
  refine ⟨P, (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_, ?_⟩
  · intro n hn
    have hmem : n ∉ Finset.range (k + 1) := by simpa using hn
    simp [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, hmem]
  · intro s hs
    have h' := congrArg Complex.reCLM (h s hs)
    rw [map_sum] at h'
    change f s = _ at h'
    change Polynomial.evalRingHom s (∑ n ∈ Finset.range (k + 1),
      Polynomial.monomial n (b n).re) = f s
    simp only [map_sum, Polynomial.coe_evalRingHom, Polynomial.eval_monomial]
    simpa [Complex.reCLM_apply, ← Complex.ofReal_pow, Complex.mul_re] using h'.symm

/-- The regularized entrance transform is quadratic on the common initial
interval. Its constant coefficient vanishes by the value of the entire
extension at spectral parameter zero. -/
theorem entrance_expValue_quadratic {T lam C : ℝ}
    (hT : 0 < T) (hlam : 0 ≤ lam) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ D ≤ T ∧
      ∀ {α : ℝ} (E : EntranceData T lam α C),
        ∃ P : ℝ → Polynomial ℝ, (∀ t ∈ Ioc 0 D,
          (P t).natDegree ≤ 2 ∧ (P t).coeff 0 = 0 ∧
            ∀ s > 0, (P t).eval s = entranceExpValue E t s) ∧
          ∀ n a, 0 < a → a ≤ D →
            AbsolutelyContinuousOnInterval (fun t => (P t).coeff n) a D := by
  obtain ⟨D₁, hD₁, hD₁T, k, hpoly⟩ := entrance_canonical_polynomial hT hlam hC
  obtain ⟨D₂, hD₂, hD₂T, hb⟩ := entrance_regularization_bounds hT hlam hC
  obtain ⟨D₃, hD₃, hD₃T, hode⟩ := entrance_exp_ode_ae hT hlam hC
  obtain ⟨D₄, hD₄, hD₄T, hful⟩ := entrance_canonical_entire hT hlam hC
  let D := min D₁ (min D₂ (min D₃ D₄))
  have hD : 0 < D := lt_min hD₁ (lt_min hD₂ (lt_min hD₃ hD₄))
  have hle₁ : D ≤ D₁ := min_le_left _ _
  have hle₂ : D ≤ D₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hle₃ : D ≤ D₃ :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hle₄ : D ≤ D₄ :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hDT := hle₁.trans hD₁T
  refine ⟨D, hD, hDT, ?_⟩
  intro α E
  let L : ℝ := C⁻¹ / 2
  let U : ℝ := C + C⁻¹ / 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hb' (t : ℝ) (ht : t ∈ Ioc 0 D) :
      L * t ≤ entranceQ E t ∧ entranceQ E t ≤ U * t ∧
        L * t ^ 2 ≤ entranceR E t ∧ entranceR E t ≤ U * t ^ 2 :=
    hb E ⟨ht.1, ht.2.trans hle₂⟩
  have hQ (t : ℝ) (ht : t ∈ Ioc 0 D) : 0 < entranceQ E t :=
    (mul_pos hL ht.1).trans_le (hb' t ht).1
  have hR (t : ℝ) (ht : t ∈ Ioc 0 D) : 0 < entranceR E t :=
    (mul_pos hL (sq_pos_of_pos ht.1)).trans_le (hb' t ht).2.2.1
  have hw (t : ℝ) (ht : t ∈ Ioc 0 D) : 0 < entranceW E t ∧ entranceW E t ≤ U ^ 2 / L := by
    refine ⟨div_pos (sq_pos_of_pos (hQ t ht)) (hR t ht), ?_⟩
    apply (div_le_iff₀ (hR t ht)).2
    calc
      _ ≤ (U * t) ^ 2 := pow_le_pow_left₀ (hQ t ht).le (hb' t ht).2.1 _
      _ = U ^ 2 / L * (L * t ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb' t ht).2.2.1 (by positivity)
  have hwc : ContinuousOn (entranceW E) (Ioc 0 D) := by
    have hQc := profile_positive_time_continuousOn
      (fun a ha haD => (entrance_regularized_moments_ac E hlam hC ha haD hDT).1)
    have hRc := profile_positive_time_continuousOn
      (fun a ha haD => (entrance_regularized_moments_ac E hlam hC ha haD hDT).2)
    exact (hQc.pow 2).div hRc (fun t ht => (hR t ht).ne')
  have hpoly' : ∀ᵐ t : ℝ, t ∈ Ioc 0 D →
      ∃ p : Polynomial ℝ, p.degree < (max k 2 + 1 : ℕ) ∧
        ∀ s > 0, p.eval s = entranceExpValue E t s := by
    filter_upwards [hpoly E] with t ht h
    obtain ⟨b, he⟩ := ht ⟨h.1, h.2.trans hle₁⟩
    obtain ⟨p, hp, hpe⟩ := profile_real_polynomial_of_complex_sum
      (fun s hs => (entrance_expValue_cast E t s).trans (he s hs))
    have hdeg : (k + 1 : ℕ) ≤ max k 2 + 1 := Nat.succ_le_succ (le_max_left _ _)
    exact ⟨p, hp.trans_le (WithBot.coe_le_coe.mpr hdeg), hpe⟩
  have hExpAC (s a : ℝ) : AbsolutelyContinuousOnInterval (fun t => Real.exp (s * t / 2)) a D := by
    have hd : ContDiff ℝ 1 (fun t : ℝ => Real.exp (s * t / 2)) := by fun_prop
    exact hd.contDiffOn.absolutelyContinuousOnInterval
  have hAC (s : ℝ) (hs : 0 < s) (a : ℝ) (ha : 0 < a) (haD : a ≤ D) :
      AbsolutelyContinuousOnInterval (fun t => entranceExpValue E t s) a D ∧
        AbsolutelyContinuousOnInterval (fun t => entranceExpFlux E t s) a D := by
    obtain ⟨hx, hz⟩ := entrance_canonical_ac E hlam hC ha haD hDT hs.le
      (fun t ht => hQ t ⟨ha.trans_le ht.1, ht.2⟩) (fun t ht => hR t ⟨ha.trans_le ht.1, ht.2⟩)
    exact ⟨(hExpAC s a).fun_mul hx, (hExpAC s a).fun_mul hz⟩
  have htr (s : ℝ) (hs : 0 < s) :
      Tendsto (fun t => entranceExpValue E t s) (𝓝[>] 0) (𝓝 (s ^ 2)) := by
    have hcont : Continuous (fun t : ℝ => Real.exp (s * t / 2)) := by fun_prop
    have hExp : Tendsto (fun t : ℝ => Real.exp (s * t / 2)) (𝓝[>] 0) (𝓝 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using hcont.tendsto 0)
    simpa only [entranceExpValue, one_mul] using
      hExp.mul (entrance_canonical_traces E hT hlam hC hs).1
  have hode' (s : ℝ) (hs : 0 < s) (a : ℝ) (ha : 0 < a) (haD : a ≤ D) :
      ∀ᵐ t : ℝ, t ∈ Ioo a D →
        HasDerivAt (fun u => entranceExpValue E u s)
          (s / 2 * (entranceExpValue E t s - entranceExpFlux E t s / entranceW E t)) t ∧
        HasDerivAt (fun u => entranceExpFlux E u s)
          (s / 2 * (entranceExpFlux E t s - entranceW E t * entranceExpValue E t s)) t := by
    filter_upwards [hode E s hs a ha (haD.trans hle₃)] with t ht hu
    exact ht ⟨hu.1, hu.2.trans_le hle₃⟩
  obtain ⟨P, hPdeg, hPev, hPac⟩ := profile_regularized_degree_two hD (le_max_right k 2) hw hwc hpoly'
    (fun s hs => profile_positive_time_continuousOn (fun a ha haD => (hAC s hs a ha haD).1))
    (fun s hs => profile_positive_time_continuousOn (fun a ha haD => (hAC s hs a ha haD).2))
    (fun s hs a ha haD => (hAC s hs a ha haD).1) (fun s hs a ha haD => (hAC s hs a ha haD).2) htr hode'
  refine ⟨P, fun t ht => ⟨hPdeg t ht, ?_, hPev t ht⟩, hPac⟩
  obtain ⟨F, hF, hF0, hFreal, _⟩ := hful E t ⟨ht.1, ht.2.trans hle₄⟩
  have hFcont : Continuous (fun s : ℝ => F (s : ℂ)) :=
    hF.continuous.comp Complex.continuous_ofReal
  have hF0' : Tendsto (fun s : ℝ => F (s : ℂ)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by simpa only [Complex.ofReal_zero, hF0] using hFcont.tendsto 0)
  have hPcont : Continuous (fun s : ℝ => (↑((P t).eval s) : ℂ)) :=
    Complex.continuous_ofReal.comp (Polynomial.continuous _)
  have hP0 : Tendsto (fun s : ℝ => F (s : ℂ)) (𝓝[>] 0) (𝓝 (↑((P t).eval 0) : ℂ)) := by
    apply (tendsto_nhdsWithin_of_tendsto_nhds (hPcont.tendsto 0)).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 0 < s := hs
    rw [hPev t ht s hs', entrance_expValue_cast, hFreal s hs']
  have h := tendsto_nhds_unique hP0 hF0'
  exact_mod_cast (show ((P t).coeff 0 : ℂ) = 0 by simpa only [Polynomial.coeff_zero_eq_eval_zero] using h)

end EntranceQuadratic

section EntranceFactor

private theorem profile_eqOn_positive_of_rat {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Ioi 0)) (hg : ContinuousOn g (Ioi 0))
    (he : ∀ s : ℚ, 0 < (s : ℝ) → f s = g s) : EqOn f g (Ioi 0) := by
  let R := range (fun s : ℚ => (s : ℝ))
  have hd : Dense R := Rat.denseRange_cast
  have h : EqOn f g (R ∩ Ioi 0) := by
    rintro s ⟨⟨q, rfl⟩, hs⟩
    exact he q hs
  exact h.of_subset_closure hf hg inter_subset_right
    (by simpa only [inter_comm] using hd.open_subset_closure_inter (isOpen_Ioi (a := (0 : ℝ))))

private theorem profile_factor_algebra {s Q R H y p q p' q' : ℝ}
    (hs : s ≠ 0) (hQ : Q ≠ 0) (hR : R ≠ 0)
    (hb : 2 * H * y / Q = s * p + s ^ 2 * q)
    (hz : 2 * s * y * (Q - 2 * H / s ^ 2) / R =
      Q ^ 2 / R * (s * p + s ^ 2 * q - 2 * (s * p' + s ^ 2 * q') / s)) :
    s * y = (Q * q / 2) * s ^ 2 + (Q * p / 2 + q - Q * q') * s + (p - Q * p') := by
  calc
    s * y = (R / (2 * Q)) * (2 * s * y * (Q - 2 * H / s ^ 2) / R) +
      (2 * H * y / Q) / s := by
        field_simp
        ring
    _ = _ := by
      rw [hz, hb]
      field_simp
      ring

private theorem profile_factor_linear_of_quadratic {y : ℝ → ℝ} {A B C : ℝ}
    (hy0 : Tendsto y (𝓝[>] 0) (𝓝 1))
    (h : ∀ s > 0, s * y s = A * s ^ 2 + B * s + C) :
    ∀ s > 0, y s = 1 + A * s := by
  have hId : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hpoly : Continuous (fun s : ℝ => A * s ^ 2 + B * s + C) := by fun_prop
  have hpoly0 : Tendsto (fun s : ℝ => A * s ^ 2 + B * s + C) (𝓝[>] 0) (𝓝 C) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by simpa using hpoly.tendsto 0)
  have hyC : Tendsto (fun s => s * y s) (𝓝[>] 0) (𝓝 C) := by
    apply hpoly0.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (h s hs).symm
  have hC : C = 0 := tendsto_nhds_unique hyC (by simpa using hId.mul hy0)
  have hyB (s : ℝ) (hs : 0 < s) : y s = B + A * s := by
    have he := h s hs
    rw [hC, add_zero, show A * s ^ 2 + B * s = s * (B + A * s) by ring] at he
    exact mul_left_cancel₀ hs.ne' he
  have hh : Tendsto y (𝓝[>] 0) (𝓝 B) := by
    have hc : Continuous (fun s : ℝ => B + A * s) := by fun_prop
    have ht : Tendsto (fun s : ℝ => B + A * s) (𝓝[>] 0) (𝓝 B) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using hc.tendsto 0)
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hyB s hs).symm
  rw [← tendsto_nhds_unique hh hy0]
  exact hyB

end EntranceFactor

section EntranceRational

open intervalIntegral

private noncomputable def entranceExpFactor {T lam α C : ℝ}
    (E : EntranceData T lam α C) (t s : ℝ) : ℝ :=
  Real.exp ((s * t - timeIntegral (fun u => E.H u s) 0 t) / 2)

private theorem entrance_complex_timeIntegral_real {T lam α C : ℝ}
    (E : EntranceData T lam α C) {t : ℝ} (ht : t ∈ Ioc 0 T) {s : ℝ} (hs : 0 ≤ s) :
    (∫ u in (0 : ℝ)..t, entranceComplexH E u (s : ℂ)) =
      (↑(timeIntegral (fun u => E.H u s) 0 t) : ℂ) := by
  rw [timeIntegral, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_ae
  rw [uIoc_of_le ht.1.le]
  filter_upwards [entranceComplexH_real_ae E] with u hu hmem
  exact hu ⟨hmem.1, hmem.2.trans ht.2⟩ s hs

private theorem entrance_expFactor_continuous {T lam α C : ℝ}
    (E : EntranceData T lam α C) (hlam : 0 ≤ lam) (hC : 0 < C)
    {t : ℝ} (ht : t ∈ Ioc 0 T) :
    ContinuousOn (entranceExpFactor E t) (Ici 0) ∧
      Tendsto (entranceExpFactor E t) (𝓝[>] 0) (𝓝 1) := by
  have hp := (entrance_complex_primitive E hlam hC ht).2
  have hr : ContinuousOn (fun s : ℝ => (∫ u in (0 : ℝ)..t, entranceComplexH E u (s : ℂ)).re)
      (Ici 0) :=
    Complex.continuous_re.comp_continuousOn
      (hp.comp Complex.continuous_ofReal.continuousOn (fun s hs => by simpa using hs))
  have hr' : ContinuousOn (fun s => timeIntegral (fun u => E.H u s) 0 t) (Ici 0) :=
    hr.congr (fun s hs => by
      change _ = (∫ u in (0 : ℝ)..t, entranceComplexH E u (s : ℂ)).re
      rw [entrance_complex_timeIntegral_real E ht hs, Complex.ofReal_re])
  have hmul : ContinuousOn (fun s : ℝ => s * t) (Ici 0) :=
    (continuous_id.mul continuous_const).continuousOn
  have hy : ContinuousOn (entranceExpFactor E t) (Ici 0) :=
    Real.continuous_exp.comp_continuousOn ((hmul.sub hr').div_const 2)
  refine ⟨hy, ?_⟩
  have h0 : entranceExpFactor E t 0 = 1 := by
    have hi := entrance_complex_timeIntegral_real E ht (s := 0) le_rfl
    have hH (u : ℝ) : entranceComplexH E u 0 = 0 := by
      simp [entranceComplexH, complexCompensatedLaplace]
    have he : timeIntegral (fun u => E.H u 0) 0 t = 0 := by
      simpa [hH] using (congrArg Complex.re hi).symm
    simp [entranceExpFactor, he]
  have hh := (hy 0 (mem_Ici.mpr le_rfl)).tendsto.mono_left
    (nhdsWithin_mono 0 (Ioi_subset_Ici_self : Ioi (0 : ℝ) ⊆ Ici 0))
  simpa only [h0] using hh

private theorem entrance_expValue_factor {T lam α C : ℝ}
    (E : EntranceData T lam α C) (t s : ℝ) :
    entranceExpValue E t s =
      2 * E.H t s * entranceExpFactor E t s / entranceQ E t := by
  unfold entranceExpValue entranceCanonicalValue entranceY entranceExpFactor
  rw [show (s * t - timeIntegral (fun u => E.H u s) 0 t) / 2 =
    s * t / 2 + (-timeIntegral (fun u => E.H u s) 0 t / 2) by ring, Real.exp_add]
  ring

private theorem entrance_expFlux_factor {T lam α C : ℝ}
    (E : EntranceData T lam α C) (t s : ℝ) :
    entranceExpFlux E t s = 2 * s * entranceExpFactor E t s *
      (entranceQ E t - 2 * E.H t s / s ^ 2) / entranceR E t := by
  unfold entranceExpFlux entranceCanonicalFlux entranceY entranceExpFactor
  rw [show (s * t - timeIntegral (fun u => E.H u s) 0 t) / 2 =
    s * t / 2 + (-timeIntegral (fun u => E.H u s) 0 t / 2) by ring, Real.exp_add]
  ring

/-- The degree-two identity forces the compensated entrance transform to
have a linear denominator. The constant term of the integrating factor
is fixed by its spectral limit at zero. -/
theorem entrance_rational_transform {T lam C : ℝ}
    (hT : 0 < T) (hlam : 0 ≤ lam) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ D ≤ T ∧
      ∀ {α : ℝ} (E : EntranceData T lam α C),
        ∀ᵐ t : ℝ, t ∈ Ioc 0 D →
          ∃ p q : ℝ, 0 ≤ q ∧ ∀ s > 0,
            E.H t s = entranceQ E t * (s * p + s ^ 2 * q) / (2 + entranceQ E t * q * s) := by
  obtain ⟨D₁, hD₁, hD₁T, hquad⟩ := entrance_expValue_quadratic hT hlam hC
  obtain ⟨D₂, hD₂, hD₂T, hb⟩ := entrance_regularization_bounds hT hlam hC
  obtain ⟨D₃, hD₃, hD₃T, hode⟩ := entrance_exp_ode_ae hT hlam hC
  let D := min D₁ (min D₂ D₃)
  have hD : 0 < D := lt_min hD₁ (lt_min hD₂ hD₃)
  have hle₁ : D ≤ D₁ := min_le_left _ _
  have hle₂ : D ≤ D₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hle₃ : D ≤ D₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hDT := hle₁.trans hD₁T
  refine ⟨D, hD, hDT, ?_⟩
  intro α E
  obtain ⟨P, hP, hPac⟩ := hquad E
  let p : ℝ → ℝ := fun t => (P t).coeff 1
  let q : ℝ → ℝ := fun t => (P t).coeff 2
  have hPev (t : ℝ) (ht : t ∈ Ioc 0 D) (s : ℝ) (hs : 0 < s) :
      entranceExpValue E t s = s * p t + s ^ 2 * q t := by
    obtain ⟨hdeg, hzero, he⟩ := hP t ⟨ht.1, ht.2.trans hle₁⟩
    rw [← he s hs, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one, hzero]
    dsimp [p, q]
    ring
  have hdiff : ∀ᵐ t : ℝ, t ∈ Ioo 0 D → DifferentiableAt ℝ p t ∧ DifferentiableAt ℝ q t := by
    apply profile_ae_Ioo_of_local hD
    intro a ha haD
    have haD₁ := haD.trans hle₁
    filter_upwards [(hPac 1 a ha haD₁).ae_differentiableAt,
      (hPac 2 a ha haD₁).ae_differentiableAt] with t hp hq ht
    have ht' : t ∈ uIcc a D₁ := uIcc_of_le haD₁ ▸ ⟨ht.1.le, ht.2.le.trans hle₁⟩
    exact ⟨hp ht', hq ht'⟩
  have hder : ∀ᵐ t : ℝ, t ∈ Ioo 0 D → ∀ s : ℚ, 0 < (s : ℝ) →
      HasDerivAt (fun u => entranceExpValue E u (s : ℝ))
        ((s : ℝ) / 2 * (entranceExpValue E t s - entranceExpFlux E t s / entranceW E t)) t := by
    apply profile_ae_Ioo_of_local hD
    intro a ha haD
    have he (s : ℚ) : ∀ᵐ t : ℝ, t ∈ Ioo a D → 0 < (s : ℝ) →
        HasDerivAt (fun u => entranceExpValue E u (s : ℝ))
          ((s : ℝ) / 2 * (entranceExpValue E t s - entranceExpFlux E t s / entranceW E t)) t := by
      by_cases hs : 0 < (s : ℝ)
      · filter_upwards [hode E s hs a ha (haD.trans hle₃)] with t ht hm _
        exact (ht ⟨hm.1, hm.2.trans_le hle₃⟩).1
      · exact Eventually.of_forall fun _ _ hs' => (hs hs').elim
    filter_upwards [ae_all_iff.mpr he] with t ht hm s hs
    exact ht s hm hs
  filter_upwards [hdiff, hder, volume.ae_ne D] with t hd htder htD ht
  have ht' : t ∈ Ioo 0 D := ⟨ht.1, lt_of_le_of_ne ht.2 htD⟩
  have htT : t ∈ Ioc 0 T := ⟨ht.1, ht.2.trans hDT⟩
  let Q := entranceQ E t
  let R := entranceR E t
  have ht0 := ht.1
  have hb' := hb E ⟨ht.1, ht.2.trans hle₂⟩
  have hQ : 0 < Q := (by positivity : 0 < C⁻¹ / 2 * t).trans_le hb'.1
  have hR : 0 < R := (by positivity : 0 < C⁻¹ / 2 * t ^ 2).trans_le hb'.2.2.1
  have hw : 0 < entranceW E t := div_pos (sq_pos_of_pos hQ) hR
  obtain ⟨hyc, hy0⟩ := entrance_expFactor_continuous E hlam hC htT
  have hfact : ∀ s > 0, entranceExpFactor E t s = 1 + (Q * q t / 2) * s := by
    apply profile_factor_linear_of_quadratic hy0 (B := Q * p t / 2 + q t - Q * deriv q t)
      (C := p t - Q * deriv p t)
    have hc : ContinuousOn (fun s : ℝ => s * entranceExpFactor E t s) (Ioi 0) :=
      continuousOn_id.mul (hyc.mono Ioi_subset_Ici_self)
    have hc' : ContinuousOn (fun s : ℝ =>
        (Q * q t / 2) * s ^ 2 + (Q * p t / 2 + q t - Q * deriv q t) * s + (p t - Q * deriv p t))
        (Ioi 0) := by fun_prop
    apply profile_eqOn_positive_of_rat hc hc'
    intro s hs
    let v : ℝ := s
    change 0 < v at hs
    have hd' : HasDerivAt (fun u => entranceExpValue E u v)
        (v * deriv p t + v ^ 2 * deriv q t) t := by
      apply (((hd ht').1.hasDerivAt.const_mul v).add
        ((hd ht').2.hasDerivAt.const_mul (v ^ 2))).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds ht'.1 ht'.2] with u hu
      exact hPev u ⟨hu.1, hu.2.le⟩ v hs
    have he : v * deriv p t + v ^ 2 * deriv q t =
        v / 2 * (entranceExpValue E t v - entranceExpFlux E t v / entranceW E t) :=
      hd'.unique (htder ht' s hs)
    have hz : entranceExpFlux E t v =
        entranceW E t * (v * p t + v ^ 2 * q t -
          2 * (v * deriv p t + v ^ 2 * deriv q t) / v) := by
      rw [hPev t ht v hs] at he
      have hh : 2 * (v * deriv p t + v ^ 2 * deriv q t) / v =
          v * p t + v ^ 2 * q t - entranceExpFlux E t v / entranceW E t := by
        rw [he]
        field_simp [hs.ne']
      rw [hh, sub_sub_cancel, mul_comm, div_mul_cancel₀ _ hw.ne']
    apply profile_factor_algebra hs.ne' hQ.ne' hR.ne'
    · rw [← entrance_expValue_factor]
      exact hPev t ht v hs
    · rw [← entrance_expFlux_factor]
      exact hz
  have hq : 0 ≤ q t := by
    apply le_of_not_gt
    intro hneg
    have hcoef : Q * q t / 2 < 0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hQ hneg) (by norm_num)
    let s := -2 / (Q * q t / 2)
    have hs : 0 < s := div_pos_of_neg_of_neg (by norm_num) hcoef
    have he := hfact s hs
    have hys : 0 < entranceExpFactor E t s := Real.exp_pos _
    have hterm : (Q * q t / 2) * s = -2 := by
      dsimp only [s]
      rw [mul_comm, div_mul_cancel₀ _ hcoef.ne]
    rw [he, hterm] at hys
    linarith
  refine ⟨p t, q t, hq, fun s hs => ?_⟩
  have he := hPev t ht s hs
  rw [entrance_expValue_factor, hfact s hs] at he
  have hden : 0 < 2 + Q * q t * s := by positivity
  apply (eq_div_iff hden.ne').2
  have hh := (div_eq_iff hQ.ne').1 he
  linear_combination hh

end EntranceRational

section ExponentialMeasure

/-- Exponential density with intensity `a` and rate `b` on the nonnegative
half-line. -/
noncomputable def profileExponentialMeasure (a b : ℝ) : Measure ℝ :=
  (volume.restrict (Ici 0)).withDensity fun x => ENNReal.ofReal (a * Real.exp (-(b * x)))

private theorem profileExp_support (a b : ℝ) :
    profileExponentialMeasure a b (Iio 0) = 0 ∧ profileExponentialMeasure a b {0} = 0 := by
  constructor
  · apply withDensity_absolutelyContinuous
    rw [Measure.restrict_apply measurableSet_Iio]
    have h : Iio (0 : ℝ) ∩ Ici 0 = ∅ := by
      ext x
      simp
    rw [h, measure_empty]
  · apply withDensity_absolutelyContinuous
    rw [Measure.restrict_apply (measurableSet_singleton (0 : ℝ))]
    exact measure_mono_null inter_subset_left (measure_singleton _)

private theorem profileExp_laplace {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    IsFiniteMeasure (profileExponentialMeasure a b) ∧
      ∀ s : ℝ, 0 ≤ s →
        (∫ x, Real.exp (-(s * x)) ∂profileExponentialMeasure a b) = a / (s + b) := by
  have hm : Measurable (fun x : ℝ => a * Real.exp (-(b * x))) := by fun_prop
  refine ⟨?_, ?_⟩
  · apply isFiniteMeasure_withDensity_ofReal
    have hi := (integrableOn_Ici_iff_integrableOn_Ioi).2
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) 0)
    simpa only [neg_mul] using (hi.const_mul a).hasFiniteIntegral
  · intro s hs
    have hrate := add_pos_of_nonneg_of_pos hs hb
    unfold profileExponentialMeasure
    rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal (mul_nonneg ha (Real.exp_pos _).le), smul_eq_mul,
      mul_assoc, ← Real.exp_add]
    simp_rw [show ∀ x : ℝ, -(b * x) + -(s * x) = -(s + b) * x from fun x => by ring]
    rw [MeasureTheory.integral_const_mul, ← restrict_Ioi_eq_restrict_Ici,
      integral_exp_mul_Ioi (neg_neg_of_pos hrate)]
    rw [mul_zero, Real.exp_zero, neg_div_neg_eq, mul_one_div]

/-- All polynomial moments of the exponential density, with their
normalization in the entrance equations. -/
theorem profileExp_moment {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (k : ℕ) :
    measureMoment (profileExponentialMeasure a b) k = a * k.factorial / b ^ (k + 1) := by
  have hm : Measurable (fun x : ℝ => a * Real.exp (-(b * x))) := by fun_prop
  unfold measureMoment profileExponentialMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg ha (Real.exp_pos _).le), smul_eq_mul,
    mul_assoc, mul_comm (Real.exp _) (_ ^ k)]
  rw [MeasureTheory.integral_const_mul, ← restrict_Ioi_eq_restrict_Ici]
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := b)
    (by positivity) hb
  rw [Real.Gamma_nat_eq_factorial] at hi
  simp_rw [show (k : ℝ) + 1 - 1 = (k : ℝ) by ring, Real.rpow_natCast] at hi
  rw [← Nat.cast_succ, Real.rpow_natCast, div_pow, one_pow] at hi
  rw [hi, Nat.succ_eq_add_one]
  ring

private theorem profile_complexLaplace_continuous {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ : ρ (Iio 0) = 0) :
    ContinuousOn (complexCompensatedLaplace ρ) {z | 0 ≤ z.re} := by
  have hx : ∀ᵐ x ∂ρ, 0 ≤ x := by simpa [ae_iff, not_le, Iio] using hρ
  apply continuousOn_of_dominated (bound := fun _ => (2 : ℝ)) (μ := ρ)
  · intro z hz
    fun_prop
  · intro z hz
    exact hx.mono fun x hxx => (profile_kernel_norm hz hxx).1
  · exact integrable_const 2
  · exact Eventually.of_forall fun x => by
      fun_prop

private theorem profile_laplace_integrable {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ : ρ (Iio 0) = 0) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun x => Real.exp (-(s * x))) ρ := by
  have hx : ∀ᵐ x ∂ρ, 0 ≤ x := by simpa [ae_iff, not_le, Iio] using hρ
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [hx] with x hx
  rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (mul_nonneg hs hx)

private theorem profile_compensated_mass_decomposition {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ : ρ (Iio 0) = 0) {s : ℝ} (hs : 0 ≤ s) :
    compensatedLaplace ρ s = (∫ x, Real.exp (-(s * x)) ∂ρ) - measureMoment ρ 0 := by
  unfold compensatedLaplace
  rw [integral_sub (profile_laplace_integrable hρ hs) (integrable_const _)]
  simp [measureMoment]

private theorem profile_compensated_atTop {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ : ρ (Iio 0) = 0) (hn : ρ {0} = 0) :
    Tendsto (compensatedLaplace ρ) atTop (𝓝 (-measureMoment ρ 0)) := by
  have hx : ∀ᵐ x ∂ρ, 0 < x := by
    rw [ae_iff]
    have hs : {x : ℝ | ¬0 < x} = Iio 0 ∪ {0} := by
      ext x
      simp [le_iff_lt_or_eq]
    rw [hs]
    exact measure_union_null hρ hn
  have hl : Tendsto (fun s : ℝ => ∫ x, Real.exp (-(s * x)) ∂ρ) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) ∂ρ by simp]
    apply tendsto_integral_filter_of_dominated_convergence (F := fun (s x : ℝ) =>
      Real.exp (-(s * x))) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    · exact Eventually.of_forall fun _ => by fun_prop
    · filter_upwards [eventually_ge_atTop 0] with s hs
      filter_upwards [hx] with x hx
      rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_one_iff]
      exact neg_nonpos.mpr (mul_nonneg hs hx.le)
    · exact integrable_const 1
    · filter_upwards [hx] with x hx
      have hh : Tendsto (fun s : ℝ => -x * s) atTop atBot :=
        tendsto_const_nhds.neg_mul_atTop (neg_neg_of_pos hx) tendsto_id
      have he : Tendsto (fun s : ℝ => Real.exp (-x * s)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hh
      convert he using 1
      funext s
      congr 1
      ring
  have hh := hl.sub_const (measureMoment ρ 0)
  simp only [zero_sub] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 0] with s hs
  exact (profile_compensated_mass_decomposition hρ hs).symm

end ExponentialMeasure

section RationalMeasure

private theorem profile_ratio_atTop (b : ℝ) :
    Tendsto (fun s : ℝ => s / (s + b)) atTop (𝓝 1) := by
  have hh := (tendsto_const_nhds (x := b)).div_atTop
    (tendsto_atTop_add_const_right atTop b tendsto_id)
  have hl := hh.const_sub (1 : ℝ)
  simp only [sub_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (|b| + 1)] with s hs
  have hd : 0 < s + b := by linarith [neg_abs_le b]
  change 1 - b / (s + b) = s / (s + b)
  field_simp
  ring

/-- A rational compensated transform with positive mass and no atom at zero
is the transform of an exponential density with a positive rate. -/
theorem profile_rational_is_exponential {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ : ρ (Iio 0) = 0) (hn : ρ {0} = 0)
    (hi : Integrable (fun x : ℝ => x) ρ) (hm : 0 < measureMoment ρ 0)
    {Q p q : ℝ} (hQ : 0 < Q) (hq : 0 ≤ q)
    (h : ∀ s > 0, s + compensatedLaplace ρ s = Q * (s * p + s ^ 2 * q) / (2 + Q * q * s)) :
    ∃ b : ℝ, 0 < b ∧ ρ = profileExponentialMeasure (measureMoment ρ 0 * b) b := by
  have hlim := profile_compensated_atTop hρ hn
  have hq' : 0 < q := by
    by_contra! hz
    have hq0 : q = 0 := le_antisymm hz hq
    have he (s : ℝ) (hs : 0 < s) :
        compensatedLaplace ρ s = (Q * p / 2 - 1) * s := by
      have hh := h s hs
      rw [hq0] at hh
      linear_combination hh
    have hfun : Tendsto (fun s : ℝ => compensatedLaplace ρ s / s) atTop (𝓝 0) :=
      hlim.div_atTop tendsto_id
    have hconst : Tendsto (fun s : ℝ => compensatedLaplace ρ s / s) atTop (𝓝 (Q * p / 2 - 1)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop 0] with s hs
      rw [he s hs, mul_div_cancel_right₀ _ hs.ne']
    have hz := tendsto_nhds_unique hconst hfun
    have ht : Tendsto (compensatedLaplace ρ) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop 0] with s hs
      simp [he s hs, hz]
    linarith [tendsto_nhds_unique hlim ht]
  let b := 2 / (Q * q)
  have hb : 0 < b := by dsimp [b]; positivity
  let c := (2 - Q * p) / (Q * q)
  have he (s : ℝ) (hs : 0 < s) :
      compensatedLaplace ρ s = -c * (s / (s + b)) := by
    have hh := h s hs
    have hden : 0 < 2 + Q * q * s := by positivity
    have hd' : 0 < s + b := add_pos hs hb
    have he := (eq_div_iff hden.ne').1 hh
    calc
      compensatedLaplace ρ s =
          ((Q * p - 2) * s) / (2 + Q * q * s) := by
            apply (eq_div_iff hden.ne').2
            linear_combination he
      _ = _ := by
        dsimp only [b, c]
        field_simp
        ring
  have hmass : measureMoment ρ 0 = c := by
    have hlim' : Tendsto (compensatedLaplace ρ) atTop (𝓝 (-c)) := by
      have hh := (profile_ratio_atTop b).const_mul (-c)
      simp only [mul_one] at hh
      apply hh.congr'
      filter_upwards [eventually_gt_atTop 0] with s hs
      exact (he s hs).symm
    linarith [tendsto_nhds_unique hlim hlim']
  let a := measureMoment ρ 0 * b
  have ha : 0 < a := mul_pos hm hb
  let ν := profileExponentialMeasure a b
  obtain ⟨hν, hνL⟩ := profileExp_laplace ha.le hb
  let _ : IsFiniteMeasure ν := hν
  have hνpos : ν (Iio 0) = 0 := (profileExp_support a b).1
  have hm0 : measureMoment ν 0 = measureMoment ρ 0 := by
    change measureMoment (profileExponentialMeasure a b) 0 = _
    rw [profileExp_moment ha.le hb]
    simp [a, hb.ne']
  have hνi : Integrable (fun x : ℝ => x) ν := by
    by_contra hn
    have hh := integral_undef hn
    have he : measureMoment ν 1 = 0 := by simpa [measureMoment] using hh
    change measureMoment (profileExponentialMeasure a b) 1 = 0 at he
    rw [profileExp_moment ha.le hb] at he
    exact (show 0 < a * ((Nat.factorial 1 : ℕ) : ℝ) / b ^ (1 + 1) by positivity).ne' he
  refine ⟨b, hb, ?_⟩
  apply profile_measure_eq_of_real_transform hm0.symm
    (fun z hz => (profile_complexLaplace_hasDerivAt hρ hi hz).2.differentiableAt.differentiableWithinAt)
    (fun z hz => (profile_complexLaplace_hasDerivAt hνpos hνi hz).2.differentiableAt.differentiableWithinAt)
    (profile_complexLaplace_continuous hρ) (profile_complexLaplace_continuous hνpos)
  intro s hs
  rw [he s hs, profile_compensated_mass_decomposition hνpos hs.le, hνL s hs.le, hm0, hmass]
  dsimp only [a]
  rw [hmass]
  field_simp
  ring

/-- The subsequential entrance measures have an exponential density on a
common initial time interval. The next step is to identify its two parameters. -/
theorem entrance_exponential_measure {T lam C : ℝ}
    (hT : 0 < T) (hlam : 0 ≤ lam) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ D ≤ T ∧
      ∀ {α : ℝ} (E : EntranceData T lam α C),
        ∀ᵐ t : ℝ, t ∈ Ioc 0 D →
          ∃ b : ℝ, 0 < b ∧ E.ν t = profileExponentialMeasure (E.S t * b) b := by
  obtain ⟨D₁, hD₁, hD₁T, hr⟩ := entrance_rational_transform hT hlam hC
  obtain ⟨D₂, hD₂, hD₂T, hb⟩ := entrance_regularization_bounds hT hlam hC
  let D := min D₁ D₂
  have hD : 0 < D := lt_min hD₁ hD₂
  have hd₁ : D ≤ D₁ := min_le_left _ _
  have hd₂ : D ≤ D₂ := min_le_right _ _
  have hDT := hd₁.trans hD₁T
  refine ⟨D, hD, hDT, ?_⟩
  intro α E
  filter_upwards [hr E, E.representation, E.bounds_S] with t ht hrep hS hm
  have hmT : t ∈ Ioc 0 T := ⟨hm.1, hm.2.trans hDT⟩
  obtain ⟨hf, hspan, h3, hH, hm0, _, _, _, h0⟩ := hrep hmT
  let _ : IsFiniteMeasure (E.ν t) := hf
  obtain ⟨p, q, hq, h⟩ := ht ⟨hm.1, hm.2.trans hd₁⟩
  have ht0 := hm.1
  have hQ : 0 < entranceQ E t :=
    (by positivity : 0 < C⁻¹ / 2 * t).trans_le (hb E ⟨hm.1, hm.2.trans hd₂⟩).1
  have hmass : 0 < measureMoment (E.ν t) 0 := by
    rw [hm0]
    exact (by positivity : 0 < C⁻¹ * t⁻¹).trans_le (hS hmT).1
  obtain ⟨b, hbp, hbe⟩ := profile_rational_is_exponential hspan h0
    (profile_first_moment_integrable h3) hmass hQ hq (fun s hs => (hH s hs.le).symm.trans (h s hs))
  exact ⟨b, hbp, by rwa [hm0] at hbe⟩

end RationalMeasure

section EntranceScalar

private theorem profile_local_constant_of_trace {D f₀ : ℝ} (hD : 0 < D) {f : ℝ → ℝ}
    (hac : ∀ a, 0 < a → a ≤ D → AbsolutelyContinuousOnInterval f a D)
    (hder : ∀ a, 0 < a → a ≤ D → ∀ᵐ t : ℝ, t ∈ Ioo a D → HasDerivAt f 0 t)
    (htrace : Tendsto f (𝓝[>] 0) (𝓝 f₀)) :
    ∀ t ∈ Ioc 0 D, f t = f₀ := by
  have hc (a : ℝ) (ha : 0 < a) (haD : a ≤ D) : f a = f D := by
    have hh : ∀ᵐ t : ℝ, t ∈ uIcc a D → HasDerivAt f 0 t := by
      filter_upwards [hder a ha haD, volume.ae_ne a, volume.ae_ne D] with t ht hta htD hm
      have hm' : t ∈ Icc a D := uIcc_of_le haD ▸ hm
      exact ht ⟨lt_of_le_of_ne hm'.1 hta.symm, lt_of_le_of_ne hm'.2 htD⟩
    obtain ⟨c, h⟩ := (hac a ha haD).const_of_ae_hasDerivAt_zero hh
    exact (h a left_mem_uIcc).trans (h D right_mem_uIcc).symm
  have hh : Tendsto f (𝓝[>] 0) (𝓝 (f D)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioc_mem_nhdsGT hD] with t ht
    exact (hc t ht.1 ht.2).symm
  intro t ht
  exact (hc t ht.1 ht.2).trans (tendsto_nhds_unique hh htrace)

private theorem entrance_dK_deriv_ae {T lam α C : ℝ} (E : EntranceData T lam α C)
    (hC : 0 < C) {a : ℝ} (ha : 0 < a) (haT : a ≤ T) :
    ∀ᵐ t : ℝ, t ∈ Ioo a T →
      HasDerivAt E.d (E.S t * E.d t) t ∧
        HasDerivAt E.K (E.S t * E.K t + E.d t ^ 2 - 1) t := by
  have hSi := entrance_integrableOn_S E hC ha le_rfl
  obtain ⟨_, hd, hK, _⟩ := E.lipschitz a ha
  have hi (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a T)) :
      IntervalIntegrable (fun t => E.S t * f t) volume a T := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le haT]
    exact hSi.mul_bdd (hf.aestronglyMeasurable measurableSet_Icc)
      (ae_restrict_of_forall_mem measurableSet_Icc hM)
  have hd2 : IntervalIntegrable (fun t => E.d t ^ 2) volume a T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le haT]
    exact (hd.continuousOn.pow 2).integrableOn_compact isCompact_Icc
  have hd' := entrance_ae_hasDerivAt_of_integral_eq haT (hi E.d hd.continuousOn)
    (fun t ht => E.ode_d a t ha ht.1 ht.2)
  have hK' := entrance_ae_hasDerivAt_of_integral_eq haT
    (((hi E.K hK.continuousOn).add hd2).sub intervalIntegrable_const)
    (fun t ht => E.ode_K a t ha ht.1 ht.2)
  filter_upwards [hd', hK'] with t hdt hKt ht
  exact ⟨hdt ht, hKt ht⟩

/-- Reciprocal rate expressed through the original entrance moments. -/
noncomputable def entranceReciprocalRate {T lam α C : ℝ} (E : EntranceData T lam α C) (t : ℝ) : ℝ :=
  E.K t / (1 + E.d t)

/-- The exponential entrance measures imply a scalar Riccati equation for
the reciprocal rate. Its parameter is fixed by the entrance matching. -/
theorem entrance_scalar_riccati {T lam C : ℝ}
    (hT : 0 < T) (hlam : 0 ≤ lam) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ D ≤ T ∧
      ∀ {α : ℝ} (E : EntranceData T lam α C),
        let g := entranceReciprocalRate E
        (∀ t ∈ Ioc 0 D, 0 < g t ∧ E.d t = (3 * α / 2) * g t ^ 2) ∧
        Tendsto g (𝓝[>] 0) (𝓝 0) ∧
        (∀ a, 0 < a → a ≤ D → AbsolutelyContinuousOnInterval g a D) ∧
        (∀ a, 0 < a → a ≤ D → ∀ᵐ t : ℝ, t ∈ Ioo a D →
          HasDerivAt g (1 + (3 * α / 2) * g t ^ 2) t) ∧
        ∀ᵐ t : ℝ, t ∈ Ioc 0 D →
          E.ν t = profileExponentialMeasure ((1 + E.d t) * (2 / g t) ^ 2) (2 / g t) := by
  obtain ⟨D₁, hD₁, hD₁T, hm⟩ := entrance_exponential_measure hT hlam hC
  let D := min D₁ (min 1 ((2 * (C * lam + 1))⁻¹))
  have hD : 0 < D := by dsimp [D]; positivity
  have hd₁ : D ≤ D₁ := min_le_left _ _
  have hDT := hd₁.trans hD₁T
  refine ⟨D, hD, hDT, ?_⟩
  intro α E
  let g := entranceReciprocalRate E
  let V : ℝ → ℝ := fun t => E.d t / g t ^ 2
  have hpos (t : ℝ) (ht : t ∈ Ioc 0 D) : 0 < 1 + E.d t ∧ 0 < E.K t ∧ 0 < g t := by
    have ht0 := ht.1
    have ht1 : t ≤ 1 := ht.2.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hsmall : t ≤ (2 * (C * lam + 1))⁻¹ :=
      ht.2.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h : t * (2 * (C * lam + 1)) ≤ 1 :=
      (le_div_iff₀ (by positivity)).1 (by simpa only [one_div] using hsmall)
    have ht2 : t ^ 2 ≤ t := by nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht1)]
    have hb := E.bounds t ⟨ht.1, ht.2.trans hDT⟩
    have hdsmall : |E.d t| ≤ 1 / 2 := by
      calc
        _ ≤ C * lam * t ^ 2 := hb.1
        _ ≤ C * lam * t := mul_le_mul_of_nonneg_left ht2 (by positivity)
        _ ≤ _ := by nlinarith only [h, ht0]
    have hd : 0 < 1 + E.d t := by linarith [(abs_le.mp hdsmall).1]
    have hK : 0 < E.K t := (by positivity : 0 < C⁻¹ * t).trans_le hb.2.1
    exact ⟨hd, hK, div_pos hK hd⟩
  have hdata : ∀ᵐ t : ℝ, t ∈ Ioc 0 D →
      E.S t * E.K t = 2 * (1 + E.d t) ^ 2 ∧
      E.S t = 2 * (1 + E.d t) / g t ∧
      E.P t = (3 / 2) * (1 + E.d t) * g t ^ 2 ∧
      E.ν t = profileExponentialMeasure ((1 + E.d t) * (2 / g t) ^ 2) (2 / g t) := by
    filter_upwards [hm E, E.representation, E.bounds_S] with t hme hr hS ht
    have htT : t ∈ Ioc 0 T := ⟨ht.1, ht.2.trans hDT⟩
    have ht0 := ht.1
    have hS' : 0 < E.S t := (by positivity : 0 < C⁻¹ * t⁻¹).trans_le (hS htT).1
    obtain ⟨b, hb, he⟩ := hme ⟨ht.1, ht.2.trans hd₁⟩
    obtain ⟨_, _, _, _, _, hd, hK, hP, _⟩ := hr htT
    rw [he, profileExp_moment (mul_nonneg hS'.le hb.le) hb] at hd hK hP
    have hd' : E.S t = (1 + E.d t) * b := by
      field_simp [hb.ne'] at hd
      norm_num at hd
      apply (mul_right_cancel₀ hb.ne')
      linear_combination hd
    have hK' : E.K t = 2 * (1 + E.d t) / b := by
      rw [hd'] at hK
      rw [← hK]
      norm_num
      field_simp [hb.ne']
    have hg : g t = 2 / b := by
      change E.K t / (1 + E.d t) = _
      rw [hK']
      field_simp [(hpos t ht).1.ne', hb.ne']
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hd', hK']
      field_simp [hb.ne']
    · rw [hd', hg]
      field_simp [hb.ne']
    · rw [← hP, hd', hg]
      norm_num
      field_simp [hb.ne']
      ring
    · have hbg : 2 / g t = b := by rw [hg]; field_simp [hb.ne']
      rw [he, hd', hbg]
      congr 1
      ring
  have hAC (a : ℝ) (ha : 0 < a) (haD : a ≤ D) :
      AbsolutelyContinuousOnInterval g a D ∧ AbsolutelyContinuousOnInterval V a D ∧
      AbsolutelyContinuousOnInterval E.d a D ∧ AbsolutelyContinuousOnInterval E.P a D := by
    have hsub : uIcc a D ⊆ Icc a T := by
      rw [uIcc_of_le haD]
      exact Icc_subset_Icc_right hDT
    obtain ⟨_, hdl, hKl, hPl⟩ := E.lipschitz a ha
    have hd := (hdl.mono hsub).absolutelyContinuousOnInterval
    have hK := (hKl.mono hsub).absolutelyContinuousOnInterval
    have hP := (hPl.mono hsub).absolutelyContinuousOnInterval
    have hconst := ((LipschitzWith.const (α := ℝ) (1 : ℝ)).lipschitzOnWith
      (s := uIcc a D)).absolutelyContinuousOnInterval
    have hgd := profile_ac_inv (hconst.fun_add hd) (by
      intro t ht
      have ht' : t ∈ Icc a D := uIcc_of_le haD ▸ ht
      exact (hpos t ⟨ha.trans_le ht'.1, ht'.2⟩).1)
    have hg : AbsolutelyContinuousOnInterval g a D := by
      change AbsolutelyContinuousOnInterval (fun t => E.K t / (1 + E.d t)) a D
      simpa only [div_eq_mul_inv] using hK.fun_mul hgd
    have hg2 : AbsolutelyContinuousOnInterval (fun t => g t ^ 2) a D := by
      simpa only [pow_two] using hg.fun_mul hg
    have hgi := profile_ac_inv hg2 (by
      intro t ht
      have ht' : t ∈ Icc a D := uIcc_of_le haD ▸ ht
      exact sq_pos_of_pos (hpos t ⟨ha.trans_le ht'.1, ht'.2⟩).2.2)
    exact ⟨hg, by simpa [V, div_eq_mul_inv] using hd.fun_mul hgi, hd, hP⟩
  have hdd : Tendsto E.d (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hh : Continuous (fun t : ℝ => C * lam * t ^ 2) := by fun_prop
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (tendsto_nhdsWithin_of_tendsto_nhds (by simpa using hh.tendsto 0))
    filter_upwards [Ioc_mem_nhdsGT hD] with t ht
    simpa only [Real.norm_eq_abs] using (E.bounds t ⟨ht.1, ht.2.trans hDT⟩).1
  have hKK : Tendsto E.K (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hh : Continuous (fun t : ℝ => C * t) := by fun_prop
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (tendsto_nhdsWithin_of_tendsto_nhds (by simpa using hh.tendsto 0))
    filter_upwards [Ioc_mem_nhdsGT hD] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (hpos t ht).2.1]
    exact (E.bounds t ⟨ht.1, ht.2.trans hDT⟩).2.2.1
  have hg0 : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    change Tendsto (E.K / fun t => 1 + E.d t) (𝓝[>] 0) (𝓝 0)
    simpa only [add_zero, div_one] using hKK.div (hdd.const_add 1) (by norm_num : 1 + 0 ≠ (0 : ℝ))
  have hder (a : ℝ) (ha : 0 < a) (haD : a ≤ D) :
      ∀ᵐ t : ℝ, t ∈ Ioo a D → HasDerivAt g (1 + E.d t) t ∧ HasDerivAt V 0 t := by
    filter_upwards [hdata, entrance_dK_deriv_ae E hC ha (haD.trans hDT)] with t hd hm ht
    have ht' : t ∈ Ioc 0 D := ⟨ha.trans ht.1, ht.2.le⟩
    have hh := hd ht'
    obtain ⟨hd', hk'⟩ := hm ⟨ht.1, ht.2.trans_le hDT⟩
    have hpos' := hpos t ht'
    have hg : HasDerivAt g (1 + E.d t) t := by
      convert hk'.div (hd'.const_add 1) hpos'.1.ne' using 1
      · rfl
      · have he : (E.S t * E.K t + E.d t ^ 2 - 1) * (1 + E.d t) - E.K t * (E.S t * E.d t) =
            E.S t * E.K t + (E.d t ^ 2 - 1) * (1 + E.d t) := by ring
        rw [he, hh.1]
        field_simp [hpos'.1.ne']
        ring
    refine ⟨hg, ?_⟩
    convert hd'.div (hg.pow 2) (pow_ne_zero _ hpos'.2.2.ne') using 1
    rw [hh.2.1, show (g ^ 2) t = g t ^ 2 from rfl]
    field_simp [hpos'.2.2.ne'] <;> ring
  have hPc : ContinuousOn E.P (Ioc 0 D) :=
    profile_positive_time_continuousOn (fun a ha haD => (hAC a ha haD).2.2.2)
  have hdc : ContinuousOn E.d (Ioc 0 D) :=
    profile_positive_time_continuousOn (fun a ha haD => (hAC a ha haD).2.2.1)
  have hgc : ContinuousOn g (Ioc 0 D) :=
    profile_positive_time_continuousOn (fun a ha haD => (hAC a ha haD).1)
  have heq : EqOn E.P (fun t => (3 / 2) * (1 + E.d t) * g t ^ 2) (Ioc 0 D) := by
    apply Measure.eqOn_Ioc_of_ae_eq volume _ hPc
      ((continuousOn_const.mul (continuousOn_const.add hdc)).mul (hgc.pow 2))
    exact (ae_restrict_iff' measurableSet_Ioc).2 (hdata.mono fun t ht hm => (ht hm).2.2.1)
  have hV0 : Tendsto V (𝓝[>] 0) (𝓝 (3 * α / 2)) := by
    have he := ((hdd.const_add 1).const_mul (3 / 2 : ℝ)).mul E.matching
    have hlim : (3 / 2 : ℝ) * (1 + 0) * α = 3 * α / 2 := by ring
    rw [hlim] at he
    apply he.congr'
    filter_upwards [Ioc_mem_nhdsGT hD] with t ht
    have hp : 0 < E.P t :=
      (by have ht0 := ht.1; positivity : 0 < C⁻¹ * t ^ 2).trans_le
        (E.bounds t ⟨ht.1, ht.2.trans hDT⟩).2.2.2.1
    change (3 / 2) * (1 + E.d t) * (E.d t / E.P t) = E.d t / g t ^ 2
    rw [heq ht]
    field_simp [(hpos t ht).1.ne', (hpos t ht).2.2.ne']
  have hv := profile_local_constant_of_trace hD (fun a ha haD => (hAC a ha haD).2.1)
    (fun a ha haD => (hder a ha haD).mono fun t ht hm => (ht hm).2) hV0
  have hdv (t : ℝ) (ht : t ∈ Ioc 0 D) : E.d t = (3 * α / 2) * g t ^ 2 :=
    (div_eq_iff (pow_ne_zero _ (hpos t ht).2.2.ne')).1 (hv t ht)
  refine ⟨fun t ht => ⟨(hpos t ht).2.2, hdv t ht⟩, hg0,
    fun a ha haD => (hAC a ha haD).1, ?_, ?_⟩
  · intro a ha haD
    filter_upwards [hder a ha haD] with t ht hm
    rw [← hdv t ⟨ha.trans hm.1, hm.2.le⟩]
    exact (ht hm).1
  · exact hdata.mono fun t ht hm => (ht hm).2.2.2

end EntranceScalar

section IdentifyEntrance

private theorem profile_reciprocal_rate_solve {D v : ℝ} (hD : 0 < D) {g : ℝ → ℝ}
    (hg0 : Tendsto g (𝓝[>] 0) (𝓝 0))
    (hac : ∀ a, 0 < a → a ≤ D → AbsolutelyContinuousOnInterval g a D)
    (hder : ∀ a, 0 < a → a ≤ D → ∀ᵐ t : ℝ, t ∈ Ioo a D →
      HasDerivAt g (1 + v * g t ^ 2) t) :
    (v = 0 → ∀ t ∈ Ioc 0 D, g t = t) ∧
      (0 < v → ∀ t ∈ Ioc 0 D, Real.arctan (Real.sqrt v * g t) = Real.sqrt v * t) := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hidac (a : ℝ) : AbsolutelyContinuousOnInterval (fun t : ℝ => t) a D := by
    have hi : ContDiff ℝ 1 (fun t : ℝ => t) := contDiff_id
    exact hi.contDiffOn.absolutelyContinuousOnInterval
  constructor
  · intro hv
    have hc := profile_local_constant_of_trace hD (f := fun t => g t - t) (f₀ := 0)
      (fun a ha haD => (hac a ha haD).fun_sub (hidac a))
      (fun a ha haD => by
        filter_upwards [hder a ha haD] with t ht hm
        simpa [hv, id_eq] using (ht hm).fun_sub (hasDerivAt_id t))
      (by simpa only [sub_zero] using hg0.sub hid)
    exact fun t ht => sub_eq_zero.mp (hc t ht)
  · intro hv
    let r := Real.sqrt v
    have hr : 0 < r := Real.sqrt_pos.mpr hv
    let G : ℝ → ℝ := fun t => Real.arctan (r * g t) - r * t
    have hGac (a : ℝ) (ha : 0 < a) (haD : a ≤ D) :
        AbsolutelyContinuousOnInterval G a D := by
      have ha' := (hac a ha haD).const_mul r
      obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn ha'.continuousOn
      have hm : MapsTo (fun t => r * g t) (uIcc a D) (Icc (-M) M) := by
        intro t ht
        exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hM t ht)
      have hh := profile_ac_contDiffOn_comp (g := Real.arctan) ha' Real.contDiff_arctan.contDiffOn hm
      exact hh.fun_sub ((hidac a).const_mul r)
    have hG0 : Tendsto G (𝓝[>] 0) (𝓝 0) := by
      have hh := Real.continuous_arctan.continuousAt.tendsto.comp (hg0.const_mul r)
      simp only [mul_zero, Real.arctan_zero] at hh
      simpa only [G, Function.comp_def, mul_zero, sub_zero] using hh.sub (hid.const_mul r)
    have hGder (a : ℝ) (ha : 0 < a) (haD : a ≤ D) :
        ∀ᵐ t : ℝ, t ∈ Ioo a D → HasDerivAt G 0 t := by
      filter_upwards [hder a ha haD] with t ht hm
      have ha' := (Real.hasDerivAt_arctan (r * g t)).comp t ((ht hm).const_mul r)
      have ha'' : HasDerivAt (fun u => Real.arctan (r * g u)) r t := by
        convert ha' using 1
        · rfl
        · rw [mul_pow, Real.sq_sqrt hv.le]
          have hp : 0 < 1 + v * g t ^ 2 := by positivity
          field_simp
      have hl : HasDerivAt (fun u : ℝ => r * u) r t := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul r
      simpa only [G, sub_self] using ha''.fun_sub hl
    exact fun t ht => sub_eq_zero.mp (profile_local_constant_of_trace hD hGac hGder hG0 t ht)

private theorem profile_parameters_of_reciprocal_rate {v t g : ℝ}
    (hv : 0 ≤ v) (ht : 0 < t) (_hg : 0 < g)
    (hzero : v = 0 → g = t)
    (hpos : 0 < v → Real.arctan (Real.sqrt v * g) = Real.sqrt v * t) :
    profileB v t = 2 / g ∧ profileA v t = (1 + v * g ^ 2) * (2 / g) ^ 2 := by
  rcases eq_or_lt_of_le hv with hv0 | hv0
  · have hv' : v = 0 := hv0.symm
    subst v
    have hg' := hzero rfl
    have hU : profileU 0 = id := by
      funext x
      simp [profileU]
    have hder : deriv (profileU 0) t = 1 := by rw [hU]; exact (hasDerivAt_id t).deriv
    rw [profileB, profileA, hder, hU, hg']
    simp [id_eq]
    ring
  · let r := Real.sqrt v
    have hr : 0 < r := Real.sqrt_pos.mpr hv0
    have harg := hpos hv0
    have hx : 0 < r * t := mul_pos hr ht
    have hx' : r * t < Real.pi / 2 := harg ▸ Real.arctan_lt_pi_div_two (r * g)
    have hcos : 0 < Real.cos (r * t) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx'⟩
    have hsin : 0 < Real.sin (r * t) := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
    let u := Real.sin (r * t) / r
    let c := Real.cos (r * t)
    have hu : 0 < u := div_pos hsin hr
    have hc : 0 < c := hcos
    have hU : profileU v = fun x => Real.sin (r * x) / r := by
      funext x
      exact ite_eq_left hv0
    have hder : deriv (profileU v) t = c := by
      rw [hU]
      have hlin : HasDerivAt (fun x : ℝ => r * x) r t := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul r
      exact ((hlin.sin.div_const r).congr_deriv (mul_div_cancel_right₀ _ hr.ne')).deriv
    have hgt : g = u / c := by
      have htan := congrArg Real.tan harg
      rw [Real.tan_arctan, Real.tan_eq_sin_div_cos] at htan
      change r * g = Real.sin (r * t) / c at htan
      dsimp only [u]
      apply (eq_div_iff hc.ne').2
      apply (eq_div_iff hr.ne').2
      linear_combination (eq_div_iff hc.ne').1 htan
    have hB : profileB v t = 2 / g := by
      rw [profileB, hder, hU, hgt]
      change 2 * c / u = 2 / (u / c)
      field_simp
    refine ⟨hB, ?_⟩
    have hunit : c ^ 2 + v * u ^ 2 = 1 := by
      change Real.cos (r * t) ^ 2 + v * (Real.sin (r * t) / r) ^ 2 = 1
      rw [div_pow, Real.sq_sqrt hv]
      rw [show v * (Real.sin (r * t) ^ 2 / v) = Real.sin (r * t) ^ 2 by field_simp]
      linarith [Real.sin_sq_add_cos_sq (r * t)]
    calc
      profileA v t = 4 / u ^ 2 := by rw [profileA, hU]
      _ = 4 * (c ^ 2 + v * u ^ 2) / u ^ 2 := by rw [hunit, mul_one]
      _ = _ := by rw [hgt]; field_simp; ring

/-- Abstract entrance rigidity. The law of the disorder enters the profile
identification only through the nonnegative matching parameter. -/
theorem entrance_profile_identification {T lam C : ℝ}
    (hT : 0 < T) (hlam : 0 ≤ lam) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ D ≤ T ∧
      ∀ {α : ℝ} (E : EntranceData T lam α C), 0 ≤ α →
        ∀ᵐ t : ℝ, t ∈ Ioc 0 D → E.ν t = profileMeasure (3 * α / 2) t := by
  obtain ⟨D, hD, hDT, hr⟩ := entrance_scalar_riccati hT hlam hC
  refine ⟨D, hD, hDT, ?_⟩
  intro α E hα
  obtain ⟨hpos, hg0, hac, hode, hν⟩ := hr E
  obtain ⟨hzero, hposv⟩ := profile_reciprocal_rate_solve hD hg0 hac hode
  filter_upwards [hν] with t ht hm
  obtain ⟨hgt, hd⟩ := hpos t hm
  obtain ⟨hB, hA⟩ := profile_parameters_of_reciprocal_rate
    (by positivity : 0 ≤ 3 * α / 2) hm.1 hgt (fun hv => hzero hv t hm) (fun hv => hposv hv t hm)
  rw [ht hm, hd, ← hA, ← hB]
  rfl

end IdentifyEntrance

open Asymptotics in
/-- Profile identification with the critical product and response conclusions
as explicit inputs. They supply positivity of the matching parameter. -/
theorem profile_identification_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ γ : ℝ}
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
    (hResponse : ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
        tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ) ∧
      (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B)) =Θ[atTop]
        fun n : ℕ => (n : ℝ) ^ 2)
    (hγ : γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃)) {lam T C : ℝ} (hlam : 0 ≤ lam)
    (hT : 0 < T) (hC : 0 < C) :
    ∃ Tstar : ℝ, 0 < Tstar ∧ Tstar ≤ T ∧
      ∀ E : EntranceData T lam (lam * κ * Real.log B ^ 2 / ℓ₃) C,
        ∀ᵐ t, t ∈ Set.Ioo 0 Tstar → E.ν t = profileMeasure (γ * lam) t := by
  obtain ⟨_, _, _, _, ⟨ell, hell, hlim⟩, _⟩ := hProd
  obtain ⟨k, hk, hlim', _⟩ := hResponse
  have hpell : 0 < ℓ₃ := by
    rw [tendsto_nhds_unique hℓ₃ hlim]
    exact hell
  have hpκ : 0 < κ := by
    rw [tendsto_nhds_unique hκ hlim']
    exact hk
  have hα : 0 ≤ lam * κ * Real.log B ^ 2 / ℓ₃ := by positivity
  have hv : 3 * (lam * κ * Real.log B ^ 2 / ℓ₃) / 2 = γ * lam := by
    rw [hγ]
    field_simp [hpell.ne']
  obtain ⟨D, hD, hDT, hE⟩ := entrance_profile_identification hT hlam hC
  refine ⟨D, hD, hDT, fun E => ?_⟩
  filter_upwards [hE E hα] with t ht hm
  rw [← hv]
  exact ht ⟨hm.1, hm.2.le⟩

end DiamondPinning
