module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Proofs.ContinuationProof
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

@[expose] public section

namespace DiamondPinning

open Filter MeasureTheory Topology
open scoped ENNReal NNReal BoundedContinuousFunction

/-- Mild propagation on tests that vanish past the absorption cutoff, in the
coordinate `y = exp(-x)`. Compactly supported smooth tests in the original
space give tests of this form after the exponential change of variables. -/
theorem projected_mild_of_transform_differences (L : ℕ → ℝ → ℝ) (η : ℝ → Measure ℝ)
    {σ r t M : ℝ} (hσ : 0 ≤ σ) (hrt : r ≤ t)
    (hf : ∀ u, IsFiniteMeasure (η u))
    (hsupp : ∀ u, ∀ᵐ y ∂(η u), y ∈ Set.Icc (0 : ℝ) 1)
    (hM : ∀ u ∈ Set.Icc r t, (η u).real Set.univ ≤ M)
    (hr : ∀ n, L n r = measureMoment (η r) n)
    (ht : ∀ n, L n t = measureMoment (η t) n)
    (ha : ∀ᵐ u : ℝ, u ∈ Set.Icc r t → ∀ n, L n u = measureMoment (η u) n)
    (hi : ∀ n : ℕ, IntervalIntegrable
      (fun x => psiS (σ + n) (L n x) - psiS σ (L 0 x)) volume r t)
    (hD : ∀ n : ℕ, ∀ u ∈ Set.uIcc r t,
      (L n u - L 0 u) - (L n r - L 0 r) =
        timeIntegral (fun x => psiS (σ + n) (L n x) - psiS σ (L 0 x)) r u)
    (g g' : ℝ → ℝ) (hg : Continuous g) (hg' : Continuous g')
    (hder : ∀ y, HasDerivAt g (g' y) y)
    (hzero : ∀ y, 1 ≤ y → g y = 0 ∧ g' y = 0)
    (hInt : IntervalIntegrable (fun u =>
      Real.exp (σ * (t - u)) * (∫ y, g (Real.exp (t - u) * y) ∂(η u ∗ₘ η u)) / 2) volume r t) :
    (∫ y, g y ∂(η t)) =
      Real.exp (σ * (t - r)) * (∫ y, g (Real.exp (t - r) * y) ∂(η r)) +
        timeIntegral (fun u =>
          Real.exp (σ * (t - u)) * (∫ y, g (Real.exp (t - u) * y) ∂(η u ∗ₘ η u)) / 2) r t := by
  let E := Real.exp (t - r)
  let C := Real.exp (σ * (t - r))
  have hC : 0 < C := Real.exp_pos _
  have hE : 0 < E := Real.exp_pos _
  have hMa : 0 ≤ M := ENNReal.toReal_nonneg.trans (hM r ⟨le_rfl, hrt⟩)
  let K := 4 * C * M + (C * E * M + C * M ^ 2) * (t - r)
  have htr := sub_nonneg.2 hrt
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let G (d : ℝ) (ν : Measure ℝ) := Real.exp (σ * d) * (∫ y, g (Real.exp d * y) ∂ν)
  let H (u : ℝ) := G (t - u) (η u ∗ₘ η u) / 2
  have hA : G (t - t) (η t) = ∫ y, g y ∂(η t) := by simp [G]
  have hGoal : G (t - t) (η t) - G (t - r) (η r) = timeIntegral H r t := by
    let err := (G (t - t) (η t) - G (t - r) (η r)) - timeIntegral H r t
    have hErr : ∀ ε > (0 : ℝ), |err| ≤ K * ε := by
      intro ε hε
      obtain ⟨p, _, hp⟩ := exists_polynomial_approx_deriv hE.le
        (fun y _ => hder y) hg'.continuousOn hε
      let P (d : ℝ) (ν : Measure ℝ) :=
        Real.exp (σ * d) * (∫ y, p.eval (Real.exp d * y) - p.eval (Real.exp d) ∂ν)
      let J (u : ℝ) := Real.exp (σ * (t - u)) * Real.exp (t - u) *
        p.derivative.eval (Real.exp (t - u)) * (η u).real Set.univ +
        P (t - u) (η u ∗ₘ η u) / 2
      have hpoly := projectedPolynomial_mild p L η hrt hf hsupp hr ht ha
        (fun n _ => hi n) (fun n _ => hD n)
      change IntervalIntegrable J volume r t ∧
        P (t - t) (η t) - P (t - r) (η r) = timeIntegral J r t at hpoly
      have hPair (d : ℝ) (hd : d ∈ Set.Icc 0 (t - r))
          (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1) :
          |P d ν - G d ν| ≤ 2 * C * ε * ν.real Set.univ := by
        have hEd : Real.exp d ≤ E := Real.exp_le_exp.2 hd.2
        have hCd : Real.exp (σ * d) ≤ C :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hd.2 hσ)
        have hEd₁ : 1 ≤ Real.exp d := Real.one_le_exp hd.1
        have hR := hp _ (show Real.exp d ∈ Set.Icc 0 E from ⟨(Real.exp_pos d).le, hEd⟩)
        have hbound : ∀ᵐ y ∂ν, ‖(p.eval (Real.exp d * y) - p.eval (Real.exp d)) -
            g (Real.exp d * y)‖ ≤ 2 * ε := by
          filter_upwards [hν] with y hy
          have hm : Real.exp d * y ∈ Set.Icc 0 E :=
            ⟨mul_nonneg (Real.exp_pos _).le hy.1, (mul_le_of_le_one_right (Real.exp_pos _).le hy.2).trans hEd⟩
          have hpx := (hp _ hm).1
          have hcut := hR.1
          rw [(hzero _ hEd₁).1, sub_zero] at hcut
          calc
            _ = |(p.eval (Real.exp d * y) - g (Real.exp d * y)) - p.eval (Real.exp d)| := by
              rw [Real.norm_eq_abs]
              congr 1
              ring
            _ ≤ |p.eval (Real.exp d * y) - g (Real.exp d * y)| + |p.eval (Real.exp d)| := by
              simpa only [Real.norm_eq_abs] using
                norm_sub_le (p.eval (Real.exp d * y) - g (Real.exp d * y)) (p.eval (Real.exp d))
            _ ≤ _ := by linarith
        have hcompact : ν.restrict (Set.Icc 0 1) = ν := Measure.restrict_eq_self_of_ae_mem hν
        have hione : Integrable (fun y => p.eval (Real.exp d * y) - p.eval (Real.exp d)) ν := by
          rw [← hcompact]
          have hp' : Continuous (fun y : ℝ => p.eval (Real.exp d * y)) := by fun_prop
          exact (hp'.sub continuous_const).continuousOn.integrableOn_compact isCompact_Icc
        have hitwo : Integrable (fun y => g (Real.exp d * y)) ν := by
          rw [← hcompact]
          have hc : Continuous (fun y : ℝ => g (Real.exp d * y)) := by fun_prop
          exact hc.continuousOn.integrableOn_compact isCompact_Icc
        unfold P G
        rw [← mul_sub, ← integral_sub hione hitwo, abs_mul, abs_of_pos (Real.exp_pos _)]
        have hin := MeasureTheory.norm_integral_le_of_norm_le_const hbound
        rw [Real.norm_eq_abs] at hin
        calc
          _ ≤ C * (2 * ε * ν.real Set.univ) :=
            mul_le_mul hCd hin (abs_nonneg _) hC.le
          _ = _ := by ring
      have hP (u : ℝ) (hu : u ∈ Set.Icc r t) :
          |P (t - u) (η u) - G (t - u) (η u)| ≤ 2 * C * ε * M := by
        letI := hf u
        exact (hPair _ ⟨sub_nonneg.2 hu.2, sub_le_sub_left hu.1 t⟩ _ (hsupp u)).trans
          (mul_le_mul_of_nonneg_left (hM _ hu) (by positivity))
      have hJ (u : ℝ) (hu : u ∈ Set.Icc r t) :
          |J u - H u| ≤ (C * E * M + C * M ^ 2) * ε := by
        letI := hf u
        letI : IsFiniteMeasure (η u ∗ₘ η u) := by unfold Measure.mconv; infer_instance
        have hdu : t - u ∈ Set.Icc 0 (t - r) := ⟨sub_nonneg.2 hu.2, sub_le_sub_left hu.1 t⟩
        have hEu : Real.exp (t - u) ≤ E := Real.exp_le_exp.2 hdu.2
        have hCu : Real.exp (σ * (t - u)) ≤ C :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hdu.2 hσ)
        have hcut := (hp _ ⟨(Real.exp_pos _).le, hEu⟩).2
        rw [(hzero _ (Real.one_le_exp hdu.1)).2, sub_zero] at hcut
        have hprod : (η u ∗ₘ η u).real Set.univ ≤ M ^ 2 := by
          rw [← measureMoment_zero_eq_mass, measureMoment_mconv_self, measureMoment_zero_eq_mass]
          exact (sq_le_sq₀ ENNReal.toReal_nonneg hMa).2 (hM _ hu)
        have hm := (hPair _ hdu _ (ae_Icc_mconv_self (hsupp u))).trans
          (mul_le_mul_of_nonneg_left hprod (by positivity))
        have hbd : |Real.exp (σ * (t - u)) * Real.exp (t - u) *
          p.derivative.eval (Real.exp (t - u)) * (η u).real Set.univ| ≤ C * E * ε * M := by
          have hmnon : 0 ≤ (η u).real Set.univ := ENNReal.toReal_nonneg
          simp only [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hmnon]
          exact mul_le_mul
            (mul_le_mul (mul_le_mul hCu hEu (Real.exp_pos _).le hC.le)
              hcut.le (abs_nonneg _) (mul_nonneg hC.le hE.le)) (hM u hu) hmnon (by positivity)
        have hh := abs_add_le
          (Real.exp (σ * (t - u)) * Real.exp (t - u) *
            p.derivative.eval (Real.exp (t - u)) * (η u).real Set.univ)
          ((P (t - u) (η u ∗ₘ η u) - G (t - u) (η u ∗ₘ η u)) / 2)
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
        rw [show J u - H u = Real.exp (σ * (t - u)) * Real.exp (t - u) *
          p.derivative.eval (Real.exp (t - u)) * (η u).real Set.univ +
          (P (t - u) (η u ∗ₘ η u) - G (t - u) (η u ∗ₘ η u)) / 2 by dsimp [J, H]; ring]
        nlinarith only [hh, hbd, hm]
      have htime : |timeIntegral J r t - timeIntegral H r t| ≤
          ((C * E * M + C * M ^ 2) * ε) * (t - r) := by
        unfold timeIntegral
        rw [← intervalIntegral.integral_sub hpoly.1 hInt, ← Real.norm_eq_abs]
        have hb := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun x => J x - H x) (a := r) (b := t) (C := (C * E * M + C * M ^ 2) * ε)
          (fun x hx => by
            rw [Real.norm_eq_abs]
            exact hJ x (Set.uIcc_of_le hrt ▸ Set.uIoc_subset_uIcc hx))
        simpa only [abs_of_nonneg (sub_nonneg.2 hrt)] using hb
      have hclose := abs_add_le
        ((G (t - t) (η t) - P (t - t) (η t)) + (P (t - r) (η r) - G (t - r) (η r)))
        (timeIntegral J r t - timeIntegral H r t)
      have hclose' := abs_add_le (G (t - t) (η t) - P (t - t) (η t))
        (P (t - r) (η r) - G (t - r) (η r))
      rw [abs_sub_comm (G (t - t) (η t))] at hclose'
      have heq : err =
          ((G (t - t) (η t) - P (t - t) (η t)) + (P (t - r) (η r) - G (t - r) (η r))) +
          (timeIntegral J r t - timeIntegral H r t) := by
        dsimp [err]
        rw [← hpoly.2]
        ring
      rw [heq]
      dsimp [K]
      nlinarith only [hclose, hclose', htime, hP t ⟨hrt, le_rfl⟩, hP r ⟨le_rfl, hrt⟩]
    have herr : err = 0 := by
      by_contra hne
      have hpos := abs_pos.2 hne
      have hden : 0 < K + 1 := by linarith
      have hb := hErr (|err| / (K + 1)) (div_pos hpos hden)
      rw [← mul_div_assoc, le_div_iff₀ hden] at hb
      nlinarith only [hb, hpos]
    exact sub_eq_zero.1 herr
  rw [← hA]
  simpa only [add_comm] using (sub_eq_iff_eq_add.1 hGoal)


/-- On the projected interval, high moments recover the mass at the absorbing
boundary `y = 1`. -/
theorem tendsto_measureMoment_boundary {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (measureMoment ν) atTop (𝓝 (ν.real {1})) := by
  let F : ℝ → ℝ := Set.indicator ({1} : Set ℝ) (fun _ => 1)
  have hF : (∫ y, F y ∂ν) = ν.real {1} := by
    change (∫ y, ({1} : Set ℝ).indicator (1 : ℝ → ℝ) y ∂ν) = _
    rw [integral_indicator_one (measurableSet_singleton _)]
  rw [← hF]
  apply MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    exact (by fun_prop : Measurable (fun y : ℝ => y ^ n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [hν] with y hy
    rw [Real.norm_of_nonneg (pow_nonneg hy.1 _)]
    exact pow_le_one₀ hy.1 hy.2
  · filter_upwards [hν] with y hy
    by_cases h : y = 1
    · subst y
      simpa [F] using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop))
    · rw [show F y = 0 from Set.indicator_of_notMem (by simpa using h) _]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one hy.1 (lt_of_le_of_ne hy.2 h)

/-- The integrated transform difference equation rules out an atom at the
absorbing boundary for almost every time in the interval. -/
theorem projected_boundary_mass_zero_ae (L : ℕ → ℝ → ℝ) (η : ℝ → Measure ℝ)
    {σ r t M : ℝ} (hrt : r ≤ t) (hM : 0 ≤ M)
    (hf : ∀ u, IsFiniteMeasure (η u))
    (hsupp : ∀ u, ∀ᵐ y ∂(η u), y ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∀ n, Measurable (L n))
    (hb : ∀ n u, u ∈ Set.Icc r t → |L n u| ≤ M)
    (ha : ∀ᵐ u : ℝ, u ∈ Set.Icc r t → ∀ n, L n u = measureMoment (η u) n)
    (hD : ∀ n : ℕ, (L n t - L 0 t) - (L n r - L 0 r) =
      timeIntegral (fun x => psiS (σ + n) (L n x) - psiS σ (L 0 x)) r t) :
    ∀ᵐ u ∂(volume.restrict (Set.Ioc r t)), η u {1} = 0 := by
  let ω := volume.restrict (Set.Ioc r t)
  let E (n : ℕ) (u : ℝ) := σ * (L n u - L 0 u) + ((L n u) ^ 2 - (L 0 u) ^ 2) / 2
  let K := 2 * |σ| * M + M ^ 2
  have hsuppω : ∀ᵐ u ∂ω, u ∈ Set.Icc r t :=
    (ae_restrict_mem measurableSet_Ioc).mono fun _ hu => ⟨hu.1.le, hu.2⟩
  have hm' (n : ℕ) : AEStronglyMeasurable (L n) ω := (hm n).aestronglyMeasurable
  have hLn (n : ℕ) : Integrable (L n) ω :=
    (integrable_const M).mono' (hm' n) (hsuppω.mono fun u hu =>
      Real.norm_eq_abs (L n u) ▸ hb n u hu)
  have hE_bound (n : ℕ) (u : ℝ) (hu : u ∈ Set.Icc r t) : ‖E n u‖ ≤ K := by
    have hLzero := hb 0 u hu
    have hLnu := hb n u hu
    have hsd : |L n u - L 0 u| ≤ 2 * M := by
      have h := norm_sub_le (L n u) (L 0 u)
      simp only [Real.norm_eq_abs] at h
      linarith
    have hsq (j : ℕ) : (L j u) ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hM).2 (hb j u hu)
    have hsqdiff : |(L n u) ^ 2 - (L 0 u) ^ 2| / 2 ≤ M ^ 2 := by
      have h := norm_sub_le ((L n u) ^ 2) ((L 0 u) ^ 2)
      simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (L n u)), abs_of_nonneg (sq_nonneg (L 0 u))] at h
      linarith [hsq n, hsq 0]
    unfold E K
    rw [Real.norm_eq_abs]
    have h := abs_add_le (σ * (L n u - L 0 u)) (((L n u) ^ 2 - (L 0 u) ^ 2) / 2)
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    linarith only [h, hsqdiff, mul_le_mul_of_nonneg_left hsd (abs_nonneg σ)]
  have hE (n : ℕ) : Integrable (E n) ω := by
    refine (integrable_const K).mono' ?_ (hsuppω.mono (hE_bound n))
    have hme : Measurable (E n) := by
      have hm₁ := hm n
      have hm₀ := hm 0
      dsimp [E]
      fun_prop
    exact hme.aestronglyMeasurable
  have hEq (n : ℕ) : (L n t - L 0 t) - (L n r - L 0 r) =
      (n : ℝ) * (∫ u, L n u ∂ω) + ∫ u, E n u ∂ω := by
    rw [hD n, timeIntegral, intervalIntegral.integral_of_le hrt]
    change (∫ u, psiS (σ + n) (L n u) - psiS σ (L 0 u) ∂ω) = _
    have hi : Integrable (fun u => (n : ℝ) * L n u) ω := (hLn n).const_mul _
    rw [← integral_const_mul, ← integral_add hi (hE n)]
    apply integral_congr_ae
    exact ae_of_all _ fun u => by dsimp [E, psiS]; ring
  have hInt (n : ℕ) (hn : 0 < n) : |∫ u, L n u ∂ω| ≤ (4 * M + K * ω.real Set.univ) / n := by
    have hEb := MeasureTheory.norm_integral_le_of_norm_le_const (hsuppω.mono (hE_bound n))
    rw [Real.norm_eq_abs] at hEb
    have hEnd (u : ℝ) (hu : u ∈ Set.Icc r t) : |L n u - L 0 u| ≤ 2 * M := by
      have h := norm_sub_le (L n u) (L 0 u)
      simp only [Real.norm_eq_abs] at h
      linarith [hb n u hu, hb 0 u hu]
    have h := norm_sub_le ((L n t - L 0 t) - (L n r - L 0 r)) (∫ u, E n u ∂ω)
    have hd := norm_sub_le (L n t - L 0 t) (L n r - L 0 r)
    simp only [Real.norm_eq_abs] at h hd
    have hEq' : (L n t - L 0 t) - (L n r - L 0 r) - (∫ u, E n u ∂ω) =
        (n : ℝ) * (∫ u, L n u ∂ω) := by linarith [hEq n]
    rw [hEq', abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at h
    apply (le_div_iff₀ (Nat.cast_pos.2 hn)).2
    linarith only [h, hEb, hd, hEnd r ⟨le_rfl, hrt⟩, hEnd t ⟨hrt, le_rfl⟩]
  have hsmall : Tendsto (fun n : ℕ => ∫ u, L n u ∂ω) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.2
    have hd : Tendsto (fun n : ℕ => (4 * M + K * ω.real Set.univ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hd
      (Eventually.of_forall fun n => norm_nonneg _) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [Real.norm_eq_abs]
    exact hInt n hn
  have hpoint : ∀ᵐ u ∂ω, Tendsto (fun n => L n u) atTop (𝓝 ((η u).real {1})) := by
    filter_upwards [hsuppω, ae_mono Measure.restrict_le_self ha] with u hu h
    letI := hf u
    simp_rw [h hu]
    exact tendsto_measureMoment_boundary (hsupp _)
  have hDom := MeasureTheory.tendsto_integral_of_dominated_convergence (μ := ω)
    (F := L) (f := fun u => (η u).real {1}) (fun _ => M) hm' (integrable_const _)
    (fun n => hsuppω.mono fun u hu => Real.norm_eq_abs (L n u) ▸ hb n u hu) hpoint
  have hlim : (∫ u, (η u).real {1} ∂ω) = 0 := tendsto_nhds_unique hDom hsmall
  have hfi : Integrable (fun u => (η u).real {1}) ω := by
    refine (integrable_const M).mono' (aestronglyMeasurable_of_tendsto_ae atTop hm' hpoint) ?_
    filter_upwards [hpoint, hsuppω] with u hu hI
    exact le_of_tendsto' hu.norm fun n => Real.norm_eq_abs (L n u) ▸ hb n u hI
  have hzero := (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all ω fun u => ENNReal.toReal_nonneg) hfi).1 hlim
  filter_upwards [hzero] with u hu
  letI := hf u
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hu


private theorem integral_floor_partial (G : ℕ → ℝ) {N u : ℝ} (hN : 0 < N) (k : ℕ)
    (hlo : (k : ℝ) / N ≤ u) (hhi : u ≤ ((k : ℝ) + 1) / N) :
    IntervalIntegrable (fun x => G ⌊N * x⌋₊) volume ((k : ℝ) / N) u ∧
      timeIntegral (fun x => G ⌊N * x⌋₊) ((k : ℝ) / N) u = (u - (k : ℝ) / N) * G k := by
  have hEq : Set.EqOn (fun _ : ℝ => G k) (fun x => G ⌊N * x⌋₊) (Set.uIoo ((k : ℝ) / N) u) := by
    rw [Set.uIoo_of_le hlo]
    intro x hx
    have hx₀ : 0 ≤ x := (div_nonneg (Nat.cast_nonneg k) hN.le).trans hx.1.le
    have hk : ⌊N * x⌋₊ = k := (Nat.floor_eq_iff (mul_nonneg hN.le hx₀)).2
      ⟨by simpa only [mul_comm N x] using (div_le_iff₀ hN).1 hx.1.le,
        by simpa only [mul_comm N x] using (lt_div_iff₀ hN).1 (hx.2.trans_le hhi)⟩
    simp only [hk]
  refine ⟨intervalIntegrable_const.congr_uIoo hEq, ?_⟩
  unfold timeIntegral
  rw [intervalIntegral.integral_congr_uIoo hEq.symm, intervalIntegral.integral_const, smul_eq_mul]

private theorem integral_floor_grid (G : ℕ → ℝ) {N : ℝ} (hN : 0 < N) {m n : ℕ} (hmn : m ≤ n) :
    IntervalIntegrable (fun x => G ⌊N * x⌋₊) volume ((m : ℝ) / N) ((n : ℝ) / N) ∧
      timeIntegral (fun x => G ⌊N * x⌋₊) ((m : ℝ) / N) ((n : ℝ) / N) =
        (∑ k ∈ Finset.Ico m n, G k) / N := by
  have hk (k : ℕ) :
      IntervalIntegrable (fun x => G ⌊N * x⌋₊) volume ((k : ℝ) / N) ((↑(k + 1) : ℝ) / N) ∧
        timeIntegral (fun x => G ⌊N * x⌋₊) ((k : ℝ) / N) ((↑(k + 1) : ℝ) / N) = G k / N := by
    obtain ⟨hI, h⟩ := integral_floor_partial G hN k
      (show (k : ℝ) / N ≤ ((k : ℝ) + 1) / N by gcongr; linarith) le_rfl
    rw [Nat.cast_add, Nat.cast_one]
    refine ⟨hI, h.trans ?_⟩
    ring
  have hI (k : ℕ) (_ : k ∈ Set.Ico m n) := (hk k).1
  refine ⟨IntervalIntegrable.trans_iterate_Ico hmn hI, ?_⟩
  unfold timeIntegral
  rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico hmn hI, Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => (hk k).2

private theorem abs_psiS_le_of_abs_le {w x T : ℝ} (hw : 0 ≤ w) (hT : 0 ≤ T)
    (hx : |x| ≤ T) : |psiS w x| ≤ w * T + T ^ 2 / 2 := by
  have hsq : x ^ 2 ≤ T ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hT).2 hx
  unfold psiS
  calc
    _ ≤ |w * x| + |x ^ 2 / 2| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg hw, abs_of_nonneg (by positivity : 0 ≤ x ^ 2 / 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left hx hw)
        (div_le_div_of_nonneg_right hsq (by norm_num))

/-- Convert a summed defect estimate for discrete transform differences into
an interval-integral estimate. The off-grid endpoints contribute at most
`2K/N`. -/
theorem discrete_difference_to_timeIntegral (D G : ℕ → ℝ)
    {N r t K ε : ℝ} (hN : 0 < N) (hr : 0 ≤ r) (hrt : r ≤ t) (hK : 0 ≤ K)
    (hG : ∀ n ∈ Set.Icc ⌊N * r⌋₊ ⌊N * t⌋₊, |G n| ≤ K)
    (hErr : ∑ n ∈ Finset.Ico ⌊N * r⌋₊ ⌊N * t⌋₊,
      |D (n + 1) - D n - G n / N| ≤ ε) :
    |D ⌊N * t⌋₊ - D ⌊N * r⌋₊ - timeIntegral (fun x => G ⌊N * x⌋₊) r t| ≤
      ε + 2 * K / N := by
  let m := ⌊N * r⌋₊
  let n := ⌊N * t⌋₊
  have hmn : m ≤ n := Nat.floor_mono (mul_le_mul_of_nonneg_left hrt hN.le)
  have hfl (u : ℝ) (hu : 0 ≤ u) :
      (⌊N * u⌋₊ : ℝ) / N ≤ u ∧ u ≤ ((⌊N * u⌋₊ : ℝ) + 1) / N := by
    constructor
    · apply (div_le_iff₀ hN).2
      simpa only [mul_comm u N] using Nat.floor_le (mul_nonneg hN.le hu)
    · apply (le_div_iff₀ hN).2
      simpa only [mul_comm u N] using (Nat.lt_floor_add_one (N * u)).le
  obtain ⟨hir, hIr⟩ := integral_floor_partial G hN m (hfl r hr).1 (hfl r hr).2
  obtain ⟨hit, hIt⟩ := integral_floor_partial G hN n (hfl t (hr.trans hrt)).1 (hfl t (hr.trans hrt)).2
  obtain ⟨higrid, hIgrid⟩ := integral_floor_grid G hN hmn
  have rt := hir.symm.trans (higrid.trans hit)
  have hI : timeIntegral (fun x => G ⌊N * x⌋₊) r t =
      (∑ k ∈ Finset.Ico m n, G k) / N + (t - (n : ℝ) / N) * G n -
        (r - (m : ℝ) / N) * G m := by
    have he₁ := intervalIntegral.integral_add_adjacent_intervals hir rt
    have he₂ := intervalIntegral.integral_add_adjacent_intervals higrid hit
    dsimp only [timeIntegral] at hIr hIt hIgrid ⊢
    linarith only [he₁, he₂, hIr, hIt, hIgrid]
  have hed : |D n - D m - (∑ k ∈ Finset.Ico m n, G k) / N| ≤ ε := by
    rw [← Finset.sum_Ico_sub D hmn, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans hErr
  have hb (u : ℝ) (hu : 0 ≤ u) (hb' : |G ⌊N * u⌋₊| ≤ K) :
      |(u - (⌊N * u⌋₊ : ℝ) / N) * G ⌊N * u⌋₊| ≤ K / N := by
    have h0 := sub_nonneg.2 (hfl u hu).1
    have h1 : u - (⌊N * u⌋₊ : ℝ) / N ≤ 1 / N := by
      have h := (hfl u hu).2
      rw [add_div] at h
      linarith
    rw [abs_mul, abs_of_nonneg h0]
    calc
      _ ≤ (1 / N) * K := mul_le_mul h1 hb' (abs_nonneg _) (by positivity)
      _ = _ := by ring
  change |D n - D m - timeIntegral (fun x => G ⌊N * x⌋₊) r t| ≤ _
  rw [hI]
  have h := norm_sub_le (D n - D m - (∑ k ∈ Finset.Ico m n, G k) / N)
    ((t - (n : ℝ) / N) * G n - (r - (m : ℝ) / N) * G m)
  have h' := norm_sub_le ((t - (n : ℝ) / N) * G n) ((r - (m : ℝ) / N) * G m)
  simp only [Real.norm_eq_abs] at h h'
  have hform : D n - D m -
      ((∑ k ∈ Finset.Ico m n, G k) / N + (t - (n : ℝ) / N) * G n - (r - (m : ℝ) / N) * G m) =
      (D n - D m - (∑ k ∈ Finset.Ico m n, G k) / N) -
        ((t - (n : ℝ) / N) * G n - (r - (m : ℝ) / N) * G m) := by ring
  rw [hform]
  have hbr : |(r - (m : ℝ) / N) * G m| ≤ K / N := hb r hr (hG m ⟨le_rfl, hmn⟩)
  have hbt : |(t - (n : ℝ) / N) * G n| ≤ K / N := hb t (hr.trans hrt) (hG n ⟨hmn, le_rfl⟩)
  rw [show 2 * K / N = K / N + K / N by ring]
  linarith only [h, h', hed, hbr, hbt]


/-- Sequential compactness for a tight family of finite measures with
convergent masses, proved by normalizing to probability measures in the
positive-mass case. -/
theorem exists_finiteMeasure_subseq_of_tight {μ : ℕ → FiniteMeasure ℝ} {m : ℝ≥0}
    (hm : Tendsto (fun j => (μ j).mass) atTop (𝓝 m))
    {K : ℕ → Set ℝ} (hK : ∀ n, IsCompact (K n))
    {a : ℕ → ℝ≥0} (ha : Tendsto a atTop (𝓝 0))
    (htail : ∀ j n, μ j (K n)ᶜ ≤ a n) :
    ∃ (ν : FiniteMeasure ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun j => μ (φ j)) atTop (𝓝 ν) := by
  by_cases hm0 : m = 0
  · refine ⟨0, id, strictMono_id, FiniteMeasure.tendsto_zero_of_tendsto_zero_mass ?_⟩
    simpa only [hm0, id_eq] using hm
  have hmpos : 0 < m := pos_iff_ne_zero.2 hm0
  let c := m / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hcm : c < m := div_lt_self hmpos (by norm_num)
  have hv : Tendsto (fun n => c⁻¹ * a n) atTop (𝓝 0) := by
    simpa only [mul_zero] using ha.const_mul c⁻¹
  have hcompact := isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le hv hK
    (Or.inl (show NormalSpace ℝ from inferInstance))
  have hnorm : ∀ᶠ j in atTop, (μ j).normalize ∈ {p : ProbabilityMeasure ℝ |
      ∀ n, p (K n)ᶜ ≤ c⁻¹ * a n} := by
    filter_upwards [hm.eventually (Ici_mem_nhds hcm)] with j hj
    have hj' : 0 < (μ j).mass := hc.trans_le hj
    have hμj : μ j ≠ 0 := (FiniteMeasure.mass_nonzero_iff _).1 hj'.ne'
    intro n
    rw [FiniteMeasure.normalize_eq_of_nonzero _ hμj]
    exact mul_le_mul (inv_anti₀ hc hj) (htail j n) (by positivity) (by positivity)
  obtain ⟨p, _, φ, hφ, hφp⟩ := hcompact.tendsto_subseq' hnorm.frequently
  have hp : Tendsto (fun j => (μ (φ j)).normalize.toFiniteMeasure) atTop (𝓝 p.toFiniteMeasure) :=
    (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds atTop).1 hφp
  refine ⟨m • p.toFiniteMeasure, φ, hφ, ?_⟩
  rw [FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto]
  intro f
  have hμ := (FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto.1 hp) f
  rw [FiniteMeasure.smul_testAgainstNN_apply, smul_eq_mul]
  have hprod := (hm.comp hφ.tendsto_atTop).mul hμ
  apply hprod.congr'
  filter_upwards with j
  exact ((μ (φ j)).testAgainstNN_eq_mass_mul f).symm


/-- The Mellin defect-sum bound gives a uniform integral identity, up to
order `1/N`, on a time interval with its left endpoint strictly inside
the interval of bounded transforms. -/
theorem transform_difference_timeIntegral_error {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {r δ a s₀ s M : ℝ} (hr : 0 < r) (hδ : 0 < δ) (ha : r < a)
    (hs₀ : 0 ≤ s₀) (hs : s₀ ≤ s) (hM : 0 ≤ M) :
    ∃ C : ℝ, ∀ᶠ N : ℝ in atTop, ∀ h : ℝ,
      (∀ t ∈ Set.Icc r (r + δ), |transformAt μ B h N ⌊N * t⌋₊ s₀| ≤ M) →
      ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ r + δ →
        let L (n : ℕ) (w : ℝ) := transformAt μ B h N n w
        let D (n : ℕ) := L n s - L n s₀
        let G (n : ℕ) := psiS s (L n s) - psiS s₀ (L n s₀)
        |D ⌊N * v⌋₊ - D ⌊N * u⌋₊ - timeIntegral (fun t => G ⌊N * t⌋₊) u v| ≤ C / N := by
  obtain ⟨F, hF⟩ := transform_floor_aux hpos hmean hB
  obtain ⟨N₁, C₁, hErr⟩ := transform_difference_aux hpos hmean hB r δ s₀ s M hr hδ hs₀ hs
  let ρ := 2 / B
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ' : ρ < 1 := (div_lt_one (by linarith)).2 hB
  let P := M + |F|
  have hP : 0 ≤ P := add_nonneg hM (abs_nonneg _)
  let K := s * P + P ^ 2 / 2 + (s₀ * M + M ^ 2 / 2)
  have hs' := hs₀.trans hs
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨C₁ + 2 * K, ?_⟩
  have ha' : 0 < a := hr.trans ha
  have hgeom : Tendsto (fun N : ℝ => N * ρ ^ ⌊N * a⌋₊) atTop (𝓝 0) := by
    simpa only [pow_one] using tendsto_pow_mul_geometric_floor hρ hρ' ha' 1
  filter_upwards [eventually_ge_atTop (max N₁ (max 1 (1 / (a - r)))),
    hgeom.eventually (Iic_mem_nhds zero_lt_one),
    (tendsto_weightExponent_atTop hB s).eventually (Ioi_mem_nhds (theta_pos hB))]
    with N hN hg hq
  intro h hbase u v hau huv hv
  have hN1 : 1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN0 : 0 < N := zero_lt_one.trans_le hN1
  have haeN : 1 / (a - r) ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hgap : 1 ≤ N * (a - r) := (div_le_iff₀ (sub_pos.2 ha)).1 haeN
  let L (n : ℕ) (w : ℝ) := transformAt μ B h N n w
  let D (n : ℕ) := L n s - L n s₀
  let G (n : ℕ) := psiS s (L n s) - psiS s₀ (L n s₀)
  let m := ⌊N * u⌋₊
  let n := ⌊N * v⌋₊
  have hu : 0 < u := ha'.trans_le hau
  have hfl₁ : r * N ≤ (m : ℝ) := by
    have hfl := Nat.lt_floor_add_one (N * u)
    dsimp [m]
    nlinarith [mul_le_mul_of_nonneg_left hau hN0.le]
  have hfl₂ : (n : ℝ) ≤ (r + δ) * N := by
    have h := Nat.floor_le (mul_nonneg hN0.le (hu.le.trans huv))
    dsimp [n]
    nlinarith [mul_le_mul_of_nonneg_left hv hN0.le]
  have hG (k : ℕ) (hk : k ∈ Set.Icc m n) : |G k| ≤ K := by
    have hkL : |L k s₀| ≤ M := by
      have htk : (k : ℝ) / N ∈ Set.Icc r (r + δ) := by
        exact ⟨(le_div_iff₀ hN0).2 (hfl₁.trans (Nat.cast_le.2 hk.1)),
          (div_le_iff₀ hN0).2 ((Nat.cast_le.2 hk.2).trans hfl₂)⟩
      have hp := hbase _ htk
      rw [show N * ((k : ℝ) / N) = k by field_simp [hN0.ne'], Nat.floor_natCast] at hp
      exact hp
    have hpow : N * ρ ^ k ≤ 1 := by
      have hka : ⌊N * a⌋₊ ≤ k := (Nat.floor_mono (mul_le_mul_of_nonneg_left hau hN0.le)).trans hk.1
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ.le hρ'.le hka) hN0.le).trans hg
    have hf := hF h N k s₀ s hN0 hs₀ hs hq.le
    have hFpow : F * N * ρ ^ k ≤ |F| := by
      rw [mul_assoc]
      calc
        _ ≤ |F| * (N * ρ ^ k) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    have hb : |L k s| ≤ P := by
      change -(F * N * ρ ^ k) ≤ L k s ∧ L k s ≤ L k s₀ + F * N * ρ ^ k at hf
      exact abs_le.2 ⟨by dsimp [P]; linarith [hf.1],
        by dsimp [P]; linarith [hf.2, (le_abs_self (L k s₀)).trans hkL]⟩
    have htri := norm_sub_le (psiS s (L k s)) (psiS s₀ (L k s₀))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at htri
    exact htri.trans (add_le_add (abs_psiS_le_of_abs_le (hs₀.trans hs) hP hb) (abs_psiS_le_of_abs_le hs₀ hM hkL))
  have hsum : ∑ k ∈ Finset.Ico m n, |D (k + 1) - D k - G k / N| ≤ C₁ / N := by
    have hev := hErr N ((le_max_left _ _).trans hN) h hbase s ⟨hs, le_rfl⟩
    have hsub : Finset.Ico m n ⊆ Finset.Ico ⌈r * N⌉₊ ⌈(r + δ) * N⌉₊ := by
      apply Finset.Ico_subset_Ico
      · exact Nat.ceil_le.2 hfl₁
      · exact_mod_cast (show (n : ℝ) ≤ (⌈(r + δ) * N⌉₊ : ℝ) from
          hfl₂.trans (Nat.le_ceil _))
    have hb := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => abs_nonneg
      (transformError μ B h N k s s₀))
    exact hb.trans hev
  have he := discrete_difference_to_timeIntegral D G hN0 hu.le huv hK hG hsum
  change |D n - D m - timeIntegral (fun t => G ⌊N * t⌋₊) u v| ≤ _
  simpa only [add_div] using he


/-- Convergence of the masses and a uniform bound at a smaller weight give
a weakly converging subsequence at a strictly larger weight. -/
theorem exists_weak_subseq_of_weight_gap {ν : ℕ → Measure ℝ} {s₀ s : ℝ} (hs : s₀ < s)
    (hν : ∀ j, ν j (Set.Iio 0) = 0)
    (hfin : ∀ j, IsFiniteMeasure (weightedMeasure (ν j) s₀))
    {C m : ℝ≥0} (hC : ∀ j, weightedMeasure (ν j) s₀ Set.univ ≤ C)
    (hm : Tendsto (fun j => (weightedMeasure (ν j) s Set.univ).toNNReal) atTop (𝓝 m)) :
    ∃ (ν' : Measure ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      WeakConvergence (fun j => weightedMeasure (ν (φ j)) s) atTop ν' := by
  have hneg (j : ℕ) (w : ℝ) : weightedMeasure (ν j) w (Set.Iio 0) = 0 :=
    withDensity_absolutelyContinuous (ν j) _ (hν j)
  have hle (j : ℕ) : weightedMeasure (ν j) s ≤ weightedMeasure (ν j) s₀ := by
    rw [show s = s₀ + (s - s₀) from by ring, weightedMeasure_add]
    exact weightedMeasure_le_of_nonneg (hneg j s₀) (sub_nonneg.2 hs.le)
  have hf (j : ℕ) : IsFiniteMeasure (weightedMeasure (ν j) s) :=
    ⟨(hle j Set.univ).trans_lt (hfin j).measure_univ_lt_top⟩
  let μ (j : ℕ) : FiniteMeasure ℝ := ⟨weightedMeasure (ν j) s, hf j⟩
  let K (n : ℕ) := Set.Icc (0 : ℝ) (n : ℝ)
  let a (n : ℕ) := (Real.exp (-(s - s₀) * (n : ℝ))).toNNReal * C
  have ha : Tendsto a atTop (𝓝 0) := by
    have hlin : Tendsto (fun n : ℕ => -(s - s₀) * (n : ℝ)) atTop atBot :=
      tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_lt_zero.2 (sub_pos.2 hs))
    have hexp := Real.tendsto_exp_atBot.comp hlin
    have ht : Tendsto (fun n : ℕ => (Real.exp (-(s - s₀) * (n : ℝ))).toNNReal) atTop
        (𝓝 ((0 : ℝ).toNNReal)) :=
      (continuous_real_toNNReal.tendsto 0).comp hexp
    simpa only [a, Real.toNNReal_zero, zero_mul, Function.comp_def] using ht.mul_const C
  have htail (j n : ℕ) : μ j (K n)ᶜ ≤ a n := by
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    change weightedMeasure (ν j) s (K n)ᶜ ≤ (a n : ℝ≥0∞)
    have hSet : (K n)ᶜ = Set.Iio 0 ∪ Set.Ioi (n : ℝ) := by
      ext x
      change (¬(0 ≤ x ∧ x ≤ (n : ℝ))) ↔ x < 0 ∨ (n : ℝ) < x
      constructor
      · intro h
        rcases lt_or_ge x 0 with hx | hx
        · exact Or.inl hx
        · exact Or.inr (lt_of_not_ge fun hn => h ⟨hx, hn⟩)
      · rintro (h | h) hx
        · exact h.not_ge hx.1
        · exact h.not_ge hx.2
    rw [hSet]
    calc
      _ ≤ weightedMeasure (ν j) s (Set.Iio 0) + weightedMeasure (ν j) s (Set.Ioi (n : ℝ)) :=
        measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-(s - s₀) * (n : ℝ))) * weightedMeasure (ν j) s₀ Set.univ := by
        rw [hneg j s, zero_add]
        exact weightedMeasure_tail_le (ν j) hs.le
      _ ≤ (a n : ℝ≥0∞) := by
        exact mul_right_mono (hC j)
  obtain ⟨ν', φ, hφ, hw⟩ := exists_finiteMeasure_subseq_of_tight (μ := μ) hm
    (fun _ => isCompact_Icc) ha htail
  refine ⟨ν', φ, hφ, ν'.2, Eventually.of_forall (fun j => hf (φ j)), ?_⟩
  intro f
  exact (FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 hw) f


/-- Simultaneous uniform subsequences for a countable family of uniformly
bounded Lipschitz approximants, with bounds depending on the family index. -/
theorem exists_subseq_boundedContinuousFamily {α : Type*} [PseudoMetricSpace α] [CompactSpace α]
    {F : ℕ → ℕ → α →ᵇ ℝ}
    (hb : ∀ k, ∃ M : ℝ, ∀ j x, |F j k x| ≤ M)
    (hL : ∀ k, ∃ L : ℝ≥0, ∀ j, LipschitzWith L (F j k)) :
    ∃ (φ : ℕ → ℕ) (G : ℕ → α →ᵇ ℝ), StrictMono φ ∧
      ∀ k, Tendsto (fun j => F (φ j) k) atTop (𝓝 (G k)) := by
  let A (k : ℕ) : Set (α →ᵇ ℝ) := Set.range (fun j => F j k)
  have hA (k : ℕ) : IsCompact (closure (A k)) := by
    obtain ⟨M, hM⟩ := hb k
    obtain ⟨L, hLip⟩ := hL k
    apply BoundedContinuousFunction.arzela_ascoli (Set.Icc (-M) M) isCompact_Icc
    · rintro f x ⟨j, rfl⟩
      exact abs_le.1 (hM j x)
    · have hE : UniformEquicontinuous (fun j x => F j k x) := by
        apply Metric.uniformEquicontinuous_iff.2
        intro ε hε
        have hp : 0 < (L : ℝ) + 1 := by positivity
        refine ⟨ε / ((L : ℝ) + 1), div_pos hε hp, ?_⟩
        intro x y hxy j
        have hlt := (lt_div_iff₀ hp).1 hxy
        calc
          _ ≤ (L : ℝ) * dist x y := (hLip j).dist_le_mul x y
          _ ≤ dist x y * ((L : ℝ) + 1) := by nlinarith [dist_nonneg (x := x) (y := y)]
          _ < ε := hlt
      apply UniformEquicontinuous.equicontinuous
      apply Metric.uniformEquicontinuous_iff.2
      intro ε hε
      obtain ⟨δ, hδ, h⟩ := Metric.uniformEquicontinuous_iff.1 hE ε hε
      refine ⟨δ, hδ, fun x y hxy f => ?_⟩
      obtain ⟨j, hj⟩ := f.2
      rw [← hj]
      exact h x y hxy j
  let J (j : ℕ) (k : ℕ) : closure (A k) := ⟨F j k, subset_closure ⟨j, rfl⟩⟩
  letI (k : ℕ) : CompactSpace (closure (A k)) := isCompact_iff_compactSpace.1 (hA k)
  obtain ⟨G, φ, hφ, h⟩ := CompactSpace.tendsto_subseq J
  refine ⟨φ, fun k => G k, hφ, fun k => ?_⟩
  exact continuous_subtype_val.continuousAt.tendsto.comp (tendsto_pi_nhds.1 h k)


/-- Asymptotically Lipschitz functions on a compact space have a common
uniformly convergent subsequence across countably many coordinates. -/
theorem exists_subseq_uniformly_of_approx_lipschitz {α : Type*} [PseudoMetricSpace α]
    [CompactSpace α] {f : ℕ → ℕ → α → ℝ}
    (h : ∀ k, ∃ (M : ℝ) (L : ℝ≥0) (e : ℕ → ℝ), 0 ≤ M ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ j in atTop, (∀ x, |f j k x| ≤ M) ∧
        (∀ x y, dist (f j k x) (f j k y) ≤ (L : ℝ) * dist x y + e j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → α →ᵇ ℝ), StrictMono φ ∧
      ∀ k, TendstoUniformly (fun j x => f (φ j) k x) (g k) atTop := by
  classical
  choose M L e hM he hgood using h
  let Good (j k : ℕ) : Prop := (∀ x, |f j k x| ≤ M k) ∧
    (∀ x y, dist (f j k x) (f j k y) ≤ (L k : ℝ) * dist x y + e k j)
  let S (j k : ℕ) (x : α) := Set.range (fun u => f j k u + (L k : ℝ) * dist x u)
  have hs (j k : ℕ) (x : α) : (S j k x).Nonempty := ⟨_, x, rfl⟩
  have hb (j k : ℕ) (x : α) (hj : Good j k) : BddBelow (S j k x) := by
    refine ⟨-M k, ?_⟩
    rintro _ ⟨u, rfl⟩
    have hu := (abs_le.1 (hj.1 u)).1
    have hp : 0 ≤ (L k : ℝ) * dist x u := by positivity
    linarith
  let Q (j k : ℕ) (x : α) := if Good j k then sInf (S j k x) else 0
  have hLip (j k : ℕ) : LipschitzWith (L k) (Q j k) := by
    apply LipschitzWith.of_dist_le_mul
    by_cases hj : Good j k
    · have hle (x y : α) : Q j k x ≤ Q j k y + (L k : ℝ) * dist x y := by
        simp only [Q, ite_eq_left hj]
        apply sub_le_iff_le_add.1
        refine le_csInf (hs j k y) ?_
        rintro _ ⟨u, rfl⟩
        have hh := csInf_le (hb j k x hj) (show f j k u + (L k : ℝ) * dist x u ∈ S j k x from
          ⟨u, rfl⟩)
        have htri := mul_le_mul_of_nonneg_left (dist_triangle x y u) (L k).coe_nonneg
        rw [mul_add] at htri
        linarith only [hh, htri]
      intro x y
      rw [Real.dist_eq, abs_le]
      refine ⟨?_, by linarith [hle x y]⟩
      have hy := hle y x
      rw [dist_comm y x] at hy
      linarith
    · intro x y
      simp only [Q, ite_eq_right hj, dist_self]
      positivity
  have hUpper (j k : ℕ) (x : α) (hj : Good j k) : Q j k x ≤ f j k x := by
    simpa only [Q, ite_eq_left hj, dist_self, mul_zero, add_zero] using
      csInf_le (hb j k x hj) (show f j k x + (L k : ℝ) * dist x x ∈ S j k x from ⟨x, rfl⟩)
  have hQ (j k : ℕ) (x : α) : |Q j k x| ≤ M k := by
    by_cases hj : Good j k
    · refine abs_le.2 ⟨?_, (hUpper j k x hj).trans (abs_le.1 (hj.1 x)).2⟩
      simp only [Q, ite_eq_left hj]
      apply le_csInf (hs j k x)
      rintro _ ⟨u, rfl⟩
      exact (abs_le.1 (hj.1 u)).1.trans (le_add_of_nonneg_right (by positivity))
    · simp [Q, hj, hM k]
  let P (j k : ℕ) : α →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨Q j k, (hLip j k).continuous⟩
  obtain ⟨φ, g, hφ, hcon⟩ := exists_subseq_boundedContinuousFamily
    (F := P) (fun k => ⟨M k, fun j x => hQ j k x⟩) (fun k => ⟨L k, fun j => hLip j k⟩)
  refine ⟨φ, g, hφ, fun k => ?_⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hP := Metric.tendstoUniformly_iff.1
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 (hcon k))
      (ε / 2) (by positivity)
  have hgood' : ∀ᶠ j in atTop, Good (φ j) k := hφ.tendsto_atTop.eventually (hgood k)
  have he' : ∀ᶠ j in atTop, e k (φ j) < ε / 2 :=
    hφ.tendsto_atTop.eventually ((he k).eventually (Iio_mem_nhds (by positivity)))
  filter_upwards [hP, hgood', he'] with j hj hgj hej x
  have hbnd : f (φ j) k x - e k (φ j) ≤ Q (φ j) k x := by
    simp only [Q, ite_eq_left hgj]
    refine le_csInf (hs (φ j) k x) ?_
    rintro _ ⟨u, rfl⟩
    have hd := hgj.2 x u
    rw [Real.dist_eq] at hd
    linarith only [hd, le_abs_self (f (φ j) k x - f (φ j) k u)]
  have hdist : dist (Q (φ j) k x) (f (φ j) k x) ≤ e k (φ j) := by
    rw [dist_comm, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (hUpper (φ j) k x hgj))]
    linarith
  have h₁ : dist (g k x) (Q (φ j) k x) < ε / 2 := hj x
  exact (dist_triangle (g k x) (Q (φ j) k x) (f (φ j) k x)).trans_lt
    (by linarith only [h₁, hdist, hej])


/-- A uniform bound at the base weight transfers to every fixed larger
weight, with a bound independent of that larger weight. -/
theorem transform_bounded_at_larger_weight {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ r b s₀ s M : ℝ, 0 < r → 0 ≤ s₀ → s₀ ≤ s → 0 ≤ M →
      ∀ᶠ N : ℝ in atTop, ∀ h : ℝ,
        (∀ t ∈ Set.Icc r b, |transformAt μ B h N ⌊N * t⌋₊ s₀| ≤ M) →
        ∀ t ∈ Set.Icc r b, |transformAt μ B h N ⌊N * t⌋₊ s| ≤ M + F := by
  obtain ⟨C, hfloor⟩ := transform_floor_aux hpos hmean hB
  refine ⟨|C|, abs_nonneg _, fun r b s₀ s M hr hs₀ hss hM => ?_⟩
  let ρ := 2 / B
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ' : ρ < 1 := (div_lt_one (by linarith)).2 hB
  have hGeom : Tendsto (fun N : ℝ => N * ρ ^ ⌊N * r⌋₊) atTop (𝓝 0) := by
    simpa only [pow_one] using tendsto_pow_mul_geometric_floor hρ hρ' hr 1
  filter_upwards [eventually_gt_atTop (0 : ℝ), hGeom.eventually (Iic_mem_nhds zero_lt_one),
    (tendsto_weightExponent_atTop hB s).eventually (Ioi_mem_nhds (theta_pos hB))]
    with N hN hGeom hq
  intro h hBase t ht
  have h := hfloor h N ⌊N * t⌋₊ s₀ s hN hs₀ hss hq.le
  have hFloor : ⌊N * r⌋₊ ≤ ⌊N * t⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left ht.1 hN.le)
  have hpow : N * ρ ^ ⌊N * t⌋₊ ≤ 1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ.le hρ'.le hFloor) hN.le).trans hGeom
  have hc : C * N * ρ ^ ⌊N * t⌋₊ ≤ |C| := calc
    _ = C * (N * ρ ^ ⌊N * t⌋₊) := by ring
    _ ≤ |C| * (N * ρ ^ ⌊N * t⌋₊) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
  change -(C * N * ρ ^ ⌊N * t⌋₊) ≤ _ ∧ _ ≤ _ + C * N * ρ ^ ⌊N * t⌋₊ at h
  have hb := (le_abs_self _).trans (hBase t ht)
  exact abs_le.2 ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The time increments of differences of transforms are uniformly
Lipschitz up to an error of order `1/N` away from the initial endpoint
of a bounded interval. -/
theorem transform_difference_approx_lipschitz {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {r δ a s₀ s M : ℝ} (hr : 0 < r) (hδ : 0 < δ) (ha : r < a)
    (hs₀ : 0 ≤ s₀) (hs : s₀ ≤ s) (hM : 0 ≤ M) :
    ∃ (K : ℝ≥0) (C : ℝ), ∀ᶠ N : ℝ in atTop, ∀ h : ℝ,
      (∀ t ∈ Set.Icc r (r + δ), |transformAt μ B h N ⌊N * t⌋₊ s₀| ≤ M) →
      ∀ u v : ℝ, u ∈ Set.Icc a (r + δ) → v ∈ Set.Icc a (r + δ) →
        let D (t : ℝ) := transformAt μ B h N ⌊N * t⌋₊ s -
          transformAt μ B h N ⌊N * t⌋₊ s₀
        dist (D u) (D v) ≤ (K : ℝ) * dist u v + C / N := by
  obtain ⟨C, hc⟩ := transform_difference_timeIntegral_error hpos hmean hB hr hδ ha hs₀ hs hM
  obtain ⟨F, hF, hbound⟩ := transform_bounded_at_larger_weight hpos hmean hB
  let K : ℝ≥0 := ⟨s * (M + F) + (M + F) ^ 2 / 2 + (s₀ * M + M ^ 2 / 2), by
    have hS := hs₀.trans hs
    positivity⟩
  refine ⟨K, C, ?_⟩
  filter_upwards [hc, hbound r (r + δ) s₀ s M hr hs₀ hs hM] with N hcalc hBnd
  intro h hb
  let L (t w : ℝ) := transformAt μ B h N ⌊N * t⌋₊ w
  let D (t : ℝ) := L t s - L t s₀
  let G (t : ℝ) := psiS s (L t s) - psiS s₀ (L t s₀)
  have hG (t : ℝ) (ht : t ∈ Set.Icc r (r + δ)) : ‖G t‖ ≤ K := by
    dsimp [G, K]
    have htri := norm_sub_le (psiS s (L t s)) (psiS s₀ (L t s₀))
    simp only [Real.norm_eq_abs] at htri
    exact htri.trans (add_le_add (abs_psiS_le_of_abs_le (hs₀.trans hs) (add_nonneg hM hF) (hBnd h hb t ht))
      (abs_psiS_le_of_abs_le hs₀ hM (hb t ht)))
  have hle (u v : ℝ) (hu : u ∈ Set.Icc a (r + δ)) (hv : v ∈ Set.Icc a (r + δ)) (huv : u ≤ v) :
      dist (D u) (D v) ≤ (K : ℝ) * dist u v + C / N := by
    have hbi := intervalIntegral.norm_integral_le_of_norm_le_const (C := (K : ℝ))
      (a := u) (b := v) (f := G) (fun x hx => by
        have hxuv : x ∈ Set.Icc u v := Set.uIcc_of_le huv ▸ Set.uIoc_subset_uIcc hx
        exact hG x ⟨ha.le.trans (hu.1.trans hxuv.1), hxuv.2.trans hv.2⟩)
    have heq : |D v - D u - timeIntegral G u v| ≤ C / N :=
      hcalc h hb u v hu.1 huv hv.2
    have htv : D v - D u = (D v - D u - timeIntegral G u v) + timeIntegral G u v := by ring
    rw [dist_comm (D u), Real.dist_eq, htv, dist_comm u, Real.dist_eq]
    have htri := abs_add_le (D v - D u - timeIntegral G u v) (timeIntegral G u v)
    rw [Real.norm_eq_abs] at hbi
    exact htri.trans (add_le_add heq hbi) |>.trans_eq (add_comm _ _)
  intro u v hu hv
  rcases le_total u v with huv | huv
  · exact hle u v hu hv huv
  · simpa only [dist_comm (D v), dist_comm v u] using hle v u hv hu huv


/-- Local subsequential compactness of the base transform and all the
differences at integer offsets above it. -/
theorem exists_subseq_transform_limits {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {r δ a s₀ M : ℝ} (hr : 0 < r) (hδ : 0 < δ) (ha : r < a) (ha' : a ≤ r + δ)
    (hs₀ : 0 ≤ s₀) (hM : 0 ≤ M) {ns h : ℕ → ℝ} (hns : Tendsto ns atTop atTop)
    (hBase : ∀ᶠ j in atTop, ∀ t ∈ Set.Icc r (r + δ),
      |transformAt μ B (h j) (ns j) ⌊ns j * t⌋₊ s₀| ≤ M) :
    let X (j k : ℕ) (t : ℝ) := transformAt μ B (h j) (ns j) ⌊ns j * t⌋₊ (s₀ + k)
    ∃ (φ : ℕ → ℕ) (L : ℕ → ℝ → ℝ), StrictMono φ ∧
      (∀ k, Measurable (L k)) ∧
      (∀ᵐ t : ℝ, t ∈ Set.Icc a (r + δ) → ∀ k,
        Tendsto (fun j => X (φ j) k t) atTop (𝓝 (L k t))) ∧
      ∀ k, TendstoUniformlyOn (fun j t => X (φ j) k t - X (φ j) 0 t)
        (fun t => L k t - L 0 t) atTop (Set.Icc a (r + δ)) := by
  let X (j k : ℕ) (t : ℝ) := transformAt μ B (h j) (ns j) ⌊ns j * t⌋₊ (s₀ + k)
  let Y (j : ℕ) (t : ℝ) := transformAt μ B (h j) (ns j) ⌊ns j * t⌋₊ s₀
  have hX0 (j : ℕ) (t : ℝ) : X j 0 t = Y j t := by simp [X, Y]
  obtain ⟨C, hc⟩ := transform_bounded_aux hpos hmean hB
  obtain ⟨N₁, CM, ε, hε, hOne⟩ := hc r δ s₀ M hr hδ hs₀
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hBase.and (hns.eventually_ge_atTop N₁))
  let p₀ (j : ℕ) := j + j₀
  have hp₀ : StrictMono p₀ := fun _ _ hij => Nat.add_lt_add_right hij _
  have hpBase (j : ℕ) : ∀ t ∈ Set.Icc r (r + δ), |Y (p₀ j) t| ≤ M :=
    (hj₀ (p₀ j) (by dsimp [p₀]; omega)).1
  have hpN (j : ℕ) : N₁ ≤ ns (p₀ j) := (hj₀ (p₀ j) (by dsimp [p₀]; omega)).2
  have hest (j : ℕ) (u v : ℝ) (hu : u ∈ Set.Icc a (r + δ)) (hv : v ∈ Set.Icc a (r + δ))
      (huv : u ≤ v) : Y (p₀ j) v - Y (p₀ j) u ≤ CM * (v - u) + ε (ns (p₀ j)) :=
    (hOne (ns (p₀ j)) (hpN j) (h (p₀ j)) (hpBase j)).2.2.2 u v
      (ha.le.trans hu.1) huv hv.2
  obtain ⟨p₁, S, hp₁, hSm, hS⟩ := exists_subseq_ae_tendsto_of_one_sided
    (f := fun j => Y (p₀ j)) ha' (hε.comp (hns.comp hp₀.tendsto_atTop))
    (fun j t ht => hpBase j t ⟨ha.le.trans ht.1, ht.2⟩) hest
  let p (j : ℕ) := p₀ (p₁ j)
  have hp : StrictMono p := hp₀.comp hp₁
  have hp' := hns.comp hp.tendsto_atTop
  let J := Set.Icc a (r + δ)
  let D (j k : ℕ) (t : J) := X (p j) k t - Y (p j) t
  obtain ⟨F, hF, hLarge⟩ := transform_bounded_at_larger_weight hpos hmean hB
  have hAscoli (k : ℕ) : ∃ (M' : ℝ) (K : ℝ≥0) (e : ℕ → ℝ), 0 ≤ M' ∧
      Tendsto e atTop (𝓝 0) ∧ ∀ᶠ j in atTop, (∀ t, |D j k t| ≤ M') ∧
        (∀ u v, dist (D j k u) (D j k v) ≤ (K : ℝ) * dist u v + e j) := by
    let s := s₀ + (k : ℝ)
    have hs : s₀ ≤ s := le_add_of_nonneg_right (Nat.cast_nonneg k)
    obtain ⟨K, C, hD⟩ := transform_difference_approx_lipschitz hpos hmean hB hr hδ ha hs₀ hs hM
    refine ⟨2 * M + F, K, fun j => C / ns (p j), by positivity, tendsto_const_nhds.div_atTop hp', ?_⟩
    filter_upwards [hp'.eventually (hLarge r (r + δ) s₀ s M hr hs₀ hs hM),
      hp'.eventually hD] with j hj₁ hj₂
    have hb := hpBase (p₁ j)
    constructor
    · intro t
      have ht : (t : ℝ) ∈ Set.Icc r (r + δ) := ⟨ha.le.trans t.2.1, t.2.2⟩
      have htri := norm_sub_le (X (p j) k t) (Y (p j) t)
      simp only [Real.norm_eq_abs] at htri
      have hX : |X (p j) k t| ≤ M + F := hj₁ (h (p j)) hb t ht
      have hY : |Y (p j) t| ≤ M := hb t ht
      exact htri.trans (by linarith)
    · exact fun u v => hj₂ (h (p j)) hb u v u.2 v.2
  obtain ⟨q, g, hq, hg⟩ := exists_subseq_uniformly_of_approx_lipschitz hAscoli
  let φ (j : ℕ) := p (q j)
  let A (k : ℕ) : ℝ → ℝ := Function.extend (Subtype.val : J → ℝ) (g k) (fun _ => 0)
  have hA (k : ℕ) (t : ℝ) (ht : t ∈ J) : A k t = g k ⟨t, ht⟩ :=
    Subtype.val_injective.extend_apply (g k) _ ⟨t, ht⟩
  have hAm (k : ℕ) : Measurable (A k) :=
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurable_extend
      (g k).continuous.measurable measurable_const
  have hGzero (t : J) : g 0 t = 0 := by
    apply tendsto_nhds_unique ((hg 0).tendsto_at t)
    simp only [D, hX0, sub_self]
    exact tendsto_const_nhds
  let L (k : ℕ) (t : ℝ) := S t + A k t
  have hLA (k : ℕ) (t : ℝ) (ht : t ∈ J) : L k t - L 0 t = g k ⟨t, ht⟩ := by
    dsimp [L]
    rw [hA k t ht, hA 0 t ht, hGzero]
    ring
  refine ⟨φ, L, hp.comp hq, fun k => hSm.add (hAm k), ?_, ?_⟩
  · filter_upwards [hS] with t ht htJ k
    have hbase := (ht htJ).comp hq.tendsto_atTop
    have hdiff := (hg k).tendsto_at (⟨t, htJ⟩ : J)
    have hh := hbase.add hdiff
    rw [← hA k t htJ] at hh
    apply hh.congr'
    filter_upwards with j
    change Y (φ j) t + (X (φ j) k t - Y (φ j) t) = _
    ring
  · intro k
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε' hε'
    filter_upwards [(Metric.tendstoUniformly_iff.1 (hg k)) ε' hε'] with j hj t ht
    change dist (L k t - L 0 t) (X (φ j) k t - X (φ j) 0 t) < ε'
    rw [hLA k t ht, hX0]
    exact hj ⟨t, ht⟩


/-- Identifying the local integral equation requires only almost-everywhere
convergence of the individual transforms and uniform convergence of their
differences. -/
theorem transform_sublimit_difference_equation {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {r δ a s₀ s M : ℝ} (hr : 0 < r) (hδ : 0 < δ) (ha : r < a)
    (hs₀ : 0 ≤ s₀) (hs : s₀ ≤ s) (hM : 0 ≤ M) {ns h : ℕ → ℝ} (hns : Tendsto ns atTop atTop)
    (hBase : ∀ᶠ j in atTop, ∀ t ∈ Set.Icc r (r + δ),
      |transformAt μ B (h j) (ns j) ⌊ns j * t⌋₊ s₀| ≤ M)
    (L₀ L : ℝ → ℝ)
    (hlim : ∀ᵐ t : ℝ, t ∈ Set.Icc a (r + δ) →
      Tendsto (fun j => transformAt μ B (h j) (ns j) ⌊ns j * t⌋₊ s₀) atTop (𝓝 (L₀ t)) ∧
      Tendsto (fun j => transformAt μ B (h j) (ns j) ⌊ns j * t⌋₊ s) atTop (𝓝 (L t)))
    (hDiff : TendstoUniformlyOn
      (fun j t => transformAt μ B (h j) (ns j) ⌊ns j * t⌋₊ s -
        transformAt μ B (h j) (ns j) ⌊ns j * t⌋₊ s₀)
      (fun t => L t - L₀ t) atTop (Set.Icc a (r + δ))) :
    ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ r + δ →
      (L v - L₀ v) - (L u - L₀ u) =
        timeIntegral (fun t => psiS s (L t) - psiS s₀ (L₀ t)) u v := by
  intro u v hu huv hv
  let X (j : ℕ) (w t : ℝ) := transformAt μ B (h j) (ns j) ⌊ns j * t⌋₊ w
  let D (j : ℕ) (t : ℝ) := X j s t - X j s₀ t
  let G (j : ℕ) (t : ℝ) := psiS s (X j s t) - psiS s₀ (X j s₀ t)
  let G' (t : ℝ) := psiS s (L t) - psiS s₀ (L₀ t)
  let R (j : ℕ) := D j v - D j u - timeIntegral (G j) u v
  have hm (j : ℕ) (w : ℝ) : Measurable (X j w) := by
    let f (n : ℕ) := transformAt μ B (h j) (ns j) n w
    have hf : Measurable f := measurable_of_countable _
    exact hf.comp (measurable_const.mul measurable_id).nat_floor
  have hψ (w : ℝ) : Continuous (psiS w) := by unfold psiS; fun_prop
  have hGm (j : ℕ) : Measurable (G j) :=
    ((hψ s).measurable.comp (hm j s)).sub ((hψ s₀).measurable.comp (hm j s₀))
  obtain ⟨F, hF, hLarge⟩ := transform_bounded_at_larger_weight hpos hmean hB
  have hbound : ∀ᶠ j in atTop, ∀ t ∈ Set.Icc r (r + δ),
      |X j s t| ≤ M + F ∧ |X j s₀ t| ≤ M := by
    filter_upwards [hBase, hns.eventually (hLarge r (r + δ) s₀ s M hr hs₀ hs hM)]
      with j hj hLj t ht
    exact ⟨hLj (h j) hj t ht, hj t ht⟩
  obtain ⟨C, hC⟩ := transform_difference_timeIntegral_error hpos hmean hB hr hδ ha hs₀ hs hM
  let K := s * (M + F) + (M + F) ^ 2 / 2 + (s₀ * M + M ^ 2 / 2)
  have hInt : Tendsto (fun j => timeIntegral (G j) u v) atTop (𝓝 (timeIntegral G' u v)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => K)
    · exact Eventually.of_forall fun j => (hGm j).aestronglyMeasurable
    · filter_upwards [hbound] with j hj
      exact ae_of_all _ fun t ht => by
        rw [Set.uIoc_of_le huv] at ht
        have ht' : t ∈ Set.Icc r (r + δ) := ⟨ha.le.trans (hu.trans ht.1.le), ht.2.trans hv⟩
        have h := norm_sub_le (psiS s (X j s t)) (psiS s₀ (X j s₀ t))
        have h₁ := abs_psiS_le_of_abs_le (hs₀.trans hs) (add_nonneg hM hF) (hj t ht').1
        have h₂ := abs_psiS_le_of_abs_le hs₀ hM (hj t ht').2
        simp only [Real.norm_eq_abs] at h
        exact h.trans (add_le_add h₁ h₂)
    · exact intervalIntegrable_const
    · filter_upwards [hlim] with t ht ht'
      rw [Set.uIoc_of_le huv] at ht'
      obtain ⟨h₀, h₁⟩ := ht ⟨hu.trans ht'.1.le, ht'.2.trans hv⟩
      exact ((hψ s).continuousAt.tendsto.comp h₁).sub ((hψ s₀).continuousAt.tendsto.comp h₀)
  have hu' : u ∈ Set.Icc a (r + δ) := ⟨hu, huv.trans hv⟩
  have hv' : v ∈ Set.Icc a (r + δ) := ⟨hu.trans huv, hv⟩
  have hvlim := hDiff.tendsto_at hv'
  have hulim := hDiff.tendsto_at hu'
  have hR : Tendsto R atTop (𝓝 ((L v - L₀ v) - (L u - L₀ u) - timeIntegral G' u v)) :=
    (hvlim.sub hulim).sub hInt
  have hR0 : Tendsto R atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.2
    have hsmall : Tendsto (fun j => C / ns j) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hns
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsmall
      (Eventually.of_forall fun j => norm_nonneg _) ?_
    filter_upwards [hBase, hns.eventually hC] with j hj hCj
    rw [Real.norm_eq_abs]
    exact hCj (h j) hj u v hu huv hv
  exact sub_eq_zero.1 (tendsto_nhds_unique hR hR0)


/-- Moments determine a finite measure supported on the projected compact
interval `[0,1]`. -/
theorem eq_measure_of_measureMoment_eq {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc (0 : ℝ) 1)
    (hν : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1)
    (h : ∀ n : ℕ, measureMoment μ n = measureMoment ν n) : μ = ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  let S := Set.Icc (0 : ℝ) 1
  let G : C(S, ℝ) := ⟨fun x => g x, g.continuous.comp continuous_subtype_val⟩
  have hG : G ∈ closure (polynomialFunctions S : Set C(S, ℝ)) := by
    change G ∈ (polynomialFunctions S).topologicalClosure
    rw [polynomialFunctions.topologicalClosure]
    trivial
  have happrox (ε : ℝ) (hε : 0 < ε) : ∃ p : Polynomial ℝ,
      ∀ x ∈ S, |g x - p.eval x| ≤ ε := by
    obtain ⟨Q, hQ, hdist⟩ := Metric.mem_closure_iff.1 hG ε hε
    rw [polynomialFunctions_coe] at hQ
    obtain ⟨p, rfl⟩ := hQ
    refine ⟨p, fun x hx => ?_⟩
    have h := (G - Polynomial.toContinuousMapOnAlgHom S p).norm_coe_le_norm ⟨x, hx⟩
    rw [dist_eq_norm] at hdist
    exact (show |g x - p.eval x| ≤ ‖G - Polynomial.toContinuousMapOnAlgHom S p‖ from h).trans hdist.le
  let diff := (∫ x, g x ∂μ) - (∫ x, g x ∂ν)
  have hdiff (ε : ℝ) (hε : 0 < ε) : |diff| ≤ ε * (μ.real Set.univ + ν.real Set.univ) := by
    obtain ⟨p, hp⟩ := happrox ε hε
    have hpoly : (∫ x, p.eval x ∂μ) = ∫ x, p.eval x ∂ν := by
      have hPμ := integral_polynomial_dilation p 1 hμ
      have hPν := integral_polynomial_dilation p 1 hν
      simp only [one_mul, one_pow, mul_one] at hPμ hPν
      rw [hPμ, hPν]
      exact Finset.sum_congr rfl fun n _ => by rw [h n]
    have hErr (ξ : Measure ℝ) [IsFiniteMeasure ξ] (hξ : ∀ᵐ y ∂ξ, y ∈ S) :
        |(∫ x, g x ∂ξ) - (∫ x, p.eval x ∂ξ)| ≤ ε * ξ.real Set.univ := by
      have hiP : Integrable (fun x => p.eval x) ξ := by
        rw [← Measure.restrict_eq_self_of_ae_mem hξ]
        exact p.continuous.continuousOn.integrableOn_compact isCompact_Icc
      rw [← integral_sub (g.integrable _) hiP, ← Real.norm_eq_abs]
      exact MeasureTheory.norm_integral_le_of_norm_le_const
        (hξ.mono fun x hx => Real.norm_eq_abs _ ▸ hp x hx)
    have htriangle := norm_sub_le
      ((∫ x, g x ∂μ) - (∫ x, p.eval x ∂μ)) ((∫ x, g x ∂ν) - (∫ x, p.eval x ∂ν))
    simp only [Real.norm_eq_abs, hpoly] at htriangle
    have heq : diff =
        ((∫ x, g x ∂μ) - ∫ x, p.eval x ∂ν) -
          ((∫ x, g x ∂ν) - ∫ x, p.eval x ∂ν) := by dsimp [diff]; ring
    have h₁ := hErr μ hμ
    have h₂ := hErr ν hν
    rw [hpoly] at h₁
    rw [heq, mul_add]
    linarith only [htriangle, h₁, h₂]
  have hz : diff = 0 := by
    by_contra hc
    have hp := abs_pos.2 hc
    have hMass : 0 ≤ μ.real Set.univ + ν.real Set.univ :=
      add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    let a := μ.real Set.univ + ν.real Set.univ
    have ha : 0 < a + 1 := by dsimp [a]; linarith
    have hb := hdiff (|diff| / (a + 1)) (div_pos hp ha)
    change |diff| ≤ (|diff| / (a + 1)) * a at hb
    rw [div_mul_eq_mul_div, le_div_iff₀ ha] at hb
    nlinarith only [hb, hp]
  exact sub_eq_zero.1 hz

/-- A pointwise weak limit of measurable finite-measure families is measurable. -/
theorem measurable_of_pointwise_weakConvergence {α : Type*} [MeasurableSpace α]
    {ν : ℕ → α → Measure ℝ} {ξ : α → Measure ℝ}
    (hν : ∀ j, Measurable (ν j))
    (hlim : ∀ t, WeakConvergence (fun j => ν j t) atTop (ξ t)) :
    Measurable ξ := by
  letI (t : α) : IsFiniteMeasure (ξ t) := (hlim t).1
  have hInt (g : ℝ →ᵇ ℝ) (hg : ∀ x, 0 ≤ g x) :
      Measurable (fun t => ∫ x, g x ∂ξ t) := by
    apply measurable_of_tendsto_metrizable (f := fun j t => ∫ x, g x ∂ν j t)
    · intro j
      have h := (Measure.measurable_lintegral (g.continuous.measurable.ennreal_ofReal)).comp (hν j)
      have he (t : α) : (∫ x, g x ∂ν j t) = (∫⁻ x, ENNReal.ofReal (g x) ∂ν j t).toReal :=
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg) g.continuous.measurable.aestronglyMeasurable
      simp_rw [he]
      exact h.ennreal_toReal
    · exact tendsto_pi_nhds.2 (fun t => (hlim t).2.2 g)
  have hUniv : Measurable (fun t => ξ t Set.univ) := by
    have h := hInt (1 : ℝ →ᵇ ℝ) (fun x => by simp)
    have he : (fun t => ENNReal.ofReal (∫ x, (1 : ℝ →ᵇ ℝ) x ∂ξ t)) = fun t => ξ t Set.univ := by
      funext t
      simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, integral_const, smul_eq_mul, mul_one]
      letI := (hlim t).1
      exact ofReal_measureReal (measure_ne_top _ _)
    rw [← he]
    exact h.ennreal_ofReal
  apply Measurable.measure_of_isPiSystem (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic _ hUniv
  rintro _ ⟨a, rfl⟩
  let F (j : ℕ) (x : ℝ) := min 1 (max 0 (1 - (j : ℝ) * (x - a)))
  have hf0 (j : ℕ) (x : ℝ) : 0 ≤ F j x := by dsimp [F]; positivity
  have hf1 (j : ℕ) (x : ℝ) : F j x ≤ 1 := min_le_left _ _
  let f (j : ℕ) : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨F j, by dsimp [F]; fun_prop⟩ 1
    (fun x y => by
      change dist (F j x) (F j y) ≤ 1
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hf0 j x, hf0 j y, hf1 j x, hf1 j y])
  have hF (x : ℝ) : Tendsto (fun j => f j x) atTop
      (𝓝 ((Set.Iic a).indicator (1 : ℝ → ℝ) x)) := by
    by_cases hx : x ≤ a
    · rw [Set.indicator_of_mem (show x ∈ Set.Iic a from hx), Pi.one_apply]
      have hconst (j : ℕ) : f j x = 1 := by
        change min 1 (max 0 (1 - (j : ℝ) * (x - a))) = 1
        apply min_eq_left
        exact le_max_of_le_right (by linarith [mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg j) (sub_nonpos.2 hx)])
      simp only [hconst, tendsto_const_nhds]
    · rw [Set.indicator_of_notMem (show x ∉ Set.Iic a from hx)]
      have hδ : 0 < x - a := sub_pos.2 (lt_of_not_ge hx)
      have hthr := (tendsto_natCast_atTop_atTop.atTop_mul_const hδ).eventually_ge_atTop 1
      apply tendsto_const_nhds.congr'
      filter_upwards [hthr] with j hj
      change 0 = min 1 (max 0 (1 - (j : ℝ) * (x - a)))
      rw [max_eq_left (by linarith), min_eq_right (by norm_num)]
  have hlimInt (t : α) : Tendsto (fun j => ∫ x, f j x ∂ξ t) atTop (𝓝 ((ξ t).real (Set.Iic a))) := by
    rw [← integral_indicator_one measurableSet_Iic]
    exact MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun j => (f j).continuous.measurable.aestronglyMeasurable) (integrable_const _)
      (fun j => ae_of_all _ fun x => by
        change ‖F j x‖ ≤ 1
        rw [Real.norm_of_nonneg (hf0 j x)]
        exact hf1 j x) (ae_of_all _ hF)
  have hm : Measurable (fun t => (ξ t).real (Set.Iic a)) :=
    measurable_of_tendsto_metrizable (fun j => hInt (f j) (hf0 j)) (tendsto_pi_nhds.2 hlimInt)
  convert hm.ennreal_ofReal using 1
  funext t
  exact (ofReal_measureReal (measure_ne_top _ _)).symm


private theorem nonneg_ae_of_Iio_zero {ν : Measure ℝ} (h : ν (Set.Iio 0) = 0) :
    ∀ᵐ x ∂ν, 0 ≤ x := by
  rw [ae_iff, show {x : ℝ | ¬0 ≤ x} = Set.Iio 0 by ext x; exact not_le]
  exact h

theorem weakConvergence_limit_Iio_zero {ν : ℕ → Measure ℝ} {ξ : Measure ℝ}
    (h : WeakConvergence ν atTop ξ) (hn : ∀ j, ν j (Set.Iio 0) = 0) :
    ξ (Set.Iio 0) = 0 := by
  let F (x : ℝ) := min 1 (max (-x) 0)
  have hf0 (x : ℝ) : 0 ≤ F x := by dsimp [F]; positivity
  have hf1 (x : ℝ) : F x ≤ 1 := min_le_left _ _
  let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨F, by dsimp [F]; fun_prop⟩ 1
    (fun x y => by
      change dist (F x) (F y) ≤ 1
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hf0 x, hf0 y, hf1 x, hf1 y])
  have heq (j : ℕ) : (∫ x, f x ∂ν j) = 0 := by
    calc
      _ = ∫ _ : ℝ, (0 : ℝ) ∂ν j := integral_congr_ae
        ((nonneg_ae_of_Iio_zero (hn j)).mono fun x hx => by
          change min (1 : ℝ) (max (-x) 0) = 0
          rw [max_eq_right (neg_nonpos.2 hx), min_eq_right zero_le_one])
      _ = _ := by simp
  have hf := h.2.2 f
  simp only [heq] at hf
  have hI : (∫ x, f x ∂ξ) = 0 := tendsto_nhds_unique hf tendsto_const_nhds
  haveI := h.1
  have h0 := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all ξ hf0) (f.integrable ξ)).1 hI
  have hNonneg : ∀ᵐ x ∂ξ, 0 ≤ x := by
    filter_upwards [h0] with x hx
    change min 1 (max (-x) 0) = 0 at hx
    exact le_of_not_gt (fun hx' => (ne_of_gt (lt_min zero_lt_one ((neg_pos.2 hx').trans_le
      (le_max_left _ _)))) hx)
  rw [ae_iff, show {x : ℝ | ¬0 ≤ x} = Set.Iio 0 by ext x; exact not_le] at hNonneg
  exact hNonneg

theorem eq_of_weighted_mass_nat_eq {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (Set.Iio 0) = 0) (hν : ν (Set.Iio 0) = 0)
    (h : ∀ n : ℕ, (weightedMeasure μ n).real Set.univ = (weightedMeasure ν n).real Set.univ) : μ = ν := by
  let f (x : ℝ) := Real.exp (-x)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hsup (ξ : Measure ℝ) (hξ : ξ (Set.Iio 0) = 0) :
      ∀ᵐ y ∂(ξ.map f), y ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_map_iff hf.aemeasurable (p := fun y : ℝ => y ∈ Set.Icc (0 : ℝ) 1) measurableSet_Icc]
    exact (nonneg_ae_of_Iio_zero hξ).mono fun x hx =>
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (neg_nonpos.2 hx)⟩
  have hzero (ξ : Measure ℝ) : weightedMeasure ξ 0 = ξ := by
    unfold weightedMeasure
    simp only [zero_mul, neg_zero, Real.exp_zero, ENNReal.ofReal_one]
    exact withDensity_one
  have hPow (ξ : Measure ℝ) (n : ℕ) :
      measureMoment (ξ.map f) n = (weightedMeasure ξ n).real Set.univ := by
    simpa only [hzero, zero_add] using measureMoment_weighted_exponential_map ξ 0 n
  have hMap := eq_measure_of_measureMoment_eq (hsup μ hμ) (hsup ν hν)
    (fun n => (hPow μ n).trans ((h n).trans (hPow ν n).symm))
  let g (x : ℝ) := -Real.log x
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hInv : g ∘ f = id := by
    funext x
    simp [f, g]
  have hc := congrArg (fun ξ : Measure ℝ => ξ.map g) hMap
  exact (by simpa only [Measure.map_map hg hf, hInv, Measure.map_id] using hc)

/-- The high-weight limit of the initial transforms fixes the common
additive trace of all the transform differences. -/
theorem profile_trace_eq_of_difference {v r σ : ℝ} {L : ℕ → ℝ}
    (hbase : L 0 ≤ profileTransform v r σ)
    (hnonneg : ∀ k, 0 ≤ L k)
    (hdiff : ∀ k : ℕ, L k - L 0 =
      profileTransform v r (σ + k) - profileTransform v r σ) :
    ∀ k : ℕ, L k = profileTransform v r (σ + k) := by
  have hlim : Tendsto (fun k : ℕ => profileTransform v r (σ + k)) atTop (𝓝 0) := by
    have hden : Tendsto (fun k : ℕ => σ + (k : ℝ) + profileB v r) atTop atTop := by
      have hc : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      refine tendsto_atTop.2 fun x => ?_
      filter_upwards [hc.eventually_ge_atTop (x - σ - profileB v r)] with k hk
      linarith
    exact tendsto_const_nhds.div_atTop hden
  have hle : profileTransform v r σ - L 0 ≤ 0 := by
    apply ge_of_tendsto' hlim
    intro k
    linarith [hdiff k, hnonneg k]
  intro k
  linarith [hdiff k]


/-- Weak convergence of finite measures is detected by further subsequences. -/
theorem weakConvergence_of_further_subsequences {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {w : ι → Measure ℝ} {ξ : Measure ℝ}
    (hξ : IsFiniteMeasure ξ) (hfin : ∀ᶠ i in l, IsFiniteMeasure (w i))
    (h : ∀ x : ℕ → ι, Tendsto x atTop l → ∃ q : ℕ → ℕ, StrictMono q ∧
      WeakConvergence (fun j => w (x (q j))) atTop ξ) :
    WeakConvergence w l ξ := by
  refine ⟨hξ, hfin, fun f => ?_⟩
  refine tendsto_of_further_subsequences
    (u := fun i => ∫ y, f y ∂(w i)) (k := 𝓝 (∫ y, f y ∂ξ)) ?_
  intro x hx
  obtain ⟨q, hq, hweak⟩ := h x hx
  exact ⟨q, hq, hweak.2.2 f⟩

/-- A weak limit inherits each limit of the integer-offset weighted masses. -/
theorem mass_moments_of_weighted_weak_limit {ν : ℕ → Measure ℝ} {ξ : Measure ℝ} {s : ℝ}
    (hn : ∀ j, ν j (Set.Iio 0) = 0)
    (hw : WeakConvergence (fun j => weightedMeasure (ν j) s) atTop ξ)
    {m : ℕ → ℝ}
    (hm : ∀ k : ℕ, Tendsto (fun j => (weightedMeasure (ν j) (s + k)).real Set.univ)
      atTop (𝓝 (m k))) :
    ξ (Set.Iio 0) = 0 ∧ ∀ k : ℕ, (weightedMeasure ξ k).real Set.univ = m k := by
  have hsup (j : ℕ) : weightedMeasure (ν j) s (Set.Iio 0) = 0 :=
    withDensity_absolutelyContinuous (ν j) _ (hn j)
  have hξ := weakConvergence_limit_Iio_zero hw hsup
  refine ⟨hξ, fun k => ?_⟩
  have hweighted := weakConvergence_weighted_of_supported hw
    (Eventually.of_forall hsup) hξ (Nat.cast_nonneg k)
  have htest := hweighted.2.2 (1 : ℝ →ᵇ ℝ)
  simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, integral_const,
    smul_eq_mul, mul_one, ← weightedMeasure_add] at htest
  exact tendsto_nhds_unique htest (hm k)

private theorem tendsto_weighted_mass_toNNReal {ν : ℕ → Measure ℝ} {s m : ℝ}
    (hm : Tendsto (fun j => (weightedMeasure (ν j) s).real Set.univ) atTop (𝓝 m)) :
    Tendsto (fun j => (weightedMeasure (ν j) s Set.univ).toNNReal) atTop (𝓝 m.toNNReal) := by
  have h := (continuous_real_toNNReal.tendsto m).comp hm
  change Tendsto (fun j => ((weightedMeasure (ν j) s).real Set.univ).toNNReal) atTop
    (𝓝 m.toNNReal) at h
  exact h.congr' (Eventually.of_forall fun _ => Real.toNNReal_coe)

/-- Assemble the weak limit from a mass bound at a smaller weight and
convergence of the integer-offset weighted masses. -/
theorem exists_weakConvergence_of_weighted_mass_limits {ν : ℕ → Measure ℝ} {s₀ s : ℝ}
    (hs : s₀ < s) (hn : ∀ j, ν j (Set.Iio 0) = 0)
    (hf : ∀ j, IsFiniteMeasure (weightedMeasure (ν j) s₀))
    {C : ℝ≥0} (hC : ∀ j, weightedMeasure (ν j) s₀ Set.univ ≤ C)
    {m : ℕ → ℝ}
    (hm : ∀ k : ℕ, Tendsto (fun j => (weightedMeasure (ν j) (s + k)).real Set.univ)
      atTop (𝓝 (m k))) :
    ∃ ξ : Measure ℝ, ξ (Set.Iio 0) = 0 ∧
      WeakConvergence (fun j => weightedMeasure (ν j) s) atTop ξ ∧
      ∀ k : ℕ, (weightedMeasure ξ k).real Set.univ = m k := by
  have hm₀ : Tendsto (fun j => (weightedMeasure (ν j) s).real Set.univ) atTop (𝓝 (m 0)) := by
    simpa only [Nat.cast_zero, add_zero] using hm 0
  have hnn := tendsto_weighted_mass_toNNReal hm₀
  obtain ⟨ξ, q, hq, hx⟩ := exists_weak_subseq_of_weight_gap hs hn hf hC hnn
  obtain ⟨hξ, hmx⟩ := mass_moments_of_weighted_weak_limit (fun j => hn (q j)) hx
    (fun k => (hm k).comp hq.tendsto_atTop)
  have hfin (j : ℕ) : IsFiniteMeasure (weightedMeasure (ν j) s) := by
    have hle : weightedMeasure (ν j) s ≤ weightedMeasure (ν j) s₀ := by
      rw [show s = s₀ + (s - s₀) by ring, weightedMeasure_add]
      exact weightedMeasure_le_of_nonneg (withDensity_absolutelyContinuous _ _ (hn j))
        (sub_nonneg.mpr hs.le)
    exact ⟨(hle Set.univ).trans_lt (hf j).measure_univ_lt_top⟩
  refine ⟨ξ, hξ, ?_, hmx⟩
  refine weakConvergence_of_further_subsequences
    (w := fun j => weightedMeasure (ν j) s) hx.1 (Eventually.of_forall hfin) ?_
  intro x hx'
  obtain ⟨ζ, p, hp, hz⟩ := exists_weak_subseq_of_weight_gap (ν := fun j => ν (x j))
    hs (fun j => hn (x j)) (fun j => hf (x j)) (fun j => hC (x j)) (hnn.comp hx')
  obtain ⟨hζ, hmz⟩ := mass_moments_of_weighted_weak_limit (fun j => hn (x (p j))) hz
    (fun k => (hm k).comp (hx'.comp hp.tendsto_atTop))
  haveI := hx.1
  haveI := hz.1
  have he : ζ = ξ := eq_of_weighted_mass_nat_eq hζ hξ (fun k => (hmz k).trans (hmx k).symm)
  exact ⟨p, hp, he ▸ hz⟩


/-- Given smaller-weight mass control, the limiting integer-offset masses
identify the whole weak limit at a larger weight, for real scales. -/
theorem weakConvergence_atTop_of_weighted_mass_limits {ν : ℝ → Measure ℝ}
    {ν' : Measure ℝ} {s₀ s : ℝ} (hs : s₀ < s) {C : ℝ≥0}
    (hb : ∀ᶠ N in atTop, ν N (Set.Iio 0) = 0 ∧ weightedMeasure (ν N) s₀ Set.univ ≤ C)
    (hn' : ν' (Set.Iio 0) = 0) (hf' : IsFiniteMeasure (weightedMeasure ν' s))
    (hm : ∀ k : ℕ, Tendsto (fun N => (weightedMeasure (ν N) (s + k)).real Set.univ)
      atTop (𝓝 ((weightedMeasure ν' (s + k)).real Set.univ))) :
    WeakConvergence (fun N => weightedMeasure (ν N) s) atTop (weightedMeasure ν' s) := by
  have hf : ∀ᶠ N in atTop, IsFiniteMeasure (weightedMeasure (ν N) s) := by
    filter_upwards [hb] with N hN
    have hle : weightedMeasure (ν N) s ≤ weightedMeasure (ν N) s₀ := by
      rw [show s = s₀ + (s - s₀) by ring, weightedMeasure_add]
      exact weightedMeasure_le_of_nonneg (withDensity_absolutelyContinuous _ _ hN.1)
        (sub_nonneg.mpr hs.le)
    exact ⟨((hle Set.univ).trans hN.2).trans_lt ENNReal.coe_lt_top⟩
  refine weakConvergence_of_further_subsequences (w := fun N => weightedMeasure (ν N) s)
    hf' hf ?_
  intro x hx
  obtain ⟨a, ha⟩ := eventually_atTop.1 (hx.eventually hb)
  let p (j : ℕ) := j + a
  have hp : StrictMono p := fun _ _ h => Nat.add_lt_add_right h _
  have hgood (j : ℕ) : ν (x (p j)) (Set.Iio 0) = 0 ∧
      weightedMeasure (ν (x (p j))) s₀ Set.univ ≤ C := ha (p j) (by dsimp [p]; omega)
  obtain ⟨ξ, hξ, hw, hmass⟩ := exists_weakConvergence_of_weighted_mass_limits
    (ν := fun j => ν (x (p j))) hs (fun j => (hgood j).1)
    (fun j => ⟨((hgood j).2).trans_lt ENNReal.coe_lt_top⟩)
    (fun j => (hgood j).2) (fun k => (hm k).comp (hx.comp hp.tendsto_atTop))
  haveI := hw.1
  haveI := hf'
  have he : ξ = weightedMeasure ν' s :=
    eq_of_weighted_mass_nat_eq hξ (withDensity_absolutelyContinuous _ _ hn') (fun k => by
      rw [← weightedMeasure_add]
      exact hmass k)
  exact ⟨p, hp, he ▸ hw⟩

/-- A fixed local extension length propagates a property up to the end of
a bounded interval, after finitely many steps. -/
theorem interval_induction_fixed_step {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    {P : ℝ → Prop} (ha : P a)
    (hstep : ∀ r ∈ Set.Icc a b, P r → ∀ t ∈ Set.Icc r (min b (r + δ)), P t) :
    ∀ t ∈ Set.Icc a b, P t := by
  have hchain : ∀ n : ℕ, ∀ t ∈ Set.Icc a (min b (a + (n : ℝ) * δ)), P t := by
    intro n
    induction n with
    | zero =>
        intro t ht
        have hta : t = a := le_antisymm (ht.2.trans (by simp)) ht.1
        exact hta ▸ ha
    | succ n ih =>
        intro t ht
        let r := min b (a + (n : ℝ) * δ)
        have hr : a ≤ r := le_min hab (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hδ.le))
        by_cases htr : t ≤ r
        · exact ih t ⟨ht.1, htr⟩
        · have hrt : r ≤ t := (lt_of_not_ge htr).le
          have hrb : r ≤ b := min_le_left _ _
          have heq : r = a + (n : ℝ) * δ := by
            dsimp [r]
            rcases le_total b (a + (n : ℝ) * δ) with hh | hh
            · exact False.elim (htr (by simpa only [r, min_eq_left hh] using ht.2.trans (min_le_left _ _)))
            · exact min_eq_right hh
          apply hstep r ⟨hr, hrb⟩ (ih r ⟨hr, le_rfl⟩) t
          refine ⟨hrt, le_min (ht.2.trans (min_le_left _ _)) ?_⟩
          rw [heq]
          have hu := ht.2.trans (min_le_right _ _)
          rw [Nat.cast_succ, add_mul, one_mul] at hu
          linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  have hn' : b ≤ a + (n : ℝ) * δ := by
    have h := (div_lt_iff₀ hδ).1 hn
    linarith
  intro t ht
  exact hchain n t ⟨ht.1, le_min ht.2 (ht.2.trans hn')⟩


/-- The model's weighted masses and Mellin transforms have the same
pointwise limit at a positive time. -/
theorem tendsto_rescaled_weighted_mass_of_transform {ι : Type*} {l : Filter ι}
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {t s z : ℝ} (ht : 0 < t) (hs : 0 ≤ s)
    {ns h : ι → ℝ} (hns : Tendsto ns l atTop)
    (hL : Tendsto (fun j => transformAt μ B (h j) (ns j) ⌊ns j * t⌋₊ s) l (𝓝 z)) :
    Tendsto (fun j =>
      (weightedMeasure (rescaledMeasure μ B (h j) (ns j) ⌊ns j * t⌋₊) s).real Set.univ)
      l (𝓝 z) := by
  let L (j : ι) := transformAt μ B (h j) (ns j) ⌊ns j * t⌋₊ s
  let G (j : ι) := ns j * (2 / B) ^ ⌊ns j * t⌋₊
  let d (j : ι) := s / (Real.log B * ns j * weightExponent B (ns j) s)
  have hG : Tendsto G l (𝓝 0) := by
    have hg := (tendsto_pow_mul_geometric_floor (show 0 < 2 / B by positivity)
      ((div_lt_one (by linarith)).2 hB) ht 1).comp hns
    change Tendsto (fun j => ns j ^ (1 : ℕ) * (2 / B) ^ ⌊ns j * t⌋₊) l (𝓝 0) at hg
    simpa only [pow_one, G] using hg
  have hq := (tendsto_weightExponent_atTop hB s).comp hns
  have hd : Tendsto d l (𝓝 0) := by
    have hlog : 0 < Real.log B := Real.log_pos (by linarith)
    have hden : Tendsto (fun j => Real.log B * ns j) l atTop := hns.const_mul_atTop hlog
    have hdiv : Tendsto (fun j => s / (Real.log B * ns j)) l (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    have hd' := hdiv.div hq (theta_pos hB).ne'
    change Tendsto (fun j => s / (Real.log B * ns j) / weightExponent B (ns j) s)
      l (𝓝 (0 / theta B)) at hd'
    simpa only [d, div_div, zero_div] using hd'
  have hL' : Tendsto L l (𝓝 z) := hL
  have hup : Tendsto (fun j => L j + (d j * (L j + G j) + G j)) l (𝓝 z) := by
    simpa only [zero_mul, zero_add, add_zero] using hL'.add ((hd.mul (hL'.add hG)).add hG)
  have hev := (hns.eventually_gt_atTop 0).and (hq.eventually (Ioi_mem_nhds (theta_pos hB)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL' hup ?_ ?_
  · filter_upwards [hev] with j hj
    exact sub_nonneg.mp
      (rescaledMeasure_weighted_mass_sub_bounds hpos hmean hB (h j) hj.1 hs hj.2 ⌊ns j * t⌋₊).1
  · filter_upwards [hev] with j hj
    have hh := (rescaledMeasure_weighted_mass_sub_bounds
      hpos hmean hB (h j) hj.1 hs hj.2 ⌊ns j * t⌋₊).2
    exact (sub_le_iff_le_add.1 hh).trans_eq (add_comm _ _)

/-- Assemble the almost-everywhere pointwise limits as a measurable kernel. -/
theorem exists_measurable_weighted_limit {α : Type*} [MeasurableSpace α]
    (ω : Measure α) {ν : ℕ → α → Measure ℝ} {s₀ s : ℝ} (hs : s₀ < s)
    (hν : ∀ j, Measurable (fun t => weightedMeasure (ν j t) s))
    {m : α → ℕ → ℝ} {C : ℝ≥0}
    (h : ∀ᵐ t ∂ω,
      (∀ j, ν j t (Set.Iio 0) = 0 ∧ weightedMeasure (ν j t) s₀ Set.univ ≤ C) ∧
      ∀ k : ℕ, Tendsto (fun j => (weightedMeasure (ν j t) (s + k)).real Set.univ)
        atTop (𝓝 (m t k))) :
    ∃ ξ : α → Measure ℝ, Measurable ξ ∧ (∀ t, IsFiniteMeasure (ξ t)) ∧
      ∀ᵐ t ∂ω, ξ t (Set.Iio 0) = 0 ∧
        WeakConvergence (fun j => weightedMeasure (ν j t) s) atTop (ξ t) ∧
        ∀ k : ℕ, (weightedMeasure (ξ t) k).real Set.univ = m t k := by
  classical
  obtain ⟨bad, hbad, hbm, hb0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  let T := badᶜ
  have hT : MeasurableSet T := hbm.compl
  have hAE : ∀ᵐ t ∂ω, t ∈ T := ae_iff.2 (by simpa [T] using hb0)
  have hExist (t : α) (ht : t ∈ T) :
      ∃ ξ : Measure ℝ, ξ (Set.Iio 0) = 0 ∧
        WeakConvergence (fun j => weightedMeasure (ν j t) s) atTop ξ ∧
        ∀ k : ℕ, (weightedMeasure ξ k).real Set.univ = m t k := by
    have hg := not_not.1 (fun hn => ht (hbad hn))
    exact exists_weakConvergence_of_weighted_mass_limits (ν := fun j => ν j t) hs
      (fun j => (hg.1 j).1) (fun j => ⟨((hg.1 j).2).trans_lt ENNReal.coe_lt_top⟩)
      (fun j => (hg.1 j).2) hg.2
  choose z hz using hExist
  let ξ (t : α) := if ht : t ∈ T then z t ht else 0
  let ν' (j : ℕ) (t : α) := if t ∈ T then weightedMeasure (ν j t) s else 0
  have hm (j : ℕ) : Measurable (ν' j) := (hν j).ite hT measurable_const
  have hlim (t : α) : WeakConvergence (fun j => ν' j t) atTop (ξ t) := by
    by_cases ht : t ∈ T
    · simpa only [ν', ξ, ite_eq_left ht, dite_eq_left ht] using (hz t ht).2.1
    · simp only [ν', ξ, ite_eq_right ht, dite_eq_right ht]
      exact ⟨inferInstance, Eventually.of_forall (fun _ => inferInstance),
        fun _ => tendsto_const_nhds⟩
  refine ⟨ξ, measurable_of_pointwise_weakConvergence hm hlim, fun t => (hlim t).1, ?_⟩
  filter_upwards [hAE] with t ht
  simpa only [ξ, dite_eq_left ht] using hz t ht


/-- The smooth tests used for the projected transport, normalized on its
support and vanishing at and beyond the absorbing boundary. -/
def ContinuationTest (g : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 g ∧ (∀ y, 1 ≤ y → g y = 0) ∧
    ∀ y ∈ Set.Icc (0 : ℝ) 1, |g y| ≤ 1

theorem ContinuationTest.abs_le_of_nonneg {g : ℝ → ℝ} (hg : ContinuationTest g)
    {y : ℝ} (hy : 0 ≤ y) : |g y| ≤ 1 := by
  rcases le_total y 1 with h | h
  · exact hg.2.2 y ⟨hy, h⟩
  · simp [hg.2.1 y h]

private theorem ae_lt_one_of_projected_support {μ : Measure ℝ}
    (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc (0 : ℝ) 1) (hμ₁ : μ {1} = 0) :
    ∀ᵐ y ∂μ, y < 1 := by
  have hne : ∀ᵐ y ∂μ, y ≠ 1 := by
    rw [ae_iff]
    rw [show {y : ℝ | ¬ y ≠ 1} = {1} by ext y; simp]
    exact hμ₁
  filter_upwards [hμ, hne] with y hy h
  exact lt_of_le_of_ne hy.2 h

/-- Smooth tests with zero boundary value control all smooth bounded tests
on projected measures with no mass at the absorbing boundary. -/
theorem continuationTest_control_smooth {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc (0 : ℝ) 1) (hν : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1)
    (hμ₁ : μ {1} = 0) (hν₁ : ν {1} = 0) {D : ℝ}
    (hD : ∀ g, ContinuationTest g → |(∫ y, g y ∂μ) - ∫ y, g y ∂ν| ≤ D)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hb : ∀ y ∈ Set.Icc (0 : ℝ) 1, |g y| ≤ 1) :
    |(∫ y, g y ∂μ) - ∫ y, g y ∂ν| ≤ D := by
  let c (n : ℕ) (y : ℝ) := Real.smoothTransition ((n : ℝ) * (1 - y))
  let f (n : ℕ) (y : ℝ) := g y * c n y
  have hc (n : ℕ) : ContDiff ℝ 1 (c n) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))
  have hc0 (n : ℕ) (y : ℝ) : 0 ≤ c n y := Real.smoothTransition.nonneg _
  have hc1 (n : ℕ) (y : ℝ) : c n y ≤ 1 := Real.smoothTransition.le_one _
  have ht (n : ℕ) : ContinuationTest (f n) := by
    refine ⟨hg.mul (hc n), ?_, ?_⟩
    · intro y hy
      have hz := Real.smoothTransition.zero_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (sub_nonpos.2 hy))
      simp only [f, c, hz, mul_zero]
    · intro y hy
      dsimp only [f]
      rw [abs_mul, abs_of_nonneg (hc0 n y)]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hc1 n y)).trans (hb y hy)
  have hlim (ρ : Measure ℝ) [IsFiniteMeasure ρ]
      (hρ : ∀ᵐ y ∂ρ, y ∈ Set.Icc (0 : ℝ) 1) (hρ₁ : ρ {1} = 0) :
      Tendsto (fun n => ∫ y, f n y ∂ρ) atTop (𝓝 (∫ y, g y ∂ρ)) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => 1)
    · exact fun n => (ht n).1.continuous.measurable.aestronglyMeasurable
    · exact integrable_const _
    · exact fun n => hρ.mono fun y hy => by rw [Real.norm_eq_abs]; exact (ht n).2.2 y hy
    · filter_upwards [ae_lt_one_of_projected_support hρ hρ₁] with y hy
      have ht' : Tendsto (fun n : ℕ => (n : ℝ) * (1 - y)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.2 hy)
      refine (tendsto_const_nhds (x := g y)).congr' ?_
      filter_upwards [ht'.eventually_ge_atTop 1] with n hn
      dsimp [f, c]
      rw [Real.smoothTransition.one_of_one_le hn, mul_one]
  exact le_of_tendsto' ((hlim μ hμ hμ₁).sub (hlim ν hν hν₁)).abs (fun n => hD _ (ht n))

theorem eq_of_continuationTest_integrals {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc (0 : ℝ) 1) (hν : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1)
    (hμ₁ : μ {1} = 0) (hν₁ : ν {1} = 0)
    (he : ∀ g, ContinuationTest g → (∫ y, g y ∂μ) = ∫ y, g y ∂ν) : μ = ν := by
  apply eq_measure_of_measureMoment_eq hμ hν
  intro n
  have h := continuationTest_control_smooth hμ hν hμ₁ hν₁
    (D := 0) (fun g hg => by rw [he g hg, sub_self, abs_zero])
    (g := fun y : ℝ => y ^ n) (contDiff_id.pow n) (fun y hy => by
      rw [abs_of_nonneg (pow_nonneg hy.1 n)]
      exact pow_le_one₀ hy.1 hy.2)
  exact sub_eq_zero.1 (abs_eq_zero.1 (le_antisymm h (abs_nonneg _)))


private theorem continuation_mul_test_integrable {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {g : ℝ → ℝ} (hg : ContinuationTest g)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) (hν : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1)
    {A : ℝ} (hA : 0 ≤ A) :
    Integrable (fun p : ℝ × ℝ => g (A * (p.1 * p.2))) (μ.prod ν) := by
  have hg' : Continuous g := hg.1.continuous
  have hm : Continuous (fun p : ℝ × ℝ => g (A * (p.1 * p.2))) := by fun_prop
  apply (integrable_const (1 : ℝ)).mono' hm.measurable.aestronglyMeasurable
  have he : MeasurableSet {p : ℝ × ℝ | ‖g (A * (p.1 * p.2))‖ ≤ 1} :=
    measurableSet_le hm.measurable.norm measurable_const
  apply (Measure.ae_prod_iff_ae_ae he).2
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  rw [Real.norm_eq_abs]
  exact hg.abs_le_of_nonneg (mul_nonneg hA (mul_nonneg hx.1 hy.1))

private theorem continuation_mconv_test_eq_integral {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {g : ℝ → ℝ} (hg : ContinuationTest g)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) (hν : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1)
    {A : ℝ} (hA : 0 ≤ A) :
    (∫ z, g (A * z) ∂(μ ∗ₘ ν)) = ∫ x, ∫ y, g (A * (x * y)) ∂ν ∂μ := by
  have hg' : Continuous g := hg.1.continuous
  rw [Measure.mconv, integral_map (by fun_prop) (by fun_prop)]
  exact integral_prod _ (continuation_mul_test_integrable hg hμ hν hA)

private theorem continuation_mconv_test_sub_right {μ ν ρ : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ] {g : ℝ → ℝ}
    (hg : ContinuationTest g)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    (hν : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1)
    (hρ : ∀ᵐ y ∂ρ, y ∈ Set.Icc (0 : ℝ) 1)
    (hν₁ : ν {1} = 0) (hρ₁ : ρ {1} = 0)
    {A D : ℝ} (hA : 0 ≤ A)
    (hD : ∀ f, ContinuationTest f → |(∫ y, f y ∂ν) - ∫ y, f y ∂ρ| ≤ D) :
    |(∫ z, g (A * z) ∂(μ ∗ₘ ν)) - ∫ z, g (A * z) ∂(μ ∗ₘ ρ)| ≤ D * μ.real Set.univ := by
  rw [continuation_mconv_test_eq_integral hg hμ hν hA,
    continuation_mconv_test_eq_integral hg hμ hρ hA,
    ← integral_sub (continuation_mul_test_integrable hg hμ hν hA).integral_prod_left
      (continuation_mul_test_integrable hg hμ hρ hA).integral_prod_left, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [hμ] with x hx
  rw [Real.norm_eq_abs]
  apply continuationTest_control_smooth hν hρ hν₁ hρ₁ hD
  · have hc : ContDiff ℝ 1 (fun y : ℝ => A * (x * y)) :=
      contDiff_const.mul (contDiff_const.mul contDiff_id)
    exact hg.1.comp hc
  · exact fun y hy => hg.abs_le_of_nonneg (mul_nonneg hA (mul_nonneg hx.1 hy.1))

/-- The quadratic term is locally Lipschitz in the supremum of differences
against the normalized projected tests. -/
theorem continuation_mconv_test_sub {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {g : ℝ → ℝ} (hg : ContinuationTest g)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) (hν : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1)
    (hμ₁ : μ {1} = 0) (hν₁ : ν {1} = 0) {A D : ℝ} (hA : 0 ≤ A)
    (hD : ∀ f, ContinuationTest f → |(∫ y, f y ∂μ) - ∫ y, f y ∂ν| ≤ D) :
    |(∫ z, g (A * z) ∂(μ ∗ₘ μ)) - ∫ z, g (A * z) ∂(ν ∗ₘ ν)| ≤
      D * (μ.real Set.univ + ν.real Set.univ) := by
  have h₁ := continuation_mconv_test_sub_right hg hμ hμ hν hμ₁ hν₁ hA hD
  have h₂ := continuation_mconv_test_sub_right hg hν hμ hν hμ₁ hν₁ hA hD
  rw [Measure.mconv_comm ν μ] at h₂
  rw [mul_add]
  exact (abs_sub_le _ _ _).trans (add_le_add h₁ h₂)


/-- Mild evolution of the projected measure, tested on smooth functions
vanishing at the absorbing boundary. -/
def ContinuationMildOn (σ r : ℝ) (J : Set ℝ) (η : ℝ → Measure ℝ) : Prop :=
  ∀ t ∈ J, ∀ g, ContinuationTest g →
    let f := fun u => Real.exp (σ * (t - u)) *
      (∫ y, g (Real.exp (t - u) * y) ∂(η u ∗ₘ η u)) / 2
    IntervalIntegrable f volume r t ∧
    (∫ y, g y ∂(η t)) =
      Real.exp (σ * (t - r)) * (∫ y, g (Real.exp (t - r) * y) ∂(η r)) +
        timeIntegral f r t

/-- On a sufficiently short interval, mild projected measures with the
same initial trace coincide. The proof uses bounded smooth tests and does
not require continuity of translations in variation. -/
theorem continuationMildOn_unique {η ζ : ℝ → Measure ℝ} {σ r b M : ℝ}
    {J : Set ℝ} (hσ : 0 ≤ σ) (hrb : r ≤ b) (hM : 0 ≤ M)
    (hsmall : Real.exp (σ * (b - r)) * M * (b - r) < 1)
    (hJ : J ⊆ Set.Icc r b) (hJae : ∀ᵐ u : ℝ, u ∈ Set.Icc r b → u ∈ J)
    (hη : ContinuationMildOn σ r J η) (hζ : ContinuationMildOn σ r J ζ)
    (hh : η r = ζ r)
    (hηJ : ∀ u ∈ J, IsFiniteMeasure (η u) ∧
      (∀ᵐ y ∂(η u), y ∈ Set.Icc (0 : ℝ) 1) ∧ η u {1} = 0 ∧ (η u).real Set.univ ≤ M)
    (hζJ : ∀ u ∈ J, IsFiniteMeasure (ζ u) ∧
      (∀ᵐ y ∂(ζ u), y ∈ Set.Icc (0 : ℝ) 1) ∧ ζ u {1} = 0 ∧ (ζ u).real Set.univ ≤ M) :
    ∀ t ∈ J, η t = ζ t := by
  let Δ (t : ℝ) (g : ℝ → ℝ) := |(∫ y, g y ∂(η t)) - ∫ y, g y ∂(ζ t)|
  let V := {x : ℝ | ∃ t ∈ J, ∃ g, ContinuationTest g ∧ x = Δ t g} ∪ {0}
  have h0 : (0 : ℝ) ∈ V := Or.inr rfl
  have hbdd : BddAbove V := by
    refine ⟨2 * M, ?_⟩
    rintro x (⟨t, ht, g, hg, rfl⟩ | rfl)
    · haveI := (hηJ t ht).1
      haveI := (hζJ t ht).1
      have hηb := norm_integral_le_of_norm_le_const
        ((hηJ t ht).2.1.mono fun y hy => show ‖g y‖ ≤ 1 from hg.2.2 y hy)
      have hζb := norm_integral_le_of_norm_le_const
        ((hζJ t ht).2.1.mono fun y hy => show ‖g y‖ ≤ 1 from hg.2.2 y hy)
      have h := norm_sub_le (∫ y, g y ∂(η t)) (∫ y, g y ∂(ζ t))
      simp only [Real.norm_eq_abs, one_mul] at hηb hζb h
      exact h.trans (by linarith [(hηJ t ht).2.2.2, (hζJ t ht).2.2.2])
    · linarith
  let D := sSup V
  have hD : 0 ≤ D := le_csSup hbdd h0
  have hTest (t : ℝ) (ht : t ∈ J) (g : ℝ → ℝ) (hg : ContinuationTest g) :
      Δ t g ≤ D := le_csSup hbdd (Or.inl ⟨t, ht, g, hg, rfl⟩)
  let K := Real.exp (σ * (b - r)) * M
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbetter (t : ℝ) (ht : t ∈ J) (g : ℝ → ℝ) (hg : ContinuationTest g) :
      Δ t g ≤ (K * (b - r)) * D := by
    let f (ξ : ℝ → Measure ℝ) (u : ℝ) := Real.exp (σ * (t - u)) *
      (∫ y, g (Real.exp (t - u) * y) ∂(ξ u ∗ₘ ξ u)) / 2
    obtain ⟨hfi, hη'⟩ := hη t ht g hg
    obtain ⟨hgi, hζ'⟩ := hζ t ht g hg
    have he : (∫ y, g y ∂η t) - (∫ y, g y ∂ζ t) =
        ∫ u in r..t, f η u - f ζ u := by
      rw [intervalIntegral.integral_sub hfi hgi, hη', hζ', hh]
      unfold timeIntegral
      ring
    change |(∫ y, g y ∂η t) - (∫ y, g y ∂ζ t)| ≤ _
    rw [he, ← Real.norm_eq_abs]
    have hrt := (hJ ht).1
    calc
      _ ≤ (K * D) * |t - r| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
        filter_upwards [hJae] with u hu hmem
        rw [Set.uIoc_of_le hrt] at hmem
        have hub : u ∈ Set.Icc r b := ⟨hmem.1.le, hmem.2.trans (hJ ht).2⟩
        have hu' := hu hub
        haveI := (hηJ u hu').1
        haveI := (hζJ u hu').1
        let A := Real.exp (t - u)
        have hconv := continuation_mconv_test_sub hg (hηJ u hu').2.1 (hζJ u hu').2.1
          (hηJ u hu').2.2.1 (hζJ u hu').2.2.1 (A := A) (Real.exp_pos _).le
          (fun g hg => hTest u hu' g hg)
        have hExpo : Real.exp (σ * (t - u)) ≤ Real.exp (σ * (b - r)) := by
          apply Real.exp_le_exp.2
          exact mul_le_mul_of_nonneg_left (by linarith [(hJ ht).2, hub.1]) hσ
        rw [Real.norm_eq_abs]
        dsimp only [f]
        rw [← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have hm := add_le_add (hηJ u hu').2.2.2 (hζJ u hu').2.2.2
        have hprod := mul_le_mul_of_nonneg_left hm hD
        calc
          _ ≤ Real.exp (σ * (t - u)) * (D * (M + M)) / 2 := by
            gcongr
            exact hconv.trans hprod
          _ ≤ Real.exp (σ * (b - r)) * (D * (M + M)) / 2 := by gcongr
          _ = K * D := by dsimp [K]; ring
      _ ≤ _ := by
        rw [abs_of_nonneg (sub_nonneg.2 hrt), mul_right_comm K (b - r) D]
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hJ ht).2 r) (mul_nonneg hK hD)
  have hcontr : D ≤ (K * (b - r)) * D := by
    apply csSup_le ⟨0, h0⟩
    rintro x (⟨t, ht, g, hg, rfl⟩ | rfl)
    · exact hbetter t ht g hg
    · positivity
  have hz : D = 0 := by
    by_contra hn
    exact (not_lt_of_ge hcontr) (mul_lt_of_lt_one_left (lt_of_le_of_ne hD (Ne.symm hn)) hsmall)
  intro t ht
  haveI := (hηJ t ht).1
  haveI := (hζJ t ht).1
  refine eq_of_continuationTest_integrals (hηJ t ht).2.1 (hζJ t ht).2.1
    (hηJ t ht).2.2.1 (hζJ t ht).2.2.1 (fun g hg => ?_)
  have h := hTest t ht g hg
  rw [hz] at h
  exact sub_eq_zero.1 (abs_eq_zero.1 (le_antisymm h (abs_nonneg _)))


private theorem continuation_mconv_univ {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ ∗ₘ ν) Set.univ = μ Set.univ * ν Set.univ := by
  rw [Measure.mconv, Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod]

private theorem continuation_mconv_kernel_measurable {η : ℝ → Measure ℝ}
    (hη : Measurable η) (hf : ∀ u, IsFiniteMeasure (η u)) :
    Measurable (fun u => η u ∗ₘ η u) := by
  let ζ (u : ℝ) : FiniteMeasure ℝ := ⟨η u, hf u⟩
  have hz : Measurable ζ := hη.subtype_mk
  exact (Measure.measurable_map (fun z : ℝ × ℝ => z.1 * z.2) (by fun_prop)).comp
    (FiniteMeasure.measurable_fun_prod.comp (hz.prodMk hz))

/-- The quadratic term in the mild identity is time integrable for a
measurable, uniformly mass-bounded projected family. -/
theorem continuation_mild_integrable {η : ℝ → Measure ℝ} {g : ℝ → ℝ}
    (hm : Measurable η) (hf : ∀ u, IsFiniteMeasure (η u)) {M : ℝ}
    (hsup : ∀ u, ∀ᵐ y ∂(η u), y ∈ Set.Icc (0 : ℝ) 1)
    (hM : ∀ u, (η u).real Set.univ ≤ M)
    (hg : ContinuationTest g) {σ r t : ℝ} (hrt : r ≤ t) (hσ : 0 ≤ σ) :
    IntervalIntegrable (fun u => Real.exp (σ * (t - u)) *
      (∫ y, g (Real.exp (t - u) * y) ∂(η u ∗ₘ η u)) / 2) volume r t := by
  let κ : ProbabilityTheory.Kernel ℝ ℝ := ⟨fun u => η u ∗ₘ η u,
    continuation_mconv_kernel_measurable hm hf⟩
  have hMn : 0 ≤ M := ENNReal.toReal_nonneg.trans (hM r)
  have hmass (u : ℝ) : η u Set.univ ≤ ENNReal.ofReal M := by
    haveI := hf u
    rw [← ofReal_measureReal (measure_ne_top (η u) Set.univ)]
    exact ENNReal.ofReal_le_ofReal (hM u)
  haveI : ProbabilityTheory.IsFiniteKernel κ := ⟨⟨(ENNReal.ofReal M)^2, by
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top, fun u => by
      change (η u ∗ₘ η u) Set.univ ≤ _
      haveI := hf u
      rw [continuation_mconv_univ, pow_two]
      exact mul_le_mul' (hmass u) (hmass u)⟩⟩
  let f (u y : ℝ) := g (Real.exp (t - u) * y)
  have hcont : Continuous (fun p : ℝ × ℝ => f p.1 p.2) := by
    have hg' := hg.1.continuous
    dsimp [f]
    fun_prop
  have hp1 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (f p.1 p.2)) :=
    hcont.measurable.ennreal_ofReal
  have hp2 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (-f p.1 p.2)) :=
    hcont.measurable.neg.ennreal_ofReal
  have hfi (u : ℝ) : Integrable (f u) (κ u) := by
    haveI := hf u
    refine (integrable_const (1 : ℝ)).mono' (by
      exact (hcont.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable) ?_
    change ∀ᵐ y ∂(η u ∗ₘ η u), ‖f u y‖ ≤ 1
    filter_upwards [ae_Icc_mconv_self (hsup u)] with y hy
    rw [Real.norm_eq_abs]
    exact hg.abs_le_of_nonneg (mul_nonneg (Real.exp_pos _).le hy.1)
  have hmeas : Measurable (fun u => ∫ y, f u y ∂κ u) := by
    have heq (u : ℝ) := integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hfi u)
    simp_rw [heq]
    exact (hp1.lintegral_kernel_prod_right' (κ := κ)).ennreal_toReal.sub
      (hp2.lintegral_kernel_prod_right' (κ := κ)).ennreal_toReal
  have hExp : Measurable (fun u : ℝ => Real.exp (σ * (t - u))) := by fun_prop
  have hMeas : Measurable (fun u => Real.exp (σ * (t-u)) * (∫ y, f u y ∂κ u) / 2) :=
    (hExp.mul hmeas).div_const _
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hrt]
  refine (integrable_const (Real.exp (σ * (t-r)) * M^2 / 2)).mono'
    hMeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  haveI := hf u
  have hb := norm_integral_le_of_norm_le_const (μ := κ u) (f := f u)
    ((ae_Icc_mconv_self (hsup u)).mono fun y hy => by
      rw [Real.norm_eq_abs]
      exact hg.abs_le_of_nonneg (mul_nonneg (Real.exp_pos _).le hy.1))
  have hb' : (κ u).real Set.univ ≤ M^2 := by
    change (η u ∗ₘ η u).real Set.univ ≤ _
    rw [← measureMoment_zero_eq_mass, measureMoment_mconv_self, measureMoment_zero_eq_mass]
    exact (sq_le_sq₀ ENNReal.toReal_nonneg hMn).2 (hM u)
  have he := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (sub_le_sub_left hu.1 t) hσ)
  change ‖Real.exp (σ * (t - u)) * (∫ y, f u y ∂κ u) / 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [Real.norm_eq_abs, one_mul] at hb
  gcongr
  exact hb.trans hb'

/-- A projected family with the transform difference equations satisfies
the mild identity at all times where its moments represent the transforms. -/
theorem continuationMildOn_of_moments (L : ℕ → ℝ → ℝ) (η : ℝ → Measure ℝ)
    {σ r b M : ℝ} {J : Set ℝ}
    (hσ : 0 ≤ σ) (hJ : J ⊆ Set.Icc r b)
    (hmeas : Measurable η) (hf : ∀ u, IsFiniteMeasure (η u))
    (hsupp : ∀ u, ∀ᵐ y ∂(η u), y ∈ Set.Icc (0 : ℝ) 1)
    (hM : ∀ u, (η u).real Set.univ ≤ M)
    (hr : ∀ n, L n r = measureMoment (η r) n)
    (hrep : ∀ t ∈ J, ∀ n, L n t = measureMoment (η t) n)
    (ha : ∀ᵐ u : ℝ, u ∈ Set.Icc r b → ∀ n, L n u = measureMoment (η u) n)
    (hi : ∀ n : ℕ, IntervalIntegrable
      (fun x => psiS (σ + n) (L n x) - psiS σ (L 0 x)) volume r b)
    (hD : ∀ n, ∀ u ∈ Set.Icc r b,
      (L n u - L 0 u) - (L n r - L 0 r) =
        timeIntegral (fun x => psiS (σ + n) (L n x) - psiS σ (L 0 x)) r u) :
    ContinuationMildOn σ r J η := by
  intro t ht g hg
  have hrt := (hJ ht).1
  have htb := (hJ ht).2
  have hsub : Set.Icc r t ⊆ Set.Icc r b := Set.Icc_subset_Icc_right htb
  have hInt := continuation_mild_integrable hmeas hf hsupp hM hg hrt hσ
  refine ⟨hInt, ?_⟩
  have hDer := hg.1.differentiable_one
  have hz (y : ℝ) (hy : 1 ≤ y) : g y = 0 ∧ deriv g y = 0 := by
    refine ⟨hg.2.1 y hy, ?_⟩
    have hd : HasDerivWithinAt g 0 (Set.Ici (1 : ℝ)) y :=
      (hasDerivAt_const y (0 : ℝ)).hasDerivWithinAt.congr_of_mem hg.2.1 hy
    exact (uniqueDiffOn_Ici _ _ hy).eq_deriv _ (hDer y).hasDerivAt.hasDerivWithinAt hd
  refine projected_mild_of_transform_differences L η hσ hrt hf hsupp
    (fun u _ => hM u) hr (hrep t ht) (ha.mono fun u hu hu' => hu (hsub hu')) ?_ ?_ g (deriv g)
    hg.1.continuous hg.1.continuous_deriv_one (fun y => (hDer y).hasDerivAt) hz hInt
  · intro n
    apply (hi n).mono_set
    rw [Set.uIcc_of_le hrt, Set.uIcc_of_le (hrt.trans htb)]
    exact hsub
  · intro n u hu
    rw [Set.uIcc_of_le hrt] at hu
    exact hD n u (hsub hu)


private theorem continuation_exp_map_support {ξ : Measure ℝ} (hξ : ξ (Set.Iio 0) = 0) :
    ∀ᵐ y ∂(ξ.map (fun x => Real.exp (-x))), y ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_map_iff (f := fun x => Real.exp (-x)) (by fun_prop)
    (p := fun y : ℝ => y ∈ Set.Icc (0 : ℝ) 1) measurableSet_Icc]
  exact (nonneg_ae_of_Iio_zero hξ).mono fun x hx =>
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (neg_nonpos.2 hx)⟩

private theorem weightedProfile_measurable (v σ : ℝ) :
    Measurable (fun t => weightedMeasure (profileMeasure v t) σ) := by
  have hU : Measurable (profileU v) := by
    by_cases hv : 0 < v
    · have he : profileU v = fun t => Real.sin (Real.sqrt v * t) / Real.sqrt v := by
        funext t
        rw [profileU, ite_eq_left hv]
      rw [he]
      fun_prop
    · have he : profileU v = id := by
        funext t
        rw [profileU, ite_eq_right hv]
        rfl
      rw [he]
      exact measurable_id
  have hA : Measurable (profileA v) := by
    change Measurable (fun t => 4 / (profileU v t)^2)
    fun_prop
  have hD : Measurable (fun t => deriv (profileU v) t) := by
    simp_rw [(hasDerivAt_profileU v _).deriv]
    by_cases hv : 0 < v
    · simp only [ite_eq_left hv]
      fun_prop
    · simp only [ite_eq_right hv]
      exact measurable_const
  have hB : Measurable (profileB v) := by
    change Measurable (fun t => 2 * deriv (profileU v) t / profileU v t)
    fun_prop
  simp_rw [weightedMeasure_profileMeasure]
  exact measurable_withDensity (μ := volume.restrict (Set.Ici 0)) (by
    change Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (profileA v p.1 * Real.exp (-(σ + profileB v p.1) * p.2)))
    fun_prop)

private theorem continuation_profile_support (v t σ : ℝ) :
    weightedMeasure (profileMeasure v t) σ (Set.Iio 0) = 0 := by
  rw [weightedMeasure_profileMeasure]
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply measurableSet_Iio]
  have heq : Set.Iio (0 : ℝ) ∩ Set.Ici 0 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    exact fun _ h => h.1.not_ge h.2
  rw [heq, measure_empty]

private theorem continuation_projected_profile_atom (v t σ : ℝ) :
    (Measure.map (fun x => Real.exp (-x)) (weightedMeasure (profileMeasure v t) σ)) {1} = 0 := by
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have hs : (fun x : ℝ => Real.exp (-x)) ⁻¹' ({1} : Set ℝ) = {0} := by
    ext x
    simp [Real.exp_eq_one_iff]
  rw [hs, weightedMeasure_profileMeasure]
  apply withDensity_absolutelyContinuous
  exact measure_singleton 0

/-- The explicit profile gives a mild solution in the projected variable
on every admissible compact time interval. -/
theorem exists_continuationMildOn_profile {v σ r b M : ℝ} (hσ : 0 ≤ σ) (hrb : r ≤ b)
    (hp : ∀ u ∈ Set.Icc r b, IsPrePoleTime v u)
    (hadm : ∀ u ∈ Set.Icc r b, 0 < σ + profileB v u)
    (hM : 0 ≤ M) (hbound : ∀ u ∈ Set.Icc r b, profileTransform v u σ ≤ M) :
    ∃ ζ : ℝ → Measure ℝ, ContinuationMildOn σ r (Set.Icc r b) ζ ∧
      (∀ u ∈ Set.Icc r b, ζ u =
        (weightedMeasure (profileMeasure v u) σ).map (fun x => Real.exp (-x))) ∧
      ∀ u ∈ Set.Icc r b,
        IsFiniteMeasure (ζ u) ∧ (∀ᵐ y ∂(ζ u), y ∈ Set.Icc (0 : ℝ) 1) ∧
          ζ u {1} = 0 ∧ (ζ u).real Set.univ ≤ M := by
  classical
  let L (n : ℕ) (u : ℝ) := profileTransform v u (σ + n)
  let ζ (u : ℝ) := if u ∈ Set.Icc r b then
    (weightedMeasure (profileMeasure v u) σ).map (fun x => Real.exp (-x)) else 0
  have hz (u : ℝ) (hu : u ∈ Set.Icc r b) :
      ζ u = (weightedMeasure (profileMeasure v u) σ).map (fun x => Real.exp (-x)) :=
    ite_eq_left hu
  have hmeas : Measurable ζ :=
    ((Measure.measurable_map (fun x : ℝ => Real.exp (-x)) (by fun_prop)).comp
      (weightedProfile_measurable v σ)).ite measurableSet_Icc measurable_const
  have hfinite (u : ℝ) : IsFiniteMeasure (ζ u) := by
    by_cases hu : u ∈ Set.Icc r b
    · rw [hz u hu]
      haveI := weightedMeasure_profileMeasure_finite (hadm u hu)
      infer_instance
    · simp only [ζ, ite_eq_right hu]
      infer_instance
  have hsup (u : ℝ) : ∀ᵐ y ∂(ζ u), y ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases hu : u ∈ Set.Icc r b
    · rw [hz u hu]
      exact continuation_exp_map_support (continuation_profile_support v u σ)
    · rw [show ζ u = 0 from ite_eq_right hu]
      simp
  have hmom (u : ℝ) (hu : u ∈ Set.Icc r b) (n : ℕ) :
      L n u = measureMoment (ζ u) n := by
    rw [hz u hu, measureMoment_weighted_exponential_map]
    have ha : 0 < σ + (n : ℝ) + profileB v u := by
      linarith [hadm u hu, Nat.cast_nonneg (α := ℝ) n]
    rw [Measure.real, weightedMeasure_profileMeasure_mass ha, ENNReal.toReal_ofReal]
    unfold profileTransform profileA
    positivity
  have hmass (u : ℝ) : (ζ u).real Set.univ ≤ M := by
    by_cases hu : u ∈ Set.Icc r b
    · rw [← measureMoment_zero_eq_mass, ← hmom u hu 0]
      simpa only [L, Nat.cast_zero, add_zero] using hbound u hu
    · simpa only [ζ, ite_eq_right hu, measureReal_zero, Pi.zero_apply] using hM
  refine ⟨ζ, ?_, hz, fun u hu => ⟨hfinite u, hsup u, ?_, hmass u⟩⟩
  · have hA (u : ℝ) (hu : u ∈ Set.Icc r b) (n : ℕ) :
        0 < σ + (n : ℝ) + profileB v u := by
        linarith [hadm u hu, Nat.cast_nonneg (α := ℝ) n]
    have hLC (n : ℕ) : ContinuousOn (L n) (Set.Icc r b) := fun u hu =>
      (profileTransform_hasDerivAt (hp u hu) (hA u hu n)).continuousAt.continuousWithinAt
    refine continuationMildOn_of_moments L ζ hσ (fun _ hx => hx) hmeas hfinite hsup hmass
      (hmom r ⟨le_rfl, hrb⟩) hmom (ae_of_all _ hmom) ?_ ?_
    · intro n
      have hp₁ : ContinuousOn (fun x => psiS (σ + n) (L n x)) (Set.Icc r b) := by
        unfold psiS
        exact (continuousOn_const.mul (hLC n)).add ((hLC n).pow 2 |>.div_const 2)
      have hp₀ : ContinuousOn (fun x => psiS σ (L 0 x)) (Set.Icc r b) := by
        unfold psiS
        exact (continuousOn_const.mul (hLC 0)).add ((hLC 0).pow 2 |>.div_const 2)
      exact (hp₁.sub hp₀).intervalIntegrable_of_Icc hrb
    · intro n u hu
      have hsub : Set.Icc r u ⊆ Set.Icc r b := Set.Icc_subset_Icc_right hu.2
      simpa only [L, Nat.cast_zero, add_zero] using
        (profileTransform_sub_integral
          (fun w hw => hp w (hsub hw)) (fun w hw => hA w (hsub hw) n)
          (fun w hw => hadm w (hsub hw)) hu.1)
  · rw [hz u hu]
    exact continuation_projected_profile_atom v u σ


private theorem continuation_intervalIntegrable_psi {L : ℝ → ℝ} {s r b M : ℝ}
    (hrb : r ≤ b) (hs : 0 ≤ s) (hM : 0 ≤ M) (hm : Measurable L)
    (hb : ∀ u ∈ Set.Icc r b, |L u| ≤ M) :
    IntervalIntegrable (fun u => psiS s (L u)) volume r b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hrb]
  have hm' : Measurable (fun u => psiS s (L u)) := by unfold psiS; fun_prop
  refine (integrable_const (s * M + M^2 / 2)).mono' hm'.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [Real.norm_eq_abs]
  exact abs_psiS_le_of_abs_le hs hM (hb u hu)

/-- Local identification of the transform limits from the projected
measure representation and the common initial trace. -/
theorem continuation_identify_transform_limits {v s₀ r b M : ℝ}
    (L : ℕ → ℝ → ℝ) (η : ℝ → Measure ℝ) (hs₀ : 0 ≤ s₀) (hrb : r ≤ b) (hM : 0 ≤ M)
    (hp : ∀ u ∈ Set.Icc r b, IsPrePoleTime v u)
    (hadm : ∀ u ∈ Set.Icc r b, 0 < s₀ + profileB v u)
    (hFb : ∀ u ∈ Set.Icc r b, |profileTransform v u s₀| ≤ M ∧
      |profileTransform v u (s₀+1)| ≤ M)
    (hsmall : Real.exp ((s₀+1) * (b-r)) * M * (b-r) < 1)
    (hsmallBase : (|s₀| + 3*M) * (b-r) < 1)
    (hmeas : Measurable η) (hfin : ∀ u, IsFiniteMeasure (η u))
    (hsup : ∀ u, ∀ᵐ y ∂(η u), y ∈ Set.Icc (0 : ℝ) 1)
    (hmass : ∀ u, (η u).real Set.univ ≤ M)
    (hLm : ∀ n, Measurable (L n))
    (hLb : ∀ n u, u ∈ Set.Icc r b → |L n u| ≤ M)
    (hinit : ∀ n : ℕ, L n r = profileTransform v r (s₀+n))
    (htrace : η r = (weightedMeasure (profileMeasure v r) (s₀+1)).map
      (fun x => Real.exp (-x)))
    (ha : ∀ᵐ u : ℝ, u ∈ Set.Icc r b → ∀ n, L (n+1) u = measureMoment (η u) n)
    (hD : ∀ (n : ℕ) u, u ∈ Set.Icc r b → (L n u - L 0 u) - (L n r - L 0 r) =
        timeIntegral (fun x => psiS (s₀ + n) (L n x) - psiS s₀ (L 0 x)) r u) :
    ∀ᵐ u : ℝ, u ∈ Set.Icc r b → ∀ n : ℕ, L n u = profileTransform v u (s₀+n) := by
  let σ := s₀ + 1
  let U (n : ℕ) := L (n+1)
  let F (n : ℕ) (u : ℝ) := profileTransform v u (s₀+n)
  have hσ : 0 ≤ σ := by dsimp [σ]; positivity
  have hcast (n : ℕ) : s₀ + ((n+1 : ℕ) : ℝ) = σ+n := by
    push_cast
    dsimp [σ]
    ring
  have hLbψ (n : ℕ) : IntervalIntegrable (fun u => psiS (s₀+n) (L n u)) volume r b :=
    continuation_intervalIntegrable_psi hrb (by positivity) hM (hLm n) (hLb n)
  have hUbψ (n : ℕ) : IntervalIntegrable (fun u => psiS (σ+n) (U n u)) volume r b := by
    rw [← hcast]
    exact hLbψ (n+1)
  have hLbψ₀ : IntervalIntegrable (fun u => psiS s₀ (L 0 u)) volume r b := by
    simpa only [Nat.cast_zero, add_zero] using hLbψ 0
  have hUψ₀ : IntervalIntegrable (fun u => psiS σ (U 0 u)) volume r b := by
    simpa only [Nat.cast_zero, add_zero] using hUbψ 0
  have hUd (n : ℕ) (u : ℝ) (hu : u ∈ Set.Icc r b) :
      (U n u - U 0 u) - (U n r - U 0 r) =
        timeIntegral (fun x => psiS (σ + n) (U n x) - psiS σ (U 0 x)) r u := by
    have hsub : Set.uIcc r u ⊆ Set.uIcc r b := by
      rw [Set.uIcc_of_le hu.1, Set.uIcc_of_le hrb]
      exact Set.Icc_subset_Icc_right hu.2
    have hlin := hD (n+1) u hu
    have hbase := hD 1 u hu
    rw [hcast n] at hlin
    have hbase' : (L 1 u - L 0 u) - (L 1 r - L 0 r) =
        timeIntegral (fun x => psiS σ (L 1 x) - psiS s₀ (L 0 x)) r u := by
      simpa only [Nat.cast_one] using hbase
    have hIn₁ : IntervalIntegrable (fun x => psiS (σ+n) (U n x) - psiS s₀ (L 0 x))
        volume r u := ((hUbψ n).sub hLbψ₀).mono_set hsub
    have hIn₂ : IntervalIntegrable (fun x => psiS σ (L 1 x) - psiS s₀ (L 0 x))
        volume r u := (hUψ₀.sub hLbψ₀).mono_set hsub
    calc
      _ = ((L (n+1) u - L 0 u) - (L (n+1) r - L 0 r)) -
          ((L 1 u - L 0 u) - (L 1 r - L 0 r)) := by dsimp [U]; ring
      _ = _ := by
        rw [hlin, hbase', timeIntegral, timeIntegral, timeIntegral,
          ← intervalIntegral.integral_sub hIn₁ hIn₂]
        congr 1
        funext x
        dsimp [U]
        ring
  have haU : ∀ᵐ u : ℝ, u ∈ Set.Icc r b → ∀ n, U n u = measureMoment (η u) n := ha
  have hAtom := projected_boundary_mass_zero_ae U η (σ := σ) hrb hM hfin hsup
    (fun n => hLm (n+1)) (fun n => hLb (n+1)) haU (fun n => hUd n b ⟨hrb, le_rfl⟩)
  rw [restrict_Ioc_eq_restrict_Icc, ae_restrict_iff' measurableSet_Icc] at hAtom
  have hTraceMom (n : ℕ) : U n r = measureMoment (η r) n := by
    rw [htrace, measureMoment_weighted_exponential_map]
    have hr := hinit (n+1)
    rw [hcast n] at hr
    change U n r = _ at hr
    have hn : 0 < σ + (n : ℝ) + profileB v r := by
      dsimp [σ]
      linarith [hadm r ⟨le_rfl, hrb⟩, Nat.cast_nonneg (α := ℝ) n]
    rw [hr, Measure.real, weightedMeasure_profileMeasure_mass hn, ENNReal.toReal_ofReal]
    exact div_nonneg (by unfold profileA; positivity) hn.le
  let J := {u | u ∈ Set.Icc r b ∧ η u {1} = 0 ∧ ∀ n, U n u = measureMoment (η u) n}
  have hJ : J ⊆ Set.Icc r b := fun _ hu => hu.1
  have hJae : ∀ᵐ u : ℝ, u ∈ Set.Icc r b → u ∈ J := by
    filter_upwards [hAtom, haU] with u h₁ h₂ hu
    exact ⟨hu, h₁ hu, h₂ hu⟩
  have hη := continuationMildOn_of_moments U η hσ hJ hmeas hfin hsup hmass
    hTraceMom (fun u hu => hu.2.2) haU (fun n => (hUbψ n).sub hUψ₀) hUd
  have hadm' (u : ℝ) (hu : u ∈ Set.Icc r b) : 0 < σ + profileB v u := by
    dsimp [σ]
    linarith [hadm u hu]
  obtain ⟨ζ, hζ, hζdef, hζgood⟩ :=
    exists_continuationMildOn_profile hσ hrb hp hadm' hM
      (fun u hu => le_trans (le_abs_self _) (hFb u hu).2)
  have hηeq (u : ℝ) (hu : u ∈ J) : η u = ζ u :=
    continuationMildOn_unique hσ hrb hM hsmall hJ hJae hη
      (fun u hu => hζ u (hJ hu)) (htrace.trans (hζdef r ⟨le_rfl, hrb⟩).symm)
      (fun u hu => ⟨hfin u, hsup u, hu.2.1, hmass u⟩)
      (fun u hu => hζgood u (hJ hu)) u hu
  have hEqU : ∀ᵐ u : ℝ, u ∈ Set.Icc r b → ∀ n, U n u = F (n+1) u := by
    filter_upwards [hJae] with u hu hmem n
    have h := hu hmem
    rw [h.2.2 n, hηeq u h, hζdef u hmem, measureMoment_weighted_exponential_map]
    dsimp [F]
    have hn : 0 < σ + (n : ℝ) + profileB v u := by
      dsimp [σ]
      linarith [hadm u hmem, Nat.cast_nonneg (α := ℝ) n]
    rw [hcast n, Measure.real, weightedMeasure_profileMeasure_mass hn, ENNReal.toReal_ofReal]
    exact div_nonneg (by unfold profileA; positivity) hn.le
  let E (u : ℝ) := F 1 u - (L 1 u - L 0 u)
  have hE (u : ℝ) (hu : u ∈ Set.Icc r b) : |E u| ≤ 3*M := by
    have ht := norm_sub_le (F 1 u) (L 1 u - L 0 u)
    have hd := norm_sub_le (L 1 u) (L 0 u)
    have hF : |F 1 u| ≤ M := by simpa only [F, Nat.cast_one] using (hFb u hu).2
    simp only [Real.norm_eq_abs] at ht hd
    change |F 1 u - (L 1 u - L 0 u)| ≤ _
    linarith [hLb 1 u hu, hLb 0 u hu]
  have hEa : ∀ᵐ u : ℝ, u ∈ Set.Icc r b → E u = L 0 u := by
    filter_upwards [hEqU] with u hu hmem
    have hu' : L 1 u = F 1 u := hu hmem 0
    dsimp [E]
    rw [hu']
    ring
  have hEaψ : ∀ᵐ u : ℝ, u ∈ Set.Icc r b →
      psiS σ (F 1 u) - psiS s₀ (E u) = psiS σ (L 1 u) - psiS s₀ (L 0 u) := by
    filter_upwards [hEa, hEqU] with u hu hF hmem
    rw [hu hmem, show L 1 u = F 1 u from hF hmem 0]
  have hEeq (u : ℝ) (hu : u ∈ Set.Icc r b) : (F 1 u - E u) - (F 1 r - E r) =
      timeIntegral (fun x => psiS σ (F 1 x) - psiS s₀ (E x)) r u := by
    have heq := intervalIntegral.integral_congr_ae (a := r) (b := u)
      (hEaψ.mono fun t ht ht' =>
        ht (by rw [Set.uIoc_of_le hu.1] at ht'; exact ⟨ht'.1.le, ht'.2.trans hu.2⟩))
    have hd := hD 1 u hu
    simp only [Nat.cast_one] at hd
    change _ = timeIntegral (fun x => psiS σ (L 1 x) - psiS s₀ (L 0 x)) r u at hd
    rw [timeIntegral, heq]
    unfold timeIntegral at hd
    dsimp [E]
    convert hd using 1 <;> ring
  have hEinit : E r = F 0 r := by
    dsimp [E, F]
    rw [hinit 1, hinit 0]
    ring
  have hF₀ (u : ℝ) (hu : u ∈ Set.Icc r b) : |F 0 u| ≤ 3*M := by
    have h := (hFb u hu).1
    dsimp [F]
    simp only [Nat.cast_zero, add_zero]
    linarith
  have hFi (n : ℕ) : ContinuousOn (F n) (Set.Icc r b) := fun u hu =>
    (profileTransform_hasDerivAt (hp u hu)
      (by linarith [hadm u hu, Nat.cast_nonneg (α := ℝ) n])).continuousAt.continuousWithinAt
  have hPsi (n : ℕ) (w : ℝ) : ContinuousOn (fun u => psiS w (F n u)) (Set.Icc r b) := by
    unfold psiS
    exact (continuousOn_const.mul (hFi n)).add ((hFi n).pow 2 |>.div_const 2)
  have hEInt : IntervalIntegrable (fun x => psiS σ (F 1 x) - psiS s₀ (E x)) volume r b := by
    have h := hUψ₀.sub hLbψ₀
    apply h.congr_ae
    rw [Set.uIoc_of_le hrb, Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    exact hEaψ.mono fun u hu hu' => (hu ⟨hu'.1.le, hu'.2⟩).symm
  have hEidentified := eq_of_identified_larger_weight (L := E) (F := F 0) (U := F 1) hrb hsmallBase hE hF₀ hEinit hEInt
    (((hPsi 1 σ).sub (hPsi 0 s₀)).intervalIntegrable_of_Icc hrb) hEeq (fun u hu => by
      have hsub : Set.Icc r u ⊆ Set.Icc r b := Set.Icc_subset_Icc_right hu.2
      simpa only [F, Nat.cast_zero, zero_add, add_zero, Nat.cast_one] using
        profileTransform_sub_integral (fun t ht => hp t (hsub ht))
          (fun t ht => hadm' t (hsub ht)) (fun t ht => hadm t (hsub ht)) hu.1)
  filter_upwards [hEqU, hEa] with u hu he hmem n
  cases n with
  | zero => exact (he hmem).symm.trans (hEidentified u hmem)
  | succ n => exact hu hmem n


private theorem measurable_limit_of_ae_weak {α : Type*} [MeasurableSpace α] {ω : Measure α}
    {μ : ℕ → α → Measure ℝ} (hm : ∀ j, Measurable (μ j)) {P : α → Measure ℝ → Prop}
    (ha : ∀ᵐ u ∂ω, ∃ ξ, WeakConvergence (fun j => μ j u) atTop ξ ∧ P u ξ) :
    ∃ ξ : α → Measure ℝ, Measurable ξ ∧ (∀ u, IsFiniteMeasure (ξ u)) ∧
      ∀ᵐ u ∂ω, WeakConvergence (fun j => μ j u) atTop (ξ u) ∧ P u (ξ u) := by
  classical
  obtain ⟨bad, hbad, hb, hb0⟩ := exists_measurable_superset_of_null (ae_iff.1 ha)
  let T := badᶜ
  have ht : MeasurableSet T := hb.compl
  have hAE : ∀ᵐ u ∂ω, u ∈ T := ae_iff.2 (by simpa [T] using hb0)
  have hchoose (u : α) (hu : u ∈ T) : ∃ ξ, WeakConvergence (fun j => μ j u) atTop ξ ∧ P u ξ :=
    not_not.1 (fun hn => hu (hbad hn))
  choose ν hν using hchoose
  let ξ (u : α) := if hu : u ∈ T then ν u hu else 0
  let μ' (j : ℕ) (u : α) := if u ∈ T then μ j u else 0
  have hlim (u : α) : WeakConvergence (fun j => μ' j u) atTop (ξ u) := by
    by_cases hu : u ∈ T
    · simpa only [μ', ξ, ite_eq_left hu, dite_eq_left hu] using (hν u hu).1
    · simp only [μ', ξ, ite_eq_right hu, dite_eq_right hu]
      exact ⟨inferInstance, Eventually.of_forall (fun _ => inferInstance),
        fun _ => tendsto_const_nhds⟩
  refine ⟨ξ, measurable_of_pointwise_weakConvergence (fun j => (hm j).ite ht measurable_const)
    hlim, fun u => (hlim u).1, ?_⟩
  filter_upwards [hAE] with u hu
  simpa only [ξ, dite_eq_left hu] using hν u hu

private theorem exists_weak_of_eventually_weighted_mass_limits {ν : ℕ → Measure ℝ} {s₀ s : ℝ}
    (hs : s₀ < s) {C : ℝ≥0}
    (hb : ∀ᶠ j in atTop, ν j (Set.Iio 0) = 0 ∧ weightedMeasure (ν j) s₀ Set.univ ≤ C)
    {m : ℕ → ℝ}
    (hm : ∀ k : ℕ, Tendsto (fun j => (weightedMeasure (ν j) (s+k)).real Set.univ)
      atTop (𝓝 (m k))) :
    ∃ ξ, WeakConvergence (fun j => weightedMeasure (ν j) s) atTop ξ ∧
      ξ (Set.Iio 0) = 0 ∧ ∀ k : ℕ, (weightedMeasure ξ k).real Set.univ = m k := by
  obtain ⟨a, ha⟩ := eventually_atTop.1 hb
  let p (j : ℕ) := j+a
  have hp : StrictMono p := fun _ _ h => Nat.add_lt_add_right h _
  have hgood (j : ℕ) : ν (p j) (Set.Iio 0) = 0 ∧ weightedMeasure (ν (p j)) s₀ Set.univ ≤ C :=
    ha (p j) (by dsimp [p]; omega)
  obtain ⟨ξ, hξ, hw, hmom⟩ := exists_weakConvergence_of_weighted_mass_limits
    (ν := fun j => ν (p j)) hs (fun j => (hgood j).1)
    (fun j => ⟨(hgood j).2.trans_lt ENNReal.coe_lt_top⟩) (fun j => (hgood j).2)
    (fun k => (hm k).comp hp.tendsto_atTop)
  refine ⟨ξ, ⟨hw.1, ?_, fun f => ?_⟩, hξ, hmom⟩
  · obtain ⟨j, hj⟩ := eventually_atTop.1 hw.2.1
    apply eventually_atTop.2
    refine ⟨j+a, fun i hi => ?_⟩
    have hji : j ≤ i-a := by omega
    have he : p (i-a) = i := by dsimp [p]; omega
    exact he ▸ hj (i-a) hji
  · exact (tendsto_add_atTop_iff_nat a).1 (hw.2.2 f)

/-- The local Mellin limits at integer offsets above a nonnegative base
weight yield a measurable projected measure at the next weight. -/
theorem continuation_model_projected_kernel {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {r b s₀ M v : ℝ} (hr : 0 < r) (hrb : r ≤ b) (hs₀ : 0 ≤ s₀)
    (hM : 0 ≤ M) (hadm : 0 < (s₀+1) + profileB v r)
    (hF : profileTransform v r (s₀+1) ≤ M)
    {ns h : ℕ → ℝ} (hns : Tendsto ns atTop atTop)
    (L : ℕ → ℝ → ℝ) (hb : ∀ u ∈ Set.Icc r b, |L 1 u| ≤ M)
    (ha : ∀ᵐ u : ℝ, u ∈ Set.Icc r b → ∀ k : ℕ,
      Tendsto (fun j => transformAt μ B (h j) (ns j) ⌊ns j * u⌋₊ (s₀+k))
        atTop (𝓝 (L k u))) :
    ∃ η : ℝ → Measure ℝ, Measurable η ∧
      (∀ u, IsFiniteMeasure (η u)) ∧ (∀ u, ∀ᵐ y ∂(η u), y ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ u, (η u).real Set.univ ≤ M) ∧
      η r = (weightedMeasure (profileMeasure v r) (s₀+1)).map (fun x => Real.exp (-x)) ∧
      ∀ᵐ u : ℝ, u ∈ Set.Icc r b → ∀ n, L (n+1) u = measureMoment (η u) n := by
  classical
  let σ := s₀+1
  let ω := volume.restrict (Set.Icc r b)
  let ν (j : ℕ) (u : ℝ) := rescaledMeasure μ B (h j) (ns j) ⌊ns j*u⌋₊
  have hmeas (j : ℕ) : Measurable (fun u => weightedMeasure (ν j u) σ) := by
    have hn : Measurable (fun n : ℕ => weightedMeasure (rescaledMeasure μ B (h j) (ns j) n) σ) :=
      measurable_of_countable _
    exact hn.comp (measurable_const.mul measurable_id).nat_floor
  have hs : s₀ < σ := by dsimp [σ]; linarith
  have hσ : 0 ≤ σ := by dsimp [σ]; positivity
  have hgood : ∀ᵐ u ∂ω, ∃ ξ, WeakConvergence (fun j => weightedMeasure (ν j u) σ) atTop ξ ∧
      ξ (Set.Iio 0) = 0 ∧ ∀ n : ℕ, (weightedMeasure ξ n).real Set.univ = L (n+1) u := by
    have ha' := ae_mono (show ω ≤ volume from Measure.restrict_le_self) ha
    filter_upwards [ae_restrict_mem measurableSet_Icc, ha'] with u hu hlim
    have hu' := hr.trans_le hu.1
    have hlow := tendsto_rescaled_weighted_mass_of_transform (s := s₀) (h := h) hpos hmean hB hu' hs₀ hns
      (by simpa only [Nat.cast_zero, add_zero] using hlim hu 0)
    have hN : ∀ᶠ j in atTop, 0 < ns j := hns.eventually_gt_atTop 0
    have hbound : ∀ᶠ j in atTop, ν j u (Set.Iio 0) = 0 ∧
        weightedMeasure (ν j u) s₀ Set.univ ≤ ENNReal.ofReal (max 0 (L 0 u + 1)) := by
      filter_upwards [hN, hlow.eventually (Iic_mem_nhds (lt_add_one (L 0 u)))] with j hj hb'
      obtain ⟨hfinite, hsup⟩ := rescaledMeasure_finite_aux hpos hmean hB (h j) hj ⌊ns j*u⌋₊
      haveI : IsFiniteMeasure (ν j u) := hfinite
      have hfin : IsFiniteMeasure (weightedMeasure (ν j u) s₀) :=
        ⟨(weightedMeasure_le_of_nonneg hsup hs₀ Set.univ).trans_lt (measure_lt_top _ _)⟩
      letI := hfin
      refine ⟨hsup, ?_⟩
      rw [← ofReal_measureReal (measure_ne_top (weightedMeasure (ν j u) s₀) Set.univ)]
      exact ENNReal.ofReal_le_ofReal (hb'.trans (le_max_right _ _))
    let C : ℝ≥0 := ⟨max 0 (L 0 u + 1), le_max_left _ _⟩
    have hC : (C : ℝ≥0∞) = ENNReal.ofReal (max 0 (L 0 u + 1)) :=
      ENNReal.ofReal_coe_nnreal.symm
    refine exists_weak_of_eventually_weighted_mass_limits (ν := fun j => ν j u) (C := C)
      hs (by rw [hC]; exact hbound) ?_
    intro n
    have hcast : s₀ + ((n+1 : ℕ) : ℝ) = σ+n := by push_cast; dsimp [σ]; ring
    refine tendsto_rescaled_weighted_mass_of_transform hpos hmean hB hu' (by positivity) hns ?_
    rw [← hcast]
    exact hlim hu (n+1)
  obtain ⟨ξ, hmξ, hfξ, hξ⟩ := measurable_limit_of_ae_weak hmeas hgood
  let p (x : ℝ) := Real.exp (-x)
  have hp : Measurable p := by dsimp [p]; fun_prop
  let E := {u | ξ u (Set.Iio 0) = 0 ∧ (ξ u).real Set.univ ≤ M}
  have hE : MeasurableSet E := by
    apply MeasurableSet.inter
    · exact measurableSet_eq_fun ((Measure.measurable_coe measurableSet_Iio).comp hmξ) measurable_const
    · exact measurableSet_le ((Measure.measurable_coe MeasurableSet.univ).comp hmξ).ennreal_toReal
        measurable_const
  let ζ := (weightedMeasure (profileMeasure v r) σ).map p
  let η₀ (u : ℝ) := if u ∈ E then (ξ u).map p else 0
  let η (u : ℝ) := if u = r then ζ else η₀ u
  have hmη : Measurable η :=
    measurable_const.ite (measurableSet_singleton _) (((Measure.measurable_map _ hp).comp hmξ).ite
      hE measurable_const)
  have hζ : IsFiniteMeasure ζ := by
    haveI := weightedMeasure_profileMeasure_finite hadm
    change IsFiniteMeasure (Measure.map p _)
    infer_instance
  have hne : ∀ᵐ u : ℝ, u ≠ r := by simp [ae_iff]
  refine ⟨η, hmη, ?_, ?_, ?_, ite_eq_left rfl, ?_⟩
  · intro u
    haveI := hfξ u
    by_cases hu : u = r
    · rw [show η u = ζ from ite_eq_left hu]; exact hζ
    · by_cases hE' : u ∈ E
      · rw [show η u = (ξ u).map p from (ite_eq_right hu).trans (ite_eq_left hE')]
        infer_instance
      · rw [show η u = 0 from (ite_eq_right hu).trans (ite_eq_right hE')]
        infer_instance
  · intro u
    by_cases hu : u = r
    · rw [show η u = ζ from ite_eq_left hu]
      exact continuation_exp_map_support (continuation_profile_support v r σ)
    · by_cases hE' : u ∈ E
      · rw [show η u = (ξ u).map p from (ite_eq_right hu).trans (ite_eq_left hE')]
        exact continuation_exp_map_support hE'.1
      · rw [show η u = 0 from (ite_eq_right hu).trans (ite_eq_right hE')]
        simp
  · intro u
    by_cases hu : u = r
    · rw [show η u = ζ from ite_eq_left hu]
      rw [← measureMoment_zero_eq_mass]
      change measureMoment ((weightedMeasure (profileMeasure v r) σ).map (fun x => Real.exp (-x))) 0 ≤ _
      rw [measureMoment_weighted_exponential_map, Nat.cast_zero, add_zero, Measure.real,
        weightedMeasure_profileMeasure_mass hadm, ENNReal.toReal_ofReal]
      · exact hF
      · unfold profileTransform profileA
        positivity
    · by_cases hE' : u ∈ E
      · rw [show η u = (ξ u).map p from (ite_eq_right hu).trans (ite_eq_left hE')]
        rw [Measure.real, Measure.map_apply hp MeasurableSet.univ, Set.preimage_univ]
        exact hE'.2
      · rw [show η u = 0 from (ite_eq_right hu).trans (ite_eq_right hE'), measureReal_zero,
          Pi.zero_apply]
        exact hM
  · change ∀ᵐ u : ℝ, u ∈ Set.Icc r b → _
    have hξ' := (ae_restrict_iff' (s := Set.Icc r b) (μ := volume) measurableSet_Icc).1 hξ
    filter_upwards [hξ', hne] with u hu une hmem n
    obtain ⟨_, hsupport, hmoment⟩ := hu hmem
    have huE : u ∈ E := by
      have hz := hmoment 0
      have hzero : weightedMeasure (ξ u) 0 = ξ u := by
        unfold weightedMeasure
        simp only [zero_mul, neg_zero, Real.exp_zero, ENNReal.ofReal_one]
        exact withDensity_one
      simp only [Nat.cast_zero, hzero] at hz
      refine ⟨hsupport, ?_⟩
      rw [hz]
      exact (le_abs_self (L 1 u)).trans (hb u hmem)
    rw [show η u = (ξ u).map p from (ite_eq_right une).trans (ite_eq_left huE)]
    have he := measureMoment_weighted_exponential_map (ξ u) 0 n
    have hzero : weightedMeasure (ξ u) 0 = ξ u := by
      unfold weightedMeasure
      simp only [zero_mul, neg_zero, Real.exp_zero, ENNReal.ofReal_one]
      exact withDensity_one
    rw [hzero, zero_add] at he
    exact ((show measureMoment ((ξ u).map p) n = _ from he).trans (hmoment n)).symm


/-- Any sequence with a bounded base transform and an identified trace
has a further subsequence whose local Mellin limits are the profile. -/
theorem continuation_local_profile_subsequence {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {v a r δ s₀ M K : ℝ} (ha : 0 < a) (hδ : 0 < δ) (har : a < r) (hrb : r ≤ a+δ)
    (hs₀ : 0 ≤ s₀) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hp : ∀ u ∈ Set.Icc r (a+δ), IsPrePoleTime v u)
    (hadm : ∀ u ∈ Set.Icc r (a+δ), 0 < s₀ + profileB v u)
    (hFb : ∀ u ∈ Set.Icc r (a+δ), |profileTransform v u s₀| ≤ K ∧
      |profileTransform v u (s₀+1)| ≤ K)
    (hsmall : Real.exp ((s₀+1) * (a+δ-r)) * (3*K) * (a+δ-r) < 1)
    (hsmallBase : (|s₀| + 3*(3*K)) * (a+δ-r) < 1)
    {ns h : ℕ → ℝ} (hns : Tendsto ns atTop atTop)
    (hBase : ∀ᶠ j in atTop, ∀ t ∈ Set.Icc a (a+δ),
      |transformAt μ B (h j) (ns j) ⌊ns j*t⌋₊ s₀| ≤ M)
    (hBig : ∀ k : ℕ, ∀ᶠ j in atTop, ∀ t ∈ Set.Icc a (a+δ),
      |transformAt μ B (h j) (ns j) ⌊ns j*t⌋₊ (s₀+k)| ≤ K)
    (hStart : ∀ k : ℕ, Tendsto (fun j => transformAt μ B (h j) (ns j) ⌊ns j*r⌋₊ (s₀+k))
      atTop (𝓝 (profileTransform v r (s₀+k)))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ u : ℝ, u ∈ Set.Icc r (a+δ) → ∀ k : ℕ,
      Tendsto (fun j => transformAt μ B (h (φ j)) (ns (φ j)) ⌊ns (φ j)*u⌋₊ (s₀+k))
        atTop (𝓝 (profileTransform v u (s₀+k))) := by
  classical
  let b := a+δ
  let F (k : ℕ) (u : ℝ) := profileTransform v u (s₀+k)
  let X (j k : ℕ) (u : ℝ) := transformAt μ B (h j) (ns j) ⌊ns j*u⌋₊ (s₀+k)
  obtain ⟨φ, L, hφ, hLm, hLim, hU⟩ := exists_subseq_transform_limits hpos hmean hB
    ha hδ har hrb hs₀ hM hns hBase
  have hT := hφ.tendsto_atTop
  have hUpd (k : ℕ) : TendstoUniformlyOn (fun j t => X (φ j) k t - X (φ j) 0 t)
      (fun t => L k t - L 0 t) atTop (Set.Icc r b) := hU k
  have hLim' : ∀ᵐ t : ℝ, t ∈ Set.Icc r b → ∀ k,
      Tendsto (fun j => X (φ j) k t) atTop (𝓝 (L k t)) := hLim
  have hBig' (k : ℕ) : ∀ᶠ j in atTop, ∀ t ∈ Set.Icc a b, |X (φ j) k t| ≤ K :=
    hT.eventually (hBig k)
  have hDif (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc r b) : |L k t - L 0 t| ≤ 2*K := by
    apply le_of_tendsto ((hUpd k).tendsto_at ht).abs
    filter_upwards [hBig' k, hBig' 0] with j h₁ h₀
    have h := norm_sub_le (X (φ j) k t) (X (φ j) 0 t)
    simp only [Real.norm_eq_abs] at h
    linarith [h₁ t ⟨har.le.trans ht.1, ht.2⟩, h₀ t ⟨har.le.trans ht.1, ht.2⟩]
  let A (u : ℝ) := if u = r then F 0 r else max (-K) (min K (L 0 u))
  let L' (k : ℕ) (u : ℝ) := A u + (L k u - L 0 u)
  have hAbsA (u : ℝ) : |A u| ≤ K := by
    by_cases hu : u = r
    · simp only [A, ite_eq_left hu, F, Nat.cast_zero, add_zero]
      exact (hFb r ⟨le_rfl, hrb⟩).1
    · apply abs_le.2
      simp only [A, ite_eq_right hu]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hL'b (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc r b) : |L' k t| ≤ 3*K :=
    (abs_add_le _ _).trans (by linarith [hAbsA t, hDif k t ht])
  have hAm : Measurable A := measurable_const.ite (measurableSet_singleton _)
    (measurable_const.max (measurable_const.min (hLm 0)))
  have hL'm (k : ℕ) : Measurable (L' k) := hAm.add ((hLm k).sub (hLm 0))
  have hEq : ∀ᵐ t : ℝ, t ∈ Set.Icc r b → ∀ k, L' k t = L k t := by
    have hne : ∀ᵐ t : ℝ, t ≠ r := by simp [ae_iff]
    filter_upwards [hLim', hne] with t ht htr hmem k
    have hL0 : |L 0 t| ≤ K :=
      le_of_tendsto (ht hmem 0).abs ((hBig' 0).mono fun j hj => hj t ⟨har.le.trans hmem.1, hmem.2⟩)
    obtain ⟨hl, hu⟩ := abs_le.1 hL0
    dsimp [L', A]
    rw [ite_eq_right htr, min_eq_right hu, max_eq_right hl]
    ring
  have hLimL' : ∀ᵐ t : ℝ, t ∈ Set.Icc r b → ∀ k,
      Tendsto (fun j => X (φ j) k t) atTop (𝓝 (L' k t)) := by
    filter_upwards [hLim', hEq] with t ht he hm k
    rw [he hm k]
    exact ht hm k
  have hstart (k : ℕ) : L' k r = F k r := by
    have h₁ := (hUpd k).tendsto_at (show r ∈ Set.Icc r b from ⟨le_rfl, hrb⟩)
    have h₂ := ((hStart k).comp hT).sub ((hStart 0).comp hT)
    have he : L k r - L 0 r = F k r - F 0 r := tendsto_nhds_unique h₁ h₂
    dsimp [L', A]
    rw [ite_eq_left rfl, he]
    ring
  have he (k : ℕ) : (fun t => L' k t - L' 0 t) = fun t => L k t - L 0 t := by
    funext t
    dsimp [L']
    ring
  have hDiff (k : ℕ) : TendstoUniformlyOn (fun j t => X (φ j) k t - X (φ j) 0 t)
      (fun t => L' k t - L' 0 t) atTop (Set.Icc r b) := by rw [he k]; exact hUpd k
  have hD (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc r b) :
      (L' k t - L' 0 t) - (L' k r - L' 0 r) =
        timeIntegral (fun x => psiS (s₀+k) (L' k x) - psiS s₀ (L' 0 x)) r t := by
    have hs : s₀ ≤ s₀ + (k : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg k)
    refine transform_sublimit_difference_equation hpos hmean hB (ns := fun j => ns (φ j))
      (h := fun j => h (φ j)) (s := s₀+k) ha hδ har hs₀ hs hM (hns.comp hT)
      (hT.eventually hBase) (L' 0) (L' k) ?_ ?_ r t le_rfl ht.1 ht.2
    · filter_upwards [hLimL'] with u hu hmem
      refine ⟨?_, hu hmem k⟩
      simpa only [X, Nat.cast_zero, add_zero] using hu hmem 0
    · simpa only [X, Nat.cast_zero, add_zero] using hDiff k
  have hsr : 0 < s₀+1+profileB v r := by linarith [hadm r ⟨le_rfl, hrb⟩]
  have hFr : profileTransform v r (s₀+1) ≤ 3*K := by
    linarith [(hFb r ⟨le_rfl, hrb⟩).2, le_abs_self (profileTransform v r (s₀+1))]
  obtain ⟨η, hmη, hfη, hsupη, hmassη, htraceη, hrepη⟩ :=
    continuation_model_projected_kernel (h := fun j => h (φ j)) hpos hmean hB (ha.trans har)
      hrb hs₀ (by positivity : 0 ≤ 3*K) hsr hFr (hns.comp hT) L' (hL'b 1) hLimL'
  have hFb' (t : ℝ) (ht : t ∈ Set.Icc r b) :
      |profileTransform v t s₀| ≤ 3*K ∧ |profileTransform v t (s₀+1)| ≤ 3*K := by
    obtain ⟨h₁,h₂⟩ := hFb t ht
    exact ⟨by linarith, by linarith⟩
  have hID := continuation_identify_transform_limits L' η hs₀ hrb (by positivity) hp hadm hFb'
    hsmall hsmallBase hmη hfη hsupη hmassη hL'm hL'b hstart htraceη hrepη hD
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hLimL', hID] with u hu he hmem k
  rw [← he hmem k]
  exact hu hmem k

/-- Uniform convergence follows from the one-sided time estimate and almost
everywhere convergence to a continuous limit. -/
theorem continuation_uniform_of_ae_transform {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {a r δ w M : ℝ} (ha : 0 < a) (hδ : 0 < δ) (har : a ≤ r) (hr : r < a+δ)
    (hw : 0 ≤ w) (hM : 0 ≤ M) {ns h : ℕ → ℝ} (hns : Tendsto ns atTop atTop)
    {F : ℝ → ℝ} (hF : ContinuousOn F (Set.Icc r (a+δ)))
    (hFb : ∀ t ∈ Set.Icc r (a+δ), |F t| ≤ M)
    (hb : ∀ᶠ j in atTop, ∀ t ∈ Set.Icc a (a+δ),
      |transformAt μ B (h j) (ns j) ⌊ns j*t⌋₊ w| ≤ M)
    (hl : ∀ᵐ t : ℝ, t ∈ Set.Icc r (a+δ) →
      Tendsto (fun j => transformAt μ B (h j) (ns j) ⌊ns j*t⌋₊ w) atTop (𝓝 (F t))) :
    ∀ J : Set ℝ, IsCompact J → J ⊆ Set.Ioo r (a+δ) →
      TendstoUniformlyOn (fun j t => transformAt μ B (h j) (ns j) ⌊ns j*t⌋₊ w) F atTop J := by
  let X (j : ℕ) (t : ℝ) := transformAt μ B (h j) (ns j) ⌊ns j*t⌋₊ w
  obtain ⟨C, hC⟩ := transform_bounded_aux hpos hmean hB
  obtain ⟨N₁, D, ε, hε, hD⟩ := hC a δ w M ha hδ hw
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hb.and (hns.eventually_ge_atTop N₁))
  let p (j : ℕ) := j+j₀
  have hp : Tendsto p atTop atTop :=
    (show StrictMono p from fun _ _ h => Nat.add_lt_add_right h _).tendsto_atTop
  have hgood (j : ℕ) : (∀ t ∈ Set.Icc a (a+δ), |X (p j) t| ≤ M) ∧ N₁ ≤ ns (p j) :=
    hj₀ (p j) (by dsimp [p]; omega)
  have hm (j : ℕ) : Measurable (X j) :=
    (measurable_of_countable (fun n : ℕ => transformAt μ B (h j) (ns j) n w)).comp
      (measurable_const.mul measurable_id).nat_floor
  have hL1 : Tendsto (fun j => ∫ t in r..(a+δ), |X (p j) t-F t|) atTop (𝓝 0) := by
    have hFmeas := (hF.intervalIntegrable_of_Icc (μ := volume) hr.le).aestronglyMeasurable
    simpa only [intervalIntegral.integral_zero] using
      (intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (a := r) (b := a+δ) (F := fun j t => |X (p j) t-F t|) (f := fun _ => 0)
        (fun _ => 2*M)
        (Eventually.of_forall fun j => by
          rw [Set.uIoc_of_le hr.le]
          simpa only [Real.norm_eq_abs, Pi.sub_apply] using
            ((hm (p j)).aestronglyMeasurable.sub hFmeas).norm)
        (Eventually.of_forall fun j => Eventually.of_forall fun t htu => by
          have ht : t ∈ Set.Icc r (a+δ) := by
            rw [Set.uIoc_of_le hr.le] at htu
            exact ⟨htu.1.le, htu.2⟩
          have htri := norm_sub_le (X (p j) t) (F t)
          rw [Real.norm_eq_abs, abs_abs]
          simp only [Real.norm_eq_abs] at htri
          linarith [(hgood j).1 t ⟨har.trans ht.1, ht.2⟩, hFb t ht])
        (intervalIntegrable_const)
        (by
          filter_upwards [hl] with t hlt htu
          rw [Set.uIoc_of_le hr.le] at htu
          simpa only [Function.comp_apply, X, sub_self, abs_zero] using
            (((hlt ⟨htu.1.le,htu.2⟩).comp hp).sub
              (tendsto_const_nhds : Tendsto (fun _ : ℕ => F t) atTop (𝓝 (F t)))).abs))
  have hu := one_sided_compactness_aux r (a+δ) D (fun j => X (p j)) F (fun j => ε (ns (p j))) hr
    ⟨M, fun j t ht => (hgood j).1 t ⟨har.trans ht.1, ht.2⟩⟩
    (fun j => (hm (p j)).aestronglyMeasurable)
    (fun j t u ht hu htu => (hD _ (hgood j).2 _ (hgood j).1).2.2.2
      t u (har.trans ht.1) htu hu.2)
    (hε.comp (hns.comp hp)) hF hL1
  intro J hJ hsub
  have H := hu J hJ hsub
  rw [Metric.tendstoUniformlyOn_iff] at H ⊢
  intro η hη
  obtain ⟨j₁, hj₁⟩ := eventually_atTop.1 (H η hη)
  refine eventually_atTop.2 ⟨j₁+j₀, fun j hj => ?_⟩
  have he : p (j-j₀) = j := by dsimp [p]; omega
  simpa only [he] using hj₁ (j-j₀) (by omega)

/-- Uniform convergence can be checked along further subsequences. -/
theorem continuation_uniform_of_further_subsequences {ι α β : Type*} [UniformSpace β]
    {l : Filter ι} [l.IsCountablyGenerated] {X : ι → α → β} {F : α → β} {J : Set α}
    (h : ∀ ns : ℕ → ι, Tendsto ns atTop l → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformlyOn (fun j => X (ns (φ j))) F atTop J) :
    TendstoUniformlyOn X F l J := by
  rw [tendstoUniformlyOn_iff_tendsto]
  apply tendsto_of_further_subsequences
  intro p hp
  have ⟨h₁, h₂⟩ := tendsto_prod_iff'.1 hp
  obtain ⟨φ, hφ, hu⟩ := h (fun j => (p j).1) h₁
  rw [tendstoUniformlyOn_iff_tendsto] at hu
  exact ⟨φ, hφ, hu.comp (tendsto_id.prodMk (h₂.comp hφ.tendsto_atTop))⟩

theorem profileTransform_abs_le_of_le_weight {v t s w : ℝ}
    (hs : 0 < s + profileB v t) (hw : s ≤ w) :
    |profileTransform v t w| ≤ |profileTransform v t s| := by
  unfold profileTransform
  have hA : 0 ≤ profileA v t := by unfold profileA; positivity
  have hsw : s + profileB v t ≤ w + profileB v t := add_le_add_left hw _
  rw [abs_of_nonneg (div_nonneg hA (hs.le.trans hsw)), abs_of_nonneg (div_nonneg hA hs.le)]
  exact div_le_div_of_nonneg_left hA hs hsw

/-- Propagate all the integer-offset transforms from an identified trace
through a short interval on which the base transform stays bounded. -/
theorem continuation_local_uniform {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {v a r δ s₀ M K : ℝ} (ha : 0 < a) (hδ : 0 < δ) (har : a < r) (hrb : r < a+δ)
    (hs₀ : 0 ≤ s₀) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hp : ∀ u ∈ Set.Icc r (a+δ), IsPrePoleTime v u)
    (hadm : ∀ u ∈ Set.Icc r (a+δ), 0 < s₀ + profileB v u)
    (hFb : ∀ u ∈ Set.Icc r (a+δ), |profileTransform v u s₀| ≤ K)
    (hsmall : Real.exp ((s₀+1) * (a+δ-r)) * (3*K) * (a+δ-r) < 1)
    (hsmallBase : (|s₀| + 3*(3*K)) * (a+δ-r) < 1)
    {ns h : ℕ → ℝ} (hns : Tendsto ns atTop atTop)
    (hBase : ∀ᶠ j in atTop, ∀ t ∈ Set.Icc a (a+δ),
      |transformAt μ B (h j) (ns j) ⌊ns j*t⌋₊ s₀| ≤ M)
    (hBig : ∀ k : ℕ, ∀ᶠ j in atTop, ∀ t ∈ Set.Icc a (a+δ),
      |transformAt μ B (h j) (ns j) ⌊ns j*t⌋₊ (s₀+k)| ≤ K)
    (hStart : ∀ k : ℕ, Tendsto (fun j => transformAt μ B (h j) (ns j) ⌊ns j*r⌋₊ (s₀+k))
      atTop (𝓝 (profileTransform v r (s₀+k)))) :
    ∀ (k : ℕ) (J : Set ℝ), IsCompact J → J ⊆ Set.Ioo r (a+δ) →
      TendstoUniformlyOn (fun j t => transformAt μ B (h j) (ns j) ⌊ns j*t⌋₊ (s₀+k))
        (fun t => profileTransform v t (s₀+k)) atTop J := by
  have hsk (k : ℕ) : s₀ ≤ s₀+k := le_add_of_nonneg_right (Nat.cast_nonneg k)
  have hFbk (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc r (a+δ)) :
      |profileTransform v t (s₀+k)| ≤ K :=
    (profileTransform_abs_le_of_le_weight (hadm t ht) (hsk k)).trans (hFb t ht)
  intro k J hJ hsub
  apply continuation_uniform_of_further_subsequences
  intro q hq
  obtain ⟨φ, hφ, hlim⟩ := continuation_local_profile_subsequence hpos hmean hB
    ha hδ har hrb.le hs₀ hM hK hp hadm
    (fun t ht => ⟨hFb t ht, by simpa only [Nat.cast_one] using hFbk 1 t ht⟩)
    hsmall hsmallBase (hns.comp hq) (hq.eventually hBase)
    (fun n => hq.eventually (hBig n)) (fun n => (hStart n).comp hq)
  refine ⟨φ, hφ, ?_⟩
  have hqφ := hq.comp hφ.tendsto_atTop
  refine continuation_uniform_of_ae_transform hpos hmean hB ha hδ har.le hrb
    (hs₀.trans (hsk k)) hK (hns.comp hqφ) ?_ (hFbk k) (hqφ.eventually (hBig k))
    (hlim.mono fun t ht hmem => ht hmem k) J hJ hsub
  exact fun t ht => (profileTransform_hasDerivAt (hp t ht)
    ((hadm t ht).trans_le (add_le_add_left (hsk k) _))).continuousAt.continuousWithinAt

private theorem continuation_ae_point {P : ℝ → Prop} {a b : ℝ} (hab : a < b)
    (h : ∀ᵐ t : ℝ, t ∈ Set.Ioo a b → P t) :
    ∃ t ∈ Set.Ioo a b, P t := by
  apply Measure.exists_mem_of_measure_ne_zero_of_ae (μ := volume)
  · rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
  · exact (ae_restrict_iff' measurableSet_Ioo).2 h

private theorem continuation_short_lengths {s K δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ δ > (0 : ℝ), δ ≤ δ₀ ∧ ∀ x ∈ Set.Icc 0 δ,
      Real.exp ((s+1)*x) * (3*K) * x < 1 ∧ (|s| + 3*(3*K))*x < 1 := by
  let A (x : ℝ) := Real.exp ((s+1)*x) * (3*K) * x
  let D (x : ℝ) := (|s| + 3*(3*K))*x
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hD : Continuous D := by dsimp [D]; fun_prop
  have H : {x | A x < 1 ∧ D x < 1} ∈ 𝓝 (0 : ℝ) := by
    have h₁ : A 0 < 1 := by simp [A]
    have h₂ : D 0 < 1 := by simp [D]
    exact (hA.continuousAt.eventually (gt_mem_nhds h₁)).and
      (hD.continuousAt.eventually (gt_mem_nhds h₂))
  obtain ⟨l,u,hu,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 H
  let δ := min δ₀ (u/2)
  have hδ : 0 < δ := lt_min hδ₀ (by linarith [hu.2])
  refine ⟨δ,hδ,min_le_left _ _,fun x hx => hsub ⟨hu.1.trans_le hx.1, ?_⟩⟩
  have hle := hx.2.trans (min_le_right δ₀ (u/2))
  linarith [hu.2]

/-- An almost everywhere identified entrance propagates to every interior
compact time set within the admissible profile region. -/
theorem continuation_uniform_from_entrance {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {v s A c d b : ℝ} (hs : 0 ≤ s) (hA : 0 < A) (hAc : A < c)
    (hcd : c ≤ d) (hdb : d < b)
    (hp : ∀ t ∈ Set.Icc A b, IsPrePoleTime v t)
    (hadm : ∀ t ∈ Set.Icc A b, 0 < s + profileB v t)
    {ns h : ℕ → ℝ} (hns : Tendsto ns atTop atTop)
    (hEntrance : ∀ᵐ t : ℝ, t ∈ Set.Ioo A c → ∀ k : ℕ,
      Tendsto (fun j => transformAt μ B (h j) (ns j) ⌊ns j*t⌋₊ (s+k))
        atTop (𝓝 (profileTransform v t (s+k))))
    {I : Set ℝ} (hI : IsCompact I) (hsub : I ⊆ Set.Icc c d) :
    TendstoUniformlyOn (fun j t => transformAt μ B (h j) (ns j) ⌊ns j*t⌋₊ s)
      (fun t => profileTransform v t s) atTop I := by
  let X (j : ℕ) (w t : ℝ) := transformAt μ B (h j) (ns j) ⌊ns j*t⌋₊ w
  let P (t : ℝ) := ∀ k : ℕ, Tendsto (fun j => X j (s+k) t) atTop
    (𝓝 (profileTransform v t (s+k)))
  have hCont : ContinuousOn (fun t => profileTransform v t s) (Set.Icc A b) :=
    fun t ht => (profileTransform_hasDerivAt (hp t ht) (hadm t ht)).continuousAt.continuousWithinAt
  obtain ⟨z, hz, hzmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (hAc.le.trans (hcd.trans hdb.le))) hCont.abs
  let M := |profileTransform v z s| + 1
  have hM : 1 ≤ M := by dsimp [M]; linarith [abs_nonneg (profileTransform v z s)]
  have hprof (t : ℝ) (ht : t ∈ Set.Icc A b) : |profileTransform v t s| < M :=
    (hzmax ht).trans_lt (lt_add_one _)
  obtain ⟨δ₀, hδ₀, hBound⟩ := transform_bounded_of_start hpos hmean hB hs hM
  obtain ⟨C, hC, hLarge⟩ := transform_bounded_at_larger_weight hpos hmean hB
  let K := M+1+C
  have hK : 0 ≤ K := by dsimp [K]; linarith
  let e := (d+b)/2
  have hde : d < e := by dsimp [e]; linarith
  have heb : e < b := by dsimp [e]; linarith
  obtain ⟨δ,hδ,hδle,hSmall⟩ := continuation_short_lengths (s := s) (K := K)
    (lt_min hδ₀ (sub_pos.2 heb))
  have hδ₀' := hδle.trans (min_le_left δ₀ (b-e))
  have hδe := hδle.trans (min_le_right δ₀ (b-e))
  have hAE : ∀ᵐ t : ℝ, t ∈ Set.Ioo A c → P t := hEntrance
  let m := min c (A+δ/4)
  have hAm : A < m := lt_min hAc (by linarith)
  have hmc : m ≤ c := min_le_left _ _
  obtain ⟨a₀,ha₀,hPa₀⟩ := continuation_ae_point (show A < (A+m)/2 by linarith)
    (hAE.mono fun t ht hm => ht ⟨hm.1, by linarith [hm.2]⟩)
  obtain ⟨r₁,hr₁,hPr₁⟩ := continuation_ae_point (show (A+m)/2 < m by linarith)
    (hAE.mono fun t ht hm => ht ⟨by linarith [hm.1], hm.2.trans_le hmc⟩)
  have hr₁c : r₁ < c := hr₁.2.trans_le hmc
  have ha₀r₁ : a₀ < r₁ := ha₀.2.trans hr₁.1
  have hr₁a₀ : r₁-a₀ < δ/4 := by
    have h := hr₁.2.trans_le (min_le_right c (A+δ/4))
    linarith [ha₀.1]
  have hwindow (a r : ℝ) (ha : A ≤ a) (har : a < r) (hre : r ≤ e)
      (hrb : r < a+δ) (hPa : P a) (hPr : P r) :
      ∀ k : ℕ, ∀ J : Set ℝ, IsCompact J → J ⊆ Set.Ioo r (a+δ) →
        TendstoUniformlyOn (fun j t => X j (s+k) t)
          (fun t => profileTransform v t (s+k)) atTop J := by
    have ha' := hA.trans_le ha
    have hmaster : Set.Icc a (a+δ) ⊆ Set.Icc A b := fun t ht =>
      ⟨ha.trans ht.1, by linarith [ht.2, har.le]⟩
    have hmaster' : Set.Icc r (a+δ) ⊆ Set.Icc A b := fun t ht =>
      hmaster ⟨har.le.trans ht.1, ht.2⟩
    have hAstart : ∀ᶠ j in atTop, X j s a ≤ M := by
      have ht : profileTransform v a s < M :=
        (le_abs_self _).trans_lt (hprof a (hmaster ⟨le_rfl, by linarith⟩))
      have hz := (hPa 0).eventually (Iic_mem_nhds (by simpa only [Nat.cast_zero, add_zero] using ht))
      simpa only [Nat.cast_zero, add_zero, Set.mem_Iic] using hz
    have hBase : ∀ᶠ j in atTop, ∀ t ∈ Set.Icc a (a+δ), |X j s t| ≤ M+1 := by
      filter_upwards [hns.eventually (hBound a ha'), hAstart] with j hj hstart t ht
      exact hj (h j) hstart t ⟨ht.1, ht.2.trans (add_le_add_right hδ₀' a)⟩
    have hBig (k : ℕ) : ∀ᶠ j in atTop, ∀ t ∈ Set.Icc a (a+δ), |X j (s+k) t| ≤ K := by
      filter_upwards [hns.eventually (hLarge a (a+δ) s (s+k) (M+1) ha' hs
        (le_add_of_nonneg_right (Nat.cast_nonneg k)) (by linarith)), hBase] with j hj hb
      exact hj (h j) hb
    have hsmall := hSmall (a+δ-r) ⟨by linarith, by linarith⟩
    exact continuation_local_uniform hpos hmean hB ha' hδ har hrb hs (by linarith)
      hK (fun t ht => hp t (hmaster' ht)) (fun t ht => hadm t (hmaster' ht))
      (fun t ht => (hprof t (hmaster' ht)).le.trans (by dsimp [K]; linarith))
      hsmall.1 hsmall.2 hns hBase hBig hPr
  have hR : r₁ ≤ e := by linarith
  have hchain : ∀ r ∈ Set.Icc r₁ e, ∀ y ∈ Set.Icc r₁ r, P y := by
    refine interval_induction_fixed_step (P := fun r => ∀ y ∈ Set.Icc r₁ r, P y)
      hR (show 0 < δ/4 by linarith) ?_ ?_
    · intro t ht
      rw [le_antisymm ht.2 ht.1]
      exact hPr₁
    · intro r hr hPrev t ht y hy
      by_cases hyr : y ≤ r
      · exact hPrev y ⟨hy.1,hyr⟩
      let a := if r₁ ≤ r-δ/4 then r-δ/4 else a₀
      have ha : A ≤ a := by
        dsimp [a]
        split_ifs with hh
        · exact ha₀.1.le.trans (ha₀r₁.le.trans hh)
        · exact ha₀.1.le
      have har : a < r := by
        dsimp [a]
        split_ifs
        · linarith
        · exact ha₀r₁.trans_le hr.1
      have hfar : r-a < δ/2 := by
        dsimp [a]
        split_ifs with hh
        · linarith
        · linarith [lt_of_not_ge hh]
      have hPa : P a := by
        dsimp [a]
        split_ifs with hh
        · exact hPrev _ ⟨hh,by linarith⟩
        · exact hPa₀
      have hy' : y ∈ Set.Ioo r (a+δ) := by
        refine ⟨lt_of_not_ge hyr, ?_⟩
        linarith [hy.2.trans (ht.2.trans (min_le_right e (r+δ/4)))]
      intro k
      exact (hwindow a r ha har hr.2 (hy'.1.trans hy'.2) hPa
        (hPrev r ⟨hr.1,le_rfl⟩) k {y} isCompact_singleton
        (Set.singleton_subset_iff.2 hy')).tendsto_at (Set.mem_singleton y)
  have hall := hchain e ⟨hR,le_rfl⟩
  have hLocal : TendstoLocallyUniformlyOn (fun j t => X j s t)
      (fun t => profileTransform v t s) atTop (Set.Ioo r₁ e) := by
    apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
    intro t ht
    let r := max r₁ (t-δ/4)
    let a := if r₁ ≤ r-δ/4 then r-δ/4 else a₀
    have hrt : r < t := max_lt ht.1 (by linarith)
    have hr : r ∈ Set.Icc r₁ e := ⟨le_max_left _ _,hrt.le.trans ht.2.le⟩
    have hra : a < r ∧ A ≤ a ∧ r-a < δ/2 ∧ P a := by
      dsimp [a]
      split_ifs with hh
      · exact ⟨by linarith, ha₀.1.le.trans (ha₀r₁.le.trans hh), by linarith,
          hall _ ⟨hh,by linarith [hr.2]⟩⟩
      · exact ⟨ha₀r₁.trans_le hr.1,ha₀.1.le,by linarith [lt_of_not_ge hh],hPa₀⟩
    have ht' : t < a+δ := by
      have h := le_max_right r₁ (t-δ/4)
      linarith [hra.2.2.1]
    let J := Set.Icc ((r+t)/2) ((t+(a+δ))/2)
    have hJ : J ∈ 𝓝[Set.Ioo r₁ e] t :=
      nhdsWithin_le_nhds (Icc_mem_nhds (by linarith) (by linarith))
    refine ⟨J,hJ,?_⟩
    have H := hwindow a r hra.2.1 hra.1 hr.2 (hrt.trans ht') hra.2.2.2 (hall r hr)
      0 J isCompact_Icc (fun y hy => ⟨by linarith [hy.1],by linarith [hy.2]⟩)
    simpa only [Nat.cast_zero, add_zero] using H
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioo).1 hLocal I
    (fun t ht => ⟨hr₁c.trans_le (hsub ht).1, (hsub ht).2.trans_lt hde⟩) hI

private theorem exists_larger_admissible_time {v s d : ℝ} (hd : IsPrePoleTime v d)
    (hsd : 0 < s + profileB v d) :
    ∃ b > d, IsPrePoleTime v b ∧ 0 < s + profileB v b := by
  have hp : {t | IsPrePoleTime v t} ∈ 𝓝 d := by
    by_cases hv : 0 < v
    · exact ((lt_mem_nhds hd.1).and (gt_mem_nhds (hd.2 hv))).mono
        fun t ht => ⟨ht.1, fun _ => ht.2⟩
    · exact (lt_mem_nhds hd.1).mono fun t ht => ⟨ht, fun h => (hv h).elim⟩
  have hB : {t | 0 < s + profileB v t} ∈ 𝓝 d :=
    ((hasDerivAt_profileB hd).const_add s).continuousAt.eventually (lt_mem_nhds hsd)
  obtain ⟨l,u,hlu,hu⟩ := mem_nhds_iff_exists_Ioo_subset.1 (inter_mem hp hB)
  obtain ⟨b,hdb,hbu⟩ := exists_between hlu.2
  exact ⟨b,hdb,hu ⟨hlu.1.trans hdb,hbu⟩⟩

private theorem continuation_uniform_of_entrance_subsequences {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {v lam Tstar s : ℝ} (hTstar : 0 < Tstar) (hs : 0 ≤ s)
    (hEntrance : ∀ Nseq : ℕ → ℝ, Tendsto Nseq atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ᵐ t : ℝ, t ∈ Set.Ioo 0 Tstar → ∀ w, 0 ≤ w → 0 < w + profileB v t →
          Tendsto (fun j => scaledTransform μ B lam (Nseq (φ j)) t w) atTop
            (𝓝 (profileTransform v t w)))
    {I : Set ℝ} (hI : IsCompact I) (hne : I.Nonempty)
    (hp : ∀ t ∈ I, IsPrePoleTime v t)
    (hadm : ∀ t ∈ I, 0 < s + profileB v t) :
    TendstoUniformlyOn (fun N t => scaledTransform μ B lam N t s)
      (fun t => profileTransform v t s) atTop I := by
  let d := sSup I
  have hd : d ∈ I := hI.sSup_mem hne
  have hmin : 0 < sInf I := (hp _ (hI.sInf_mem hne)).1
  let c := min (sInf I) (Tstar/2)
  have hc : 0 < c := lt_min hmin (by linarith)
  have hcT : c < Tstar := (min_le_right _ _).trans_lt (by linarith)
  have hsub : I ⊆ Set.Icc c d := fun t ht =>
    ⟨(min_le_left _ _).trans (csInf_le hI.bddBelow ht), le_csSup hI.bddAbove ht⟩
  have hcd : c ≤ d := (hsub hd).1
  obtain ⟨b,hdb,hpb,hab⟩ := exists_larger_admissible_time (hp d hd) (hadm d hd)
  let A := c/2
  have hA : 0 < A := by dsimp [A]; linarith
  have hAc : A < c := by dsimp [A]; linarith
  have hp' (t : ℝ) (ht : t ∈ Set.Icc A b) : IsPrePoleTime v t :=
    ⟨hA.trans_le ht.1, fun hv => ht.2.trans_lt (hpb.2 hv)⟩
  have hadm' (t : ℝ) (ht : t ∈ Set.Icc A b) : 0 < s + profileB v t :=
    hab.trans_le (add_le_add_right (profileB_antitoneOn v (hp' t ht) hpb ht.2) s)
  apply continuation_uniform_of_further_subsequences
  intro ns hns
  obtain ⟨φ,hφ,hφAE⟩ := hEntrance ns hns
  have hAE : ∀ᵐ t : ℝ, t ∈ Set.Ioo A c → ∀ k : ℕ,
      Tendsto (fun j => scaledTransform μ B lam (ns (φ j)) t (s+k))
        atTop (𝓝 (profileTransform v t (s+k))) := by
    filter_upwards [hφAE] with t ht hmem k
    have ht' : t ∈ Set.Icc A b := ⟨hmem.1.le,hmem.2.le.trans (hcd.trans hdb.le)⟩
    exact ht ⟨hA.trans hmem.1,hmem.2.trans hcT⟩ (s+k) (by positivity)
      ((hadm' t ht').trans_le (by linarith [Nat.cast_nonneg (α := ℝ) k]))
  exact ⟨φ,hφ,continuation_uniform_from_entrance hpos hmean hB hs hA hAc hcd hdb hp' hadm'
    (hns.comp hφ.tendsto_atTop) hAE hI hsub⟩

private theorem continuation_weak_of_transform_limits {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {v lam t s₀ s : ℝ} (ht : 0 < t) (hs₀ : 0 ≤ s₀) (hss : s₀ < s)
    (hadm : 0 < s₀ + profileB v t)
    (hlim : ∀ w : ℝ, s₀ ≤ w → Tendsto (fun N => scaledTransform μ B lam N t w) atTop
      (𝓝 (profileTransform v t w))) :
    WeakConvergence (fun N => weightedMeasure (scalingMeasure μ B lam N t) s) atTop
      (weightedMeasure (profileMeasure v t) s) := by
  let ν (N : ℝ) := scalingMeasure μ B lam N t
  let ν' := profileMeasure v t
  have hmass (w : ℝ) (hw : s₀ ≤ w) :
      Tendsto (fun N => (weightedMeasure (ν N) w).real Set.univ) atTop
        (𝓝 (profileTransform v t w)) :=
    tendsto_rescaled_weighted_mass_of_transform (ns := id) (h := scalingField μ B lam)
      hpos hmean hB ht (hs₀.trans hw) tendsto_id (hlim w hw)
  let C : ℝ≥0 := ⟨max 0 (profileTransform v t s₀ + 1), le_max_left _ _⟩
  have hb : ∀ᶠ N in atTop, ν N (Set.Iio 0) = 0 ∧ weightedMeasure (ν N) s₀ Set.univ ≤ C := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (hmass s₀ le_rfl).eventually (Iic_mem_nhds (lt_add_one _))] with N hN hmassN
    obtain ⟨hf,hsup⟩ :=
      rescaledMeasure_finite_aux hpos hmean hB (scalingField μ B lam N) hN ⌊N*t⌋₊
    haveI : IsFiniteMeasure (ν N) := hf
    have hfin : IsFiniteMeasure (weightedMeasure (ν N) s₀) :=
      ⟨(weightedMeasure_le_of_nonneg hsup hs₀ Set.univ).trans_lt (measure_lt_top _ _)⟩
    letI := hfin
    refine ⟨hsup, ?_⟩
    rw [← ofReal_measureReal (measure_ne_top (weightedMeasure (ν N) s₀) Set.univ),
      ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hmassN.trans (le_max_right _ _))
  have hadm' (w : ℝ) (hw : s₀ ≤ w) : 0 < w + profileB v t :=
    hadm.trans_le (add_le_add_left hw _)
  have hp : ν' (Set.Iio 0) = 0 := by
    have hz : weightedMeasure ν' 0 = ν' := by
      unfold weightedMeasure
      simp only [zero_mul, neg_zero, Real.exp_zero, ENNReal.ofReal_one]
      exact withDensity_one
    rw [← hz]
    exact continuation_profile_support v t 0
  refine weakConvergence_atTop_of_weighted_mass_limits (ν := ν) (ν' := ν') hss hb hp
    (weightedMeasure_profileMeasure_finite (hadm' s hss.le)) ?_
  intro k
  have hw : s₀ ≤ s+k := hss.le.trans (le_add_of_nonneg_right (Nat.cast_nonneg k))
  have hEq : (weightedMeasure ν' (s+k)).real Set.univ = profileTransform v t (s+k) := by
    rw [measureReal_def, weightedMeasure_profileMeasure_mass (hadm' _ hw),
      ENNReal.toReal_ofReal]
    exact div_nonneg (by unfold profileA; positivity) (hadm' _ hw).le
  rw [hEq]
  exact hmass _ hw

theorem continuation_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ γ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hγ : γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃)) {lam : ℝ} (hlam : 0 < lam)
    {I : Set ℝ} (hI : IsCompact I) (hIpole : ∀ t ∈ I, IsPrePoleTime (γ * lam) t)
    {s : ℝ} (hs : 0 < s) (hadm : 0 < s + sInf (profileB (γ * lam) '' I))
    (hCompact : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ lam T : ℝ, 0 ≤ lam → 0 < T → lam * T ^ 2 ≤ η₀ →
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
              WeakConvergence (fun j => scalingMeasure μ B lam (Nseq (φ j)) t) atTop (E.ν t)))
    (hProfile : ∀ lam T C : ℝ, 0 ≤ lam → 0 < T → 0 < C →
      ∃ Tstar : ℝ, 0 < Tstar ∧ Tstar ≤ T ∧
      ∀ E : EntranceData T lam (lam * κ * Real.log B ^ 2 / ℓ₃) C,
        ∀ᵐ t, t ∈ Set.Ioo 0 Tstar → E.ν t = profileMeasure (γ * lam) t) :
    TendstoUniformlyOn (fun N t => scaledTransform μ B lam N t s)
        (fun t => profileTransform (γ * lam) t s) atTop I ∧
      ∀ t ∈ I, WeakConvergence (fun N => weightedMeasure (scalingMeasure μ B lam N t) s) atTop
        (weightedMeasure (profileMeasure (γ * lam) t) s) := by
  classical
  by_cases hne : I.Nonempty
  · let v := γ * lam
    obtain ⟨s₀,hs₀,hss₀⟩ := exists_continuation_base_weight hI hne hIpole hs hadm
    have hadm₀ (t : ℝ) (ht : t ∈ I) : 0 < s₀ + profileB v t :=
      hss₀ t (hIpole t ht).1 (le_csSup hI.bddAbove ht)
    obtain ⟨Tstar,hTstar,hent⟩ := continuation_entrance_subsequence hpos hmean hB hlam hCompact hProfile
    have hlim (w : ℝ) (hw : s₀ ≤ w) :
        TendstoUniformlyOn (fun N t => scaledTransform μ B lam N t w)
          (fun t => profileTransform v t w) atTop I :=
      continuation_uniform_of_entrance_subsequences hpos hmean hB hTstar (hs₀.1.le.trans hw)
        (fun ns hns => by
          obtain ⟨φ,hm,hae⟩ := hent ns hns
          exact ⟨φ,hm,hae.mono fun t ht hmem z hz hza => (ht hmem z hz hza).2⟩)
        hI hne hIpole (fun t ht => (hadm₀ t ht).trans_le (add_le_add_left hw _))
    exact ⟨hlim s hs₀.2.le, fun t ht => continuation_weak_of_transform_limits hpos hmean hB
      (hIpole t ht).1 hs₀.1.le hs₀.2 (hadm₀ t ht) (fun w hw => (hlim w hw).tendsto_at ht)⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    subst I
    exact ⟨tendstoUniformlyOn_empty, fun _ ht => False.elim ht⟩

end DiamondPinning
