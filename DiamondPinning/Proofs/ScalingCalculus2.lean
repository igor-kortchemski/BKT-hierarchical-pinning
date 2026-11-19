module

public import DiamondPinning.Proofs.ScalingCalculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
Uniform estimates for the derivative of the Mellin defect and the resulting
proof of `cont:defectdifference`, together with the algebraic one-step
estimates for the transform recurrence.  This covers `source/scaling.tex`,
lines 138--167 and 170--192.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Set

private noncomputable def defectQDeriv (B q r : ℝ) : ℝ :=
  Real.log B * B ^ q - Real.log (r + (B - 1)) * (r + (B - 1)) ^ q +
    Real.log r * r ^ q

private noncomputable def defectQDeriv_r (B q r : ℝ) : ℝ :=
  r ^ (q - 1) * (1 + q * Real.log r) -
    (r + (B - 1)) ^ (q - 1) * (1 + q * Real.log (r + (B - 1)))

private noncomputable def unitSlope (r : ℝ) : ℝ := (r - 1) / (r + 1)

private theorem hasDerivAt_defectKernel_q {B q r : ℝ} (hB : 2 < B) (hr : 0 < r) :
    HasDerivAt (fun q => defectKernel B q r) (defectQDeriv B q r) q := by
  have hBr : 0 < B := by linarith
  have hrc : 0 < r + (B - 1) := by linarith
  have h1 := (Real.hasStrictDerivAt_const_rpow hBr q).hasDerivAt
  have h2 := (Real.hasStrictDerivAt_const_rpow hrc q).hasDerivAt
  have h3 := (Real.hasStrictDerivAt_const_rpow hr q).hasDerivAt
  convert ((h1.sub (hasDerivAt_const q 1)).sub h2).add h3 using 1
  · funext q
    simp [defectKernel]
  · unfold defectQDeriv
    ring

private theorem hasDerivAt_defectQDeriv_r {B q r : ℝ} (hB : 2 < B) (hr : 0 < r) :
    HasDerivAt (defectQDeriv B q) (defectQDeriv_r B q r) r := by
  have hrc : 0 < r + (B - 1) := by linarith
  have hp (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun x => Real.log x * x ^ q)
        (x ^ (q - 1) * (1 + q * Real.log x)) x := by
    have h := (Real.hasDerivAt_log hx.ne').mul
      (Real.hasDerivAt_rpow_const (p := q) (Or.inl hx.ne'))
    convert h using 1
    rw [Real.rpow_sub_one hx.ne']
    field_simp
  have h1 := (hp (r + (B - 1)) hrc).comp r ((hasDerivAt_id r).add_const (B - 1))
  have h2 := hp r hr
  convert ((hasDerivAt_const r (Real.log B * B ^ q)).sub h1).add h2 using 1
  · funext x
    simp [defectQDeriv, Function.comp_def]
  · simp only [zero_sub, mul_one]
    unfold defectQDeriv_r
    ring

private theorem continuousOn_defectQDeriv_r {B : ℝ} (hB : 2 < B) {b : ℝ} (hb : 0 < b) :
    ContinuousOn (fun p : ℝ × ℝ => defectQDeriv_r B p.1 p.2)
      (Set.univ ×ˢ Set.Ici b) := by
  intro p hp
  have hr : 0 < p.2 := hb.trans_le hp.2
  have hrc : 0 < p.2 + (B - 1) := by linarith
  apply ContinuousAt.continuousWithinAt
  have hadd : ContinuousAt (fun p : ℝ × ℝ => p.2 + (B - 1)) p :=
    continuousAt_snd.add continuousAt_const
  have hrpow : ContinuousAt (fun p : ℝ × ℝ => p.2 ^ (p.1 - 1)) p :=
    continuousAt_snd.rpow (continuousAt_fst.sub continuousAt_const) (Or.inl hr.ne')
  have hrcpow : ContinuousAt (fun p : ℝ × ℝ => (p.2 + (B - 1)) ^ (p.1 - 1)) p :=
    (continuousAt_snd.add continuousAt_const).rpow
      (continuousAt_fst.sub continuousAt_const) (Or.inl hrc.ne')
  have hlogr : ContinuousAt (fun p : ℝ × ℝ => Real.log p.2) p :=
    continuousAt_snd.log hr.ne'
  have hlogrc : ContinuousAt (fun p : ℝ × ℝ => Real.log (p.2 + (B - 1))) p :=
    hadd.log hrc.ne'
  exact (hrpow.mul (continuousAt_const.add (continuousAt_fst.mul hlogr))).sub
    (hrcpow.mul (continuousAt_const.add (continuousAt_fst.mul hlogrc)))

private theorem compact_bound_defectQDeriv_r {B b q₁ q₂ : ℝ} (hB : 2 < B) (hb : 0 < b) :
    ∃ K : ℝ, ∀ q ∈ Set.Icc q₁ q₂, ∀ r ∈ Set.Icc b 2,
      |defectQDeriv_r B q r| ≤ K := by
  have hc : IsCompact (Set.Icc q₁ q₂ ×ˢ Set.Icc b 2) := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => |defectQDeriv_r B p.1 p.2|)
      (Set.Icc q₁ q₂ ×ˢ Set.Icc b 2) :=
    (continuousOn_defectQDeriv_r hB hb).norm.mono
      (Set.prod_mono (Set.subset_univ _) Set.Icc_subset_Ici_self)
  obtain ⟨K, hK⟩ := hc.bddAbove_image hcont
  refine ⟨K, fun q hq r hr => ?_⟩
  exact hK ⟨(q, r), ⟨hq, hr⟩, rfl⟩

private theorem log_rpow_deriv_bound {q q₁ q₂ x : ℝ} (hq₁ : 0 < q₁) (hq₂ : q₂ < 1)
    (hq : q ∈ Set.Icc q₁ q₂) (hx : 2 ≤ x) :
    |x ^ (q - 1) * (1 + q * Real.log x)| ≤
      2 ^ (q₂ - 1) + q₂ * (2 ^ (q₂ - 1 + (1 - q₂) / 2) / ((1 - q₂) / 2)) := by
  let ε := (1 - q₂) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hq0 : 0 < q := hq₁.trans_le hq.1
  have hq20 : 0 < q₂ := hq0.trans_le hq.2
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hpow0 : 0 < x ^ (q - 1) := Real.rpow_pos_of_pos hx0 _
  have hpow : x ^ (q - 1) ≤ 2 ^ (q₂ - 1) := by
    calc
      x ^ (q - 1) ≤ 2 ^ (q - 1) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by linarith [hq.2])
      _ ≤ 2 ^ (q₂ - 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (sub_le_sub_right hq.2 1)
  have hexp : q - 1 + ε ≤ q₂ - 1 + ε := by linarith [hq.2]
  have hexpneg : q₂ - 1 + ε < 0 := by dsimp [ε]; linarith
  have hpow2 : x ^ (q - 1 + ε) ≤ 2 ^ (q₂ - 1 + ε) := by
    calc
      x ^ (q - 1 + ε) ≤ x ^ (q₂ - 1 + ε) :=
        Real.rpow_le_rpow_of_exponent_le hx1 hexp
      _ ≤ 2 ^ (q₂ - 1 + ε) := Real.rpow_le_rpow_of_nonpos (by norm_num) hx hexpneg.le
  have hlogpow : x ^ (q - 1) * (q * Real.log x) ≤ q₂ * (2 ^ (q₂ - 1 + ε) / ε) := by
    have hl := Real.log_le_rpow_div hx0.le hε
    calc
      x ^ (q - 1) * (q * Real.log x) ≤ x ^ (q - 1) * (q * (x ^ ε / ε)) := by
        gcongr
      _ = q * (x ^ (q - 1 + ε) / ε) := by
        rw [Real.rpow_add hx0]
        field_simp
      _ ≤ q₂ * (2 ^ (q₂ - 1 + ε) / ε) := by
        exact mul_le_mul hq.2 (div_le_div_of_nonneg_right hpow2 hε.le)
          (div_nonneg (Real.rpow_nonneg hx0.le _) hε.le) hq20.le
  rw [abs_of_nonneg (by positivity)]
  dsimp [ε] at hpow2 hlogpow ⊢
  nlinarith

private theorem defectQDeriv_bound_large {B q q₁ q₂ r : ℝ} (hB : 2 < B)
    (hq₁ : 0 < q₁) (hq₂ : q₂ < 1) (hq : q ∈ Set.Icc q₁ q₂) (hr : 2 ≤ r) :
    |defectQDeriv B q r| ≤ Real.log B * B + (B - 1) *
      (2 ^ (q₂ - 1) + q₂ * (2 ^ (q₂ - 1 + (1 - q₂) / 2) / ((1 - q₂) / 2))) := by
  let K := 2 ^ (q₂ - 1) + q₂ * (2 ^ (q₂ - 1 + (1 - q₂) / 2) / ((1 - q₂) / 2))
  have hB0 : 0 < B := by linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hc : 0 < B - 1 := by linarith
  have hrc : 2 ≤ r + (B - 1) := by linarith
  have hdiff : |Real.log (r + (B - 1)) * (r + (B - 1)) ^ q - Real.log r * r ^ q| ≤
      K * (B - 1) := by
    have hd : ∀ x ∈ Set.Icc r (r + (B - 1)),
        DifferentiableAt ℝ (fun x => Real.log x * x ^ q) x := by
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have h := (Real.hasDerivAt_log hx0.ne').mul
        (Real.hasDerivAt_rpow_const (p := q) (Or.inl hx0.ne'))
      exact h.differentiableAt
    have hb : ∀ x ∈ Set.Icc r (r + (B - 1)),
        ‖deriv (fun x => Real.log x * x ^ q) x‖ ≤ K := by
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hx2 : 2 ≤ x := hr.trans hx.1
      have h := (Real.hasDerivAt_log hx0.ne').mul
        (Real.hasDerivAt_rpow_const (p := q) (Or.inl hx0.ne'))
      change HasDerivAt (fun x => Real.log x * x ^ q) _ x at h
      rw [h.deriv]
      have heq : x⁻¹ * x ^ q + Real.log x * (q * x ^ (q - 1)) =
          x ^ (q - 1) * (1 + q * Real.log x) := by
        rw [Real.rpow_sub_one hx0.ne']
        field_simp
      rw [heq, Real.norm_eq_abs]
      exact log_rpow_deriv_bound hq₁ hq₂ hq hx2
    have hm := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc r (r + (B - 1)))
      (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
    simpa [Real.norm_eq_abs, abs_of_pos hc, mul_comm] using hm
  have hterm : |Real.log B * B ^ q| ≤ Real.log B * B := by
    rw [abs_of_nonneg (mul_nonneg hlogB (Real.rpow_nonneg hB0.le _))]
    have hp : B ^ q ≤ B := by
      calc
        B ^ q ≤ B ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (hq.2.trans hq₂.le)
        _ = B := Real.rpow_one B
    exact mul_le_mul_of_nonneg_left hp hlogB
  unfold defectQDeriv
  calc
    |Real.log B * B ^ q - Real.log (r + (B - 1)) * (r + (B - 1)) ^ q + Real.log r * r ^ q| =
        |Real.log B * B ^ q -
          (Real.log (r + (B - 1)) * (r + (B - 1)) ^ q - Real.log r * r ^ q)| := by
      congr 1
      ring
    _ ≤ |Real.log B * B ^ q| +
          |Real.log (r + (B - 1)) * (r + (B - 1)) ^ q - Real.log r * r ^ q| := abs_sub _ _
    _ ≤ Real.log B * B + K * (B - 1) := add_le_add hterm hdiff
    _ = Real.log B * B + (B - 1) * K := by ring

private theorem unitSlope_one : unitSlope 1 = 0 := by simp [unitSlope]

private theorem unitSlope_abs_le_one {b r : ℝ} (hb : 0 < b) (hr : b ≤ r) :
    |unitSlope r| ≤ 1 := by
  have hr0 : 0 < r := hb.trans_le hr
  have hd : 0 < r + 1 := by linarith
  rw [unitSlope, abs_div, abs_of_pos hd, div_le_one hd, abs_le]
  constructor <;> linarith

private theorem defectQDeriv_uniform_comparison {B b q₁ q₂ : ℝ} (hB : 2 < B)
    (hb : 0 < b) (hb1 : b < 1) (hq₁ : 0 < q₁) (hq₂ : q₂ < 1) :
    ∃ K : ℝ, ∀ q ∈ Set.Icc q₁ q₂, ∀ r : ℝ, b ≤ r →
      |defectQDeriv B q r| ≤ K * |unitSlope r| := by
  obtain ⟨L, hL⟩ := compact_bound_defectQDeriv_r hB hb (q₁ := q₁) (q₂ := q₂)
  let G := Real.log B * B + (B - 1) *
    (2 ^ (q₂ - 1) + q₂ * (2 ^ (q₂ - 1 + (1 - q₂) / 2) / ((1 - q₂) / 2)))
  have hlocal : ∀ q ∈ Set.Icc q₁ q₂, ∀ r ∈ Set.Icc b 2,
      |defectQDeriv B q r| ≤ 3 * L * |unitSlope r| := by
    intro q hq r hr
    have hr0 : 0 < r := hb.trans_le hr.1
    have hL0 : 0 ≤ L := (abs_nonneg (defectQDeriv_r B q r)).trans (hL q hq r hr)
    have hd : ∀ x ∈ Set.Icc b 2, DifferentiableAt ℝ (defectQDeriv B q) x := by
      intro x hx
      exact (hasDerivAt_defectQDeriv_r hB (hb.trans_le hx.1)).differentiableAt
    have hbnd : ∀ x ∈ Set.Icc b 2, ‖deriv (defectQDeriv B q) x‖ ≤ L := by
      intro x hx
      rw [(hasDerivAt_defectQDeriv_r hB (hb.trans_le hx.1)).deriv, Real.norm_eq_abs]
      exact hL q hq x hx
    have hm := Convex.norm_image_sub_le_of_norm_deriv_le hd hbnd (convex_Icc b 2)
      ⟨hb1.le, by norm_num⟩ hr
    have hone : defectQDeriv B q 1 = 0 := by simp [defectQDeriv]
    rw [hone, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hm
    have hm' : |defectQDeriv B q r| ≤ L * |r - 1| := hm
    have hs : |r - 1| ≤ 3 * |unitSlope r| := by
      have hd : 0 < r + 1 := by linarith
      rw [unitSlope, abs_div, abs_of_pos hd]
      rw [show 3 * (|r - 1| / (r + 1)) = 3 * |r - 1| / (r + 1) by ring,
        le_div_iff₀ hd]
      have hm := mul_le_mul_of_nonneg_left
        (show r + 1 ≤ 3 by linarith [hr.2]) (abs_nonneg (r - 1))
      nlinarith
    calc
      |defectQDeriv B q r| ≤ L * |r - 1| := hm'
      _ ≤ L * (3 * |unitSlope r|) := mul_le_mul_of_nonneg_left hs hL0
      _ = 3 * L * |unitSlope r| := by ring
  refine ⟨3 * (L + G + 1), fun q hq r hr => ?_⟩
  have hq20 : 0 < q₂ := (hq₁.trans_le hq.1).trans_le hq.2
  have hL0 : 0 ≤ L := (abs_nonneg (defectQDeriv_r B q 1)).trans
    (hL q hq 1 ⟨hb1.le, by norm_num⟩)
  have hG0 : 0 ≤ G := by
    have hlog : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
    dsimp [G]
    have hε : 0 < (1 - q₂) / 2 := by linarith
    exact add_nonneg (mul_nonneg hlog (by linarith))
      (mul_nonneg (show 0 ≤ B - 1 by linarith)
        (add_nonneg (Real.rpow_nonneg (by norm_num) _)
          (mul_nonneg hq20.le (div_nonneg (Real.rpow_nonneg (by norm_num) _) hε.le))))
  by_cases hr2 : r ≤ 2
  · have h := hlocal q hq r ⟨hr, hr2⟩
    have hK : 3 * L ≤ 3 * (L + G + 1) := by nlinarith
    exact h.trans (mul_le_mul_of_nonneg_right hK (abs_nonneg _))
  · have hr2' : 2 ≤ r := le_of_not_ge hr2
    have h := defectQDeriv_bound_large hB hq₁ hq₂ hq hr2'
    change |defectQDeriv B q r| ≤ G at h
    have hs : 1 ≤ 3 * |unitSlope r| := by
      have hd : 0 < r + 1 := by linarith
      have hm : 0 ≤ unitSlope r := by
        dsimp [unitSlope]
        exact div_nonneg (by linarith) hd.le
      rw [abs_of_nonneg hm]
      dsimp [unitSlope]
      rw [show 3 * ((r - 1) / (r + 1)) = 3 * (r - 1) / (r + 1) by ring,
        le_div_iff₀ hd]
      nlinarith
    have hGA : G ≤ L + G + 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ L + G + 1 by positivity)
    calc
      |defectQDeriv B q r| ≤ G := h
      _ ≤ L + G + 1 := hGA
      _ = (L + G + 1) * 1 := by ring
      _ ≤ (L + G + 1) * (3 * |unitSlope r|) := hmul
      _ = 3 * (L + G + 1) * |unitSlope r| := by ring

private theorem defectKernel_sub_pointwise {B b q₁ q₂ : ℝ} (hB : 2 < B)
    (hb : 0 < b) (hb1 : b < 1) (hq₁ : 0 < q₁) (hq₂ : q₂ < 1) :
    ∃ K : ℝ, ∀ q ∈ Set.Icc q₁ q₂, ∀ q₀ ∈ Set.Icc q₁ q₂,
      ∀ r : ℝ, b ≤ r →
      |defectKernel B q r - defectKernel B q₀ r| ≤ K * |q - q₀| * |unitSlope r| := by
  obtain ⟨K, hK⟩ := defectQDeriv_uniform_comparison hB hb hb1 hq₁ hq₂
  refine ⟨K, fun q hq q₀ hq₀ r hr => ?_⟩
  have hr0 : 0 < r := hb.trans_le hr
  have hd : ∀ u ∈ Set.Icc q₁ q₂,
      DifferentiableAt ℝ (fun q => defectKernel B q r) u := by
    intro u hu
    exact (hasDerivAt_defectKernel_q hB hr0).differentiableAt
  have hbnd : ∀ u ∈ Set.Icc q₁ q₂,
      ‖deriv (fun q => defectKernel B q r) u‖ ≤ K * |unitSlope r| := by
    intro u hu
    rw [(hasDerivAt_defectKernel_q hB hr0).deriv, Real.norm_eq_abs]
    exact hK u hu r hr
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le hd hbnd (convex_Icc q₁ q₂) hq₀ hq
  simp only [Real.norm_eq_abs] at hm
  calc
    |defectKernel B q r - defectKernel B q₀ r| ≤ K * |unitSlope r| * |q - q₀| := hm
    _ = K * |q - q₀| * |unitSlope r| := by ring

private theorem isProbabilityMeasure_productLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (B h : ℝ) (n : ℕ) : IsProbabilityMeasure (productLaw μ B h n) := by
  let : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  rw [productLaw]
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

private theorem ae_floor_productLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ r ∂(productLaw μ B h n), floorSeq B 1 ^ 2 ≤ r := by
  let : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  rw [productLaw, ae_map_iff (by fun_prop) measurableSet_Ici]
  rw [Measure.ae_prod_iff_ae_ae (by measurability)]
  have hfloor := ae_floorSeq_le_lawR hpos hB h n
  filter_upwards [hfloor] with x hx
  filter_upwards [hfloor] with y hy
  have hb : 0 ≤ floorSeq B 1 := floorSeq_nonneg hB 1
  have hb1 : floorSeq B 1 ≤ floorSeq B n := floorSeq_one_le hB hn
  calc
    floorSeq B 1 ^ 2 = floorSeq B 1 * floorSeq B 1 := pow_two _
    _ ≤ x * y := mul_le_mul (hb1.trans hx) (hb1.trans hy) hb (hb1.trans hx |>.trans' hb)

private theorem ae_floor_sq_productLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    ∀ᵐ r ∂(productLaw μ B h n), floorSeq B n ^ 2 ≤ r := by
  let : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  rw [productLaw, ae_map_iff (by fun_prop) measurableSet_Ici]
  rw [Measure.ae_prod_iff_ae_ae (by measurability)]
  have hfloor := ae_floorSeq_le_lawR hpos hB h n
  filter_upwards [hfloor] with x hx
  filter_upwards [hfloor] with y hy
  have hb : 0 ≤ floorSeq B n := floorSeq_nonneg hB n
  exact (pow_two _).trans_le (mul_le_mul hx hy hb (hb.trans hx))

private theorem integrable_defectKernel {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {B b : ℝ} (hB : 2 < B) (hb : 0 < b)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (h : ℝ) (n : ℕ)
    (hfloor : ∀ᵐ r ∂(productLaw μ B h n), b ≤ r) :
    Integrable (defectKernel B q) (productLaw μ B h n) := by
  let : IsProbabilityMeasure (productLaw μ B h n) := isProbabilityMeasure_productLaw B h n
  let K := |B ^ q - 1| + (B - 1) * (q * b ^ (q - 1))
  have hmeas : Measurable (defectKernel B q) := by
    unfold defectKernel
    fun_prop
  apply (integrable_const K).mono' hmeas.aestronglyMeasurable
  filter_upwards [hfloor] with r hr
  have hr0 : 0 < r := hb.trans_le hr
  have hrc : 0 < r + (B - 1) := by linarith
  have hc : 0 < B - 1 := by linarith
  have hdiff : |(r + (B - 1)) ^ q - r ^ q| ≤ (B - 1) * (q * b ^ (q - 1)) := by
    have hd : ∀ x ∈ Set.Icc r (r + (B - 1)), DifferentiableAt ℝ (fun x => x ^ q) x := by
      intro x hx
      exact (Real.hasDerivAt_rpow_const (p := q)
        (Or.inl (show x ≠ 0 by linarith [hx.1]))).differentiableAt
    have hbnd : ∀ x ∈ Set.Icc r (r + (B - 1)),
        ‖deriv (fun x => x ^ q) x‖ ≤ q * b ^ (q - 1) := by
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      rw [Real.deriv_rpow_const, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hq0.le (Real.rpow_nonneg hx0.le _))]
      have hp : x ^ (q - 1) ≤ b ^ (q - 1) :=
        Real.rpow_le_rpow_of_nonpos hb (hr.trans hx.1) (by linarith)
      exact mul_le_mul_of_nonneg_left hp hq0.le
    have hm := Convex.norm_image_sub_le_of_norm_deriv_le hd hbnd (convex_Icc r (r + (B - 1)))
      (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
    simpa [Real.norm_eq_abs, abs_of_pos hc, mul_comm] using hm
  change ‖defectKernel B q r‖ ≤ K
  rw [Real.norm_eq_abs]
  calc
    |defectKernel B q r| = |(B ^ q - 1) - ((r + (B - 1)) ^ q - r ^ q)| := by
      congr 1
      simp [defectKernel]
      ring
    _ ≤ |B ^ q - 1| + |(r + (B - 1)) ^ q - r ^ q| := abs_sub _ _
    _ ≤ K := by dsimp [K]; exact add_le_add (le_refl _) hdiff

private theorem integrable_unitSlope {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Integrable unitSlope (productLaw μ B h n) := by
  let : IsProbabilityMeasure (productLaw μ B h n) := isProbabilityMeasure_productLaw B h n
  have hm : Measurable unitSlope := by unfold unitSlope; fun_prop
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_floor_productLaw hpos hB h hn] with r hr
  rw [Real.norm_eq_abs]
  exact unitSlope_abs_le_one (sq_pos_of_pos (floorSeq_one_pos hB)) hr

private theorem unitSlope_abs_floor {B r ρ : ℝ} (hB : 2 < B) (hfloor : 0 ≤ ρ)
    (hr : floorSeq B 1 ^ 2 ≤ r) (hρ : 1 - r ≤ 2 * ρ) :
    |unitSlope r| ≤ unitSlope r + 4 * ρ := by
  have hb : 0 < floorSeq B 1 ^ 2 := sq_pos_of_pos (floorSeq_one_pos hB)
  have hr0 : 0 < r := hb.trans_le hr
  have hd : 0 < r + 1 := by linarith
  by_cases hr1 : 1 ≤ r
  · have hm : 0 ≤ unitSlope r := by dsimp [unitSlope]; positivity
    rw [abs_of_nonneg hm]
    linarith
  · have hr1' : r < 1 := lt_of_not_ge hr1
    have hm : unitSlope r ≤ 0 := by
      dsimp [unitSlope]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    rw [abs_of_nonpos hm]
    have hdiv : 2 * (1 - r) / (r + 1) ≤ 2 * (1 - r) := by
      apply (div_le_iff₀ hd).2
      nlinarith
    dsimp [unitSlope]
    calc
      -((r - 1) / (r + 1)) = (r - 1) / (r + 1) + 2 * (1 - r) / (r + 1) := by ring
      _ ≤ (r - 1) / (r + 1) + 2 * (1 - r) := add_le_add (le_refl _) hdiv
      _ ≤ (r - 1) / (r + 1) + 4 * ρ := by linarith

private theorem rescale_defect_estimate {x d ρ A E C : ℝ} (hρ : 0 ≤ ρ)
    (hd : 0 ≤ d + C * ρ) (hAC : A ≤ C) (hE : E ≤ C * A)
    (hx : x ≤ A * d + E * ρ) : x ≤ C * (d + C * ρ) := by
  have h1 : 0 ≤ (C - A) * (d + C * ρ) := mul_nonneg (sub_nonneg.mpr hAC) hd
  have h2 : 0 ≤ (C * A - E) * ρ := mul_nonneg (sub_nonneg.mpr hE) hρ
  nlinarith

/-- The quadratic Taylor bound `|exp z - 1 - z| ≤ |z|²` for real `z` with
`|z| ≤ 1`. -/
theorem abs_exp_sub_one_sub_id_le {z : ℝ} (hz : |z| ≤ 1) :
    |Real.exp z - 1 - z| ≤ |z| ^ 2 := by
  have h := Complex.norm_exp_sub_one_sub_id_le (x := (z : ℂ)) (by simpa using hz)
  have heq : Complex.exp (z : ℂ) - 1 - (z : ℂ) = ((Real.exp z - 1 - z : ℝ) : ℂ) := by
    simp [← Complex.ofReal_exp]
  rw [heq] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, pow_abs] using h

/-- Rewrites one step of the transform recurrence as its `psiS` increment plus
the exponential and defect error terms. -/
theorem recurrence_error_identity {E N s L L' D : ℝ} (hN : N ≠ 0)
    (hrec : L' = E * L + E / (2 * N) * L ^ 2 - N / 2 * E * D) :
    L' - L - psiS s L / N =
      (E - 1) * L - s * L / N + (E - 1) / (2 * N) * L ^ 2 - N / 2 * E * D := by
  rw [hrec]
  unfold psiS
  field_simp
  ring

/-- Solves the transform recurrence for the Mellin defect in terms of the
one-step transform increment. -/
theorem recurrence_defect_identity {E N L L' D : ℝ} (hN : N ≠ 0) (hE : E ≠ 0)
    (hrec : L' = E * L + E / (2 * N) * L ^ 2 - N / 2 * E * D) :
    D = 2 * (E - 1) / (N * E) * L + L ^ 2 / N ^ 2 - 2 / (N * E) * (L' - L) := by
  rw [hrec]
  field_simp
  ring

/-- Bounds the change of a real sequence between two indices by the sum of the
absolute one-step changes. -/
theorem abs_sub_le_sum_abs_steps (x : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    |x n - x m| ≤ ∑ k ∈ Finset.Ico m n, |x (k + 1) - x k| := by
  rw [← Finset.sum_Ico_sub x hmn]
  exact Finset.abs_sum_le_sum_abs _ _

/-- Bounds absolute variation along a monotone sampling of indices by the
variation over all intervening unit steps. -/
theorem monotone_sum_steps_le (x : ℕ → ℝ) (v : ℕ → ℕ) (hv : Monotone v) (p : ℕ) :
    ∑ i ∈ Finset.range p, |x (v (i + 1)) - x (v i)| ≤
      ∑ k ∈ Finset.Ico (v 0) (v p), |x (k + 1) - x k| := by
  induction p with
  | zero => simp
  | succ p ih =>
      rw [Finset.sum_range_succ]
      have hi := abs_sub_le_sum_abs_steps x (hv (Nat.le_add_right p 1))
      calc
        (∑ i ∈ Finset.range p, |x (v (i + 1)) - x (v i)|) + |x (v (p + 1)) - x (v p)| ≤
            (∑ k ∈ Finset.Ico (v 0) (v p), |x (k + 1) - x k|) +
              ∑ k ∈ Finset.Ico (v p) (v (p + 1)), |x (k + 1) - x k| := add_le_add ih hi
        _ = ∑ k ∈ Finset.Ico (v 0) (v (p + 1)), |x (k + 1) - x k| := by
          rw [Finset.sum_Ico_consecutive _ (hv (Nat.zero_le p)) (hv (Nat.le_add_right p 1))]
        _ = ∑ k ∈ Finset.Ico (v 0) (v (p + 1)), |x (k + 1) - x k| := rfl

/-- The uniform one-sided upper bound for a transform increment obtained from
`cont:onesided`, with quadratic scale error and geometric defect error. -/
theorem transform_step_upper {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {N s₀ M C : ℝ} (hN : 1 ≤ N) (hs₀ : 0 ≤ s₀) (hsN : s₀ ≤ N)
    (hM : 0 ≤ M) (hC : 0 ≤ C) {n : ℕ} (hn : 1 ≤ n)
    (hL : |transformAt μ B h N n s₀| ≤ M)
    (hD : -(C * (2 / B) ^ n) ≤ defectMean μ B h n (weightExponent B N s₀)) :
    transformAt μ B h N (n + 1) s₀ - transformAt μ B h N n s₀ ≤
      psiS s₀ (transformAt μ B h N n s₀) / N +
        (s₀ ^ 2 * M + (s₀ + 1) * M ^ 2) / N ^ 2 + 2 * C * N * (2 / B) ^ n := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  let E := Real.exp (s₀ / N)
  let L := transformAt μ B h N n s₀
  let D := defectMean μ B h n (weightExponent B N s₀)
  let ρ := (2 / B) ^ n
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hx0 : 0 ≤ s₀ / N := div_nonneg hs₀ hN0.le
  have hx1 : s₀ / N ≤ 1 := (div_le_one hN0).2 hsN
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp hx0
  have hexp : |E - 1 - s₀ / N| ≤ |s₀ / N| ^ 2 :=
    abs_exp_sub_one_sub_id_le (by rw [abs_of_nonneg hx0]; exact hx1)
  have hE3 : E ≤ 3 := by
    have hh := le_abs_self (E - 1 - s₀ / N)
    rw [abs_of_nonneg hx0] at hexp
    have hxx : (s₀ / N) ^ 2 ≤ s₀ / N := by nlinarith
    nlinarith [hexp]
  have hrec : transformAt μ B h N (n + 1) s₀ =
      E * L + E / (2 * N) * L ^ 2 - N / 2 * E * D :=
    transform_recurrence_aux hpos hmean hB h hN0 hn hs₀
  have hid := recurrence_error_identity (s := s₀) hN0.ne' hrec
  have hL2 : L ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg L) hM).2 hL
  have ht1 : (E - 1) * L - s₀ * L / N ≤ s₀ ^ 2 * M / N ^ 2 := by
    have heq : (E - 1) * L - s₀ * L / N = (E - 1 - s₀ / N) * L := by ring
    rw [heq]
    calc
      (E - 1 - s₀ / N) * L ≤ |E - 1 - s₀ / N| * |L| := by
        exact (le_abs_self ((E - 1 - s₀ / N) * L)).trans (by rw [abs_mul])
      _ ≤ |s₀ / N| ^ 2 * M := mul_le_mul hexp hL (abs_nonneg _) (sq_nonneg _)
      _ = s₀ ^ 2 * M / N ^ 2 := by
        rw [abs_of_nonneg hx0, div_pow]
        field_simp
  have ht2 : (E - 1) / (2 * N) * L ^ 2 ≤ (s₀ + 1) * M ^ 2 / N ^ 2 := by
    have hEsmall : E - 1 ≤ 2 * (s₀ / N) := by
      have hh := le_abs_self (E - 1 - s₀ / N)
      rw [abs_of_nonneg hx0] at hexp
      nlinarith [sq_nonneg (s₀ / N - 1)]
    calc
      (E - 1) / (2 * N) * L ^ 2 ≤ (2 * (s₀ / N)) / (2 * N) * M ^ 2 := by gcongr
      _ = s₀ * M ^ 2 / N ^ 2 := by field_simp
      _ ≤ (s₀ + 1) * M ^ 2 / N ^ 2 := by gcongr; nlinarith
  have ht3 : -(N / 2 * E * D) ≤ 2 * C * N * ρ := by
    have hneg : -D ≤ C * ρ := by linarith
    have hmul := mul_le_mul_of_nonneg_left hneg (show 0 ≤ N / 2 * E by positivity)
    have hcN : N / 2 * E ≤ 2 * N := by nlinarith
    have hcl : N / 2 * E * (C * ρ) ≤ 2 * N * (C * ρ) :=
      mul_le_mul_of_nonneg_right hcN (mul_nonneg hC hρ)
    calc
      -(N / 2 * E * D) = N / 2 * E * (-D) := by ring
      _ ≤ N / 2 * E * (C * ρ) := hmul
      _ ≤ 2 * N * (C * ρ) := hcl
      _ = 2 * C * N * ρ := by ring
  have hid' : transformAt μ B h N (n + 1) s₀ - L =
      psiS s₀ L / N + ((E - 1) * L - s₀ * L / N +
        (E - 1) / (2 * N) * L ^ 2 - N / 2 * E * D) := by linarith
  calc
    transformAt μ B h N (n + 1) s₀ - transformAt μ B h N n s₀ =
        psiS s₀ L / N + ((E - 1) * L - s₀ * L / N +
          (E - 1) / (2 * N) * L ^ 2 - N / 2 * E * D) := hid'
    _ ≤ psiS s₀ L / N + (s₀ ^ 2 * M / N ^ 2 + (s₀ + 1) * M ^ 2 / N ^ 2 +
          2 * C * N * ρ) := add_le_add le_rfl (add_le_add (add_le_add ht1 ht2) ht3)
    _ = psiS s₀ (transformAt μ B h N n s₀) / N +
        (s₀ ^ 2 * M + (s₀ + 1) * M ^ 2) / N ^ 2 + 2 * C * N * (2 / B) ^ n := by
      dsimp [L, ρ]
      ring

/-- Controls the absolute Mellin defect by the transform increment, quadratic
scale errors, and the geometric lower-bound error. -/
theorem defect_step_upper {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {N s₀ M C : ℝ} (hN : 1 ≤ N) (hs₀ : 0 ≤ s₀) (hsN : s₀ ≤ N)
    (hM : 0 ≤ M) (hC : 0 ≤ C) {n : ℕ} (hn : 1 ≤ n)
    (hL : |transformAt μ B h N n s₀| ≤ M)
    (hD : -(C * (2 / B) ^ n) ≤ defectMean μ B h n (weightExponent B N s₀)) :
    |defectMean μ B h n (weightExponent B N s₀)| ≤
      (4 * s₀ * M + M ^ 2) / N ^ 2 -
        2 / (N * Real.exp (s₀ / N)) *
          (transformAt μ B h N (n + 1) s₀ - transformAt μ B h N n s₀) +
        2 * C * (2 / B) ^ n := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  let E := Real.exp (s₀ / N)
  let L := transformAt μ B h N n s₀
  let D := defectMean μ B h n (weightExponent B N s₀)
  let ρ := (2 / B) ^ n
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hx0 : 0 ≤ s₀ / N := div_nonneg hs₀ hN0.le
  have hx1 : s₀ / N ≤ 1 := (div_le_one hN0).2 hsN
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp hx0
  have hexp : |E - 1 - s₀ / N| ≤ |s₀ / N| ^ 2 :=
    abs_exp_sub_one_sub_id_le (by rw [abs_of_nonneg hx0]; exact hx1)
  have hEsmall : E - 1 ≤ 2 * (s₀ / N) := by
    have hh := le_abs_self (E - 1 - s₀ / N)
    rw [abs_of_nonneg hx0] at hexp
    nlinarith [sq_nonneg (s₀ / N - 1)]
  have hrec : transformAt μ B h N (n + 1) s₀ =
      E * L + E / (2 * N) * L ^ 2 - N / 2 * E * D :=
    transform_recurrence_aux hpos hmean hB h hN0 hn hs₀
  have hid := recurrence_defect_identity hN0.ne' hE0.ne' hrec
  have hL2 : L ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg L) hM).2 hL
  have hfirst : 2 * (E - 1) / (N * E) * L ≤ 4 * s₀ * M / N ^ 2 := by
    have hc : 0 ≤ 2 * (E - 1) / (N * E) := by positivity
    calc
      2 * (E - 1) / (N * E) * L ≤ |2 * (E - 1) / (N * E) * L| := le_abs_self _
      _ = (2 * (E - 1) / (N * E)) * |L| := by rw [abs_mul, abs_of_nonneg hc]
      _ ≤ (4 * (s₀ / N) / N) * M := by
        have hcoeff : 2 * (E - 1) / (N * E) ≤ 4 * (s₀ / N) / N := by
          apply (div_le_div_iff₀ (mul_pos hN0 hE0) hN0).2
          have hne : N ≤ N * E := by nlinarith
          have hxE : s₀ / N ≤ (s₀ / N) * E := by nlinarith
          nlinarith
        exact mul_le_mul hcoeff hL (abs_nonneg _) (by positivity)
      _ = 4 * s₀ * M / N ^ 2 := by field_simp
  have habsD : |D| ≤ D + 2 * C * ρ := by
    by_cases hD0 : 0 ≤ D
    · rw [abs_of_nonneg hD0]
      have : 0 ≤ C * ρ := mul_nonneg hC hρ
      linarith
    · rw [abs_of_neg (lt_of_not_ge hD0)]
      have : 0 ≤ C * ρ := mul_nonneg hC hρ
      linarith
  calc
    |D| ≤ D + 2 * C * ρ := habsD
    _ = 2 * (E - 1) / (N * E) * L + L ^ 2 / N ^ 2 -
        2 / (N * E) * (transformAt μ B h N (n + 1) s₀ - L) + 2 * C * ρ := by rw [hid]
    _ ≤ 4 * s₀ * M / N ^ 2 + M ^ 2 / N ^ 2 -
        2 / (N * E) * (transformAt μ B h N (n + 1) s₀ - L) + 2 * C * ρ := by
      gcongr
    _ = (4 * s₀ * M + M ^ 2) / N ^ 2 -
        2 / (N * Real.exp (s₀ / N)) *
          (transformAt μ B h N (n + 1) s₀ - transformAt μ B h N n s₀) +
        2 * C * (2 / B) ^ n := by
      dsimp [E, L, ρ]
      ring

/-- Controls the absolute transform increment by the transform bound and the
absolute Mellin defect. -/
theorem transform_step_abs {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {N s₀ M : ℝ} (hN : 1 ≤ N) (hs₀ : 0 ≤ s₀) (hsN : s₀ ≤ N)
    (hM : 0 ≤ M) {n : ℕ} (hn : 1 ≤ n) (hL : |transformAt μ B h N n s₀| ≤ M) :
    |transformAt μ B h N (n + 1) s₀ - transformAt μ B h N n s₀| ≤
      (2 * s₀ * M + 3 * M ^ 2 / 2) / N + N * Real.exp (s₀ / N) / 2 *
        |defectMean μ B h n (weightExponent B N s₀)| := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  let E := Real.exp (s₀ / N)
  let L := transformAt μ B h N n s₀
  let D := defectMean μ B h n (weightExponent B N s₀)
  have hx0 : 0 ≤ s₀ / N := div_nonneg hs₀ hN0.le
  have hx1 : s₀ / N ≤ 1 := (div_le_one hN0).2 hsN
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp hx0
  have hexp : |E - 1 - s₀ / N| ≤ |s₀ / N| ^ 2 :=
    abs_exp_sub_one_sub_id_le (by rw [abs_of_nonneg hx0]; exact hx1)
  have hEsmall : E - 1 ≤ 2 * (s₀ / N) := by
    have hh := le_abs_self (E - 1 - s₀ / N)
    rw [abs_of_nonneg hx0] at hexp
    nlinarith [sq_nonneg (s₀ / N - 1)]
  have hE3 : E ≤ 3 := by
    have hh := le_abs_self (E - 1 - s₀ / N)
    have hxx : (s₀ / N) ^ 2 ≤ s₀ / N := by nlinarith
    nlinarith [hexp]
  have hrec : transformAt μ B h N (n + 1) s₀ =
      E * L + E / (2 * N) * L ^ 2 - N / 2 * E * D :=
    transform_recurrence_aux hpos hmean hB h hN0 hn hs₀
  have hid : transformAt μ B h N (n + 1) s₀ - L =
      (E - 1) * L + E / (2 * N) * L ^ 2 - N / 2 * E * D := by rw [hrec]; ring
  have hL2 : L ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg L) hM).2 hL
  have h1 : |(E - 1) * L| ≤ 2 * s₀ * M / N := by
    calc
      |(E - 1) * L| = (E - 1) * |L| := by rw [abs_mul, abs_of_nonneg (by linarith)]
      _ ≤ (2 * (s₀ / N)) * M := mul_le_mul hEsmall hL (abs_nonneg _) (by positivity)
      _ = 2 * s₀ * M / N := by ring
  have h2 : |E / (2 * N) * L ^ 2| ≤ (3 * M ^ 2 / 2) / N := by
    rw [abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (sq_nonneg _)]
    calc
      E / (2 * N) * L ^ 2 ≤ 3 / (2 * N) * M ^ 2 := by gcongr
      _ = (3 * M ^ 2 / 2) / N := by ring
  have h3 : |N / 2 * E * D| = N * E / 2 * |D| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_pos hE0]
    ring
  rw [hid]
  calc
    |(E - 1) * L + E / (2 * N) * L ^ 2 - N / 2 * E * D| ≤
        |(E - 1) * L| + |E / (2 * N) * L ^ 2| + |N / 2 * E * D| := by
      exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * s₀ * M / N + (3 * M ^ 2 / 2) / N + N * E / 2 * |D| := by
      rw [← h3]
      exact add_le_add (add_le_add h1 h2) le_rfl
    _ = (2 * s₀ * M + 3 * M ^ 2 / 2) / N + N * E / 2 * |D| := by ring
    _ = (2 * s₀ * M + 3 * M ^ 2 / 2) / N + N * Real.exp (s₀ / N) / 2 *
        |defectMean μ B h n (weightExponent B N s₀)| := rfl

-- The two compact derivative comparisons and the integral comparison share
-- one elaboration budget.
set_option maxHeartbeats 400000 in
/-- The difference of Mellin defects at two exponents is Lipschitz in their separation, with
constant governed by the reference defect and a geometric floor error.
This proves `DiamondPinning.defectMean_sub` (in
`DiamondPinning.Statements.Scaling`). -/
theorem defectMean_sub_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    ∀ q₁ q₂ : ℝ, 0 < q₁ → q₂ < 1 → ∃ C : ℝ, ∀ (h : ℝ) (n : ℕ), 1 ≤ n →
      ∀ q ∈ Set.Icc q₁ q₂, ∀ q₀ ∈ Set.Icc q₁ q₂,
        |defectMean μ B h n q - defectMean μ B h n q₀| ≤
          C * |q - q₀| * (defectMean μ B h n q₀ + C * (2 / B) ^ n) := by
  intro q₁ q₂ hq₁ hq₂
  let b := floorSeq B 1 ^ 2
  have hb : 0 < b := sq_pos_of_pos (floorSeq_one_pos hB)
  have hb1 : b < 1 := by
    change floorSeq B 1 ^ 2 < 1
    nlinarith [floorSeq_lt_one hB 1, floorSeq_one_pos hB]
  obtain ⟨K, hK⟩ := defectKernel_sub_pointwise hB hb hb1 hq₁ hq₂
  let K₀ := max K 0
  have hK₀ : 0 ≤ K₀ := le_max_right _ _
  obtain ⟨C₀, hC₀⟩ := kernel_comparison_aux hpos hmean hB q₁ q₂ hq₁ hq₂
  have hm : Measurable unitSlope := by unfold unitSlope; fun_prop
  have hd : ∀ᶠ r in 𝓝 (1 : ℝ), DifferentiableAt ℝ unitSlope r := by
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 1 by norm_num)] with r hr
    change -1 < r at hr
    unfold unitSlope
    exact (differentiableAt_id.sub_const 1).div (differentiableAt_id.add_const 1) (by linarith)
  obtain ⟨CF, hCF⟩ := hC₀ unitSlope hm
    ⟨1, fun r hr => unitSlope_abs_le_one hb hr⟩ hd
  obtain ⟨CL, hCL⟩ := defectMean_lower_aux hpos hmean hB q₁ q₂ hq₁ hq₂
  let A := max |CF| 1
  let C₁ := |C₀| + 2 * |CL| + 1
  let E := A * C₁ + 4
  let C' := A + E + |CL| + 1
  let C := K₀ * C' + C'
  refine ⟨C, fun h n hn q hq q₀ hq₀ => ?_⟩
  let : IsProbabilityMeasure (productLaw μ B h n) := isProbabilityMeasure_productLaw B h n
  let ρ := (2 / B) ^ n
  let D := defectMean μ B h n q₀
  let J := ∫ r, unitSlope r ∂(productLaw μ B h n)
  let JA := ∫ r, |unitSlope r| ∂(productLaw μ B h n)
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hi : Integrable unitSlope (productLaw μ B h n) := integrable_unitSlope hpos hB h hn
  have hdi : Integrable (defectKernel B q) (productLaw μ B h n) :=
    integrable_defectKernel hB hb (hq₁.trans_le hq.1) (hq.2.trans_lt hq₂) h n
      (ae_floor_productLaw hpos hB h hn)
  have hdi₀ : Integrable (defectKernel B q₀) (productLaw μ B h n) :=
    integrable_defectKernel hB hb (hq₁.trans_le hq₀.1) (hq₀.2.trans_lt hq₂) h n
      (ae_floor_productLaw hpos hB h hn)
  have hpoint : ∀ᵐ r ∂(productLaw μ B h n),
      |defectKernel B q r - defectKernel B q₀ r| ≤ K₀ * |q - q₀| * |unitSlope r| := by
    filter_upwards [ae_floor_productLaw hpos hB h hn] with r hr
    have hp := hK q hq q₀ hq₀ r hr
    exact hp.trans (by
      have hkn : K ≤ K₀ := le_max_left _ _
      have hδ : 0 ≤ |q - q₀| := abs_nonneg _
      have hm : 0 ≤ |unitSlope r| := abs_nonneg _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkn hδ) hm)
  have hint : |defectMean μ B h n q - D| ≤ K₀ * |q - q₀| * JA := by
    calc
      |defectMean μ B h n q - D| =
          |∫ r, (defectKernel B q r - defectKernel B q₀ r) ∂(productLaw μ B h n)| := by
        dsimp [D]
        unfold defectMean
        rw [integral_sub hdi hdi₀]
      _ ≤ ∫ r, |defectKernel B q r - defectKernel B q₀ r| ∂(productLaw μ B h n) :=
        abs_integral_le_integral_abs
      _ ≤ ∫ r, K₀ * |q - q₀| * |unitSlope r| ∂(productLaw μ B h n) :=
        integral_mono_ae ((hdi.sub hdi₀).abs) (hi.abs.const_mul _) hpoint
      _ = K₀ * |q - q₀| * JA := by rw [integral_const_mul]
  have hJA : JA ≤ J + 4 * ρ := by
    have hmono := integral_mono_ae hi.abs (hi.add (integrable_const (4 * ρ))) (by
      filter_upwards [ae_floor_productLaw hpos hB h hn,
        ae_floor_sq_productLaw hpos hB h n] with r hr hrn
      have hf := one_sub_floorSeq_le hB n
      have hb0 := floorSeq_nonneg hB n
      have hrρ : 1 - r ≤ 2 * ρ := by dsimp [ρ]; nlinarith
      exact unitSlope_abs_floor hB hρ hr hrρ)
    simpa only [Pi.add_apply, integral_add hi (integrable_const _), integral_const,
      probReal_univ, smul_eq_mul, one_mul] using hmono
  have hcomp : |J| ≤ CF * (D + C₀ * ρ) := by
    simpa [J, D, ρ, kernelExpectation, unitSlope_one] using hCF h n hn q₀ hq₀
  have hlower : -(|CL| * ρ) ≤ D := by
    have hl := hCL h n hn q₀ hq₀
    have ha := mul_le_mul_of_nonneg_right (le_abs_self CL) hρ
    dsimp [D, ρ]
    nlinarith
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have habs : |D + C₀ * ρ| ≤ D + C₁ * ρ := by
    have hc := mul_le_mul_of_nonneg_right (le_abs_self C₀) hρ
    have hc' := mul_le_mul_of_nonneg_right (neg_abs_le C₀) hρ
    rw [abs_le]
    constructor
    · dsimp [C₁]
      nlinarith [hρ]
    · have hcoef : C₀ ≤ C₁ := by dsimp [C₁]; nlinarith [le_abs_self C₀, abs_nonneg CL]
      exact add_le_add (le_refl D) (mul_le_mul_of_nonneg_right hcoef hρ)
  have hA : 1 ≤ A := le_max_right _ _
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hCFabs : CF * (D + C₀ * ρ) ≤ A * (D + C₁ * ρ) := by
    calc
      CF * (D + C₀ * ρ) ≤ |CF * (D + C₀ * ρ)| := le_abs_self _
      _ = |CF| * |D + C₀ * ρ| := abs_mul _ _
      _ ≤ A * |D + C₀ * ρ| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
      _ ≤ A * (D + C₁ * ρ) := mul_le_mul_of_nonneg_left habs hA0
  have hJA' : JA ≤ A * D + E * ρ := by
    have hJ : JA ≤ CF * (D + C₀ * ρ) + 4 * ρ := hJA.trans (by
      have habsJ : J ≤ |J| := le_abs_self J
      linarith)
    calc
      JA ≤ CF * (D + C₀ * ρ) + 4 * ρ := hJ
      _ ≤ A * (D + C₁ * ρ) + 4 * ρ := add_le_add hCFabs le_rfl
      _ = A * D + E * ρ := by dsimp [E]; ring
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hC'0 : 0 ≤ C' := by dsimp [C']; positivity
  have hC'A : A ≤ C' := by dsimp [C']; nlinarith [abs_nonneg CL]
  have hEC' : E ≤ C' * A := by
    have hE : E ≤ C' := by dsimp [C']; nlinarith [hA0, abs_nonneg CL]
    calc
      E ≤ C' * 1 := by simpa using hE
      _ ≤ C' * A := mul_le_mul_of_nonneg_left hA hC'0
  have hdC' : 0 ≤ D + C' * ρ := by
    have hc := mul_le_mul_of_nonneg_right (show |CL| ≤ C' by dsimp [C']; nlinarith [hA0, hE0]) hρ
    nlinarith
  have hres' : JA ≤ C' * (D + C' * ρ) :=
    rescale_defect_estimate hρ hdC' hC'A hEC' hJA'
  have hCC' : C' ≤ C := by dsimp [C]; nlinarith [mul_nonneg hK₀ hC'0]
  have hCA : K₀ * C' ≤ C := by dsimp [C]; nlinarith [mul_nonneg hK₀ hC'0]
  have hEC : K₀ * C' ^ 2 ≤ C * (K₀ * C') := by
    have hs : 0 ≤ (K₀ * C') ^ 2 := sq_nonneg _
    dsimp [C]
    nlinarith
  have hdC : 0 ≤ D + C * ρ := by
    have hc := mul_le_mul_of_nonneg_right hCC' hρ
    nlinarith
  have hres : K₀ * JA ≤ C * (D + C * ρ) := by
    apply rescale_defect_estimate hρ hdC hCA hEC
    calc
      K₀ * JA ≤ K₀ * (C' * (D + C' * ρ)) := mul_le_mul_of_nonneg_left hres' hK₀
      _ = (K₀ * C') * D + (K₀ * C' ^ 2) * ρ := by ring
  calc
    |defectMean μ B h n q - defectMean μ B h n q₀| ≤ K₀ * |q - q₀| * JA := hint
    _ = |q - q₀| * (K₀ * JA) := by ring
    _ ≤ |q - q₀| * (C * (D + C * ρ)) :=
      mul_le_mul_of_nonneg_left hres (abs_nonneg _)
    _ = C * |q - q₀| * (D + C * ρ) := by ring
    _ = C * |q - q₀| * (defectMean μ B h n q₀ + C * (2 / B) ^ n) := by rfl

end DiamondPinning
