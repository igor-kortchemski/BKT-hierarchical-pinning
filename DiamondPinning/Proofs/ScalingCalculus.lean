module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Model.Basic
public import DiamondPinning.Model.Scaling
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
Mellin-product integrability, the exact real-moment recurrence, and the kernel
comparison estimates of `scaling:mellin-calculus`.  This covers
`source/scaling.tex`, lines 124--147 and 170--188, together with the
finiteness and negative-support properties of the rescaled measure used in
lines 90--101.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Set

private theorem isProbabilityMeasure_productLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (B h : ℝ) (n : ℕ) : IsProbabilityMeasure (productLaw μ B h n) := by
  let : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  rw [productLaw]
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

/-- Almost every product of two generation-`n` variables is bounded below by the
square of the first-generation floor. -/
theorem ae_floorSeq_one_sq_le_productLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
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

private theorem ae_pos_productLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    ∀ᵐ r ∂(productLaw μ B h n), 0 < r := by
  let : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  rw [productLaw, ae_map_iff (by fun_prop) measurableSet_Ioi]
  rw [Measure.ae_prod_iff_ae_ae (by measurability)]
  have hp := ae_pos_lawR hpos hB h n
  filter_upwards [hp] with x hx
  filter_upwards [hp] with y hy
  exact mul_pos hx hy

private theorem rpow_le_one_add {x q : ℝ} (hx : 0 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    x ^ q ≤ 1 + x := by
  rcases le_total x 1 with hx1 | hx1
  · exact (Real.rpow_le_one hx hx1 hq0).trans (by linarith)
  · calc
      x ^ q ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hq1
      _ = x := Real.rpow_one x
      _ ≤ 1 + x := by linarith

private theorem integrable_rpow_lawR {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Integrable (fun x : ℝ => x ^ q) (lawR μ B h n) := by
  let : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have hi := integrable_lawR_of hpos hmean hB h n
  apply ((integrable_const (1 : ℝ)).add hi).mono'
    (Real.continuous_rpow_const hq0).measurable.aestronglyMeasurable
  filter_upwards [ae_pos_lawR hpos hB h n] with x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le q)]
  exact rpow_le_one_add hx.le hq0 hq1

private theorem integrable_id_productLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : Integrable (fun r : ℝ => r) (productLaw μ B h n) := by
  let : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have hi := integrable_lawR_of hpos hmean hB h n
  rw [productLaw]
  apply (integrable_map_measure measurable_id.aestronglyMeasurable (by fun_prop)).2
  simpa [Function.comp_def] using hi.mul_prod hi

private theorem integrable_rpow_productLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Integrable (fun r : ℝ => r ^ q) (productLaw μ B h n) := by
  let : IsProbabilityMeasure (productLaw μ B h n) := isProbabilityMeasure_productLaw B h n
  have hi := integrable_id_productLaw hpos hmean hB h n
  apply ((integrable_const (1 : ℝ)).add hi).mono'
    (Real.continuous_rpow_const hq0).measurable.aestronglyMeasurable
  filter_upwards [ae_pos_productLaw hpos hB h n] with r hr
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hr.le q)]
  exact rpow_le_one_add hr.le hq0 hq1

private theorem integrable_defectKernel {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Integrable (fun r => defectKernel B q r) (productLaw μ B h n) := by
  let : IsProbabilityMeasure (productLaw μ B h n) := isProbabilityMeasure_productLaw B h n
  have hr := integrable_rpow_productLaw hpos hmean hB h n hq0 hq1
  have hrc : Integrable (fun r : ℝ => (r + (B - 1)) ^ q) (productLaw μ B h n) := by
    have hi : Integrable (fun r : ℝ => 1 + (r + (B - 1))) (productLaw μ B h n) := by
      have hadd := (integrable_const B).add (integrable_id_productLaw hpos hmean hB h n)
      convert hadd using 1
      funext x
      simp only [Pi.add_apply]
      ring
    apply hi.mono' (((Real.continuous_rpow_const hq0).comp
      (continuous_id.add_const (B - 1)))).measurable.aestronglyMeasurable
    filter_upwards [ae_pos_productLaw hpos hB h n] with r hr
    change ‖(r + (B - 1)) ^ q‖ ≤ 1 + (r + (B - 1))
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) q)]
    exact rpow_le_one_add (by linarith) hq0 hq1
  exact (((integrable_const (B ^ q - 1)).sub hrc).add hr)

private theorem hasDerivAt_defectKernel {B q r : ℝ} (hr : r ≠ 0) (hrc : r + (B - 1) ≠ 0) :
    HasDerivAt (defectKernel B q)
      (q * r ^ (q - 1) - q * (r + (B - 1)) ^ (q - 1)) r := by
  have h1 := (Real.hasDerivAt_rpow_const (p := q) (Or.inl hrc)).comp r
    ((hasDerivAt_id r).add_const (B - 1))
  have h2 := Real.hasDerivAt_rpow_const (p := q) (Or.inl hr)
  convert ((hasDerivAt_const r (B ^ q - 1)).sub h1).add h2 using 1
  · funext x
    simp only [defectKernel, Function.comp_apply, id_eq, Pi.sub_apply, Pi.add_apply]
  · simp only [zero_sub, mul_one]
    ring

private theorem defectKernel_one (B : ℝ) (q : ℝ) : defectKernel B q 1 = 0 := by
  simp [defectKernel]

private theorem defectKernel_nonneg_of_one_le {B q r : ℝ} (hB : 2 < B)
    (hq0 : 0 < q) (hq1 : q < 1) (hr : 1 ≤ r) : 0 ≤ defectKernel B q r := by
  have hcont : ContinuousOn (defectKernel B q) (Set.Ici 1) := by
    unfold defectKernel
    fun_prop
  have hdiff : DifferentiableOn ℝ (defectKernel B q) (interior (Set.Ici 1)) := by
    intro x hx
    rw [interior_Ici] at hx
    change 1 < x at hx
    have hd := hasDerivAt_defectKernel (B := B) (q := q) (r := x)
      (by linarith) (by linarith)
    exact hd.differentiableAt.differentiableWithinAt
  have hder : ∀ x ∈ interior (Set.Ici (1 : ℝ)), 0 ≤ deriv (defectKernel B q) x := by
    intro x hx
    rw [interior_Ici] at hx
    change 1 < x at hx
    rw [(hasDerivAt_defectKernel (by linarith) (by linarith)).deriv]
    have hdec : (x + (B - 1)) ^ (q - 1) ≤ x ^ (q - 1) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    nlinarith
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici 1) hcont hdiff hder
    (Set.mem_Ici.mpr le_rfl) hr hr
  simpa [defectKernel_one] using hm

private theorem defectKernel_lower_on_Icc {B b q q₁ : ℝ} (hB : 2 < B)
    (hb : 0 < b) (hb1 : b < 1) (hq0 : 0 < q) (hq1 : q < 1) (hqq : q₁ ≤ q)
    {r : ℝ} (hr : r ∈ Set.Icc b 1) :
    -(b ^ (q₁ - 1) * (1 - r)) ≤ defectKernel B q r := by
  let C := b ^ (q₁ - 1)
  have hC : 0 < C := Real.rpow_pos_of_pos hb _
  have hd : ∀ x ∈ Set.Icc b (1 : ℝ), DifferentiableAt ℝ (defectKernel B q) x := by
    intro x hx
    exact (hasDerivAt_defectKernel (ne_of_gt (hb.trans_le hx.1))
      (by linarith [hx.1])).differentiableAt
  have hbound : ∀ x ∈ Set.Icc b (1 : ℝ), ‖deriv (defectKernel B q) x‖ ≤ C := by
    intro x hx
    have hxpos : 0 < x := hb.trans_le hx.1
    have hxε : 0 < x + (B - 1) := by linarith
    rw [(hasDerivAt_defectKernel hxpos.ne' hxε.ne').deriv]
    have hdec : (x + (B - 1)) ^ (q - 1) ≤ x ^ (q - 1) :=
      Real.rpow_le_rpow_of_nonpos hxpos (by linarith) (by linarith)
    have hnon : 0 ≤ q * x ^ (q - 1) - q * (x + (B - 1)) ^ (q - 1) := by
      nlinarith [Real.rpow_nonneg hxpos.le (q - 1), Real.rpow_nonneg hxε.le (q - 1)]
    rw [Real.norm_of_nonneg hnon]
    calc
      q * x ^ (q - 1) - q * (x + (B - 1)) ^ (q - 1) ≤ q * x ^ (q - 1) := by
        have : 0 ≤ q * (x + (B - 1)) ^ (q - 1) := mul_nonneg hq0.le (Real.rpow_nonneg hxε.le _)
        linarith
      _ ≤ x ^ (q - 1) := by
        nlinarith [Real.rpow_nonneg hxpos.le (q - 1)]
      _ ≤ b ^ (q - 1) := Real.rpow_le_rpow_of_nonpos hb hx.1 (by linarith)
      _ ≤ b ^ (q₁ - 1) := Real.rpow_le_rpow_of_exponent_ge hb hb1.le (by linarith)
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le hd hbound (convex_Icc b 1) hr
    (right_mem_Icc.mpr hb1.le)
  simp only [defectKernel_one, Real.norm_eq_abs, zero_sub, abs_neg] at hm
  rw [abs_of_nonneg (sub_nonneg.mpr hr.2)] at hm
  have ha := neg_abs_le (defectKernel B q r)
  dsimp [C] at hm
  linarith

private theorem defectKernel_lower {B b β q q₁ r ρ : ℝ} (hB : 2 < B)
    (hb : 0 < b) (hb1 : b < 1) (hq0 : 0 < q) (hq1 : q < 1) (hqq : q₁ ≤ q)
    (hρ : 0 ≤ ρ) (hbr : b ≤ r) (hβr : β ≤ r) (hbfloor : 1 - β ≤ 2 * ρ) :
    -(2 * b ^ (q₁ - 1) * ρ) ≤ defectKernel B q r := by
  have hb0 : 0 ≤ b := hb.le
  have hb_le : b ≤ 1 := hb1.le
  by_cases hr : 1 ≤ r
  · have hd := defectKernel_nonneg_of_one_le hB hq0 hq1 hr
    have : 0 ≤ 2 * b ^ (q₁ - 1) * ρ := by positivity
    linarith
  · have hr1 : r ≤ 1 := le_of_not_ge hr
    have hd := defectKernel_lower_on_Icc hB hb hb1 hq0 hq1 hqq ⟨hbr, hr1⟩
    have hnon : 0 ≤ b ^ (q₁ - 1) := Real.rpow_nonneg hb.le _
    have hfac : 1 - r ≤ 2 * ρ := by nlinarith
    have := mul_le_mul_of_nonneg_left hfac hnon
    linarith

private theorem measurable_rpow_const (q : ℝ) : Measurable (fun x : ℝ => x ^ q) := by
  by_cases hq : q = 0
  · subst q
    simp
  let f : ℝ → ℝ := fun x => if x ≤ 0 then
    (if x = 0 then (if q = 0 then 1 else 0)
      else Real.exp (Real.log x * q) * Real.cos (q * Real.pi))
    else Real.exp (Real.log x * q)
  have hm : Measurable f := by
    apply Measurable.ite (measurableSet_le measurable_id measurable_const)
    · apply Measurable.ite (measurableSet_eq)
      · simp only [hq, ite_false]
        exact measurable_const
      · exact (Real.measurable_exp.comp (Real.measurable_log.mul_const q)).mul
          (Real.measurable_cos.comp measurable_const)
    · exact Real.measurable_exp.comp (Real.measurable_log.mul_const q)
  have heq : f = (fun x : ℝ => x ^ q) := by
    funext x
    by_cases hx : x ≤ 0
    · dsimp [f]
      rw [ite_eq_left hx, Real.rpow_def_of_nonpos hx]
    · have hx0 : 0 < x := lt_of_not_ge hx
      dsimp [f]
      rw [ite_eq_right hx, Real.rpow_def_of_pos hx0]
  rw [← heq]
  exact hm

private theorem integrable_rpow_productLaw_floor {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq1 : q ≤ 1) :
    Integrable (fun r : ℝ => r ^ q) (productLaw μ B h n) := by
  by_cases hq0 : 0 ≤ q
  · exact integrable_rpow_productLaw hpos hmean hB h n hq0 hq1
  let : IsProbabilityMeasure (productLaw μ B h n) := isProbabilityMeasure_productLaw B h n
  let b := floorSeq B n ^ 2
  apply (integrable_const (b ^ q)).mono' (measurable_rpow_const q).aestronglyMeasurable
  filter_upwards [ae_floor_sq_productLaw hpos hB h n] with r hr
  have hb : 0 < b := sq_pos_of_pos ((floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn))
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (hb.trans_le hr).le q)]
  exact Real.rpow_le_rpow_of_nonpos hb hr (le_of_not_ge hq0)

private theorem integrable_shift_rpow_productLaw_floor {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq1 : q ≤ 1) :
    Integrable (fun r : ℝ => (r + (B - 1)) ^ q) (productLaw μ B h n) := by
  by_cases hq0 : 0 ≤ q
  · let : IsProbabilityMeasure (productLaw μ B h n) := isProbabilityMeasure_productLaw B h n
    have hi : Integrable (fun r : ℝ => 1 + (r + (B - 1))) (productLaw μ B h n) := by
      have hadd := (integrable_const B).add (integrable_id_productLaw hpos hmean hB h n)
      convert hadd using 1
      funext x
      simp only [Pi.add_apply]
      ring
    apply hi.mono' (((measurable_rpow_const q).comp
      (measurable_id.add_const (B - 1))).aestronglyMeasurable)
    filter_upwards [ae_pos_productLaw hpos hB h n] with r hr
    change ‖(r + (B - 1)) ^ q‖ ≤ 1 + (r + (B - 1))
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) q)]
    exact rpow_le_one_add (by linarith) hq0 hq1
  let : IsProbabilityMeasure (productLaw μ B h n) := isProbabilityMeasure_productLaw B h n
  let b := floorSeq B n ^ 2 + (B - 1)
  apply (integrable_const (b ^ q)).mono' ((measurable_rpow_const q).comp
    (measurable_id.add_const (B - 1))).aestronglyMeasurable
  filter_upwards [ae_floor_sq_productLaw hpos hB h n] with r hr
  have hb : 0 < b := by
    dsimp [b]
    have hb0 := (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)
    nlinarith [sq_nonneg (floorSeq B n)]
  change ‖(r + (B - 1)) ^ q‖ ≤ b ^ q
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by
    dsimp [b] at hb ⊢
    linarith) q)]
  apply Real.rpow_le_rpow_of_nonpos hb (by dsimp [b]; linarith) (le_of_not_ge hq0)

/-- The `q`-moment of the product law factors as the square of the real moment,
which is the product identity used in the recurrence at `source/scaling.tex` line 179. -/
theorem integral_rpow_productLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {q : ℝ} :
    (∫ r : ℝ, r ^ q ∂productLaw μ B h n) = realMoment μ B h n q ^ 2 := by
  let : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have hp : ∀ᵐ p : ℝ × ℝ ∂((lawR μ B h n).prod (lawR μ B h n)),
      (p.1 * p.2) ^ q = p.1 ^ q * p.2 ^ q := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    filter_upwards [ae_pos_lawR hpos hB h n] with y hy
    exact Real.mul_rpow hx.le hy.le
  rw [productLaw, integral_map (by fun_prop) (measurable_rpow_const q).aestronglyMeasurable,
    integral_congr_ae hp, integral_prod_mul (fun x : ℝ => x ^ q) (fun y : ℝ => y ^ q)]
  simp only [realMoment]
  ring

/-- The exact recursion
`G_{n+1}(q) = B^{-q} (G_n(q)^2 + B^q - 1 - D_n(q))` from
`source/scaling.tex` line 179. -/
theorem realMoment_succ {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq1 : q ≤ 1) :
    realMoment μ B h (n + 1) q = B ^ (-q) *
      (realMoment μ B h n q ^ 2 + B ^ q - 1 - defectMean μ B h n q) := by
  let : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  let : IsProbabilityMeasure (productLaw μ B h n) := isProbabilityMeasure_productLaw B h n
  have hB0 : 0 < B := by linarith
  have hri : Integrable (fun r : ℝ => r ^ q) (productLaw μ B h n) :=
    integrable_rpow_productLaw_floor hpos hmean hB h hn hq1
  have hci : Integrable (fun r : ℝ => (r + (B - 1)) ^ q) (productLaw μ B h n) :=
    integrable_shift_rpow_productLaw_floor hpos hmean hB h hn hq1
  have hrec : realMoment μ B h (n + 1) q =
      (∫ r : ℝ, (r + (B - 1)) ^ q ∂productLaw μ B h n) / B ^ q := by
    unfold realMoment
    rw [lawR_succ, integral_map (by fun_prop) (measurable_rpow_const q).aestronglyMeasurable]
    rw [productLaw, integral_map]
    · rw [← integral_div]
      apply integral_congr_ae
      have hpair : ∀ᵐ p : ℝ × ℝ ∂((lawR μ B h n).prod (lawR μ B h n)),
          0 < p.1 * p.2 := by
        rw [Measure.ae_prod_iff_ae_ae (by measurability)]
        filter_upwards [ae_pos_lawR hpos hB h n] with x hx
        filter_upwards [ae_pos_lawR hpos hB h n] with y hy
        exact mul_pos hx hy
      filter_upwards [hpair] with p hp
      exact Real.div_rpow (by linarith) hB0.le q
    · fun_prop
    · exact ((measurable_rpow_const q).comp
        (measurable_id.add_const (B - 1))).aestronglyMeasurable
  have hD : defectMean μ B h n q = B ^ q - 1 -
      (∫ r : ℝ, (r + (B - 1)) ^ q ∂productLaw μ B h n) +
      ∫ r : ℝ, r ^ q ∂productLaw μ B h n := by
    unfold defectMean defectKernel
    calc
      (∫ r : ℝ, B ^ q - 1 - (r + (B - 1)) ^ q + r ^ q ∂productLaw μ B h n) =
          (∫ r : ℝ, B ^ q - 1 - (r + (B - 1)) ^ q ∂productLaw μ B h n) +
            ∫ r : ℝ, r ^ q ∂productLaw μ B h n :=
        integral_add ((integrable_const _).sub hci) hri
      _ = _ := by
        rw [integral_sub (integrable_const _) hci, integral_const]
        simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [hrec, hD, integral_rpow_productLaw hpos hB h n]
  rw [div_eq_mul_inv, ← Real.rpow_neg hB0.le q]
  ring

private theorem weight_rpow_neg {B N s q : ℝ} (hB : 2 < B) (hN : 0 < N)
    (hq : q = weightExponent B N s) : 2 * B ^ (-q) = Real.exp (s / N) := by
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hN0 : N ≠ 0 := hN.ne'
  have hlogB0 : Real.log B ≠ 0 := hlogB.ne'
  rw [Real.rpow_def_of_pos (by linarith : 0 < B), hq, weightExponent, theta]
  rw [show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log]; norm_num, ← Real.exp_add]
  congr 1
  field_simp
  simp only [Real.log_exp]
  ring

private noncomputable def defectSlope (B q₁ q₂ : ℝ) : ℝ :=
  q₁ * 2 ^ (q₁ - 1) * (1 - ((B + 1) / 2) ^ (q₂ - 1))

private theorem defectSlope_pos {B q₁ q₂ : ℝ} (hB : 2 < B)
    (hq₁ : 0 < q₁) (hq₂ : q₂ < 1) : 0 < defectSlope B q₁ q₂ := by
  unfold defectSlope
  have hpow : ((B + 1) / 2) ^ (q₂ - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  positivity

private theorem defect_deriv_lower {B q q₁ q₂ x : ℝ} (hB : 2 < B)
    (hq₁ : 0 < q₁) (hqq₁ : q₁ ≤ q) (hqq₂ : q ≤ q₂) (hq₂ : q₂ < 1)
    (hx : x ∈ Set.Icc (1 : ℝ) 2) :
    defectSlope B q₁ q₂ ≤ q * x ^ (q - 1) - q * (x + (B - 1)) ^ (q - 1) := by
  let E := (B + 1) / 2
  have hE : 1 < E := by dsimp [E]; linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx.1
  have hratio0 : 0 < (x + (B - 1)) / x := div_pos (by linarith) hx0
  have hratioE : E ≤ (x + (B - 1)) / x := by
    rw [le_div_iff₀ hx0]
    dsimp [E]
    nlinarith [hx.2]
  have hfactor : ((x + (B - 1)) / x) ^ (q - 1) ≤ E ^ (q₂ - 1) := by
    calc
      ((x + (B - 1)) / x) ^ (q - 1) ≤ E ^ (q - 1) :=
        Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans hE) hratioE (by linarith)
      _ ≤ E ^ (q₂ - 1) := Real.rpow_le_rpow_of_exponent_le hE.le (sub_le_sub_right hqq₂ 1)
  have hA : 2 ^ (q₁ - 1) ≤ x ^ (q - 1) := by
    calc
      2 ^ (q₁ - 1) ≤ 2 ^ (q - 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (sub_le_sub_right hqq₁ 1)
      _ ≤ x ^ (q - 1) := Real.rpow_le_rpow_of_nonpos hx0 hx.2 (by linarith)
  have hid : (x + (B - 1)) ^ (q - 1) =
      ((x + (B - 1)) / x) ^ (q - 1) * x ^ (q - 1) := by
    rw [← Real.mul_rpow hratio0.le hx0.le]
    congr 1
    field_simp
  have hm := mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hx0.le (q - 1))
  rw [← hid] at hm
  have hfacnon : 0 ≤ 1 - E ^ (q₂ - 1) :=
    sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg hE (by linarith)).le
  have hAm := mul_le_mul_of_nonneg_left hA hfacnon
  have hd : 2 ^ (q₁ - 1) * (1 - E ^ (q₂ - 1)) ≤
      x ^ (q - 1) - (x + (B - 1)) ^ (q - 1) := by
    nlinarith [Real.rpow_nonneg hx0.le (q - 1)]
  have hd0 : 0 ≤ 2 ^ (q₁ - 1) * (1 - E ^ (q₂ - 1)) := mul_nonneg (by positivity) hfacnon
  have hqmul := mul_le_mul_of_nonneg_right hqq₁ (hd0.trans hd)
  unfold defectSlope
  nlinarith

private theorem defectKernel_linear_lower {B q q₁ q₂ r : ℝ} (hB : 2 < B)
    (hq₁ : 0 < q₁) (hqq₁ : q₁ ≤ q) (hqq₂ : q ≤ q₂) (hq₂ : q₂ < 1)
    (hr : r ∈ Set.Icc (1 : ℝ) 2) :
    defectSlope B q₁ q₂ * (r - 1) ≤ defectKernel B q r := by
  have hq0 : 0 ≤ q := hq₁.le.trans hqq₁
  have hcont : ContinuousOn (defectKernel B q) (Set.Icc (1 : ℝ) 2) := by
    unfold defectKernel
    apply ContinuousOn.add
    · exact continuousOn_const.sub (((Real.continuous_rpow_const hq0).comp
        (continuous_id.add_const (B - 1))).continuousOn)
    · exact (Real.continuous_rpow_const hq0).continuousOn
  have hdiff : DifferentiableOn ℝ (defectKernel B q) (interior (Set.Icc (1 : ℝ) 2)) := by
    intro x hx
    rw [interior_Icc] at hx
    have hd := hasDerivAt_defectKernel (B := B) (q := q) (r := x)
      (by linarith [hx.1]) (by linarith [hx.1])
    exact hd.differentiableAt.differentiableWithinAt
  have hder : ∀ x ∈ interior (Set.Icc (1 : ℝ) 2),
      defectSlope B q₁ q₂ ≤ deriv (defectKernel B q) x := by
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_defectKernel (by linarith [hx.1]) (by linarith [hx.1])).deriv]
    exact defect_deriv_lower hB hq₁ hqq₁ hqq₂ hq₂ ⟨hx.1.le, hx.2.le⟩
  have hm := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc 1 2) hcont hdiff hder
    1 (left_mem_Icc.mpr (by norm_num)) r hr hr.1
  simpa [defectKernel_one] using hm

private theorem defectKernel_ge_two {B q r : ℝ} (hB : 2 < B)
    (hq0 : 0 < q) (hq1 : q < 1) (hr : 2 ≤ r) :
    defectKernel B q 2 ≤ defectKernel B q r := by
  have hcont : ContinuousOn (defectKernel B q) (Set.Ici 1) := by
    unfold defectKernel
    apply ContinuousOn.add
    · exact continuousOn_const.sub (((Real.continuous_rpow_const hq0.le).comp
        (continuous_id.add_const (B - 1))).continuousOn)
    · exact (Real.continuous_rpow_const hq0.le).continuousOn
  have hdiff : DifferentiableOn ℝ (defectKernel B q) (interior (Set.Ici 1)) := by
    intro x hx
    rw [interior_Ici] at hx
    change 1 < x at hx
    have hd := hasDerivAt_defectKernel (B := B) (q := q) (r := x)
      (by linarith) (by linarith)
    exact hd.differentiableAt.differentiableWithinAt
  have hder : ∀ x ∈ interior (Set.Ici (1 : ℝ)), 0 ≤ deriv (defectKernel B q) x := by
    intro x hx
    rw [interior_Ici] at hx
    change 1 < x at hx
    rw [(hasDerivAt_defectKernel (by linarith) (by linarith)).deriv]
    have hdec : (x + (B - 1)) ^ (q - 1) ≤ x ^ (q - 1) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    nlinarith
  exact monotoneOn_of_deriv_nonneg (convex_Ici 1) hcont hdiff hder
    (by norm_num) (show 1 ≤ r by linarith) hr

private theorem kernel_pointwise_comparison {B b q₁ q₂ : ℝ} (F : ℝ → ℝ)
    (hB : 2 < B) (hb : 0 < b) (hb1 : b < 1) (hq₁ : 0 < q₁) (hq₂ : q₂ < 1)
    (KF : ℝ) (hFbound : ∀ r : ℝ, b ≤ r → |F r| ≤ KF)
    (hF1 : DifferentiableAt ℝ F 1) :
    ∃ CF : ℝ, ∀ q ∈ Set.Icc q₁ q₂, ∀ r : ℝ, b ≤ r →
      |F r - F 1| ≤ CF * (defectKernel B q r +
        2 * b ^ (q₁ - 1) * max (1 - r) 0) := by
  obtain ⟨L, hL⟩ := hF1.hasDerivAt.isBigO_sub.bound
  rw [Metric.eventually_nhds_iff] at hL
  obtain ⟨ε, hε, hL⟩ := hL
  let e := min ε 1
  let K := b ^ (q₁ - 1)
  let m := defectSlope B q₁ q₂
  let mK := min K m
  let LP := |L| + 1
  let δ := min (K * e) (min (m * e) m)
  let CL := LP / mK
  let CG := (KF + |F 1|) / δ
  have he : 0 < e := lt_min hε zero_lt_one
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  have hK : 0 < K := Real.rpow_pos_of_pos hb _
  have hm : 0 < m := defectSlope_pos hB hq₁ hq₂
  have hmK : 0 < mK := lt_min hK hm
  have hLP : 0 < LP := by dsimp [LP]; positivity
  have hδ : 0 < δ := lt_min (mul_pos hK he) (lt_min (mul_pos hm he) hm)
  have hCL : 0 ≤ CL := (div_pos hLP hmK).le
  have hKF : 0 ≤ KF := (abs_nonneg (F b)).trans (hFbound b le_rfl)
  have hCG : 0 ≤ CG := div_nonneg (add_nonneg hKF (abs_nonneg _)) hδ.le
  let CF := max CL CG
  have hCFL : CL ≤ CF := le_max_left _ _
  have hCFG : CG ≤ CF := le_max_right _ _
  have hCF : 0 ≤ CF := hCL.trans hCFL
  have hmulCL : CL * mK = LP := by dsimp [CL]; field_simp
  have hmulCG : CG * δ = KF + |F 1| := by dsimp [CG]; field_simp
  refine ⟨CF, fun q hq r hr => ?_⟩
  have hq0 : 0 < q := hq₁.trans_le hq.1
  have hq1 : q < 1 := hq.2.trans_lt hq₂
  have hcorr : 0 ≤ 2 * K * max (1 - r) 0 := by positivity
  have hbelow : r < 1 → K * (1 - r) ≤ defectKernel B q r + 2 * K * max (1 - r) 0 := by
    intro hr1
    have hd := defectKernel_lower_on_Icc hB hb hb1 hq0 hq1 hq.1 ⟨hr, hr1.le⟩
    have hmax : max (1 - r) 0 = 1 - r := max_eq_left (by linarith)
    dsimp [K] at hd ⊢
    rw [hmax]
    linarith
  have habove12 : 1 ≤ r → r ≤ 2 → m * (r - 1) ≤
      defectKernel B q r + 2 * K * max (1 - r) 0 := by
    intro hr1 hr2
    exact (defectKernel_linear_lower hB hq₁ hq.1 hq.2 hq₂ ⟨hr1, hr2⟩).trans (by linarith)
  by_cases hlocal : dist r 1 < e
  · have hLe : dist r 1 < ε := hlocal.trans_le heε
    have hF := hL hLe
    simp only [Real.norm_eq_abs] at hF ⊢
    have hL' : L ≤ LP := by dsimp [LP]; linarith [le_abs_self L]
    have hFL : |F r - F 1| ≤ LP * |r - 1| := by
      apply hF.trans
      exact mul_le_mul_of_nonneg_right hL' (abs_nonneg _)
    have hr2 : r ≤ 2 := by
      rw [Real.dist_eq] at hlocal
      have : |r - 1| < 1 := hlocal.trans_le he1
      have hh := (abs_lt.mp this).2
      linarith
    have hbase : mK * |r - 1| ≤ defectKernel B q r + 2 * K * max (1 - r) 0 := by
      rcases lt_or_ge r 1 with hr1 | hr1
      · have hd := hbelow hr1
        rw [abs_of_neg (sub_neg.mpr hr1)]
        have hKm : mK ≤ K := min_le_left _ _
        have hmul := mul_le_mul_of_nonneg_right hKm (sub_nonneg.mpr hr1.le)
        linarith
      · have hd := habove12 hr1 hr2
        rw [abs_of_nonneg (sub_nonneg.mpr hr1)]
        have hmm : mK ≤ m := min_le_right _ _
        have hmul := mul_le_mul_of_nonneg_right hmm (sub_nonneg.mpr hr1)
        linarith
    calc
      |F r - F 1| ≤ LP * |r - 1| := hFL
      _ = CL * (mK * |r - 1|) := by rw [← hmulCL]; ring
      _ ≤ CL * (defectKernel B q r + 2 * K * max (1 - r) 0) :=
        mul_le_mul_of_nonneg_left hbase hCL
      _ ≤ CF * (defectKernel B q r + 2 * K * max (1 - r) 0) := by
        have hrhs : 0 ≤ defectKernel B q r + 2 * K * max (1 - r) 0 := by
          rcases lt_or_ge r 1 with hr1 | hr1
          · have hd := hbelow hr1
            have : 0 ≤ K * (1 - r) := by positivity
            linarith
          · have hd := defectKernel_nonneg_of_one_le hB hq0 hq1 hr1
            dsimp [K] at hcorr ⊢
            linarith
        exact mul_le_mul_of_nonneg_right hCFL hrhs
  · have hdelta : δ ≤ defectKernel B q r + 2 * K * max (1 - r) 0 := by
      rcases lt_or_ge r 1 with hr1 | hr1
      · have hd := hbelow hr1
        have hdist : e ≤ 1 - r := by
          have : e ≤ |r - 1| := by simpa [Real.dist_eq] using hlocal
          simpa [abs_of_neg (sub_neg.mpr hr1)] using this
        have hKe : K * e ≤ K * (1 - r) := mul_le_mul_of_nonneg_left hdist hK.le
        exact (min_le_left _ _).trans (hKe.trans hd)
      · by_cases hr2 : r ≤ 2
        · have hd := habove12 hr1 hr2
          have hdist : e ≤ r - 1 := by
            have : e ≤ |r - 1| := by simpa [Real.dist_eq] using hlocal
            simpa [abs_of_nonneg (sub_nonneg.mpr hr1)] using this
          have hme : m * e ≤ m * (r - 1) := mul_le_mul_of_nonneg_left hdist hm.le
          exact ((min_le_right _ _).trans (min_le_left _ _)).trans (hme.trans hd)
        · have hr2' : 2 ≤ r := le_of_not_ge hr2
          have hd2 := defectKernel_ge_two hB hq0 hq1 hr2'
          have hm2 : m ≤ defectKernel B q 2 := by
            change defectSlope B q₁ q₂ ≤ defectKernel B q 2
            convert defectKernel_linear_lower hB hq₁ hq.1 hq.2 hq₂
              (show (2 : ℝ) ∈ Set.Icc 1 2 by norm_num) using 1; norm_num
          have hd : m ≤ defectKernel B q r + 2 * K * max (1 - r) 0 := by
            dsimp [K] at hcorr ⊢
            linarith
          exact ((min_le_right _ _).trans (min_le_right _ _)).trans hd
    have hrhs : 0 ≤ defectKernel B q r + 2 * K * max (1 - r) 0 := hδ.le.trans hdelta
    calc
      |F r - F 1| ≤ |F r| + |F 1| := abs_sub _ _
      _ ≤ KF + |F 1| := add_le_add_left (hFbound r hr) _
      _ = CG * δ := hmulCG.symm
      _ ≤ CG * (defectKernel B q r + 2 * K * max (1 - r) 0) :=
        mul_le_mul_of_nonneg_left hdelta hCG
      _ ≤ CF * (defectKernel B q r + 2 * K * max (1 - r) 0) :=
        mul_le_mul_of_nonneg_right hCFG hrhs

/-- The exact one-generation recurrence for the rescaled real transform, including its
Mellin-defect term.
This proves `DiamondPinning.transform_recurrence` (in
`DiamondPinning.Statements.Scaling`). -/
theorem transform_recurrence_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {N : ℝ} (hN : 0 < N) {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    transformAt μ B h N (n + 1) s =
      Real.exp (s / N) * transformAt μ B h N n s +
        Real.exp (s / N) / (2 * N) * transformAt μ B h N n s ^ 2 -
        N / 2 * Real.exp (s / N) * defectMean μ B h n (weightExponent B N s) := by
  let q := weightExponent B N s
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hq1 : q ≤ 1 := by
    dsimp [q, weightExponent]
    have hnneg : 0 ≤ s / (Real.log B * N) := div_nonneg hs (mul_nonneg hlogB.le hN.le)
    linarith [theta_lt_one hB]
  have hrec := realMoment_succ hpos hmean hB h hn hq1
  have he : 2 * B ^ (-q) = Real.exp (s / N) := weight_rpow_neg hB hN rfl
  have hBB : B ^ (-q) * B ^ q = 1 := by
    rw [← Real.rpow_add (by linarith : 0 < B)]
    simp
  unfold transformAt
  change N * (realMoment μ B h (n + 1) q - 1) = _
  rw [hrec, ← he]
  calc
    N * (B ^ (-q) * (realMoment μ B h n q ^ 2 + B ^ q - 1 - defectMean μ B h n q) - 1) =
        N * (B ^ (-q) * (realMoment μ B h n q ^ 2 + B ^ q - 1 - defectMean μ B h n q) -
          B ^ (-q) * B ^ q) := by rw [hBB]
    _ = 2 * B ^ (-q) * (N * (realMoment μ B h n q - 1)) +
        2 * B ^ (-q) / (2 * N) * (N * (realMoment μ B h n q - 1)) ^ 2 -
        N / 2 * (2 * B ^ (-q)) * defectMean μ B h n q := by
      field_simp [hN.ne']
      ring

/-- The geometric lower bound and the monotonicity comparison of transforms above the reference
weight.
This proves `DiamondPinning.transform_floor` (in
`DiamondPinning.Statements.Scaling`). -/
theorem transform_floor_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    ∃ C : ℝ, ∀ (h N : ℝ) (n : ℕ) (s₀ s : ℝ), 0 < N → 0 ≤ s₀ → s₀ ≤ s →
      0 ≤ weightExponent B N s →
      -(C * N * (2 / B) ^ n) ≤ transformAt μ B h N n s ∧
        transformAt μ B h N n s ≤ transformAt μ B h N n s₀ + C * N * (2 / B) ^ n := by
  refine ⟨1, fun h N n s₀ s hN hs₀ hss hs => ?_⟩
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hden : 0 < Real.log B * N := mul_pos hlogB hN
  have hq1 : weightExponent B N s ≤ 1 := by
    have hsdiv : 0 ≤ s / (Real.log B * N) := div_nonneg (hs₀.trans hss) hden.le
    unfold weightExponent
    linarith [theta_lt_one hB]
  have hq₀0 : 0 ≤ weightExponent B N s₀ := by
    unfold weightExponent at hs ⊢
    have hdiv : s₀ / (Real.log B * N) ≤ s / (Real.log B * N) :=
      div_le_div_of_nonneg_right hss hden.le
    linarith
  have hq₀1 : weightExponent B N s₀ ≤ 1 := by
    have hsdiv : 0 ≤ s₀ / (Real.log B * N) := div_nonneg hs₀ hden.le
    unfold weightExponent
    linarith [theta_lt_one hB]
  have hqq : weightExponent B N s ≤ weightExponent B N s₀ := by
    unfold weightExponent
    have hdiv : s₀ / (Real.log B * N) ≤ s / (Real.log B * N) :=
      div_le_div_of_nonneg_right hss hden.le
    linarith
  let : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have hri := integrable_rpow_lawR hpos hmean hB h n hs hq1
  have hri₀ := integrable_rpow_lawR hpos hmean hB h n hq₀0 hq₀1
  have hb : 0 ≤ floorSeq B n := floorSeq_nonneg hB n
  have hb1 : floorSeq B n ≤ 1 := floorSeq_le_one hB n
  have hρ : 0 ≤ (2 / B) ^ n := by positivity
  have hlow : 1 - (2 / B) ^ n ≤ realMoment μ B h n (weightExponent B N s) := by
    have hm := integral_mono_ae (integrable_const (floorSeq B n)) hri (by
      filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx
      have hexp : floorSeq B n ≤ x ^ weightExponent B N s := by
        calc
          floorSeq B n ≤ floorSeq B n ^ weightExponent B N s :=
            Real.self_le_rpow_of_le_one hb hb1 hq1
          _ ≤ x ^ weightExponent B N s := Real.rpow_le_rpow hb hx hs
      exact hexp)
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hm
    change 1 - (2 / B) ^ n ≤ ∫ x : ℝ, x ^ weightExponent B N s ∂lawR μ B h n
    have hf := one_sub_floorSeq_le hB n
    linarith
  have hupp : realMoment μ B h n (weightExponent B N s) -
      realMoment μ B h n (weightExponent B N s₀) ≤ (2 / B) ^ n := by
    have hm := integral_mono_ae (hri.sub hri₀) (integrable_const ((2 / B) ^ n)) (by
      filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx
      by_cases hx1 : 1 ≤ x
      · have hd : x ^ weightExponent B N s ≤ x ^ weightExponent B N s₀ :=
          Real.rpow_le_rpow_of_exponent_le hx1 hqq
        change x ^ weightExponent B N s - x ^ weightExponent B N s₀ ≤ (2 / B) ^ n
        linarith
      · have hx1' : x ≤ 1 := le_of_not_ge hx1
        have hxq : x ^ weightExponent B N s ≤ 1 := Real.rpow_le_one (hb.trans hx) hx1' hs
        have hx0q : x ≤ x ^ weightExponent B N s₀ :=
          Real.self_le_rpow_of_le_one (hb.trans hx) hx1' hq₀1
        have hf := one_sub_floorSeq_le hB n
        change x ^ weightExponent B N s - x ^ weightExponent B N s₀ ≤ (2 / B) ^ n
        linarith)
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hm
    change (∫ x : ℝ, (x ^ weightExponent B N s - x ^ weightExponent B N s₀)
      ∂lawR μ B h n) ≤ (2 / B) ^ n at hm
    rw [integral_sub hri hri₀] at hm
    exact hm
  constructor
  · unfold transformAt
    nlinarith
  · unfold transformAt
    nlinarith

/-- The rescaled measure is finite and assigns zero mass to the negative half-line.
This proves `DiamondPinning.rescaledMeasure_finite` (in
`DiamondPinning.Statements.Scaling`). -/
theorem rescaledMeasure_finite_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {N : ℝ} (hN : 0 < N) (n : ℕ) :
    IsFiniteMeasure (rescaledMeasure μ B h N n) ∧
      rescaledMeasure μ B h N n (Set.Iio 0) = 0 := by
  let : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have hi : Integrable (fun x : ℝ => N * (x ^ theta B - 1))
      ((lawR μ B h n).restrict (Set.Ici 1)) :=
    (((integrable_rpow_lawR hpos hmean hB h n (theta_pos hB).le
      (theta_lt_one hB).le).sub (integrable_const 1)).const_mul N).restrict
  have hfin : IsFiniteMeasure (((lawR μ B h n).restrict (Set.Ici 1)).withDensity
      fun x => ENNReal.ofReal (N * (x ^ theta B - 1))) :=
    isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  constructor
  · let := hfin
    unfold rescaledMeasure
    infer_instance
  · unfold rescaledMeasure
    rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
    have hsub : (fun x : ℝ => Real.log x / (Real.log B * N)) ⁻¹' Set.Iio 0 ⊆
        (Set.Ici (1 : ℝ))ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_Ici, not_le]
      by_contra hx1
      have hx1' : 1 ≤ x := le_of_not_gt hx1
      have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1'
      have hden : 0 < Real.log B * N := mul_pos (Real.log_pos (by linarith)) hN
      exact (not_lt_of_ge (div_nonneg hlog hden.le)) hx
    apply measure_mono_null hsub
    rw [withDensity_apply _ measurableSet_Ici.compl]
    have hem : Set.Iio (1 : ℝ) ∩ Set.Ici 1 = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false,
        iff_false, not_and]
      exact fun h1 h2 => (not_lt_of_ge h2) h1
    simp [hem]

/-- Uniformly on compact exponent intervals, the negative part of the Mellin defect is at most a
geometric floor error.
This proves `DiamondPinning.defectMean_lower` (in
`DiamondPinning.Statements.Scaling`). -/
theorem defectMean_lower_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    ∀ q₁ q₂ : ℝ, 0 < q₁ → q₂ < 1 → ∃ C : ℝ, ∀ (h : ℝ) (n : ℕ), 1 ≤ n →
      ∀ q ∈ Set.Icc q₁ q₂, -(C * (2 / B) ^ n) ≤ defectMean μ B h n q := by
  intro q₁ q₂ hq₁ hq₂
  let C := 2 * (floorSeq B 1 ^ 2) ^ (q₁ - 1)
  refine ⟨C, fun h n hn q hq => ?_⟩
  let : IsProbabilityMeasure (productLaw μ B h n) := isProbabilityMeasure_productLaw B h n
  have hi := integrable_defectKernel hpos hmean hB h n
    (le_trans hq₁.le hq.1) (hq.2.trans hq₂.le)
  rw [defectMean]
  have hmono := integral_mono_ae (integrable_const (-(C * (2 / B) ^ n))) hi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hmono
  apply hmono
  filter_upwards [ae_floor_sq_productLaw hpos hB h n] with r hr
  have hb : 0 < floorSeq B 1 ^ 2 := sq_pos_of_pos (floorSeq_one_pos hB)
  have hb1 : floorSeq B 1 ^ 2 < 1 := by nlinarith [floorSeq_lt_one hB 1, floorSeq_one_pos hB]
  have hρ : 0 ≤ (2 / B) ^ n := by positivity
  have hbf : 1 - floorSeq B n ^ 2 ≤ 2 * (2 / B) ^ n := by
    have hf := one_sub_floorSeq_le hB n
    have hb0 := floorSeq_nonneg hB n
    nlinarith
  have hb1r : floorSeq B 1 ^ 2 ≤ r := by
    apply le_trans _ hr
    have hm := floorSeq_monotone hB hn
    nlinarith [floorSeq_nonneg hB 1, floorSeq_nonneg hB n]
  exact defectKernel_lower hB hb hb1 (hq₁.trans_le hq.1) (hq.2.trans_lt hq₂)
    hq.1 hρ hb1r hr hbf

/-- For a bounded function differentiable near one, the product-kernel expectation is controlled
by the Mellin defect and a geometric floor error.
This proves `DiamondPinning.kernel_comparison` (in
`DiamondPinning.Statements.Scaling`). -/
theorem kernel_comparison_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    ∀ q₁ q₂ : ℝ, 0 < q₁ → q₂ < 1 → ∃ C : ℝ, ∀ F : ℝ → ℝ, Measurable F →
      (∃ K : ℝ, ∀ r : ℝ, floorSeq B 1 ^ 2 ≤ r → |F r| ≤ K) →
      (∀ᶠ r in 𝓝 (1 : ℝ), DifferentiableAt ℝ F r) →
      ∃ CF : ℝ, ∀ (h : ℝ) (n : ℕ), 1 ≤ n → ∀ q₀ ∈ Set.Icc q₁ q₂,
        |kernelExpectation μ B h n F - F 1| ≤
          CF * (defectMean μ B h n q₀ + C * (2 / B) ^ n) := by
  intro q₁ q₂ hq₁ hq₂
  let b := floorSeq B 1 ^ 2
  let K := 2 * b ^ (q₁ - 1)
  let C := 2 * K
  have hb : 0 < b := sq_pos_of_pos (floorSeq_one_pos hB)
  have hb1 : b < 1 := by
    change floorSeq B 1 ^ 2 < 1
    nlinarith [floorSeq_lt_one hB 1, floorSeq_one_pos hB]
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : C = 4 * b ^ (q₁ - 1) := by dsimp [C, K]; ring
  refine ⟨C, fun F hFm hFb hFd => ?_⟩
  obtain ⟨KF, hKF⟩ := hFb
  obtain ⟨CF, hCF⟩ := kernel_pointwise_comparison F hB hb hb1 hq₁ hq₂ KF hKF
    hFd.self_of_nhds
  refine ⟨CF, fun h n hn q₀ hq₀ => ?_⟩
  let : IsProbabilityMeasure (productLaw μ B h n) := isProbabilityMeasure_productLaw B h n
  have hFi : Integrable F (productLaw μ B h n) := by
    apply (integrable_const KF).mono' hFm.aestronglyMeasurable
    filter_upwards [ae_floorSeq_one_sq_le_productLaw hpos hB h hn] with r hr
    exact hKF r hr
  have hdi := integrable_defectKernel hpos hmean hB h n
    (hq₁.le.trans hq₀.1) (hq₀.2.trans hq₂.le)
  have hpi : Integrable (fun r : ℝ => max (1 - r) 0) (productLaw μ B h n) :=
    ((integrable_const 1).sub (integrable_id_productLaw hpos hmean hB h n)).pos_part
  have hpri : Integrable (fun r => defectKernel B q₀ r + K * max (1 - r) 0)
      (productLaw μ B h n) := hdi.add (hpi.const_mul K)
  have hai : Integrable (fun r => |F r - F 1|) (productLaw μ B h n) :=
    (hFi.sub (integrable_const (F 1))).abs
  have hmono : (∫ r, |F r - F 1| ∂productLaw μ B h n) ≤
      ∫ r, CF * (defectKernel B q₀ r + K * max (1 - r) 0) ∂productLaw μ B h n := by
    apply integral_mono_ae hai (hpri.const_mul CF)
    filter_upwards [ae_floorSeq_one_sq_le_productLaw hpos hB h hn] with r hr
    exact hCF q₀ hq₀ r hr
  have hJ : (∫ r : ℝ, max (1 - r) 0 ∂productLaw μ B h n) ≤ 2 * (2 / B) ^ n := by
    have hm := integral_mono_ae hpi (integrable_const (2 * (2 / B) ^ n)) (by
      filter_upwards [ae_floor_sq_productLaw hpos hB h n] with r hr
      have hf := one_sub_floorSeq_le hB n
      have hb0 := floorSeq_nonneg hB n
      have hp : 0 ≤ (2 / B) ^ n := by positivity
      exact max_le (by nlinarith) (by positivity))
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hm
  have hcf0 : 0 ≤ CF := by
    have hp := hCF q₀ hq₀ 2 (hb1.le.trans (by norm_num))
    have hm0 : 0 < defectSlope B q₁ q₂ := defectSlope_pos hB hq₁ hq₂
    have hm2 : defectSlope B q₁ q₂ ≤ defectKernel B q₀ 2 := by
      convert defectKernel_linear_lower hB hq₁ hq₀.1 hq₀.2 hq₂
        (show (2 : ℝ) ∈ Set.Icc 1 2 by norm_num) using 1; norm_num
    have hpos : 0 < defectKernel B q₀ 2 + K * max (1 - 2) 0 := by
      have hc : 0 ≤ K * max (1 - 2) 0 := by positivity
      linarith
    have hnon : 0 ≤ CF * (defectKernel B q₀ 2 + K * max (1 - 2) 0) :=
      (abs_nonneg _).trans hp
    exact nonneg_of_mul_nonneg_left hnon hpos
  calc
    |kernelExpectation μ B h n F - F 1| = |∫ r, (F r - F 1) ∂productLaw μ B h n| := by
      rw [integral_sub hFi (integrable_const _)]
      simp [kernelExpectation]
    _ ≤ ∫ r, |F r - F 1| ∂productLaw μ B h n := abs_integral_le_integral_abs
    _ ≤ ∫ r, CF * (defectKernel B q₀ r + K * max (1 - r) 0) ∂productLaw μ B h n := hmono
    _ = CF * (defectMean μ B h n q₀ +
        K * ∫ r : ℝ, max (1 - r) 0 ∂productLaw μ B h n) := by
      rw [integral_const_mul, integral_add hdi (hpi.const_mul K), integral_const_mul]
      rfl
    _ ≤ CF * (defectMean μ B h n q₀ + C * (2 / B) ^ n) := by
      have hine : defectMean μ B h n q₀ +
          K * ∫ r : ℝ, max (1 - r) 0 ∂productLaw μ B h n ≤
          defectMean μ B h n q₀ + C * (2 / B) ^ n := by
        have hKJ := mul_le_mul_of_nonneg_left hJ hK.le
        dsimp [C]
        linarith
      exact mul_le_mul_of_nonneg_left hine hcf0

end DiamondPinning
