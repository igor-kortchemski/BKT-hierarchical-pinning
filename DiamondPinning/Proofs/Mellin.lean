module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Model.Moments
public import DiamondPinning.Model.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.ComplexMGF

/-!
# Holomorphy and bounds for the Mellin correction

This module writes the correction `C_n(z)` as a shifted-moment integral,
proves its holomorphy on `Re z < 1`, and obtains bounds uniform in `n` on
compact subsets. This proves `lem:mellin-correction` and equation `eq:C`,
`source/critical.tex` lines 56–77.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Asymptotics
open scoped Interval

private theorem isProbabilityMeasure_productLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (B h : ℝ) (n : ℕ) : IsProbabilityMeasure (productLaw μ B h n) := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  rw [productLaw]
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

private theorem ae_floor_productLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ s ∂(productLaw μ B h n), (floorSeq B 1) ^ 2 ≤ s := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  rw [productLaw, ae_map_iff (by fun_prop) measurableSet_Ici]
  rw [Measure.ae_prod_iff_ae_ae (by measurability)]
  have hfloor := ae_floorSeq_le_lawR hpos hB h n
  filter_upwards [hfloor] with x hx
  filter_upwards [hfloor] with y hy
  have hb : 0 ≤ floorSeq B 1 := (floorSeq_nonneg hB 1)
  have hb1 : floorSeq B 1 ≤ floorSeq B n := floorSeq_one_le hB hn
  calc
    (floorSeq B 1) ^ 2 = floorSeq B 1 * floorSeq B 1 := pow_two _
    _ ≤ x * y := mul_le_mul (hb1.trans hx) (hb1.trans hy) hb (hb1.trans hx |>.trans' hb)

private theorem ae_pos_productLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ s ∂(productLaw μ B h n), 0 < s := by
  filter_upwards [ae_floor_productLaw hpos hB h hn] with s hs
  have hb : 0 < floorSeq B 1 := floorSeq_one_pos hB
  exact (sq_pos_of_pos hb).trans_le hs

private theorem integrable_id_productLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : Integrable (fun s : ℝ => s) (productLaw μ B h n) := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have hi := integrable_lawR_of hpos hmean hB h n
  rw [productLaw]
  apply (integrable_map_measure measurable_id.aestronglyMeasurable (by fun_prop)).2
  simpa [Function.comp_def] using hi.mul_prod hi

/-- Real exponential moments of `log (x + d)` below the first moment, using only a
positive almost sure floor and integrability of `x + d`. -/
private theorem integrable_exp_mul_log_add_of_floor {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {b d q : ℝ} (hb : 0 < b) (hd : 0 ≤ d) (hbx : ∀ᵐ x ∂ν, b ≤ x)
    (hi : Integrable (fun x : ℝ => x + d) ν) (hq : q < 1) :
    Integrable (fun x : ℝ => Real.exp (q * Real.log (x + d))) ν := by
  have hpos : ∀ᵐ x ∂ν, 0 < x + d := by
    filter_upwards [hbx] with x hx
    have : 0 < b + d := add_pos_of_pos_of_nonneg hb hd
    linarith
  have hlow : Integrable (fun x : ℝ => Real.exp ((q - 1) * Real.log (x + d))) ν := by
    apply (integrable_const ((b + d) ^ (q - 1))).mono'
      (Real.measurable_exp.comp (measurable_const.mul
        (Real.measurable_log.comp (measurable_id.add_const d)))).aestronglyMeasurable
    filter_upwards [hbx] with x hx
    have hxpos : 0 < x + d := by
      have : 0 < b + d := add_pos_of_pos_of_nonneg hb hd
      linarith
    change |Real.exp ((q - 1) * Real.log (x + d))| ≤ (b + d) ^ (q - 1)
    rw [abs_of_pos (Real.exp_pos _)]
    rw [Real.rpow_def_of_pos (add_pos_of_pos_of_nonneg hb hd)]
    apply Real.exp_le_exp.mpr
    have hlog : Real.log (b + d) ≤ Real.log (x + d) := by
      apply Real.log_le_log (by positivity)
      linarith
    nlinarith
  have hupp : Integrable (fun x : ℝ => Real.exp (1 * Real.log (x + d))) ν := by
    apply hi.congr
    filter_upwards [hpos] with x hx
    simp [Real.exp_log hx]
  exact ProbabilityTheory.integrable_exp_mul_of_le_of_le hlow hupp (by linarith) hq.le

private theorem integrable_rpow_add_of_floor {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {b d q : ℝ} (hb : 0 < b) (hd : 0 ≤ d) (hbx : ∀ᵐ x ∂ν, b ≤ x)
    (hi : Integrable (fun x : ℝ => x + d) ν) (hq : q < 1) :
    Integrable (fun x : ℝ => (x + d) ^ q) ν := by
  have hpos : ∀ᵐ x ∂ν, 0 < x + d := by
    filter_upwards [hbx] with x hx
    have : 0 < b + d := add_pos_of_pos_of_nonneg hb hd
    linarith
  apply (integrable_exp_mul_log_add_of_floor hb hd hbx hi hq).congr
  filter_upwards [hpos] with x hx
  rw [Real.rpow_def_of_pos hx, mul_comm]

private theorem integrable_cpow_add_of_floor {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {b d : ℝ} {z : ℂ} (hb : 0 < b) (hd : 0 ≤ d) (hbx : ∀ᵐ x ∂ν, b ≤ x)
    (hi : Integrable (fun x : ℝ => x + d) ν) (hz : z.re < 1) :
    Integrable (fun x : ℝ => ((x + d : ℝ) : ℂ) ^ z) ν := by
  have hpos : ∀ᵐ x ∂ν, 0 < x + d := by
    filter_upwards [hbx] with x hx
    have : 0 < b + d := add_pos_of_pos_of_nonneg hb hd
    linarith
  have hm : AEStronglyMeasurable
      (fun x : ℝ => Complex.exp (z * (Real.log (x + d) : ℂ))) ν :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (Real.measurable_log.comp (measurable_id.add_const d))))).aestronglyMeasurable
  have heq : (fun x : ℝ => Complex.exp (z * (Real.log (x + d) : ℂ))) =ᵐ[ν]
      (fun x : ℝ => ((x + d : ℝ) : ℂ) ^ z) := by
    filter_upwards [hpos] with x hx
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne')]
    rw [← Complex.ofReal_log hx.le]
    congr 1
    simp [mul_comm]
  rw [← integrable_norm_iff (hm.congr heq)]
  apply (integrable_rpow_add_of_floor hb hd hbx hi hz).congr
  filter_upwards [hpos] with x hx
  exact (Complex.norm_cpow_eq_rpow_re_of_pos hx z).symm

private theorem integral_cpow_add_eq_complexMGF {ν : Measure ℝ}
    {d : ℝ} (hpos : ∀ᵐ x ∂ν, 0 < x + d) (z : ℂ) :
    (∫ x : ℝ, ((x + d : ℝ) : ℂ) ^ z ∂ν) =
      ProbabilityTheory.complexMGF (fun x : ℝ => Real.log (x + d)) ν z := by
  rw [ProbabilityTheory.complexMGF]
  apply integral_congr_ae
  filter_upwards [hpos] with x hx
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne')]
  rw [← Complex.ofReal_log hx.le]
  congr 1
  simp [mul_comm]

private theorem mem_interior_integrableExpSet_log_add {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {b d : ℝ} {z : ℂ} (hb : 0 < b) (hd : 0 ≤ d) (hbx : ∀ᵐ x ∂ν, b ≤ x)
    (hi : Integrable (fun x : ℝ => x + d) ν) (hz : z.re < 1) :
    z.re ∈ interior (ProbabilityTheory.integrableExpSet (fun x : ℝ => Real.log (x + d)) ν) := by
  have hsub : Set.Iio 1 ⊆ ProbabilityTheory.integrableExpSet
      (fun x : ℝ => Real.log (x + d)) ν := by
    intro q hq
    exact integrable_exp_mul_log_add_of_floor hb hd hbx hi hq
  exact (interior_maximal hsub isOpen_Iio) hz

private theorem cpow_add_differentiableAt {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {b d : ℝ} {z : ℂ} (hb : 0 < b) (hd : 0 ≤ d) (hbx : ∀ᵐ x ∂ν, b ≤ x)
    (hi : Integrable (fun x : ℝ => x + d) ν) (hpos : ∀ᵐ x ∂ν, 0 < x + d)
    (hz : z.re < 1) :
    DifferentiableAt ℂ (fun z : ℂ => ∫ x : ℝ, ((x + d : ℝ) : ℂ) ^ z ∂ν) z := by
  have heq : (fun z : ℂ => ∫ x : ℝ, ((x + d : ℝ) : ℂ) ^ z ∂ν) =
      ProbabilityTheory.complexMGF (fun x : ℝ => Real.log (x + d)) ν := by
    funext w
    exact integral_cpow_add_eq_complexMGF hpos w
  rw [heq]
  exact (ProbabilityTheory.hasDerivAt_complexMGF
    (mem_interior_integrableExpSet_log_add hb hd hbx hi hz)).differentiableAt

private theorem cpow_ftc {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (z : ℂ) :
    z * (∫ t in (0 : ℝ)..c, (((s + t : ℝ) : ℂ) ^ (z - 1))) =
      (((s + c : ℝ) : ℂ) ^ z) - (s : ℂ) ^ z := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) c,
      HasDerivAt (fun u : ℝ => (((s + u : ℝ) : ℂ) ^ z))
        (z * (((s + t : ℝ) : ℂ) ^ (z - 1))) t := by
    intro t ht
    have ht0 : 0 ≤ t := by
      rw [Set.uIcc_of_le hc.le] at ht
      exact ht.1
    have hst : 0 < s + t := by linarith
    have hd := ((hasDerivAt_const (t : ℂ) (s : ℂ)).add
      (hasDerivAt_id (t : ℂ))).cpow_const (c := z)
      (by simpa using Complex.ofReal_mem_slitPlane.mpr hst)
    simpa only [Pi.add_apply, id_eq, zero_add, mul_one, Complex.ofReal_add] using hd.comp_ofReal
  have hcont : ContinuousOn (fun t : ℝ => z * (((s + t : ℝ) : ℂ) ^ (z - 1)))
      (Set.uIcc (0 : ℝ) c) := by
    apply ContinuousOn.const_mul
    intro t ht
    have ht0 : 0 ≤ t := by
      rw [Set.uIcc_of_le hc.le] at ht
      exact ht.1
    apply ContinuousAt.continuousWithinAt
    simpa [Function.comp_def] using
      (Complex.continuousAt_ofReal_cpow_const (s + t) (z - 1)
        (Or.inr (by positivity : s + t ≠ 0))).comp (continuousAt_const.add continuousAt_id)
  rw [← intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp

private theorem integrable_shifted_cpow_prod {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ} (hn : 1 ≤ n)
    {z : ℂ} (hz : z.re < 1) :
    Integrable (Function.uncurry (fun t s : ℝ => (((s + t : ℝ) : ℂ) ^ (z - 1))))
      ((volume.restrict (Set.uIoc (0 : ℝ) (B - 1))).prod (productLaw μ B h n)) := by
  letI : IsProbabilityMeasure (productLaw μ B h n) := isProbabilityMeasure_productLaw B h n
  letI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) (B - 1))) := ⟨by
    rw [Measure.restrict_apply_univ, Set.uIoc]
    exact measure_Ioc_lt_top⟩
  let b := (floorSeq B 1) ^ 2
  have hb : 0 < b := sq_pos_of_pos (floorSeq_one_pos hB)
  have hbpos : ∀ᵐ s ∂(productLaw μ B h n), b ≤ s := ae_floor_productLaw hpos hB h hn
  have hbase : Measurable (fun p : ℝ × ℝ => p.2 + p.1) := measurable_snd.add measurable_fst
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Complex.exp ((z - 1) * (Real.log (p.2 + p.1) : ℂ)))
      ((volume.restrict (Set.uIoc (0 : ℝ) (B - 1))).prod (productLaw μ B h n)) :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (Real.measurable_log.comp hbase)))).aestronglyMeasurable
  have hpos_prod : ∀ᵐ p ∂((volume.restrict (Set.uIoc (0 : ℝ) (B - 1))).prod
      (productLaw μ B h n)), 0 < p.2 + p.1 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
        (ae_restrict_mem measurableSet_uIoc),
      Measure.quasiMeasurePreserving_snd.ae hbpos] with p hp hs
    have ht : 0 ≤ p.1 := by
      rw [Set.uIoc_of_le (by linarith : (0 : ℝ) ≤ B - 1)] at hp
      exact hp.1.le
    have hspos : 0 < p.2 := hb.trans_le hs
    linarith
  have heq : (fun p : ℝ × ℝ => Complex.exp ((z - 1) * (Real.log (p.2 + p.1) : ℂ))) =ᵐ[
      (volume.restrict (Set.uIoc (0 : ℝ) (B - 1))).prod (productLaw μ B h n)]
      (Function.uncurry (fun t s : ℝ => (((s + t : ℝ) : ℂ) ^ (z - 1)))) := by
    filter_upwards [hpos_prod] with p hp
    change Complex.exp ((z - 1) * (Real.log (p.2 + p.1) : ℂ)) =
      (((p.2 + p.1 : ℝ) : ℂ) ^ (z - 1))
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne')]
    rw [← Complex.ofReal_log hp.le]
    congr 1
    simp [mul_comm]
  apply (integrable_const (b ^ (z - 1).re)).mono' (hm.congr heq)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem measurableSet_uIoc),
    Measure.quasiMeasurePreserving_snd.ae hbpos] with p hp hs
  have ht : 0 ≤ p.1 := by
    rw [Set.uIoc_of_le (by linarith : (0 : ℝ) ≤ B - 1)] at hp
    exact hp.1.le
  have hbp : b ≤ p.2 + p.1 := by linarith
  have hpos' : 0 < p.2 + p.1 := hb.trans_le hbp
  change ‖((p.2 + p.1 : ℝ) : ℂ) ^ (z - 1)‖ ≤ b ^ (z - 1).re
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos']
  exact Real.rpow_le_rpow_of_nonpos hb hbp (by simp only [Complex.sub_re, Complex.one_re]; linarith)

/-- The correction is `z` times the shifted-moment integral with exponent
`z - 1`, giving equation `eq:C` and proving `DiamondPinning.correction_eq` (in
`DiamondPinning.Statements.Critical`). -/
theorem correction_eq_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z.re < 1) :
    correction μ B h n z = z * shiftedMomentIntegral μ B h n (z - 1) := by
  letI : IsProbabilityMeasure (productLaw μ B h n) := isProbabilityMeasure_productLaw B h n
  have hc : 0 < B - 1 := by linarith
  have hb : 0 < (floorSeq B 1) ^ 2 := sq_pos_of_pos (floorSeq_one_pos hB)
  have hpoint : ∀ᵐ s ∂(productLaw μ B h n), 0 < s := ae_pos_productLaw hpos hB h hn
  calc
    correction μ B h n z = ∫ s, z * (∫ t in (0 : ℝ)..(B - 1),
        (((s + t : ℝ) : ℂ) ^ (z - 1))) ∂(productLaw μ B h n) := by
      unfold correction
      apply integral_congr_ae
      filter_upwards [hpoint] with s hs
      exact (cpow_ftc hs hc z).symm
    _ = z * (∫ s, (∫ t in (0 : ℝ)..(B - 1),
        (((s + t : ℝ) : ℂ) ^ (z - 1))) ∂(productLaw μ B h n)) := by
      rw [integral_const_mul]
    _ = z * (∫ t in (0 : ℝ)..(B - 1), ∫ s,
        (((s + t : ℝ) : ℂ) ^ (z - 1)) ∂(productLaw μ B h n)) := by
      congr 1
      exact (intervalIntegral_integral_swap (integrable_shifted_cpow_prod hpos hB h hn hz)).symm
    _ = z * shiftedMomentIntegral μ B h n (z - 1) := by
      rfl

/-- The correction is holomorphic on the half-plane `Re z < 1`, proving
`DiamondPinning.differentiableOn_correction` (in `DiamondPinning.Statements.Critical`). -/
theorem differentiableOn_correction_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {n : ℕ} (hn : 1 ≤ n) :
    DifferentiableOn ℂ (correction μ B h n) {z : ℂ | z.re < 1} := by
  letI : IsProbabilityMeasure (productLaw μ B h n) := isProbabilityMeasure_productLaw B h n
  let b := (floorSeq B 1) ^ 2
  have hb : 0 < b := sq_pos_of_pos (floorSeq_one_pos hB)
  have hbx : ∀ᵐ s ∂(productLaw μ B h n), b ≤ s := ae_floor_productLaw hpos hB h hn
  have hi : Integrable (fun s : ℝ => s) (productLaw μ B h n) :=
    integrable_id_productLaw hpos hmean hB h n
  have hspos : ∀ᵐ s ∂(productLaw μ B h n), 0 < s := ae_pos_productLaw hpos hB h hn
  intro z hz
  have hc : 0 ≤ B - 1 := by linarith
  have hic : Integrable (fun s : ℝ => s + (B - 1)) (productLaw μ B h n) := by
    simpa using hi.add (integrable_const (B - 1))
  have hscpos : ∀ᵐ s ∂(productLaw μ B h n), 0 < s + (B - 1) := by
    filter_upwards [hspos] with s hs
    linarith
  have hi0 : Integrable (fun s : ℝ => s + 0) (productLaw μ B h n) := by simpa using hi
  have hs0pos : ∀ᵐ s ∂(productLaw μ B h n), 0 < s + 0 := by simpa using hspos
  have hicpow : Integrable (fun s : ℝ => ((s + (B - 1) : ℝ) : ℂ) ^ z)
      (productLaw μ B h n) := integrable_cpow_add_of_floor hb hc hbx hic hz
  have hi0cpow0 : Integrable (fun s : ℝ => ((s + 0 : ℝ) : ℂ) ^ z)
      (productLaw μ B h n) := integrable_cpow_add_of_floor hb le_rfl hbx hi0 hz
  have hi0cpow : Integrable (fun s : ℝ => (s : ℂ) ^ z) (productLaw μ B h n) := by
    simpa using hi0cpow0
  have hdsc : DifferentiableAt ℂ (fun w : ℂ => ∫ s : ℝ,
      ((s + (B - 1) : ℝ) : ℂ) ^ w ∂(productLaw μ B h n)) z :=
    cpow_add_differentiableAt hb hc hbx hic hscpos hz
  have hds00 : DifferentiableAt ℂ (fun w : ℂ => ∫ s : ℝ,
      ((s + 0 : ℝ) : ℂ) ^ w ∂(productLaw μ B h n)) z :=
    cpow_add_differentiableAt hb le_rfl hbx hi0 hs0pos hz
  have hds0 : DifferentiableAt ℂ (fun w : ℂ => ∫ s : ℝ,
      (s : ℂ) ^ w ∂(productLaw μ B h n)) z := by
    simpa using hds00
  apply (hdsc.sub hds0).differentiableWithinAt.congr_of_eventuallyEq_of_mem _ hz
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hicpow' : Integrable (fun s : ℝ => ((s + (B - 1) : ℝ) : ℂ) ^ w)
      (productLaw μ B h n) := integrable_cpow_add_of_floor hb hc hbx hic hw
  have hi0cpow0' : Integrable (fun s : ℝ => ((s + 0 : ℝ) : ℂ) ^ w)
      (productLaw μ B h n) := integrable_cpow_add_of_floor hb le_rfl hbx hi0 hw
  have hi0cpow' : Integrable (fun s : ℝ => (s : ℂ) ^ w) (productLaw μ B h n) := by
    simpa using hi0cpow0'
  exact integral_sub hicpow' hi0cpow'

private theorem cpow_sub_one_norm_le {R b x : ℝ} {z : ℂ} (hb : 0 < b) (hbx : b ≤ x)
    (hR0 : 0 ≤ R) (hzR : ‖z‖ ≤ R) (hz : z.re < 1) :
    ‖(x : ℂ) ^ (z - 1)‖ ≤ 1 + b ^ (-R - 1) := by
  have hx : 0 < x := hb.trans_le hbx
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : -R ≤ z.re := by
    have ha := (Complex.abs_re_le_norm z).trans hzR
    linarith [neg_abs_le z.re]
  have hq : -R - 1 ≤ z.re - 1 := by linarith
  by_cases hx1 : 1 ≤ x
  · have hle : x ^ (z.re - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    exact hle.trans (le_add_of_nonneg_right (Real.rpow_nonneg hb.le _))
  · have hx1' : x ≤ 1 := le_of_not_ge hx1
    calc
      x ^ (z.re - 1) ≤ x ^ (-R - 1) :=
        Real.rpow_le_rpow_of_exponent_ge hx hx1' hq
      _ ≤ b ^ (-R - 1) := Real.rpow_le_rpow_of_nonpos hb hbx (by linarith)
      _ ≤ 1 + b ^ (-R - 1) := le_add_of_nonneg_left zero_le_one

/-- On every compact subset of `Re z < 1`, the correction has a norm bound
uniform in the height, proving `DiamondPinning.correction_bounded` (in
`DiamondPinning.Statements.Critical`). -/
theorem correction_bounded_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ {z : ℂ | z.re < 1}) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ z ∈ K, ‖correction μ B h n z‖ ≤ C := by
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  let R := max r 0
  have hR0 : 0 ≤ R := le_max_right _ _
  have hzR : ∀ z ∈ K, ‖z‖ ≤ R := fun z hz => (hr z hz).trans (le_max_left _ _)
  let b := (floorSeq B 1) ^ 2
  let M := 1 + b ^ (-R - 1)
  refine ⟨R * (M * (B - 1)), ?_⟩
  intro n hn z hzK
  letI : IsProbabilityMeasure (productLaw μ B h n) := isProbabilityMeasure_productLaw B h n
  have hb : 0 < b := sq_pos_of_pos (floorSeq_one_pos hB)
  have hbx : ∀ᵐ s ∂(productLaw μ B h n), b ≤ s := ae_floor_productLaw hpos hB h hn
  have hz : z.re < 1 := hKsub hzK
  have hc : 0 < B - 1 := by linarith
  have hM : ‖shiftedMomentIntegral μ B h n (z - 1)‖ ≤ M * (B - 1) := by
    unfold shiftedMomentIntegral
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => shiftedMoment μ B h n t (z - 1)) (C := M) (a := (0 : ℝ)) (b := B - 1) ?_
    · simpa [abs_of_pos hc] using hi
    intro t ht
    unfold shiftedMoment
    have ht0 : 0 ≤ t := by
      rw [Set.uIoc_of_le hc.le] at ht
      exact ht.1.le
    have hnorm : ∀ᵐ s ∂(productLaw μ B h n),
        ‖((s + t : ℝ) : ℂ) ^ (z - 1)‖ ≤ M := by
      filter_upwards [hbx] with s hs
      exact cpow_sub_one_norm_le hb (by linarith) hR0 (hzR z hzK) hz
    simpa using norm_integral_le_of_norm_le_const hnorm
  rw [correction_eq_aux hpos hmean hB h hn hz, norm_mul]
  exact mul_le_mul (hzR z hzK) hM (norm_nonneg _) hR0

end DiamondPinning
