module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Proofs.FieldDerivProof
public import DiamondPinning.Proofs.BallotProof
public import DiamondPinning.Proofs.CriticalMoments
public import DiamondPinning.Proofs.IntegrabilityProof
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Moments.Variance

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Asymptotics ProbabilityTheory
open scoped BigOperators

/-- Tilted masses are strictly positive. -/
theorem tiltedMass_pos_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : 0 < tiltedMass μ B h n := by
  have : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have hi : Integrable (fun x : ℝ => x ^ theta B) (lawR μ B h n) := by
    simpa only [Real.rpow_zero, mul_one] using
      integrable_absTiltedLogRpow_aux hpos hmean hB h n (s := 0) (le_refl 0)
  have hnon : 0 ≤ᵐ[lawR μ B h n] (fun x : ℝ => x ^ theta B) := by
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    exact Real.rpow_nonneg hx.le _
  have hpos' : ∀ᵐ x ∂(lawR μ B h n), 0 < x ^ theta B := by
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    exact Real.rpow_pos_of_pos hx _
  apply (integral_pos_iff_support_of_nonneg_ae hnon hi).2
  apply pos_iff_ne_zero.mpr
  intro hz
  have hzero : (fun x : ℝ => x ^ theta B) =ᵐ[lawR μ B h n] 0 := ae_iff.mp hz
  obtain ⟨x, hx, hx0⟩ := (hpos'.and hzero).exists
  rw [Pi.zero_apply] at hx0
  exact (ne_of_gt hx) hx0

/-- The size-biased spine marginals are probability measures. -/
theorem isProbabilityMeasure_tiltedLaw_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (j : ℕ) : IsProbabilityMeasure (tiltedLaw μ B h j) := by
  have hi : Integrable (fun x : ℝ => x ^ theta B) (lawR μ B h j) := by
    simpa only [Real.rpow_zero, mul_one] using
      integrable_absTiltedLogRpow_aux hpos hmean hB h j (s := 0) (le_refl 0)
  have hA := tiltedMass_pos_of hpos hmean hB h j
  have hnon : 0 ≤ᵐ[lawR μ B h j] (fun x : ℝ => x ^ theta B / tiltedMass μ B h j) := by
    filter_upwards [ae_pos_lawR hpos hB h j] with x hx
    exact div_nonneg (Real.rpow_nonneg hx.le _) hA.le
  rw [isProbabilityMeasure_iff, tiltedLaw, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.div_const _) hnon]
  have hreal : (∫ x, x ^ theta B / tiltedMass μ B h j ∂(lawR μ B h j)) = 1 := by
    rw [integral_div]
    exact div_self hA.ne'
  rw [hreal, ENNReal.ofReal_one]

/-- Spine marginals are supported on positive reals. -/
theorem ae_pos_tiltedLaw_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (j : ℕ) :
    ∀ᵐ x ∂(tiltedLaw μ B h j), 0 < x := by
  rw [tiltedLaw, ae_withDensity_iff
    (((Real.continuous_rpow_const (theta_pos hB).le).measurable.div_const _).ennreal_ofReal)]
  filter_upwards [ae_pos_lawR hpos hB h j] with x hx
  intro _
  exact hx

/-- Logarithms are integrable under the size-biased spine marginals. -/
theorem integrable_log_tiltedLaw_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (j : ℕ) : Integrable Real.log (tiltedLaw μ B h j) := by
  have : IsProbabilityMeasure (lawR μ B h j) := isProbabilityMeasure_lawR B h j
  have hi := integrable_tiltedLogPower_of hpos hmean hB h j (q := 1) (by norm_num)
  rw [tiltedLaw, integrable_withDensity_iff
    (((Real.continuous_rpow_const (theta_pos hB).le).measurable.div_const _).ennreal_ofReal)
    (by simp)]
  have hm : Measurable (fun x : ℝ => Real.log x *
      (ENNReal.ofReal (x ^ theta B / tiltedMass μ B h j)).toReal) := by
    fun_prop
  apply ((hi.div_const (tiltedMass μ B h j)).mono' hm.aestronglyMeasurable)
  filter_upwards [ae_pos_lawR hpos hB h j] with x hx
  rw [ENNReal.toReal_ofReal (div_nonneg (Real.rpow_nonneg hx.le _)
    (tiltedMass_pos_of hpos hmean hB h j).le)]
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (Real.rpow_nonneg hx.le _),
    abs_of_nonneg (le_of_lt (tiltedMass_pos_of hpos hmean hB h j)), Real.rpow_one]
  exact le_of_eq (by ring)

/-- Integration against a size-biased marginal. -/
theorem integral_tiltedLaw_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (j : ℕ) (f : ℝ → ℝ) :
    (∫ x, f x ∂(tiltedLaw μ B h j)) =
      (∫ x, x ^ theta B * f x ∂(lawR μ B h j)) / tiltedMass μ B h j := by
  rw [tiltedLaw, integral_withDensity_eq_integral_toReal_smul
    (((Real.continuous_rpow_const (theta_pos hB).le).measurable.div_const _).ennreal_ofReal)
    (by simp), ← integral_div]
  apply integral_congr_ae
  filter_upwards [ae_pos_lawR hpos hB h j] with x hx
  rw [ENNReal.toReal_ofReal (div_nonneg (Real.rpow_nonneg hx.le _)
      (tiltedMass_pos_of hpos hmean hB h j).le)]
  simp only [smul_eq_mul]
  ring

/-- Shifted logarithmic moments under a size-biased marginal. -/
theorem integral_tiltedLaw_log_sub_pow_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (j k : ℕ) :
    (∫ x, (Real.log x - Real.log B) ^ k ∂(tiltedLaw μ B h j)) =
      tiltedLogMoment μ B h k j / tiltedMass μ B h j := by
  rw [integral_tiltedLaw_of hpos hmean hB h]
  rfl

/-- Every power of the shifted logarithm is integrable under a spine marginal. -/
theorem integrable_tiltedLaw_log_sub_pow_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (j k : ℕ) :
    Integrable (fun x => (Real.log x - Real.log B) ^ k) (tiltedLaw μ B h j) := by
  have : IsProbabilityMeasure (lawR μ B h j) := isProbabilityMeasure_lawR B h j
  have hi := integrable_absTiltedLogRpow_aux hpos hmean hB h j (s := (k : ℝ)) (by positivity)
  rw [tiltedLaw, integrable_withDensity_iff
    (((Real.continuous_rpow_const (theta_pos hB).le).measurable.div_const _).ennreal_ofReal)
    (by simp)]
  have hm : Measurable (fun x : ℝ => (Real.log x - Real.log B) ^ k *
      (ENNReal.ofReal (x ^ theta B / tiltedMass μ B h j)).toReal) := by
    fun_prop
  apply ((hi.div_const (tiltedMass μ B h j)).mono' hm.aestronglyMeasurable)
  filter_upwards [ae_pos_lawR hpos hB h j] with x hx
  rw [ENNReal.toReal_ofReal (div_nonneg (Real.rpow_nonneg hx.le _)
    (tiltedMass_pos_of hpos hmean hB h j).le)]
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (Real.rpow_nonneg hx.le _),
    abs_of_nonneg (tiltedMass_pos_of hpos hmean hB h j).le]
  rw [abs_pow, Real.rpow_natCast]
  ring_nf
  exact le_rfl

/-- The common deterministic lower bound for spine increments at times at least one. -/
theorem ae_floorSeq_tiltedLaw_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (j : ℕ) :
    ∀ᵐ x ∂(tiltedLaw μ B h j), floorSeq B j ≤ x := by
  rw [tiltedLaw, ae_withDensity_iff
    (((Real.continuous_rpow_const (theta_pos hB).le).measurable.div_const _).ennreal_ofReal)]
  filter_upwards [ae_floorSeq_le_lawR hpos hB h j] with x hx
  intro _
  exact hx

/-- Cauchy--Schwarz in integral form, without roots in the conclusion. -/
theorem integral_mul_sq_le_integral_sq_mul_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {f g : Ω → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
    (hf0 : 0 ≤ᵐ[ν] f) (hg0 : 0 ≤ᵐ[ν] g) :
    (∫ x, f x * g x ∂ν) ^ 2 ≤ (∫ x, f x ^ 2 ∂ν) * ∫ x, g x ^ 2 ∂ν := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := 2) (q := 2) (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hf0 hg0
    (by simpa using hf) (by simpa using hg)
  have hfg : 0 ≤ ∫ x, f x * g x ∂ν := integral_nonneg_of_ae (by filter_upwards [hf0, hg0] with x hxf hxg using mul_nonneg hxf hxg)
  have hf' : 0 ≤ ∫ x, f x ^ 2 ∂ν := integral_nonneg_of_ae (hf0.mono fun x hx => sq_nonneg _)
  have hg' : 0 ≤ ∫ x, g x ^ 2 ∂ν := integral_nonneg_of_ae (hg0.mono fun x hx => sq_nonneg _)
  have hfroot : ((∫ x, f x ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)) ^ 2 =
      ∫ x, f x ^ 2 ∂ν := by
    convert Real.rpow_inv_natCast_pow hf' (n := 2) (by norm_num) using 1 <;>
      norm_num [Real.rpow_two, one_div]
  have hgroot : ((∫ x, g x ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)) ^ 2 =
      ∫ x, g x ^ 2 ∂ν := by
    convert Real.rpow_inv_natCast_pow hg' (n := 2) (by norm_num) using 1 <;>
      norm_num [Real.rpow_two, one_div]
  calc
    (∫ x, f x * g x ∂ν) ^ 2 ≤
        (((∫ x, f x ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)) *
          (∫ x, g x ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ hfg h 2
    _ = (∫ x, f x ^ 2 ∂ν) * ∫ x, g x ^ 2 ∂ν := by
      rw [mul_pow, hfroot, hgroot]

/-- The fourth-moment estimate behind the Paley--Zygmund lower bound for the
positive part of a centered random variable. -/
theorem second_cube_le_posPart_sq_mul_fourth {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {Z : Ω → ℝ} (hZ : MemLp Z 4 ν)
    (hmean : ∫ x, Z x ∂ν = 0) :
    (∫ x, Z x ^ 2 ∂ν) ^ 3 ≤ 4 * (∫ x, (Z x)⁺ ∂ν) ^ 2 * ∫ x, Z x ^ 4 ∂ν := by
  have hZ1 : MemLp Z 1 ν := hZ.mono_exponent (by norm_num)
  have hZ2 : MemLp Z 2 ν := hZ.mono_exponent (by norm_num)
  have hZ3 : MemLp Z 3 ν := hZ.mono_exponent (by norm_num)
  have hi1 : Integrable Z ν := memLp_one_iff_integrable.mp hZ1
  have habs : MemLp (fun x => |Z x|) 2 ν := by simpa using hZ2.norm
  have hsqrt : MemLp (fun x => Real.sqrt |Z x|) 2 ν := by
    rw [memLp_two_iff_integrable_sq (by fun_prop)]
    convert hi1.norm using 1
    ext x
    simp [Real.sq_sqrt (abs_nonneg _)]
  have hweighted : MemLp (fun x => |Z x| * Real.sqrt |Z x|) 2 ν := by
    rw [memLp_two_iff_integrable_sq (by fun_prop)]
    have hi := hZ3.integrable_norm_pow (p := 3) (by norm_num)
    convert hi using 1
    ext x
    simp only [Real.norm_eq_abs]
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
    ring
  have hfirst := integral_mul_sq_le_integral_sq_mul_integral_sq hsqrt hweighted
    (Eventually.of_forall fun x => Real.sqrt_nonneg _)
    (Eventually.of_forall fun x => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
  have hfirst' : (∫ x, Z x ^ 2 ∂ν) ^ 2 ≤
      (∫ x, |Z x| ∂ν) * ∫ x, |Z x| ^ 3 ∂ν := by
    have hp : (fun x => Real.sqrt |Z x| * (|Z x| * Real.sqrt |Z x|)) =
        fun x => Z x ^ 2 := by
      funext x
      have hs := Real.sq_sqrt (abs_nonneg (Z x))
      rw [← sq_abs]
      nlinarith
    have hf : (fun x => Real.sqrt |Z x| ^ 2) = fun x => |Z x| := by
      funext x
      exact Real.sq_sqrt (abs_nonneg _)
    have hg : (fun x => (|Z x| * Real.sqrt |Z x|) ^ 2) = fun x => |Z x| ^ 3 := by
      funext x
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
      ring
    simpa only [hp, hf, hg] using hfirst
  have hZsq : MemLp (fun x => Z x ^ 2) 2 ν := by
    rw [memLp_two_iff_integrable_sq (by fun_prop)]
    convert hZ.integrable_norm_pow (p := 4) (by norm_num) using 1
    ext x
    simp only [Real.norm_eq_abs]
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ Z x ^ 4)]
    ring
  have hsecond := integral_mul_sq_le_integral_sq_mul_integral_sq habs hZsq
    (Eventually.of_forall fun x => abs_nonneg _)
    (Eventually.of_forall fun x => sq_nonneg _)
  have hsecond' : (∫ x, |Z x| ^ 3 ∂ν) ^ 2 ≤
      (∫ x, Z x ^ 2 ∂ν) * ∫ x, Z x ^ 4 ∂ν := by
    have hp : (fun x => |Z x| * Z x ^ 2) = fun x => |Z x| ^ 3 := by
      funext x
      rw [← sq_abs]
      ring
    have hf : (fun x => |Z x| ^ 2) = fun x => Z x ^ 2 := by
      funext x
      exact sq_abs _
    have hg : (fun x => (Z x ^ 2) ^ 2) = fun x => Z x ^ 4 := by
      funext x
      ring
    simpa only [hp, hf, hg] using hsecond
  have habs_eq : (∫ x, |Z x| ∂ν) = 2 * ∫ x, (Z x)⁺ ∂ν := by
    rw [integral_abs_eq_two_mul_integral_posPart_sub_integral hi1, hmean]
    ring
  have hV : 0 ≤ ∫ x, Z x ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
  have hA : 0 ≤ ∫ x, |Z x| ∂ν := integral_nonneg fun x => abs_nonneg _
  have hT : 0 ≤ ∫ x, |Z x| ^ 3 ∂ν := integral_nonneg fun x => pow_nonneg (abs_nonneg _) _
  have hQ : 0 ≤ ∫ x, Z x ^ 4 ∂ν := integral_nonneg fun x => by positivity
  rw [habs_eq] at hfirst'
  by_cases hV0 : ∫ x, Z x ^ 2 ∂ν = 0
  · rw [hV0]
    norm_num
    positivity
  · have hVpos : 0 < ∫ x, Z x ^ 2 ∂ν := lt_of_le_of_ne hV (Ne.symm hV0)
    have hsquare := pow_le_pow_left₀ (sq_nonneg (∫ x, Z x ^ 2 ∂ν)) hfirst' 2
    have hstep := mul_le_mul_of_nonneg_left hsecond'
      (by positivity : 0 ≤ 4 * (∫ x, (Z x)⁺ ∂ν) ^ 2)
    nlinarith

/-- Paley--Zygmund for the positive part, with a prescribed lower bound on its mean. -/
theorem paleyZygmund_posPart {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {Z : Ω → ℝ} (hZm : Measurable Z)
    (hZ : MemLp Z 2 ν) {m : ℝ} (hm : 0 < m) (hmZ : m ≤ ∫ x, (Z x)⁺ ∂ν) :
    m ^ 2 ≤ 4 * ν.real {x | m / 2 ≤ Z x} * ∫ x, Z x ^ 2 ∂ν := by
  let E : Set Ω := {x | m / 2 ≤ Z x}
  have hE : MeasurableSet E := measurableSet_le measurable_const hZm
  have hXp : MemLp (fun x => (Z x)⁺) 2 ν := hZ.pos_part
  have hiXp : Integrable (fun x => (Z x)⁺) ν := memLp_one_iff_integrable.mp
    (hZ.mono_exponent (by norm_num) |>.pos_part)
  have hf : MemLp (E.indicator fun x => (Z x)⁺) 2 ν := hXp.indicator hE.nullMeasurableSet
  have hg : MemLp (E.indicator fun _ => (1 : ℝ)) 2 ν :=
    (memLp_const 1).indicator hE.nullMeasurableSet
  have hC := integral_mul_sq_le_integral_sq_mul_integral_sq hf hg
    (Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => posPart_nonneg _) _)
    (Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hfg : (fun x => (E.indicator (fun x => (Z x)⁺) x) * E.indicator (fun _ => (1 : ℝ)) x) =
      E.indicator fun x => (Z x)⁺ := by
    funext x
    by_cases hx : x ∈ E <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have hf_sq : (∫ x, (E.indicator (fun x => (Z x)⁺) x) ^ 2 ∂ν) ≤
      ∫ x, Z x ^ 2 ∂ν := by
    apply integral_mono_ae (hf.integrable_sq) hZ.integrable_sq
    filter_upwards [] with x
    by_cases hx : x ∈ E
    · simp only [Set.indicator_of_mem hx]
      change (Z x ⊔ 0) ^ 2 ≤ Z x ^ 2
      by_cases hz : 0 ≤ Z x
      · rw [sup_of_le_left hz]
      · rw [sup_of_le_right (le_of_not_ge hz)]
        nlinarith [sq_nonneg (Z x)]
    · simp [Set.indicator_of_notMem hx, sq_nonneg]
  have hg_sq : (∫ x, (E.indicator (fun _ => (1 : ℝ)) x) ^ 2 ∂ν) = ν.real E := by
    convert integral_indicator_one (μ := ν) hE using 1
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ E <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rw [hfg, hg_sq] at hC
  have hC' : (∫ x, E.indicator (fun x => (Z x)⁺) x ∂ν) ^ 2 ≤
      ν.real E * ∫ x, Z x ^ 2 ∂ν := by
    have hp : 0 ≤ ν.real E := measureReal_nonneg
    calc
      _ ≤ (∫ x, (E.indicator (fun x => (Z x)⁺) x) ^ 2 ∂ν) * ν.real E := hC
      _ ≤ (∫ x, Z x ^ 2 ∂ν) * ν.real E :=
        mul_le_mul_of_nonneg_right hf_sq hp
      _ = _ := mul_comm _ _
  have hcomp : (∫ x, Eᶜ.indicator (fun x => (Z x)⁺) x ∂ν) ≤ m / 2 := by
    calc
      _ ≤ ∫ _x : Ω, m / 2 ∂ν := by
        apply integral_mono_ae (hiXp.indicator hE.compl) (integrable_const _)
        filter_upwards [] with x
        by_cases hx : x ∈ E
        · have hx' : x ∉ Eᶜ := by simpa using hx
          rw [Set.indicator_of_notMem hx']
          positivity
        · have hx' : x ∈ Eᶜ := hx
          rw [Set.indicator_of_mem hx']
          exact max_le (le_of_not_ge hx) (by positivity)
      _ = m / 2 := by simp
  have hsplit : (∫ x, E.indicator (fun x => (Z x)⁺) x ∂ν) +
      ∫ x, Eᶜ.indicator (fun x => (Z x)⁺) x ∂ν = ∫ x, (Z x)⁺ ∂ν := by
    rw [integral_indicator hE, integral_indicator hE.compl]
    exact integral_add_compl hE hiXp
  have hpI : 0 ≤ ∫ x, E.indicator (fun x => (Z x)⁺) x ∂ν :=
    integral_nonneg fun x => Set.indicator_nonneg (fun _ _ => posPart_nonneg _) _
  have hI : m / 2 ≤ ∫ x, E.indicator (fun x => (Z x)⁺) x ∂ν := by linarith
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ m / 2) hI 2
  nlinarith

/-- Second-moment recurrence for adding an independent centered variable. -/
theorem integral_add_sq_centered {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {S X : Ω → ℝ} (hSm : Measurable S) (hXm : Measurable X)
    (hS : MemLp S 2 ν) (hX : MemLp X 2 ν)
    (hmeanS : ∫ x, S x ∂ν = 0) (hmeanX : ∫ x, X x ∂ν = 0)
    (hind : S ⟂ᵢ[ν] X) :
    (∫ x, (S x + X x) ^ 2 ∂ν) = (∫ x, S x ^ 2 ∂ν) + ∫ x, X x ^ 2 ∂ν := by
  have hSi : Integrable S ν := memLp_one_iff_integrable.mp (hS.mono_exponent (by norm_num))
  have hXi : Integrable X ν := memLp_one_iff_integrable.mp (hX.mono_exponent (by norm_num))
  have hprod : Integrable (fun x => S x * X x) ν := by
    change Integrable (S * X) ν
    exact hind.integrable_mul hSi hXi
  have hfactor : (∫ x, S x * X x ∂ν) = 0 := by
    rw [hind.integral_fun_mul_eq_mul_integral hSm.aestronglyMeasurable hXm.aestronglyMeasurable,
      hmeanS, zero_mul]
  have hexpand : (fun x => (S x + X x) ^ 2) = fun x =>
      S x ^ 2 + 2 * (S x * X x) + X x ^ 2 := by funext x; ring
  rw [hexpand]
  have hlin := integral_add (μ := ν) (f := fun x => S x ^ 2 + 2 * (S x * X x))
    (g := fun x => X x ^ 2) (hS.integrable_sq.add (hprod.const_mul 2)) hX.integrable_sq
  rw [hlin]
  have hlin' := integral_add (μ := ν) (f := fun x => S x ^ 2)
    (g := fun x => 2 * (S x * X x)) hS.integrable_sq (hprod.const_mul 2)
  rw [hlin', integral_const_mul, hfactor]
  ring

/-- Fourth-moment recurrence for adding an independent centered variable. -/
theorem integral_add_pow_four_centered {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {S X : Ω → ℝ} (hSm : Measurable S) (hXm : Measurable X)
    (hS : MemLp S 4 ν) (hX : MemLp X 4 ν)
    (hmeanS : ∫ x, S x ∂ν = 0) (hmeanX : ∫ x, X x ∂ν = 0)
    (hind : S ⟂ᵢ[ν] X) :
    (∫ x, (S x + X x) ^ 4 ∂ν) = (∫ x, S x ^ 4 ∂ν) +
      6 * (∫ x, S x ^ 2 ∂ν) * (∫ x, X x ^ 2 ∂ν) + ∫ x, X x ^ 4 ∂ν := by
  have hS1 : MemLp S 1 ν := hS.mono_exponent (by norm_num)
  have hX1 : MemLp X 1 ν := hX.mono_exponent (by norm_num)
  have hS2 : MemLp S 2 ν := hS.mono_exponent (by norm_num)
  have hX2 : MemLp X 2 ν := hX.mono_exponent (by norm_num)
  have hS3 : MemLp S 3 ν := hS.mono_exponent (by norm_num)
  have hX3 : MemLp X 3 ν := hX.mono_exponent (by norm_num)
  have hiS1 : Integrable S ν := memLp_one_iff_integrable.mp hS1
  have hiX1 : Integrable X ν := memLp_one_iff_integrable.mp hX1
  have hiS2 : Integrable (fun x => S x ^ 2) ν := hS2.integrable_sq
  have hiX2 : Integrable (fun x => X x ^ 2) ν := hX2.integrable_sq
  have hiS3 : Integrable (fun x => S x ^ 3) ν := by
    apply (integrable_norm_iff (hSm.pow_const 3).aestronglyMeasurable).1
    simpa only [Real.norm_eq_abs, abs_pow] using hS3.integrable_norm_pow (p := 3) (by norm_num)
  have hiX3 : Integrable (fun x => X x ^ 3) ν := by
    apply (integrable_norm_iff (hXm.pow_const 3).aestronglyMeasurable).1
    simpa only [Real.norm_eq_abs, abs_pow] using hX3.integrable_norm_pow (p := 3) (by norm_num)
  have hiS4 : Integrable (fun x => S x ^ 4) ν := by
    apply (integrable_norm_iff (hSm.pow_const 4).aestronglyMeasurable).1
    simpa only [Real.norm_eq_abs, abs_pow] using hS.integrable_norm_pow (p := 4) (by norm_num)
  have hiX4 : Integrable (fun x => X x ^ 4) ν := by
    apply (integrable_norm_iff (hXm.pow_const 4).aestronglyMeasurable).1
    simpa only [Real.norm_eq_abs, abs_pow] using hX.integrable_norm_pow (p := 4) (by norm_num)
  have hind31 : (fun x => S x ^ 3) ⟂ᵢ[ν] X := by
    simpa only [Function.comp_def, id_eq] using hind.comp (by fun_prop : Measurable fun x : ℝ => x ^ 3) measurable_id
  have hind13 : S ⟂ᵢ[ν] (fun x => X x ^ 3) := by
    simpa only [Function.comp_def, id_eq] using hind.comp measurable_id (by fun_prop : Measurable fun x : ℝ => x ^ 3)
  have hind22 : (fun x => S x ^ 2) ⟂ᵢ[ν] (fun x => X x ^ 2) := by
    simpa only [Function.comp_def, id_eq] using hind.comp
      (by fun_prop : Measurable fun x : ℝ => x ^ 2) (by fun_prop : Measurable fun x : ℝ => x ^ 2)
  have hi31 : Integrable (fun x => S x ^ 3 * X x) ν := by
    change Integrable ((fun x => S x ^ 3) * X) ν
    exact hind31.integrable_mul hiS3 hiX1
  have hi13 : Integrable (fun x => S x * X x ^ 3) ν := by
    change Integrable (S * fun x => X x ^ 3) ν
    exact hind13.integrable_mul hiS1 hiX3
  have hi22 : Integrable (fun x => S x ^ 2 * X x ^ 2) ν := by
    change Integrable ((fun x => S x ^ 2) * fun x => X x ^ 2) ν
    exact hind22.integrable_mul hiS2 hiX2
  have hf31 : (∫ x, S x ^ 3 * X x ∂ν) = 0 := by
    rw [hind31.integral_fun_mul_eq_mul_integral
      (hSm.pow_const 3).aestronglyMeasurable hXm.aestronglyMeasurable, hmeanX, mul_zero]
  have hf13 : (∫ x, S x * X x ^ 3 ∂ν) = 0 := by
    rw [hind13.integral_fun_mul_eq_mul_integral hSm.aestronglyMeasurable (hXm.pow_const 3).aestronglyMeasurable,
      hmeanS, zero_mul]
  have hf22 : (∫ x, S x ^ 2 * X x ^ 2 ∂ν) =
      (∫ x, S x ^ 2 ∂ν) * ∫ x, X x ^ 2 ∂ν := by
    exact hind22.integral_fun_mul_eq_mul_integral (hSm.pow_const 2).aestronglyMeasurable
      (hXm.pow_const 2).aestronglyMeasurable
  have hexpand : (fun x => (S x + X x) ^ 4) = fun x =>
      S x ^ 4 + 4 * (S x ^ 3 * X x) + 6 * (S x ^ 2 * X x ^ 2) +
        4 * (S x * X x ^ 3) + X x ^ 4 := by funext x; ring
  rw [hexpand]
  have hlin1 := integral_add (μ := ν) (f := fun x => S x ^ 4)
    (g := fun x => 4 * (S x ^ 3 * X x)) hiS4 (hi31.const_mul 4)
  have hlin2 := integral_add (μ := ν) (f := fun x => S x ^ 4 + 4 * (S x ^ 3 * X x))
    (g := fun x => 6 * (S x ^ 2 * X x ^ 2))
    (hiS4.add (hi31.const_mul 4)) (hi22.const_mul 6)
  have hlin3 := integral_add (μ := ν)
    (f := fun x => S x ^ 4 + 4 * (S x ^ 3 * X x) + 6 * (S x ^ 2 * X x ^ 2))
    (g := fun x => 4 * (S x * X x ^ 3))
    ((hiS4.add (hi31.const_mul 4)).add (hi22.const_mul 6)) (hi13.const_mul 4)
  have hlin4 := integral_add (μ := ν)
    (f := fun x => S x ^ 4 + 4 * (S x ^ 3 * X x) + 6 * (S x ^ 2 * X x ^ 2) +
      4 * (S x * X x ^ 3)) (g := fun x => X x ^ 4)
    (((hiS4.add (hi31.const_mul 4)).add (hi22.const_mul 6)).add (hi13.const_mul 4)) hiX4
  rw [hlin4, hlin3, hlin2, hlin1]
  simp only [integral_const_mul, hf31, hf13, hf22]
  ring

/-- Eventual quadratic growth of a sum with nonnegative terms and eventual linear lower bounds. -/
theorem eventually_sum_range_sq_lower {q : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hq0 : ∀ j, 0 ≤ q j) (hq : ∀ᶠ j : ℕ in atTop, c * (j : ℝ) ≤ q j) :
    ∀ᶠ n : ℕ in atTop, c / 16 * (n : ℝ) ^ 2 ≤ ∑ j ∈ Finset.range n, q j := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hq
  filter_upwards [eventually_ge_atTop (2 * N + 2)] with n hn
  let m := n - N
  have hm2 : 2 ≤ m := by dsimp [m]; omega
  have hNn : N ≤ n := by omega
  have hmn : N + m = n := by dsimp [m]; omega
  have hNm : N ≤ m := by dsimp [m]; omega
  have hmR : (N : ℝ) + m = n := by exact_mod_cast hmn
  have hsumNat := Finset.sum_range_id_mul_two m
  have hsum : (∑ j ∈ Finset.range m, (j : ℝ)) = (m : ℝ) * (m - 1) / 2 := by
    have htwo : (∑ j ∈ Finset.range m, (j : ℝ)) * 2 = (m : ℝ) * (m - 1) := by
      calc
        _ = (((∑ j ∈ Finset.range m, j) * 2 : ℕ) : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_sum]
          norm_num
        _ = ((m * (m - 1) : ℕ) : ℝ) := by rw [hsumNat]
        _ = _ := by rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m)]; simp
    linarith
  have hsmall : ((n : ℝ) ^ 2) / 16 ≤ ∑ j ∈ Finset.range m, (j : ℝ) := by
    rw [hsum]
    have hmR2 : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    have hNR : (N : ℝ) ≤ m := by exact_mod_cast hNm
    nlinarith [sq_nonneg (n : ℝ), sq_nonneg (m : ℝ)]
  have hmul : c / 16 * (n : ℝ) ^ 2 ≤ c * ∑ j ∈ Finset.range m, (j : ℝ) := by
    have hc' := mul_le_mul_of_nonneg_left hsmall hc.le
    convert hc' using 1 <;> ring
  have hterm : c * (∑ j ∈ Finset.range m, (j : ℝ)) ≤
      ∑ j ∈ Finset.range m, q (N + j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    calc
      c * (j : ℝ) ≤ c * (N + j : ℕ) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        exact_mod_cast Nat.le_add_left j N
      _ ≤ _ := hN (N + j) (Nat.le_add_right N j)
  have hnon : 0 ≤ ∑ j ∈ Finset.range N, q j :=
    Finset.sum_nonneg fun j _ => hq0 j
  have htotal : c * (∑ j ∈ Finset.range m, (j : ℝ)) ≤
      (∑ j ∈ Finset.range N, q j) + ∑ j ∈ Finset.range m, q (N + j) :=
    hterm.trans (le_add_of_nonneg_left hnon)
  have hfin := hmul.trans htotal
  rw [← hmn] at hfin
  rw [← hmn]
  simpa only [Finset.sum_range_add] using hfin

/-- A uniform lower tail for centered sums from second- and fourth-moment bounds. -/
theorem eventually_centered_tail {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {Z : ℕ → Ω → ℝ}
    (hZm : ∀ n, Measurable (Z n)) (hZ4 : ∀ n, MemLp (Z n) 4 ν)
    (hZmean : ∀ n, (∫ x, Z n x ∂ν) = 0) {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hVlow : ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ 2 ≤ ∫ x, Z n x ^ 2 ∂ν)
    (hVupp : ∀ᶠ n : ℕ in atTop, (∫ x, Z n x ^ 2 ∂ν) ≤ C * (n : ℝ) ^ 2)
    (hQupp : ∀ᶠ n : ℕ in atTop, (∫ x, Z n x ^ 4 ∂ν) ≤ C ^ 2 * (n : ℝ) ^ 4) :
    ∃ η δ : ℝ, 0 < η ∧ 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      δ ≤ ν.real {x | η * (n : ℝ) ≤ Z n x} := by
  let d := min c 1
  let k := d ^ 2 / (2 * C)
  refine ⟨k / 2, k ^ 2 / (4 * C), by positivity, by positivity, ?_⟩
  filter_upwards [hVlow, hVupp, hQupp, eventually_ge_atTop 1] with n hVlo hVup hQup hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnn (r : ℕ) : 0 ≤ (n : ℝ) ^ r := by positivity
  let m := k * (n : ℝ)
  have hd : 0 < d := by dsimp [d]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hm : 0 < m := by dsimp [m]; positivity
  have hV0 : 0 ≤ ∫ x, Z n x ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
  have hQ0 : 0 ≤ ∫ x, Z n x ^ 4 ∂ν := integral_nonneg fun x => by positivity
  have hP0 : 0 ≤ ∫ x, (Z n x)⁺ ∂ν := integral_nonneg fun x => posPart_nonneg _
  have hVpos : 0 < ∫ x, Z n x ^ 2 ∂ν := by
    have : 0 < c * (n : ℝ) ^ 2 := by positivity
    linarith
  have hcube := second_cube_le_posPart_sq_mul_fourth ν (hZ4 n) (hZmean n)
  have hQpos : 0 < ∫ x, Z n x ^ 4 ∂ν := by
    by_contra hq
    have hq0 : (∫ x, Z n x ^ 4 ∂ν) = 0 := le_antisymm (le_of_not_gt hq) hQ0
    rw [hq0, mul_zero] at hcube
    have : (∫ x, Z n x ^ 2 ∂ν) ^ 3 = 0 := le_antisymm hcube (by positivity)
    have hp := pow_pos hVpos 3
    linarith
  have hd4 : d ^ 4 ≤ c ^ 3 := by
    by_cases h : c ≤ 1
    · have hd' : d = c := min_eq_left h
      rw [hd']
      nlinarith [sq_nonneg c, pow_nonneg hc.le 3]
    · have hd' : d = 1 := min_eq_right (le_of_not_ge h)
      have hc1 : 1 ≤ c := le_of_not_ge h
      rw [hd']
      norm_num
      nlinarith [sq_nonneg (c - 1), hC]
  have hleft : 4 * (∫ x, Z n x ^ 4 ∂ν) * m ^ 2 ≤
      4 * (∫ x, (Z n x)⁺ ∂ν) ^ 2 * (∫ x, Z n x ^ 4 ∂ν) := by
    calc
      4 * (∫ x, Z n x ^ 4 ∂ν) * m ^ 2 ≤
          4 * (C ^ 2 * (n : ℝ) ^ 4) * m ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hQup (by norm_num : (0 : ℝ) ≤ 4)) (sq_nonneg _)
      _ = d ^ 4 * (n : ℝ) ^ 6 := by
        dsimp [m, k]
        field_simp
        ring
      _ ≤ c ^ 3 * (n : ℝ) ^ 6 :=
        mul_le_mul_of_nonneg_right hd4 (by positivity)
      _ ≤ (∫ x, Z n x ^ 2 ∂ν) ^ 3 := by
        have hb : 0 ≤ c * (n : ℝ) ^ 2 := by positivity
        have hp := pow_le_pow_left₀ hb hVlo 3
        convert hp using 1 <;> ring
      _ ≤ _ := hcube
  have hmP : m ^ 2 ≤ (∫ x, (Z n x)⁺ ∂ν) ^ 2 := by
    have hcanc : 4 * (∫ x, Z n x ^ 4 ∂ν) * m ^ 2 ≤
        4 * (∫ x, Z n x ^ 4 ∂ν) * (∫ x, (Z n x)⁺ ∂ν) ^ 2 := by
      exact hleft.trans_eq (by ring)
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < 4 * (∫ x, Z n x ^ 4 ∂ν))).mp hcanc
  have hmZ : m ≤ ∫ x, (Z n x)⁺ ∂ν := by
    exact (sq_le_sq₀ hm.le hP0).mp hmP
  have hpaley := paleyZygmund_posPart ν (hZm n)
    ((hZ4 n).mono_exponent (by norm_num)) hm hmZ
  have hmu : m ^ 2 ≤
      4 * ν.real {x | m / 2 ≤ Z n x} * (C * (n : ℝ) ^ 2) := by
    exact hpaley.trans (mul_le_mul_of_nonneg_left hVup
      (by positivity : 0 ≤ 4 * ν.real {x | m / 2 ≤ Z n x}))
  have htail : k ^ 2 / (4 * C) ≤ ν.real {x | m / 2 ≤ Z n x} := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * C)).2
    have hcanc : k ^ 2 * (n : ℝ) ^ 2 ≤
        ν.real {x | m / 2 ≤ Z n x} * (4 * C) * (n : ℝ) ^ 2 := by
      convert hmu using 1
      · dsimp [m]
        ring
      · ring
    have hs := (mul_le_mul_iff_left₀ (sq_pos_of_pos hn0)).mp hcanc
    convert hs using 1 <;> ring
  have heta : m / 2 = (k / 2) * (n : ℝ) := by dsimp [m]; ring
  rw [← heta]
  exact htail

/-- A random variable centered by its Bochner mean. -/
noncomputable def centered {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (Y : Ω → ℝ) : Ω → ℝ := fun x => Y x - ∫ y, Y y ∂ν

/-- Second moment of a centered random variable. -/
theorem integral_centered_sq_of {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {Y : Ω → ℝ} (hY : MemLp Y 2 ν) :
    (∫ x, centered ν Y x ^ 2 ∂ν) = (∫ x, Y x ^ 2 ∂ν) - (∫ x, Y x ∂ν) ^ 2 := by
  have hi : Integrable Y ν := memLp_one_iff_integrable.mp (hY.mono_exponent (by norm_num))
  have hsq := hY.integrable_sq
  have hexpand : (fun x => centered ν Y x ^ 2) = fun x =>
      Y x ^ 2 - 2 * (∫ y, Y y ∂ν) * Y x + (∫ y, Y y ∂ν) ^ 2 := by
    funext x
    simp only [centered]
    ring
  rw [hexpand]
  have hlin1 := integral_sub (μ := ν) (f := fun x => Y x ^ 2)
    (g := fun x => 2 * (∫ y, Y y ∂ν) * Y x) hsq (hi.const_mul _)
  have hlin2 := integral_add (μ := ν) (f := fun x => Y x ^ 2 - 2 * (∫ y, Y y ∂ν) * Y x)
    (g := fun _ => (∫ y, Y y ∂ν) ^ 2) (hsq.sub (hi.const_mul _)) (integrable_const _)
  rw [hlin2, hlin1, integral_const_mul, integral_const, probReal_univ, one_smul]
  ring

/-- A fourth-moment bound after centering. -/
theorem integral_centered_fourth_le_of {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {Y : Ω → ℝ} (hY : MemLp Y 4 ν) :
    (∫ x, centered ν Y x ^ 4 ∂ν) ≤
      8 * ((∫ x, Y x ^ 4 ∂ν) + (∫ x, Y x ∂ν) ^ 4) := by
  have hi4 : Integrable (fun x => Y x ^ 4) ν := by
    have hi := hY.integrable_norm_pow (p := 4) (by norm_num)
    convert hi using 1
    ext x
    simp only [Real.norm_eq_abs]
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ Y x ^ 4)]
  have hc4 : Integrable (fun x => centered ν Y x ^ 4) ν := by
    have hc : MemLp (centered ν Y) 4 ν :=
      (by
        change MemLp (Y - fun _ => ∫ y, Y y ∂ν) 4 ν
        exact hY.sub (memLp_const _))
    have hi := hc.integrable_norm_pow (p := 4) (by norm_num)
    convert hi using 1
    ext x
    simp only [Real.norm_eq_abs]
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ centered ν Y x ^ 4)]
  have hpoint : ∀ x, centered ν Y x ^ 4 ≤
      8 * (Y x ^ 4 + (∫ y, Y y ∂ν) ^ 4) := by
    intro x
    dsimp [centered]
    nlinarith [sq_nonneg (Y x), sq_nonneg (∫ y, Y y ∂ν),
      sq_nonneg (Y x - ∫ y, Y y ∂ν), sq_nonneg (Y x + ∫ y, Y y ∂ν),
      sq_nonneg (Y x ^ 2 - (∫ y, Y y ∂ν) ^ 2),
      sq_nonneg (Y x * ∫ y, Y y ∂ν)]
  have hbound := integral_mono_ae hc4 ((hi4.add (integrable_const _)).const_mul 8)
    (Eventually.of_forall hpoint)
  have hadd := integral_add (μ := ν) (f := fun x => Y x ^ 4)
    (g := fun _ => (∫ y, Y y ∂ν) ^ 4) hi4 (integrable_const _)
  simp only [Pi.add_apply] at hbound
  rw [integral_const_mul, hadd, integral_const, probReal_univ, one_smul] at hbound
  exact hbound

/-- Exact second and fourth moments of sums of independent centered variables. -/
theorem centered_sum_moments {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {Y : ℕ → Ω → ℝ}
    (hYm : ∀ j, Measurable (Y j)) (hYind : iIndepFun Y ν)
    (hY4 : ∀ j, MemLp (Y j) 4 ν) (n : ℕ) :
    let Z := fun j => centered ν (Y j)
    let S := fun k : ℕ => fun x => ∑ j ∈ Finset.range k, Z j x
    MemLp (S n) 4 ν ∧ (∫ x, S n x ∂ν) = 0 ∧
      (∫ x, S n x ^ 2 ∂ν) = ∑ j ∈ Finset.range n, ∫ x, Z j x ^ 2 ∂ν ∧
      (∫ x, S n x ^ 4 ∂ν) =
        (∑ j ∈ Finset.range n, ∫ x, Z j x ^ 4 ∂ν) +
          6 * ∑ j ∈ Finset.range n,
            (∑ k ∈ Finset.range j, ∫ x, Z k x ^ 2 ∂ν) * ∫ x, Z j x ^ 2 ∂ν := by
  let Z := fun j => centered ν (Y j)
  let S := fun k : ℕ => fun x => ∑ j ∈ Finset.range k, Z j x
  have hZm (j : ℕ) : Measurable (Z j) := by
    exact (hYm j).sub measurable_const
  have hZ4 (j : ℕ) : MemLp (Z j) 4 ν := (hY4 j).sub (memLp_const _)
  have hZind : iIndepFun Z ν := by
    have hc := hYind.comp (fun j x => x - ∫ y, Y j y ∂ν) (fun _ => measurable_id.sub measurable_const)
    change iIndepFun (fun j x => Y j x - ∫ y, Y j y ∂ν) ν
    exact hc
  have hZmean (j : ℕ) : (∫ x, Z j x ∂ν) = 0 := by
    have hi : Integrable (Y j) ν := memLp_one_iff_integrable.mp ((hY4 j).mono_exponent (by norm_num : (1 : ENNReal) ≤ 4))
    simp only [Z, centered]
    rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul]
    simp
  induction n with
  | zero => simp
  | succ n ih =>
      have hSm : Measurable (S n) := by
        unfold S
        fun_prop
      have hind : S n ⟂ᵢ[ν] Z n := by
        have hi := hZind.indepFun_finsetSum_of_notMem hZm
          (s := Finset.range n) (i := n) (by simp)
        have heq : S n = ∑ j ∈ Finset.range n, Z j := by
          funext x
          simp [S]
        rw [heq]
        exact hi
      have hS4 := ih.1
      have hmeanS := ih.2.1
      have hsecond := integral_add_sq_centered hSm (hZm n)
        (hS4.mono_exponent (by norm_num)) ((hZ4 n).mono_exponent (by norm_num))
        hmeanS (hZmean n) hind
      have hfourth := integral_add_pow_four_centered hSm (hZm n) hS4 (hZ4 n)
        hmeanS (hZmean n) hind
      simp only [Finset.sum_range_succ]
      refine ⟨?_, ?_, ?_, ?_⟩
      · change MemLp (fun x => S n x + Z n x) 4 ν
        change MemLp (S n + Z n) 4 ν
        exact hS4.add (hZ4 n)
      · change (∫ x, S n x + Z n x ∂ν) = 0
        have hlin := integral_add (μ := ν) (f := S n) (g := Z n)
          (memLp_one_iff_integrable.mp (hS4.mono_exponent (by norm_num)))
          (memLp_one_iff_integrable.mp ((hZ4 n).mono_exponent (by norm_num)))
        rw [hlin, hmeanS, hZmean]
        simp
      · change (∫ x, (S n x + Z n x) ^ 2 ∂ν) = _
        rw [hsecond, ih.2.2.1]
      · change (∫ x, (S n x + Z n x) ^ 4 ∂ν) = _
        rw [hfourth, ih.2.2.1, ih.2.2.2]
        simp only
        ring

/-- The infinite independent extension of the spine's increment coordinates. -/
noncomputable def infiniteSpineMeasure (μ : Measure ℝ) (B h : ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun j : ℕ => tiltedLaw μ B h j

/-- The shifted logarithmic spine increments on the infinite extension. -/
noncomputable def spineIncrement (B : ℝ) (j : ℕ) (u : ℕ → ℝ) : ℝ :=
  Real.log (u j) - Real.log B

/-- Evaluation at a coordinate preserves the infinite spine law. -/
theorem measurePreserving_infiniteSpine_eval {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (j : ℕ) :
    MeasurePreserving (fun u : ℕ → ℝ => u j) (infiniteSpineMeasure μ B h) (tiltedLaw μ B h j) := by
  have (i : ℕ) : IsProbabilityMeasure (tiltedLaw μ B h i) :=
    isProbabilityMeasure_tiltedLaw_of hpos hmean hB h i
  exact ⟨measurable_pi_apply j, Measure.infinitePi_map_eval _ j⟩

/-- The infinite spine increments are independent. -/
theorem iIndepFun_spineIncrement {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) : iIndepFun (spineIncrement B) (infiniteSpineMeasure μ B h) := by
  have (i : ℕ) : IsProbabilityMeasure (tiltedLaw μ B h i) :=
    isProbabilityMeasure_tiltedLaw_of hpos hmean hB h i
  exact iIndepFun_infinitePi (fun j => Real.measurable_log.sub measurable_const)

/-- Coordinate powers on the infinite spine reduce to tilted-marginal powers. -/
theorem integral_spineIncrement_pow {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (j k : ℕ) :
    (∫ u, spineIncrement B j u ^ k ∂(infiniteSpineMeasure μ B h)) =
      tiltedLogMoment μ B h k j / tiltedMass μ B h j := by
  let mp := measurePreserving_infiniteSpine_eval hpos hmean hB h j
  change (∫ u : ℕ → ℝ, (Real.log (u j) - Real.log B) ^ k ∂(infiniteSpineMeasure μ B h)) = _
  calc
    _ = ∫ x : ℝ, (Real.log x - Real.log B) ^ k
        ∂((infiniteSpineMeasure μ B h).map (fun u : ℕ → ℝ => u j)) := by
      symm
      apply integral_map mp.measurable.aemeasurable
      fun_prop
    _ = ∫ x : ℝ, (Real.log x - Real.log B) ^ k ∂(tiltedLaw μ B h j) := by rw [mp.map_eq]
    _ = _ := integral_tiltedLaw_log_sub_pow_of hpos hmean hB h j k

/-- Every infinite spine increment has finite fourth moment. -/
theorem memLp_spineIncrement_four {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (j : ℕ) : MemLp (spineIncrement B j) 4 (infiniteSpineMeasure μ B h) := by
  let mp := measurePreserving_infiniteSpine_eval hpos hmean hB h j
  have hi := integrable_tiltedLaw_log_sub_pow_of hpos hmean hB h j 4
  have hm : MemLp (fun x : ℝ => Real.log x - Real.log B) 4 (tiltedLaw μ B h j) := by
    apply (integrable_norm_rpow_iff
      (Real.measurable_log.sub measurable_const).aestronglyMeasurable
      (by norm_num : (4 : ENNReal) ≠ 0) (by norm_num)).1
    convert hi.norm using 1
    ext x
    simp only [Pi.sub_apply, Real.norm_eq_abs, abs_pow]
    norm_num
  have hc := hm.comp_measurePreserving mp
  change MemLp ((fun x : ℝ => Real.log x - Real.log B) ∘ (fun u : ℕ → ℝ => u j)) 4
    (infiniteSpineMeasure μ B h)
  exact hc

/-- The deterministic lower bound for increments of index at least one. -/
theorem ae_spineIncrement_lower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    ∀ᵐ u ∂(infiniteSpineMeasure μ B h),
      -(Real.log B - Real.log (floorSeq B 1)) ≤ spineIncrement B j u := by
  let mp := measurePreserving_infiniteSpine_eval hpos hmean hB h j
  have hf := mp.quasiMeasurePreserving.ae (ae_floorSeq_tiltedLaw_of hpos hB h j)
  filter_upwards [hf] with u hu
  have hfloor : floorSeq B 1 ≤ u j := (floorSeq_one_le hB hj).trans hu
  have hpos1 : 0 < floorSeq B 1 := floorSeq_one_pos hB
  have hlog := Real.log_le_log hpos1 hfloor
  change -(Real.log B - Real.log (floorSeq B 1)) ≤ Real.log (u j) - Real.log B
  linarith

/-- The finite-horizon spine measures are probability measures. -/
theorem isProbabilityMeasure_spineMeasure_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : IsProbabilityMeasure (spineMeasure μ B h n) := by
  have : IsProbabilityMeasure (tiltedLaw μ B h 0) :=
    isProbabilityMeasure_tiltedLaw_of hpos hmean hB h 0
  have (j : Fin n) : IsProbabilityMeasure (tiltedLaw μ B h j) :=
    isProbabilityMeasure_tiltedLaw_of hpos hmean hB h j
  rw [spineMeasure]
  infer_instance

/-! ### The infinite spine: restriction, moments and the ballot estimate -/

/-- The infinite spine extension is a probability measure. -/
theorem isProbabilityMeasure_infiniteSpineMeasure {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) :
    IsProbabilityMeasure (infiniteSpineMeasure μ B h) := by
  have (i : ℕ) : IsProbabilityMeasure (tiltedLaw μ B h i) :=
    isProbabilityMeasure_tiltedLaw_of hpos hmean hB h i
  unfold infiniteSpineMeasure
  infer_instance

/-- Restricting the infinite spine to its first `n` coordinates gives the finite product
of the size-biased marginals. -/
theorem map_infiniteSpine_restrict {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) :
    (infiniteSpineMeasure μ B h).map (fun v : ℕ → ℝ => fun j : Fin n => v j) =
      Measure.pi fun j : Fin n => tiltedLaw μ B h j := by
  have (i : ℕ) : IsProbabilityMeasure (tiltedLaw μ B h i) :=
    isProbabilityMeasure_tiltedLaw_of hpos hmean hB h i
  have := isProbabilityMeasure_infiniteSpineMeasure hpos hmean hB h
  have hind : iIndepFun (fun (j : Fin n) (v : ℕ → ℝ) => v j) (infiniteSpineMeasure μ B h) := by
    have h0 := iIndepFun_infinitePi (P := fun j : ℕ => tiltedLaw μ B h j)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id)
    exact h0.precomp (g := fun j : Fin n => (j : ℕ)) Fin.val_injective
  rw [hind.map_fun_eq_pi_map fun (j : Fin n) => (measurable_pi_apply (j : ℕ)).aemeasurable]
  congr 1
  funext j
  exact (measurePreserving_infiniteSpine_eval hpos hmean hB h j).map_eq

/-- The finite-horizon spine walk is the partial sum of the infinite increments. -/
theorem spineWalk_restrict (B : ℝ) {n k : ℕ} (hk : k ≤ n) (v : ℕ → ℝ) :
    spineWalk B (fun j : Fin n => v j) k =
      ∑ j ∈ Finset.range k, spineIncrement B j v := by
  unfold spineWalk spineIncrement
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < k then Real.log (v j) - Real.log B else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- Measurability of the finite-horizon spine walk. -/
theorem measurable_spineWalk (B : ℝ) (n k : ℕ) :
    Measurable (fun u : Fin n → ℝ => spineWalk B u k) := by
  unfold spineWalk
  refine Finset.measurable_sum _ fun j _ => ?_
  by_cases hj : (j : ℕ) < k
  · simp only [hj, ite_true]
    exact (Real.measurable_log.comp (measurable_pi_apply j)).sub_const _
  · simp only [hj, ite_false]
    exact measurable_const

/-- Measurability of the survival events of the finite-horizon spine walk. -/
theorem measurableSet_spineWalk_survive (B : ℝ) (n : ℕ) (z : ℝ) :
    MeasurableSet {u : Fin n → ℝ | ∀ k ≤ n, -z ≤ spineWalk B u k} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    measurableSet_le measurable_const (measurable_spineWalk B n k)

/-- Upgrading an eventual polynomial bound to a bound for all indices. -/
theorem exists_forall_le_of_eventually_pow {f : ℕ → ℝ} {D : ℝ} {k : ℕ}
    (hf : ∀ᶠ j : ℕ in atTop, f j ≤ D * ((j : ℝ) + 1) ^ k) :
    ∃ D' : ℝ, 0 ≤ D' ∧ ∀ j : ℕ, f j ≤ D' * ((j : ℝ) + 1) ^ k := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hf
  have hs : 0 ≤ ∑ i ∈ Finset.range N, |f i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨max D 0 + ∑ i ∈ Finset.range N, |f i|, by positivity, fun j => ?_⟩
  have hpow : 1 ≤ ((j : ℝ) + 1) ^ k := one_le_pow₀ (by linarith [j.cast_nonneg (α := ℝ)])
  by_cases hj : N ≤ j
  · calc f j ≤ D * ((j : ℝ) + 1) ^ k := hN j hj
      _ ≤ (max D 0 + ∑ i ∈ Finset.range N, |f i|) * ((j : ℝ) + 1) ^ k :=
        mul_le_mul_of_nonneg_right
          (le_add_of_le_of_nonneg (le_max_left _ _) hs) (by positivity)
  · have hmem : j ∈ Finset.range N := Finset.mem_range.2 (by omega)
    have hj' : |f j| ≤ ∑ i ∈ Finset.range N, |f i| :=
      Finset.single_le_sum (f := fun i => |f i|) (fun i _ => abs_nonneg _) hmem
    calc f j ≤ |f j| := le_abs_self _
      _ ≤ max D 0 + ∑ i ∈ Finset.range N, |f i| := by
        linarith [le_max_right D 0]
      _ ≤ (max D 0 + ∑ i ∈ Finset.range N, |f i|) * ((j : ℝ) + 1) ^ k :=
        le_mul_of_one_le_right (by positivity) hpow

/-- The ballot estimate for the infinite spine walk, from the moment asymptotics of the
tilted laws (`response.tex` lines 101–119): the increments `log U_j - a` are independent,
bounded below for `j ≥ 1`, with summable positive mean parts, and a Paley--Zygmund
argument gives the linear lower tail. -/
theorem spine_ballot_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) {h : ℝ}
    (hA1 : ∀ᶠ n : ℕ in atTop, 1 < tiltedMass μ B h n)
    (hAlim : Tendsto (fun n : ℕ => tiltedMass μ B h n) atTop (𝓝 1))
    (hHlim : Tendsto (fun n : ℕ => tiltedLogMoment μ B h 1 n) atTop (𝓝 0))
    {C₀ : ℝ} (hHup : ∀ n : ℕ, 1 ≤ n → tiltedLogMoment μ B h 1 n ≤ C₀ * (2 / B) ^ n)
    {CK : ℝ} (hKup : ∀ n : ℕ, 1 ≤ n → tiltedLogMoment μ B h 2 n ≤ CK * ((n : ℝ) + 1))
    {cK : ℝ} (hcK : 0 < cK)
    (hKlow : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ cK * |tiltedLogMoment μ B h 2 n|)
    {CL : ℝ} (hLup : ∀ n : ℕ, 1 ≤ n → tiltedLogMoment μ B h 4 n ≤ CL * ((n : ℝ) + 1) ^ 3) :
    ∃ C : ℝ, ∀ (n : ℕ) (z : ℝ), 0 ≤ z →
      (infiniteSpineMeasure μ B h).real
          {v | ∀ k ≤ n, -z ≤ ∑ j ∈ Finset.range k, spineIncrement B j v} ≤
        C * (z + 1) / (n + 1) := by
  have := isProbabilityMeasure_infiniteSpineMeasure hpos hmean hB h
  -- notation
  let P := infiniteSpineMeasure μ B h
  let A := fun j : ℕ => tiltedMass μ B h j
  let H := fun j : ℕ => tiltedLogMoment μ B h 1 j
  let K := fun j : ℕ => tiltedLogMoment μ B h 2 j
  let L := fun j : ℕ => tiltedLogMoment μ B h 4 j
  let V := fun j : ℕ => ∫ x, centered P (spineIncrement B j) x ^ 2 ∂P
  let Q := fun j : ℕ => ∫ x, centered P (spineIncrement B j) x ^ 4 ∂P
  have hρ0 : (0 : ℝ) ≤ 2 / B := div_nonneg (by norm_num) (by linarith)
  have hρ1 : 2 / B < 1 := (div_lt_one (by linarith)).2 hB
  have hYm (j : ℕ) : Measurable (spineIncrement B j) := by
    unfold spineIncrement
    exact (Real.measurable_log.comp (measurable_pi_apply j)).sub_const _
  have hY4 (j : ℕ) : MemLp (spineIncrement B j) 4 P := memLp_spineIncrement_four hpos hmean hB h j
  have hYi (j : ℕ) : Integrable (spineIncrement B j) P :=
    memLp_one_iff_integrable.mp ((hY4 j).mono_exponent (by norm_num))
  have hind : iIndepFun (spineIncrement B) P := iIndepFun_spineIncrement hpos hmean hB h
  have hApos (j : ℕ) : 0 < A j := tiltedMass_pos_of hpos hmean hB h j
  have hm (j : ℕ) : (∫ u, spineIncrement B j u ∂P) = H j / A j := by
    simpa using integral_spineIncrement_pow hpos hmean hB h j 1
  have hsq (j : ℕ) : (∫ u, spineIncrement B j u ^ 2 ∂P) = K j / A j :=
    integral_spineIncrement_pow hpos hmean hB h j 2
  have hfour (j : ℕ) : (∫ u, spineIncrement B j u ^ 4 ∂P) = L j / A j :=
    integral_spineIncrement_pow hpos hmean hB h j 4
  have hV (j : ℕ) : V j = K j / A j - (H j / A j) ^ 2 := by
    change (∫ x, centered P (spineIncrement B j) x ^ 2 ∂P) = _
    rw [integral_centered_sq_of ((hY4 j).mono_exponent (by norm_num)), hsq, hm]
  have hQ (j : ℕ) : Q j ≤ 8 * (L j / A j + (H j / A j) ^ 4) := by
    have h8 := integral_centered_fourth_le_of (hY4 j)
    rw [hfour, hm] at h8
    exact h8
  have hV0 (j : ℕ) : 0 ≤ V j := integral_nonneg fun _ => sq_nonneg _
  have hK0 (j : ℕ) : 0 ≤ K j := by
    have h1 : 0 ≤ K j / A j := hsq j ▸ integral_nonneg fun _ => sq_nonneg _
    have h2 := mul_nonneg h1 (hApos j).le
    rwa [div_mul_cancel₀ _ (hApos j).ne'] at h2
  have hL0 (j : ℕ) : 0 ≤ L j := by
    have h1 : 0 ≤ L j / A j := hfour j ▸ integral_nonneg fun _ => by positivity
    have h2 := mul_nonneg h1 (hApos j).le
    rwa [div_mul_cancel₀ _ (hApos j).ne'] at h2
  have hmlim : Tendsto (fun j => H j / A j) atTop (𝓝 0) := by
    have h0 := hHlim.div hAlim one_ne_zero
    rw [zero_div] at h0
    exact h0
  have hev : ∀ᶠ j : ℕ in atTop, 1 ≤ j ∧ 1 < A j ∧ A j < 2 ∧ H j / A j ∈ Set.Icc (-1 : ℝ) 1 :=
    (eventually_ge_atTop 1).and (hA1.and ((hAlim.eventually (gt_mem_nhds (by norm_num))).and
      (hmlim.eventually (Icc_mem_nhds (by norm_num) (by norm_num)))))
  -- uniform polynomial bounds on the centered moments
  have hVev : ∀ᶠ j : ℕ in atTop, V j ≤ |CK| * ((j : ℝ) + 1) ^ 1 := by
    filter_upwards [hev] with j ⟨hj1, hA, _, _⟩
    rw [hV j, pow_one]
    have h1 : K j / A j ≤ K j := div_le_self (hK0 j) hA.le
    have h2 := hKup j hj1
    have h3 : CK * ((j : ℝ) + 1) ≤ |CK| * ((j : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    nlinarith [sq_nonneg (H j / A j)]
  have hQev : ∀ᶠ j : ℕ in atTop, Q j ≤ (8 * (|CL| + 1)) * ((j : ℝ) + 1) ^ 3 := by
    filter_upwards [hev] with j ⟨hj1, hA, _, hmI⟩
    have hm2 : (H j / A j) ^ 2 ≤ 1 := by nlinarith [hmI.1, hmI.2]
    have hm4 : (H j / A j) ^ 4 ≤ 1 := by
      have he : (H j / A j) ^ 4 = ((H j / A j) ^ 2) ^ 2 := by ring
      nlinarith [sq_nonneg (H j / A j)]
    have h1 : L j / A j ≤ L j := div_le_self (hL0 j) hA.le
    have h2 := hLup j hj1
    have hp1 : 1 ≤ ((j : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith [j.cast_nonneg (α := ℝ)])
    have h3 : CL * ((j : ℝ) + 1) ^ 3 ≤ |CL| * ((j : ℝ) + 1) ^ 3 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have := hQ j
    nlinarith
  obtain ⟨D₁, hD₁, hD₁b⟩ := exists_forall_le_of_eventually_pow hVev
  obtain ⟨D₂, hD₂, hD₂b⟩ := exists_forall_le_of_eventually_pow hQev
  set D := D₁ + D₂ with hD
  have hD0 : 0 ≤ D := add_nonneg hD₁ hD₂
  have hVb (j : ℕ) : V j ≤ D * ((j : ℝ) + 1) := by
    have := hD₁b j
    rw [pow_one] at this
    nlinarith [j.cast_nonneg (α := ℝ)]
  have hQb (j : ℕ) : Q j ≤ D * ((j : ℝ) + 1) ^ 3 := by
    have := hD₂b j
    have hp : 0 ≤ ((j : ℝ) + 1) ^ 3 := by positivity
    nlinarith
  -- eventual linear lower bound on the centered variances
  have hVlow : ∀ᶠ j : ℕ in atTop, 1 / (4 * cK) * (j : ℝ) ≤ V j := by
    filter_upwards [hev, hKlow, eventually_ge_atTop ⌈4 * cK⌉₊] with j ⟨_, _, hA2, hmI⟩ hKl hjc
    have hjc' : 4 * cK ≤ (j : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hjc)
    have hK := hK0 j
    change (j : ℝ) ≤ cK * |K j| at hKl
    rw [abs_of_nonneg hK] at hKl
    have hm2 : (H j / A j) ^ 2 ≤ 1 := by nlinarith [hmI.1, hmI.2]
    have hKA : K j / 2 ≤ K j / A j := div_le_div_of_nonneg_left hK (hApos j) hA2.le
    have ht : (j : ℝ) / cK ≤ K j := by rw [div_le_iff₀ hcK]; linarith
    have ht4 : 4 ≤ (j : ℝ) / cK := by rw [le_div_iff₀ hcK]; linarith
    have he : 1 / (4 * cK) * (j : ℝ) = (j : ℝ) / cK / 4 := by field_simp
    rw [he, hV j]
    linarith
  -- second and fourth moments of the centered sums
  have hcs (n : ℕ) := centered_sum_moments hYm hind hY4 n
  dsimp only at hcs
  have hZm (n : ℕ) : Measurable
      (fun x => ∑ j ∈ Finset.range n, centered P (spineIncrement B j) x) :=
    Finset.measurable_sum _ fun j _ => by
      unfold centered
      exact (hYm j).sub_const _
  have hsumV := eventually_sum_range_sq_lower (q := V) (c := 1 / (4 * cK)) (by positivity)
    hV0 hVlow
  have hVupp : ∀ᶠ n : ℕ in atTop,
      (∫ x, (∑ j ∈ Finset.range n, centered P (spineIncrement B j) x) ^ 2 ∂P) ≤
        (3 * D + 1) * (n : ℝ) ^ 2 := by
    refine Eventually.of_forall fun n => ?_
    rw [(hcs n).2.2.1]
    have hle : ∑ j ∈ Finset.range n, V j ≤ ∑ _j ∈ Finset.range n, D * (n : ℝ) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjn : (j : ℝ) + 1 ≤ n := by
        have := Finset.mem_range.1 hj
        exact_mod_cast this
      exact (hVb j).trans (mul_le_mul_of_nonneg_left hjn hD0)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hn2 : 0 ≤ (n : ℝ) ^ 2 := by positivity
    change ∑ j ∈ Finset.range n, V j ≤ _
    nlinarith
  have hQupp : ∀ᶠ n : ℕ in atTop,
      (∫ x, (∑ j ∈ Finset.range n, centered P (spineIncrement B j) x) ^ 4 ∂P) ≤
        (3 * D + 1) ^ 2 * (n : ℝ) ^ 4 := by
    refine Eventually.of_forall fun n => ?_
    rw [(hcs n).2.2.2]
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    have hle1 : ∑ j ∈ Finset.range n, Q j ≤ ∑ _j ∈ Finset.range n, D * (n : ℝ) ^ 3 := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjn : (j : ℝ) + 1 ≤ n := by
        have := Finset.mem_range.1 hj
        exact_mod_cast this
      exact (hQb j).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hjn 3) hD0)
    have hle2 : ∑ j ∈ Finset.range n, (∑ k ∈ Finset.range j, V k) * V j ≤
        ∑ _j ∈ Finset.range n, (n * (D * n)) * (D * n) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjn' := Finset.mem_range.1 hj
      have hVn (k : ℕ) (hk : k < n) : V k ≤ D * n := by
        have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
        exact (hVb k).trans (mul_le_mul_of_nonneg_left hkn hD0)
      have hin : ∑ k ∈ Finset.range j, V k ≤ n * (D * n) := by
        have h1 : ∑ k ∈ Finset.range j, V k ≤ ∑ _k ∈ Finset.range j, D * (n : ℝ) :=
          Finset.sum_le_sum fun k hk => hVn k ((Finset.mem_range.1 hk).trans hjn')
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
        have hjR : (j : ℝ) ≤ n := by exact_mod_cast hjn'.le
        exact h1.trans (mul_le_mul_of_nonneg_right hjR (mul_nonneg hD0 hn0))
      exact mul_le_mul hin (hVn j hjn') (hV0 j) (by positivity)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle1 hle2
    change ∑ j ∈ Finset.range n, Q j +
        6 * ∑ j ∈ Finset.range n, (∑ k ∈ Finset.range j, V k) * V j ≤ _
    have hn4 : 0 ≤ (n : ℝ) ^ 4 := by positivity
    have heq1 : (n : ℝ) * (D * n ^ 3) = D * n ^ 4 := by ring
    have heq2 : (n : ℝ) * (n * (D * n) * (D * n)) = D ^ 2 * n ^ 4 := by ring
    have hDD : D + 6 * D ^ 2 ≤ (3 * D + 1) ^ 2 := by nlinarith
    nlinarith
  obtain ⟨η, δ, hη, hδ, htail⟩ := eventually_centered_tail (ν := P)
    (Z := fun n x => ∑ j ∈ Finset.range n, centered P (spineIncrement B j) x)
    hZm (fun n => (hcs n).1) (fun n => (hcs n).2.1) (c := 1 / (4 * cK) / 16)
    (C := 3 * D + 1) (by positivity) (by positivity)
    (by
      filter_upwards [hsumV] with n hn
      rw [(hcs n).2.2.1]
      exact hn)
    hVupp hQupp
  -- the drift is negligible on the linear scale
  have hces := hmlim.cesaro
  have hces' : ∀ᶠ n : ℕ in atTop,
      -(η / 2) < (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H i / A i :=
    hces.eventually (lt_mem_nhds (neg_lt_zero.2 (half_pos hη)))
  have htail' : ∀ᶠ n : ℕ in atTop,
      δ ≤ P.real {v | η / 2 * n ≤ ∑ j ∈ Finset.range n, spineIncrement B j v} := by
    filter_upwards [htail, hces', eventually_ge_atTop 1] with n hn hcn hn1
    refine hn.trans (measureReal_mono ?_)
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    have hsplit : ∑ j ∈ Finset.range n, centered P (spineIncrement B j) v =
        ∑ j ∈ Finset.range n, spineIncrement B j v - ∑ j ∈ Finset.range n, H j / A j := by
      simp only [centered, hm]
      rw [Finset.sum_sub_distrib]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hmul := mul_lt_mul_of_pos_left hcn hnpos
    rw [← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul] at hmul
    rw [hsplit] at hv
    nlinarith
  -- the ballot lemma
  have hlower : ∀ j, 1 ≤ j → ∀ᵐ v ∂P,
      -max (Real.log B - Real.log (floorSeq B 1)) 0 ≤ spineIncrement B j v := by
    intro j hj
    filter_upwards [ae_spineIncrement_lower hpos hmean hB h hj] with v hv
    linarith [le_max_left (Real.log B - Real.log (floorSeq B 1)) 0]
  have hsum : Summable fun j => (∫ v, spineIncrement B j v ∂P)⁺ := by
    refine Summable.of_norm_bounded_eventually_nat
      ((summable_geometric_of_lt_one hρ0 hρ1).mul_left |C₀|) ?_
    filter_upwards [hev] with j ⟨hj1, hA, _, _⟩
    rw [hm j, Real.norm_of_nonneg (posPart_nonneg _)]
    have hpow : 0 ≤ (2 / B) ^ j := pow_nonneg hρ0 j
    refine sup_le ?_ (mul_nonneg (abs_nonneg _) hpow)
    by_cases hH : H j ≤ 0
    · have : H j / A j ≤ 0 := div_nonpos_of_nonpos_of_nonneg hH (hApos j).le
      exact this.trans (mul_nonneg (abs_nonneg _) hpow)
    · rw [not_le] at hH
      calc H j / A j ≤ H j := div_le_self hH.le hA.le
        _ ≤ C₀ * (2 / B) ^ j := hHup j hj1
        _ ≤ |C₀| * (2 / B) ^ j := mul_le_mul_of_nonneg_right (le_abs_self _) hpow
  exact response_ballot_aux P (spineIncrement B) hind hYi (le_max_right _ _) (half_pos hη) hδ
    hlower (hYi 0).neg_part hsum htail'

/-! ### The spine weight -/

/-- The base of the spine weight is at least one. -/
theorem one_le_spineW_base {B : ℝ} (hB : 2 < B) {n : ℕ} {r : ℝ} (hr : 0 < r)
    (u : Fin n → ℝ) :
    1 ≤ 1 + (B - 1) / (B * r) * ∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B u k) :=
  le_add_of_nonneg_right (mul_nonneg (div_nonneg (by linarith) (mul_pos (by linarith) hr).le)
    (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le))

/-- The spine weight is nonnegative. -/
theorem spineW_nonneg {B : ℝ} (hB : 2 < B) {n : ℕ} {r : ℝ} (hr : 0 < r) (u : Fin n → ℝ) :
    0 ≤ spineW B n r u :=
  Real.rpow_nonneg (zero_le_one.trans (one_le_spineW_base hB hr u)) _

/-- Layered pointwise bound for the spine weight (`response.tex` lines 121–130): with
`p = 1 - θ` and `x = e^{-p}`, `w_n ≤ ∑_{m<L} x^m 1{∀ k ≤ n, S_k ≥ -(m + 1 + t)} + x^L`
whenever `log (B R_0^* / c) ≤ t`. -/
theorem spineW_le_layers {B : ℝ} (hB : 2 < B) {n : ℕ} {r : ℝ} (hr : 0 < r)
    (u : Fin n → ℝ) (L : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (hlt : Real.log (B * r / (B - 1)) ≤ t) :
    spineW B n r u ≤ ∑ m ∈ Finset.range L, Real.exp (-(1 - theta B)) ^ m *
        {u : Fin n → ℝ | ∀ k ≤ n, -((m : ℝ) + 1 + t) ≤ spineWalk B u k}.indicator 1 u +
      Real.exp (-(1 - theta B)) ^ L := by
  classical
  set p := 1 - theta B with hpdef
  have hp : 0 < p := by have := theta_lt_one hB; linarith
  set x := Real.exp (-p) with hxdef
  have hx0 : 0 < x := Real.exp_pos _
  set ℓ := Real.log (B * r / (B - 1)) with hℓ
  have hBr : 0 < B * r := mul_pos (by linarith) hr
  have hfrac : 0 < B * r / (B - 1) := div_pos hBr (by linarith)
  have hcoef : (B - 1) / (B * r) = Real.exp (-ℓ) := by
    rw [hℓ, Real.exp_neg, Real.exp_log hfrac, inv_div]
  set base := 1 + (B - 1) / (B * r) * ∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B u k)
    with hbase
  have hbase1 : 1 ≤ base := one_le_spineW_base hB hr u
  have hw : spineW B n r u = base ^ (-p) := rfl
  have hw1 : spineW B n r u ≤ 1 := by
    rw [hw]
    exact Real.rpow_le_one_of_one_le_of_nonpos hbase1 (by linarith)
  let G : ℕ → Prop := fun m => ∀ k ∈ Finset.Icc 1 n, -((m : ℝ) + 1) ≤ ℓ + spineWalk B u k
  have hbad (m : ℕ) (hm : ¬ G m) : spineW B n r u ≤ x ^ (m + 1) := by
    simp only [G, not_forall, not_le] at hm
    obtain ⟨k, hk, hlt'⟩ := hm
    have hterm : Real.exp ((m : ℝ) + 1) ≤
        (B - 1) / (B * r) * Real.exp (-spineWalk B u k) := by
      rw [hcoef, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have hsum : (B - 1) / (B * r) * Real.exp (-spineWalk B u k) ≤
        (B - 1) / (B * r) * ∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B u k) :=
      mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (f := fun k => Real.exp (-spineWalk B u k))
          (fun _ _ => (Real.exp_pos _).le) hk) (div_nonneg (by linarith) hBr.le)
    have hle : Real.exp ((m : ℝ) + 1) ≤ base := by rw [hbase]; linarith
    rw [hw]
    calc base ^ (-p) ≤ Real.exp ((m : ℝ) + 1) ^ (-p) :=
          Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hle (by linarith)
      _ = x ^ (m + 1) := by
          rw [← Real.exp_mul, hxdef, ← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
  have hgood (m : ℕ) (hm : G m) :
      u ∈ {u : Fin n → ℝ | ∀ k ≤ n, -((m : ℝ) + 1 + t) ≤ spineWalk B u k} := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have h0 : spineWalk B u 0 = 0 := by simp [spineWalk]
      rw [h0]
      have : (0 : ℝ) ≤ m := m.cast_nonneg
      linarith
    · have := hm k (Finset.mem_Icc.2 ⟨hk0, hk⟩)
      linarith
  have hterm_nonneg (m : ℕ) : 0 ≤ x ^ m *
      {u : Fin n → ℝ | ∀ k ≤ n, -((m : ℝ) + 1 + t) ≤ spineWalk B u k}.indicator 1 u :=
    mul_nonneg (pow_pos hx0 m).le (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hsum0 : 0 ≤ ∑ m ∈ Finset.range L, x ^ m *
      {u : Fin n → ℝ | ∀ k ≤ n, -((m : ℝ) + 1 + t) ≤ spineWalk B u k}.indicator 1 u :=
    Finset.sum_nonneg fun m _ => hterm_nonneg m
  have hex : ∃ m, G m ∨ m = L := ⟨L, Or.inr rfl⟩
  set m₀ := Nat.find hex with hm₀
  have hm₀L : m₀ ≤ L := Nat.find_min' hex (Or.inr rfl)
  have hwm : spineW B n r u ≤ x ^ m₀ := by
    rcases Nat.eq_zero_or_pos m₀ with h0 | hpos'
    · rw [h0, pow_zero]
      exact hw1
    · obtain ⟨m', hm'⟩ : ∃ m', m₀ = m' + 1 := ⟨m₀ - 1, by omega⟩
      have hnot := Nat.find_min hex (show m' < Nat.find hex by omega)
      rw [hm']
      exact hbad m' fun hG => hnot (Or.inl hG)
  by_cases hlt' : m₀ < L
  · have hG : G m₀ := (Nat.find_spec hex).resolve_right (ne_of_lt hlt')
    have hmem := hgood m₀ hG
    have hsingle := Finset.single_le_sum (fun m _ => hterm_nonneg m)
      (Finset.mem_range.2 hlt')
    rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one] at hsingle
    have hxL : 0 ≤ x ^ L := (pow_pos hx0 L).le
    linarith
  · have hL : m₀ = L := le_antisymm hm₀L (not_lt.1 hlt')
    rw [hL] at hwm
    linarith

/-- The probabilistic estimate behind `response:linear` (`response.tex` lines 119–130):
a ballot bound for the spine walk gives `Ê w_n ≤ C / (n + 1)`. -/
theorem spineMeanW_le_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) {h : ℝ}
    (hball : ∃ C : ℝ, ∀ (n : ℕ) (z : ℝ), 0 ≤ z →
      (infiniteSpineMeasure μ B h).real
          {v | ∀ k ≤ n, -z ≤ ∑ j ∈ Finset.range k, spineIncrement B j v} ≤
        C * (z + 1) / (n + 1)) :
    ∃ C : ℝ, ∀ n : ℕ, spineMeanW μ B h n ≤ C / ((n : ℝ) + 1) := by
  have (i : ℕ) : IsProbabilityMeasure (tiltedLaw μ B h i) :=
    isProbabilityMeasure_tiltedLaw_of hpos hmean hB h i
  obtain ⟨C₁, hC₁⟩ := hball
  set C := max C₁ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  set p := 1 - theta B with hpdef
  have hp : 0 < p := by have := theta_lt_one hB; linarith
  set x := Real.exp (-p) with hxdef
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := by
    have h1 := Real.exp_lt_exp.2 (show -p < 0 by linarith)
    rwa [Real.exp_zero] at h1
  have hxn : ‖x‖ < 1 := by rw [Real.norm_of_nonneg hx0.le]; exact hx1
  have hS0 : Summable (fun m : ℕ => x ^ m) := summable_geometric_of_lt_one hx0.le hx1
  have hS1 : Summable (fun m : ℕ => x ^ m * ((m : ℝ) + 2)) := by
    have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1 hxn).add (hS0.mul_left 2)
    convert h1 using 1
    funext m
    ring
  set G0 := ∑' m : ℕ, x ^ m with hG0def
  set G1 := ∑' m : ℕ, x ^ m * ((m : ℝ) + 2) with hG1def
  have hG0 : 0 ≤ G0 := tsum_nonneg fun m => (pow_pos hx0 m).le
  have hG1 : 0 ≤ G1 := tsum_nonneg fun m => mul_nonneg (pow_pos hx0 m).le (by positivity)
  set c0 := |Real.log B - Real.log (B - 1)| with hc0def
  have hc0 : 0 ≤ c0 := abs_nonneg _
  have hlogint : Integrable (fun r => |Real.log r|) (tiltedLaw μ B h 0) :=
    (integrable_log_tiltedLaw_of hpos hmean hB h 0).abs
  set E1 := ∫ r, |Real.log r| ∂(tiltedLaw μ B h 0) with hE1def
  have hE1 : 0 ≤ E1 := integral_nonneg fun _ => abs_nonneg _
  refine ⟨C * (G1 + G0 * (E1 + c0)) + 1 / p, fun n => ?_⟩
  set π := Measure.pi fun j : Fin n => tiltedLaw μ B h j with hπdef
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hCn : 0 ≤ C / ((n : ℝ) + 1) := div_nonneg hC0 hn1.le
  have hρm : Measurable (fun v : ℕ → ℝ => fun j : Fin n => v j) := by fun_prop
  have hπE (z : ℝ) (hz : 0 ≤ z) :
      π.real {u : Fin n → ℝ | ∀ k ≤ n, -z ≤ spineWalk B u k} ≤
        C * (z + 1) / ((n : ℝ) + 1) := by
    rw [hπdef, ← map_infiniteSpine_restrict hpos hmean hB h n,
      map_measureReal_apply hρm (measurableSet_spineWalk_survive B n z)]
    have hpre : (fun v : ℕ → ℝ => fun j : Fin n => v j) ⁻¹'
        {u : Fin n → ℝ | ∀ k ≤ n, -z ≤ spineWalk B u k} =
        {v | ∀ k ≤ n, -z ≤ ∑ j ∈ Finset.range k, spineIncrement B j v} := by
      ext v
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      constructor
      · intro hv k hk
        rw [← spineWalk_restrict B hk v]
        exact hv k hk
      · intro hv k hk
        rw [spineWalk_restrict B hk v]
        exact hv k hk
    rw [hpre]
    refine (hC₁ n z hz).trans ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)) hn1.le
  -- the inner (walk) integral at a fixed positive `R_0^*`
  have hinner (r : ℝ) (hr : 0 < r) :
      ∫ u, spineW B n r u ∂π ≤
        C / ((n : ℝ) + 1) * G0 * |Real.log r| +
          (C / ((n : ℝ) + 1) * (G1 + G0 * c0) + x ^ (n + 1)) := by
    set t := |Real.log r| + c0 with htdef
    have ht0 : 0 ≤ t := by positivity
    have hlt : Real.log (B * r / (B - 1)) ≤ t := by
      rw [Real.log_div (mul_pos (by linarith) hr).ne' (by linarith),
        Real.log_mul (by linarith) hr.ne']
      have h1 := le_abs_self (Real.log r)
      have h2 := le_abs_self (Real.log B - Real.log (B - 1))
      linarith
    let E := fun m : ℕ => {u : Fin n → ℝ | ∀ k ≤ n, -((m : ℝ) + 1 + t) ≤ spineWalk B u k}
    have hE (m : ℕ) : MeasurableSet (E m) := measurableSet_spineWalk_survive B n _
    have hterm (m : ℕ) : Integrable (fun u => x ^ m * (E m).indicator 1 u) π :=
      ((integrable_const (1 : ℝ)).indicator (hE m)).const_mul _
    have hsumi : Integrable (fun u => ∑ m ∈ Finset.range (n + 1),
        x ^ m * (E m).indicator 1 u) π :=
      integrable_finsetSum _ fun m _ => hterm m
    have hpt (u : Fin n → ℝ) : spineW B n r u ≤
        ∑ m ∈ Finset.range (n + 1), x ^ m * (E m).indicator 1 u + x ^ (n + 1) :=
      spineW_le_layers hB hr u (n + 1) ht0 hlt
    have hsum_le : ∑ m ∈ Finset.range (n + 1), x ^ m * ((m : ℝ) + 2) ≤ G1 :=
      hS1.sum_le_tsum _ fun m _ => mul_nonneg (pow_pos hx0 m).le (by positivity)
    have hsum_le' : ∑ m ∈ Finset.range (n + 1), x ^ m ≤ G0 :=
      hS0.sum_le_tsum _ fun m _ => (pow_pos hx0 m).le
    calc ∫ u, spineW B n r u ∂π
        ≤ ∫ u, (∑ m ∈ Finset.range (n + 1), x ^ m * (E m).indicator 1 u + x ^ (n + 1)) ∂π :=
          integral_mono_of_nonneg (Eventually.of_forall fun u => spineW_nonneg hB hr u)
            (hsumi.add (integrable_const _)) (Eventually.of_forall hpt)
      _ = ∑ m ∈ Finset.range (n + 1), x ^ m * π.real (E m) + x ^ (n + 1) := by
          rw [integral_add hsumi (integrable_const _), integral_finsetSum _ fun m _ => hterm m]
          congr 1
          · refine Finset.sum_congr rfl fun m _ => ?_
            rw [integral_const_mul, integral_indicator_one (hE m)]
          · simp
      _ ≤ ∑ m ∈ Finset.range (n + 1), x ^ m * (C * (((m : ℝ) + 1 + t) + 1) / ((n : ℝ) + 1)) +
            x ^ (n + 1) := by
          refine add_le_add (Finset.sum_le_sum fun m _ => ?_) le_rfl
          exact mul_le_mul_of_nonneg_left (hπE _ (by positivity)) (pow_pos hx0 m).le
      _ = C / ((n : ℝ) + 1) * (∑ m ∈ Finset.range (n + 1), x ^ m * ((m : ℝ) + 2) +
            t * ∑ m ∈ Finset.range (n + 1), x ^ m) + x ^ (n + 1) := by
          congr 1
          rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun m _ => ?_
          field_simp
          ring
      _ ≤ C / ((n : ℝ) + 1) * (G1 + t * G0) + x ^ (n + 1) := by
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ hCn) le_rfl
          exact add_le_add hsum_le (mul_le_mul_of_nonneg_left hsum_le' ht0)
      _ = _ := by rw [htdef]; ring
  -- the outer integral over `R_0^*`
  have hint : Integrable (fun y : ℝ × (Fin n → ℝ) => spineW B n y.1 y.2)
      ((tiltedLaw μ B h 0).prod π) := (integrable_spine_aux hpos hmean hB h n).1
  have hxL : x ^ (n + 1) ≤ 1 / p / ((n : ℝ) + 1) := by
    have he : x ^ (n + 1) = 1 / Real.exp (p * ((n : ℝ) + 1)) := by
      rw [hxdef, ← Real.exp_nat_mul, one_div, ← Real.exp_neg]
      congr 1
      push_cast
      ring
    have hpn : 0 < p * ((n : ℝ) + 1) := mul_pos hp hn1
    have hexp : p * ((n : ℝ) + 1) ≤ Real.exp (p * ((n : ℝ) + 1)) := by
      linarith [Real.add_one_le_exp (p * ((n : ℝ) + 1))]
    rw [he, div_div]
    exact one_div_le_one_div_of_le hpn hexp
  have hRHS : Integrable (fun r => C / ((n : ℝ) + 1) * G0 * |Real.log r| +
      (C / ((n : ℝ) + 1) * (G1 + G0 * c0) + x ^ (n + 1))) (tiltedLaw μ B h 0) :=
    (hlogint.const_mul _).add (integrable_const _)
  calc spineMeanW μ B h n
      = ∫ r, ∫ u, spineW B n r u ∂π ∂(tiltedLaw μ B h 0) := integral_prod _ hint
    _ ≤ ∫ r, (C / ((n : ℝ) + 1) * G0 * |Real.log r| +
          (C / ((n : ℝ) + 1) * (G1 + G0 * c0) + x ^ (n + 1))) ∂(tiltedLaw μ B h 0) := by
        refine integral_mono_ae hint.integral_prod_left hRHS ?_
        filter_upwards [ae_pos_tiltedLaw_of hpos hB h 0] with r hr
        exact hinner r hr
    _ = C / ((n : ℝ) + 1) * G0 * E1 + (C / ((n : ℝ) + 1) * (G1 + G0 * c0) + x ^ (n + 1)) := by
        rw [integral_add (hlogint.const_mul _) (integrable_const _), integral_const_mul]
        simp [hE1def]
    _ ≤ (C * (G1 + G0 * (E1 + c0)) + 1 / p) / ((n : ℝ) + 1) := by
        have he : C / ((n : ℝ) + 1) * G0 * E1 + C / ((n : ℝ) + 1) * (G1 + G0 * c0) =
            C * (G1 + G0 * (E1 + c0)) / ((n : ℝ) + 1) := by
          field_simp
          ring
        rw [add_div]
        linarith

/-- `response:linear` (`response.tex` lines 98–132), from `th:product` and the spine
identities: at `h_c > h_a`, `𝒟_n = ∂_h A_n(h_c) ≤ C (n + 1)` for all `n`.

The strict shift `_hshift` is the source's standing assumption of `response_linear`; in this
conditional form it enters only through `hProd` (the conclusion of `criticalProduct`, which
assumes it), so the proof does not use it directly. -/
theorem response_linear_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (_hshift : Real.log (B - 1) < criticalPoint μ B)
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
    (hSpine : ∀ n : ℕ,
      0 < 1 / theta B - Real.log B ∧
        deriv (fun h' => tiltedMass μ B h' n) (criticalPoint μ B) /
            tiltedProduct μ B (criticalPoint μ B) n =
          theta B * tiltedMass μ B (criticalPoint μ B) 0 *
            spineMeanW μ B (criticalPoint μ B) n ∧
        deriv (fun h' => tiltedLogMoment μ B h' 1 n) (criticalPoint μ B) /
            tiltedProduct μ B (criticalPoint μ B) n =
          theta B * tiltedMass μ B (criticalPoint μ B) 0 *
            spineMeanWLog μ B (criticalPoint μ B) n) :
    ∃ C : ℝ, ∀ n : ℕ,
      deriv (fun h => tiltedMass μ B h n) (criticalPoint μ B) ≤ C * ((n : ℝ) + 1) := by
  obtain ⟨C, hC, hbd, -, -, hA1, hAΘ, hKΘ, hHO, -⟩ := hProd
  obtain ⟨C₀, hC₀⟩ := criticalMoments_aux hB
  have hcrit := (hC₀ μ hpos hmean (criticalPoint μ B)
    (criticalPoint_isGreatest_aux hpos hmean hB).1).1
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hAlim : Tendsto (fun n : ℕ => tiltedMass μ B (criticalPoint μ B) n) atTop (𝓝 1) :=
    tendsto_sub_nhds_zero_iff.1 (hAΘ.isBigO.trans_tendsto hinv)
  have hHlim := hHO.trans_tendsto hinv
  obtain ⟨cK, hcK, hKw⟩ := hKΘ.isBigO_symm.exists_pos
  have hKlow : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ≤ cK * |tiltedLogMoment μ B (criticalPoint μ B) 2 n| := by
    filter_upwards [hKw.bound] with n hn
    simpa using hn
  have hKup : ∀ n : ℕ, 1 ≤ n →
      tiltedLogMoment μ B (criticalPoint μ B) 2 n ≤ C * ((n : ℝ) + 1) := by
    intro n hn
    obtain ⟨-, hPi, hK2, -⟩ := hbd n hn
    have hM : 0 ≤ C * ((n : ℝ) + 1) := by positivity
    have hsq : tiltedLogMoment μ B (criticalPoint μ B) 2 n ^ 2 ≤ (C * ((n : ℝ) + 1)) ^ 2 := by
      nlinarith
    nlinarith
  obtain ⟨Cb, hCb⟩ := spine_ballot_of hpos hmean hB hA1 hAlim hHlim
    (fun n hn => (hcrit n hn).2) hKup hcK hKlow (fun n hn => (hbd n hn).2.2.2)
  obtain ⟨Cw, hCw⟩ := spineMeanW_le_of hpos hmean hB ⟨Cb, hCb⟩
  have hA0 := tiltedMass_pos_of hpos hmean hB (criticalPoint μ B) 0
  have hκ : 0 ≤ theta B * tiltedMass μ B (criticalPoint μ B) 0 :=
    mul_nonneg (theta_pos hB).le hA0.le
  refine ⟨theta B * tiltedMass μ B (criticalPoint μ B) 0 * max Cw 0 * (C + 1), fun n => ?_⟩
  have hPipos : 0 < tiltedProduct μ B (criticalPoint μ B) n :=
    Finset.prod_pos fun j _ => tiltedMass_pos_of hpos hmean hB _ j
  have hs := (hSpine n).2.1
  rw [div_eq_iff hPipos.ne'] at hs
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hPiup : tiltedProduct μ B (criticalPoint μ B) n ≤ (C + 1) * ((n : ℝ) + 1) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [tiltedProduct]
      linarith
    · have := (hbd n hn).2.1
      nlinarith [sq_nonneg ((n : ℝ) + 1)]
  have hw : spineMeanW μ B (criticalPoint μ B) n ≤ max Cw 0 / ((n : ℝ) + 1) :=
    (hCw n).trans (div_le_div_of_nonneg_right (le_max_left _ _) hn1.le)
  have hM : 0 ≤ max Cw 0 / ((n : ℝ) + 1) := div_nonneg (le_max_right _ _) hn1.le
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hκ) hPipos.le
  have h2 := mul_le_mul_of_nonneg_left hPiup (mul_nonneg hκ hM)
  have h3 : theta B * tiltedMass μ B (criticalPoint μ B) 0 * (max Cw 0 / ((n : ℝ) + 1)) *
      ((C + 1) * ((n : ℝ) + 1) ^ 2) =
      theta B * tiltedMass μ B (criticalPoint μ B) 0 * max Cw 0 * (C + 1) * ((n : ℝ) + 1) := by
    field_simp
  rw [hs]
  linarith

end DiamondPinning
