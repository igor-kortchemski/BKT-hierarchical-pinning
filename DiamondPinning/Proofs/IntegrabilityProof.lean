module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Model.Basic
public import DiamondPinning.Model.Contacts
public import DiamondPinning.Model.Spine
public import DiamondPinning.Model.Window
public import DiamondPinning.Proofs.Env
public import DiamondPinning.Proofs.ContactsProof
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Integrability for the field response

This file proves the tilted logarithmic-moment bounds, the finite exponential-sum
differentiation envelope, and the contact, product-kernel and spine
integrability results used by `Statements/Response`.  It covers the moment
integrability in `source/response.tex`, lines 79–95, the kernel calculation at
lines 175–196, and the contact-moment setting at lines 205–242.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology
open scoped BigOperators

/-- A tilted absolute logarithmic power is linearly bounded on the positive
reals.  This is the shifted form of `exists_tiltedLogPower_bound`. -/
theorem exists_rpow_abs_log_sub_bound {θ a s : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hs : 0 ≤ s) :
    ∃ C : ℝ, ∀ x : ℝ, 0 < x → x ^ θ * |Real.log x - a| ^ s ≤ C * (1 + x) := by
  let B := Real.exp (Real.log 2 / θ)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 2 < B := by
    rw [show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)]]
    rw [Real.exp_lt_exp]
    exact (lt_div_iff₀ hθ).2 (by nlinarith)
  have htheta : theta B = θ := by
    simp only [theta, B, Real.log_exp]
    field_simp
  obtain ⟨C, hC⟩ := exists_tiltedLogPower_bound hB hs
  have hC0 : 0 ≤ C := by
    have h := hC (Real.exp 1) (Real.exp_pos 1)
    rw [htheta, Real.log_exp, abs_one, Real.one_rpow] at h
    have hl : 0 ≤ Real.exp 1 ^ θ := Real.rpow_nonneg (Real.exp_pos 1).le _
    have hr : 0 ≤ C * (1 + Real.exp 1) := hl.trans (by simpa using h)
    exact (mul_nonneg_iff_of_pos_right (by positivity : (0 : ℝ) < 1 + Real.exp 1)).mp hr
  let d := 1 + Real.exp (-a)
  have hd1 : 1 ≤ d := by dsimp [d]; linarith [Real.exp_pos (-a)]
  have hexp : Real.exp (-a) ≤ d := by dsimp [d]; linarith [Real.exp_pos (-a)]
  refine ⟨Real.exp (a * θ) * C * d, fun x hx => ?_⟩
  have hea : 0 < Real.exp a := Real.exp_pos a
  have hy : 0 < x / Real.exp a := div_pos hx hea
  have h := hC (x / Real.exp a) hy
  rw [htheta, Real.log_div hx.ne' hea.ne', Real.log_exp] at h
  have hexp_rpow : Real.exp (a * θ) = Real.exp a ^ θ := by
    rw [Real.rpow_def_of_pos hea, Real.log_exp]
  have hscale : x ^ θ = Real.exp (a * θ) * (x / Real.exp a) ^ θ := by
    calc
      x ^ θ = (x / Real.exp a * Real.exp a) ^ θ := by rw [div_mul_cancel₀ x hea.ne']
      _ = Real.exp (a * θ) * (x / Real.exp a) ^ θ := by
        rw [Real.mul_rpow hy.le hea.le, hexp_rpow]
        ring
  rw [hscale]
  calc
    Real.exp (a * θ) * (x / Real.exp a) ^ θ * |Real.log x - a| ^ s =
        Real.exp (a * θ) * ((x / Real.exp a) ^ θ * |Real.log x - a| ^ s) := by ring
    _ ≤ Real.exp (a * θ) * (C * (1 + x / Real.exp a)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ ≤ Real.exp (a * θ) * (C * (d * (1 + x))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ hC0
      rw [div_eq_mul_inv, ← Real.exp_neg a]
      have hx0 : 0 ≤ x := hx.le
      have hd0 : 0 ≤ d := zero_le_one.trans hd1
      nlinarith [mul_le_mul_of_nonneg_right hexp hx0,
        mul_le_mul_of_nonneg_right hd1 hx0]
    _ = Real.exp (a * θ) * C * d * (1 + x) := by ring

/-- The corresponding domination gives integrability whenever the positive
random variable has a finite first moment. -/
theorem integrable_rpow_abs_log_sub_of {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {q : Ω → ℝ} (hq : AEMeasurable q ν)
    (hqpos : ∀ᵐ x ∂ν, 0 < q x) (hqint : Integrable q ν)
    {θ a s : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hs : 0 ≤ s) :
    Integrable (fun x => q x ^ θ * |Real.log (q x) - a| ^ s) ν := by
  obtain ⟨C, hC⟩ := exists_rpow_abs_log_sub_bound hθ hθ1 hs
  have hdom : Integrable (fun x => C * (1 + q x)) ν :=
    ((integrable_const 1).add hqint).const_mul C
  apply hdom.mono'
  have hlogabs : AEMeasurable (fun x => |Real.log (q x) - a|) ν := by fun_prop
  exact (by fun_prop)
  filter_upwards [hqpos] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _)
    (Real.rpow_nonneg (abs_nonneg _) _))]
  exact hC (q x) hx

/-- The shifted absolute tilted logarithmic powers are integrable under `lawR`.
This proves `DiamondPinning.integrable_absTiltedLogRpow` (in `DiamondPinning.Statements.Response`).
-/
theorem integrable_absTiltedLogRpow_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun x : ℝ => x ^ theta B * |Real.log x - Real.log B| ^ s)
      (lawR μ B h n) := by
  let : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  exact integrable_rpow_abs_log_sub_of (lawR μ B h n) measurable_id.aemeasurable
    (ae_pos_lawR hpos hB h n) (integrable_lawR_of hpos hmean hB h n)
    (theta_pos hB) (theta_lt_one hB) hs


/-! ### Deterministic finite exponential sums -/

private noncomputable def expSum {m : ℕ} (p : Fin (m + 1) → ℝ) (d : ℕ) (h : ℝ) : ℝ :=
  ∑ k, p k * (k.val : ℝ) ^ d * Real.exp ((k.val : ℝ) * h)

private noncomputable def logExpSum {m : ℕ} (p : Fin (m + 1) → ℝ) (h : ℝ) : ℝ :=
  Real.log (expSum p 0 h)

private noncomputable def logExpSumD {m : ℕ} (p : Fin (m + 1) → ℝ) (h : ℝ) : ℝ :=
  expSum p 1 h / expSum p 0 h

private noncomputable def logExpSumD2 {m : ℕ} (p : Fin (m + 1) → ℝ) (h : ℝ) : ℝ :=
  expSum p 2 h / expSum p 0 h - (logExpSumD p h) ^ 2

private theorem hasDerivAt_expSum {m : ℕ} (p : Fin (m + 1) → ℝ) (d : ℕ) (h : ℝ) :
    HasDerivAt (expSum p d) (expSum p (d + 1) h) h := by
  apply HasDerivAt.fun_sum
  intro k _
  convert (hasDerivAt_const h (p k * (k.val : ℝ) ^ d)).mul
    (((hasDerivAt_id h).const_mul (k.val : ℝ)).exp) using 1
  · ext y
    rfl
  · simp only [id_eq, pow_succ]
    ring

private theorem expSum_nonneg {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (d : ℕ) (h : ℝ) : 0 ≤ expSum p d h := by
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (mul_nonneg (hp k) (pow_nonneg (Nat.cast_nonneg _) _))
    (Real.exp_pos _).le

private theorem expSum_zero_pos {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hsum : 0 < ∑ k, p k) (h : ℝ) : 0 < expSum p 0 h := by
  obtain ⟨k, _, hk⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun k (_ : k ∈ Finset.univ) => hp k)).mp hsum
  have hterm : 0 < p k * Real.exp ((k.val : ℝ) * h) := mul_pos hk (Real.exp_pos _)
  have hk' : 0 < p k * (k.val : ℝ) ^ 0 * Real.exp ((k.val : ℝ) * h) := by
    simpa using hterm
  exact Finset.sum_pos' (fun i _ => mul_nonneg
    (mul_nonneg (hp i) (pow_nonneg (Nat.cast_nonneg _) _)) (Real.exp_pos _).le)
    ⟨k, Finset.mem_univ _, hk'⟩

private theorem hasDerivAt_logExpSum {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hsum : 0 < ∑ k, p k) (h : ℝ) :
    HasDerivAt (logExpSum p) (logExpSumD p h) h := by
  change HasDerivAt (fun h => Real.log (expSum p 0 h))
    (expSum p 1 h / expSum p 0 h) h
  simpa only [zero_add] using
    (hasDerivAt_expSum p 0 h).log (expSum_zero_pos hp hsum h).ne'

private theorem hasDerivAt_logExpSumD {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hsum : 0 < ∑ k, p k) (h : ℝ) :
    HasDerivAt (logExpSumD p)
      ((expSum p 2 h * expSum p 0 h - expSum p 1 h * expSum p 1 h) /
        expSum p 0 h ^ 2) h := by
  change HasDerivAt (fun h => expSum p 1 h / expSum p 0 h)
    ((expSum p 2 h * expSum p 0 h - expSum p 1 h * expSum p 1 h) /
      expSum p 0 h ^ 2) h
  convert (hasDerivAt_expSum p 1 h).div (hasDerivAt_expSum p 0 h)
      (expSum_zero_pos hp hsum h).ne' using 1

private theorem logExpSumD_nonneg {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hsum : 0 < ∑ k, p k) (h : ℝ) :
    0 ≤ logExpSumD p h :=
  div_nonneg (expSum_nonneg hp 1 h) (expSum_zero_pos hp hsum h).le

private theorem logExpSumD_le {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hsum : 0 < ∑ k, p k) (h : ℝ) :
    logExpSumD p h ≤ (m : ℝ) := by
  rw [logExpSumD, div_le_iff₀ (expSum_zero_pos hp hsum h)]
  simp only [expSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hk : (k.val : ℝ) ≤ (m : ℝ) := by exact_mod_cast k.is_le
  have hp' : 0 ≤ p k := hp k
  have he : 0 < Real.exp ((k.val : ℝ) * h) := Real.exp_pos _
  simp only [pow_zero, pow_one, mul_one]
  calc
    p k * (k.val : ℝ) * Real.exp ((k.val : ℝ) * h) =
        (p k * Real.exp ((k.val : ℝ) * h)) * (k.val : ℝ) := by ring
    _ ≤ (p k * Real.exp ((k.val : ℝ) * h)) * (m : ℝ) :=
      mul_le_mul_of_nonneg_left hk (mul_nonneg hp' he.le)
    _ = m * (p k * Real.exp ((k.val : ℝ) * h)) := by ring

private theorem secondRatio_nonneg {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hsum : 0 < ∑ k, p k) (h : ℝ) :
    0 ≤ expSum p 2 h / expSum p 0 h :=
  div_nonneg (expSum_nonneg hp 2 h) (expSum_zero_pos hp hsum h).le

private theorem secondRatio_le {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hsum : 0 < ∑ k, p k) (h : ℝ) :
    expSum p 2 h / expSum p 0 h ≤ (m : ℝ) ^ 2 := by
  rw [div_le_iff₀ (expSum_zero_pos hp hsum h)]
  simp only [expSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hk : (k.val : ℝ) ≤ (m : ℝ) := by exact_mod_cast k.is_le
  have hk0 : 0 ≤ (k.val : ℝ) := Nat.cast_nonneg _
  have hp' : 0 ≤ p k := hp k
  have he : 0 < Real.exp ((k.val : ℝ) * h) := Real.exp_pos _
  simp only [pow_zero, mul_one]
  have hk2 : (k.val : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ hk0 hk 2
  calc
    p k * (k.val : ℝ) ^ 2 * Real.exp ((k.val : ℝ) * h) =
        (p k * Real.exp ((k.val : ℝ) * h)) * (k.val : ℝ) ^ 2 := by ring
    _ ≤ (p k * Real.exp ((k.val : ℝ) * h)) * (m : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hk2 (mul_nonneg hp' he.le)
    _ = m ^ 2 * (p k * Real.exp ((k.val : ℝ) * h)) := by ring

private theorem logExpSumD2_abs_le {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hsum : 0 < ∑ k, p k) (h : ℝ) :
    |logExpSumD2 p h| ≤ 2 * (m : ℝ) ^ 2 := by
  have h0 := logExpSumD_nonneg hp hsum h
  have h1 := logExpSumD_le hp hsum h
  have h20 := secondRatio_nonneg hp hsum h
  have h21 := secondRatio_le hp hsum h
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  rw [logExpSumD2, abs_le]
  constructor <;> nlinarith [sq_nonneg (logExpSumD p h)]

private theorem measurable_expSum {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    {ν : Measure Ω} {p : Fin (m + 1) → Ω → ℝ} (hp : ∀ k, AEMeasurable (p k) ν)
    (d : ℕ) (h : ℝ) : AEMeasurable (fun e => expSum (fun k => p k e) d h) ν := by
  simp only [expSum]
  fun_prop

private theorem measurable_logExpSum {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    {ν : Measure Ω} {p : Fin (m + 1) → Ω → ℝ} (hp : ∀ k, AEMeasurable (p k) ν) (h : ℝ) :
    AEMeasurable (fun e => logExpSum (fun k => p k e) h) ν := by
  exact Real.measurable_log.comp_aemeasurable (measurable_expSum hp 0 h)

private theorem measurable_logExpSumD {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    {ν : Measure Ω} {p : Fin (m + 1) → Ω → ℝ} (hp : ∀ k, AEMeasurable (p k) ν) (h : ℝ) :
    AEMeasurable (fun e => logExpSumD (fun k => p k e) h) ν := by
  exact (measurable_expSum hp 1 h).div (measurable_expSum hp 0 h)

private theorem measurable_logExpSumD2 {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    {ν : Measure Ω} {p : Fin (m + 1) → Ω → ℝ} (hp : ∀ k, AEMeasurable (p k) ν) (h : ℝ) :
    AEMeasurable (fun e => logExpSumD2 (fun k => p k e) h) ν := by
  exact ((measurable_expSum hp 2 h).div (measurable_expSum hp 0 h)).sub
    ((measurable_logExpSumD hp h).pow_const 2)


private noncomputable def fieldD {m : ℕ} (φ : ℝ → ℝ) (p : Fin (m + 1) → ℝ)
    (h : ℝ) : ℝ :=
  iteratedDeriv 1 φ (logExpSum p h) * logExpSumD p h

private noncomputable def fieldD2 {m : ℕ} (φ : ℝ → ℝ) (p : Fin (m + 1) → ℝ)
    (h : ℝ) : ℝ :=
  iteratedDeriv 2 φ (logExpSum p h) * (logExpSumD p h) ^ 2 +
    iteratedDeriv 1 φ (logExpSum p h) * logExpSumD2 p h

private theorem hasDerivAt_iterated_comp {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hsum : 0 < ∑ k, p k) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ)
    {i : ℕ} (hi : i < 3) (h : ℝ) :
    HasDerivAt (fun h => iteratedDeriv i φ (logExpSum p h))
      (iteratedDeriv (i + 1) φ (logExpSum p h) * logExpSumD p h) h := by
  have hdi := (hφ.differentiable_iteratedDeriv i (by exact_mod_cast hi) (logExpSum p h)).hasDerivAt
  convert hdi.comp h (hasDerivAt_logExpSum hp hsum h) using 1
  · rfl
  · rw [← iteratedDeriv_succ]

private theorem logExpSumD2_eq {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hsum : 0 < ∑ k, p k) (h : ℝ) :
    (expSum p 2 h * expSum p 0 h - expSum p 1 h * expSum p 1 h) /
        expSum p 0 h ^ 2 = logExpSumD2 p h := by
  rw [logExpSumD2, logExpSumD]
  field_simp [(expSum_zero_pos hp hsum h).ne']

private theorem hasDerivAt_field {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hsum : 0 < ∑ k, p k) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ)
    (h : ℝ) :
    HasDerivAt (fun h => φ (logExpSum p h)) (fieldD φ p h) h := by
  simpa only [fieldD, iteratedDeriv_zero, zero_add] using
    hasDerivAt_iterated_comp hp hsum hφ (i := 0) (by norm_num) h

private theorem hasDerivAt_fieldD {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hsum : 0 < ∑ k, p k) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ)
    (h : ℝ) : HasDerivAt (fieldD φ p) (fieldD2 φ p h) h := by
  have h1 := hasDerivAt_iterated_comp hp hsum hφ (i := 1) (by norm_num) h
  have hd := hasDerivAt_logExpSumD hp hsum h
  rw [logExpSumD2_eq hp hsum h] at hd
  convert h1.mul hd using 1
  · rfl
  · simp only [fieldD2, one_add_one_eq_two]
    ring

private theorem deriv_field {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hsum : 0 < ∑ k, p k) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ) :
    deriv (fun h => φ (logExpSum p h)) = fieldD φ p := by
  funext h
  exact (hasDerivAt_field hp hsum hφ h).deriv

private theorem deriv_fieldD {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hsum : 0 < ∑ k, p k) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ) :
    deriv (fieldD φ p) = fieldD2 φ p := by
  funext h
  exact (hasDerivAt_fieldD hp hsum hφ h).deriv

private theorem measurable_field {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    {ν : Measure Ω} {p : Fin (m + 1) → Ω → ℝ} (hp : ∀ k, AEMeasurable (p k) ν) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 3 φ) (h : ℝ) :
    AEMeasurable (fun e => φ (logExpSum (fun k => p k e) h)) ν := by
  have hc : Continuous φ := by
    simpa only [iteratedDeriv_zero] using hφ.continuous_iteratedDeriv 0 (by norm_num)
  exact hc.measurable.comp_aemeasurable (measurable_logExpSum hp h)

private theorem measurable_fieldD {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    {ν : Measure Ω} {p : Fin (m + 1) → Ω → ℝ} (hp : ∀ k, AEMeasurable (p k) ν) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 3 φ) (h : ℝ) :
    AEMeasurable (fun e => fieldD φ (fun k => p k e) h) ν := by
  exact ((hφ.continuous_iteratedDeriv 1 (by norm_num)).measurable.comp_aemeasurable
    (measurable_logExpSum hp h)).mul (measurable_logExpSumD hp h)

private theorem measurable_fieldD2 {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    {ν : Measure Ω} {p : Fin (m + 1) → Ω → ℝ} (hp : ∀ k, AEMeasurable (p k) ν) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 3 φ) (h : ℝ) :
    AEMeasurable (fun e => fieldD2 φ (fun k => p k e) h) ν := by
  exact (((hφ.continuous_iteratedDeriv 2 (by norm_num)).measurable.comp_aemeasurable
    (measurable_logExpSum hp h)).mul ((measurable_logExpSumD hp h).pow_const 2)).add
    (((hφ.continuous_iteratedDeriv 1 (by norm_num)).measurable.comp_aemeasurable
      (measurable_logExpSum hp h)).mul (measurable_logExpSumD2 hp h))


private theorem logExpSum_abs_sub_le {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hsum : 0 < ∑ k, p k) {h₀ h : ℝ}
    (hh : |h - h₀| ≤ 1) :
    |logExpSum p h - logExpSum p h₀| ≤ (m : ℝ) := by
  have hh' : h ∈ Metric.closedBall h₀ 1 := by
    rw [Metric.mem_closedBall, Real.dist_eq]
    exact hh
  have hbound : ∀ z ∈ Metric.closedBall h₀ (1 : ℝ),
      ‖deriv (logExpSum p) z‖ ≤ (m : ℝ) := by
    intro z _
    rw [(hasDerivAt_logExpSum hp hsum z).deriv, Real.norm_eq_abs, abs_of_nonneg
      (logExpSumD_nonneg hp hsum z)]
    exact logExpSumD_le hp hsum z
  have hmv := (convex_closedBall h₀ (1 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (hasDerivAt_logExpSum hp hsum z).differentiableAt) hbound
    (Metric.mem_closedBall_self (by norm_num)) hh'
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  calc
    |logExpSum p h - logExpSum p h₀| ≤ (m : ℝ) * |h - h₀| := hmv
    _ ≤ (m : ℝ) * 1 := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)
    _ = (m : ℝ) := mul_one _

private theorem field_envelope_pointwise {m : ℕ} {p : Fin (m + 1) → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hsum : 0 < ∑ k, p k)
    {K θ a s h₀ : ℝ} (hθ : 0 < θ) (hs : 0 ≤ s) {φ : ℝ → ℝ}
    (hg : ∀ i ≤ (3 : ℕ), ∀ x : ℝ,
      |iteratedDeriv i φ x| ≤ K * Real.exp (θ * x) * (1 + |x - a|) ^ s)
    {h : ℝ} (hh : |h - h₀| ≤ 1) :
    |fieldD φ p h| + |fieldD2 φ p h| ≤
      |K| * ((m : ℝ) + 3 * (m : ℝ) ^ 2) *
        (Real.exp (θ * (m : ℝ)) * (1 + (m : ℝ)) ^ s) *
        (Real.exp (θ * logExpSum p h₀) * (1 + |logExpSum p h₀ - a|) ^ s) := by
  let C₀ := Real.exp (θ * (m : ℝ)) * (1 + (m : ℝ)) ^ s
  let g := Real.exp (θ * logExpSum p h₀) * (1 + |logExpSum p h₀ - a|) ^ s
  have hclose := logExpSum_abs_sub_le hp hsum hh
  have hdiff : logExpSum p h - logExpSum p h₀ ≤ (m : ℝ) :=
    (le_abs_self _).trans hclose
  have hexp : Real.exp (θ * logExpSum p h) ≤
      Real.exp (θ * (m : ℝ)) * Real.exp (θ * logExpSum p h₀) := by
    calc
      Real.exp (θ * logExpSum p h) =
          Real.exp (θ * (logExpSum p h - logExpSum p h₀)) *
            Real.exp (θ * logExpSum p h₀) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (θ * (m : ℝ)) * Real.exp (θ * logExpSum p h₀) :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdiff hθ.le))
          (Real.exp_pos _).le
  have hbase : 1 + |logExpSum p h - a| ≤
      (1 + (m : ℝ)) * (1 + |logExpSum p h₀ - a|) := by
    have htri : |logExpSum p h - a| ≤
        |logExpSum p h - logExpSum p h₀| + |logExpSum p h₀ - a| := by
      have := abs_add_le (logExpSum p h - logExpSum p h₀) (logExpSum p h₀ - a)
      convert this using 1
      all_goals ring_nf
    nlinarith [abs_nonneg (logExpSum p h₀ - a), Nat.cast_nonneg (α := ℝ) m]
  have hpow : (1 + |logExpSum p h - a|) ^ s ≤
      (1 + (m : ℝ)) ^ s * (1 + |logExpSum p h₀ - a|) ^ s := by
    calc
      (1 + |logExpSum p h - a|) ^ s ≤
          ((1 + (m : ℝ)) * (1 + |logExpSum p h₀ - a|)) ^ s :=
        Real.rpow_le_rpow (by positivity) hbase hs
      _ = (1 + (m : ℝ)) ^ s * (1 + |logExpSum p h₀ - a|) ^ s :=
        Real.mul_rpow (by positivity) (by positivity)
  have hEP : Real.exp (θ * logExpSum p h) * (1 + |logExpSum p h - a|) ^ s ≤
      C₀ * g := by
    calc
      Real.exp (θ * logExpSum p h) * (1 + |logExpSum p h - a|) ^ s ≤
          (Real.exp (θ * (m : ℝ)) * Real.exp (θ * logExpSum p h₀)) *
            ((1 + (m : ℝ)) ^ s * (1 + |logExpSum p h₀ - a|) ^ s) :=
        mul_le_mul hexp hpow (Real.rpow_nonneg (by positivity) _)
          (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      _ = C₀ * g := by ring
  have hgb (i : ℕ) (hi : i ≤ 3) :
      |iteratedDeriv i φ (logExpSum p h)| ≤ |K| * C₀ * g := by
    calc
      |iteratedDeriv i φ (logExpSum p h)| ≤
          K * Real.exp (θ * logExpSum p h) * (1 + |logExpSum p h - a|) ^ s :=
        hg i hi _
      _ = K * (Real.exp (θ * logExpSum p h) * (1 + |logExpSum p h - a|) ^ s) := by ring
      _ ≤ |K| * (Real.exp (θ * logExpSum p h) * (1 + |logExpSum p h - a|) ^ s) := by
        apply mul_le_mul_of_nonneg_right (le_abs_self K)
        exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by positivity) _)
      _ ≤ |K| * (C₀ * g) := mul_le_mul_of_nonneg_left hEP (abs_nonneg _)
      _ = |K| * C₀ * g := by ring
  have hd0 := logExpSumD_nonneg hp hsum h
  have hd1 := logExpSumD_le hp hsum h
  have hder : |fieldD φ p h| ≤ |K| * (m : ℝ) * C₀ * g := by
    calc
      |fieldD φ p h| = |iteratedDeriv 1 φ (logExpSum p h)| * |logExpSumD p h| := by
        rw [fieldD, abs_mul]
      _ ≤ (|K| * C₀ * g) * (m : ℝ) := by
        apply mul_le_mul (hgb 1 (by norm_num))
        · rwa [abs_of_nonneg hd0]
        · exact abs_nonneg _
        · exact mul_nonneg (mul_nonneg (abs_nonneg _) (by dsimp [C₀]; positivity))
            (by dsimp [g]; positivity)
      _ = |K| * (m : ℝ) * C₀ * g := by ring
  have hdbig : |logExpSumD p h ^ 2| ≤ (m : ℝ) ^ 2 := by
    rw [abs_pow, abs_of_nonneg hd0]
    exact pow_le_pow_left₀ hd0 hd1 2
  have hA : |iteratedDeriv 2 φ (logExpSum p h) * (logExpSumD p h) ^ 2| ≤
      (|K| * C₀ * g) * (m : ℝ) ^ 2 := by
    rw [abs_mul]
    apply mul_le_mul (hgb 2 (by norm_num)) hdbig (abs_nonneg _)
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (by dsimp [C₀]; positivity))
      (by dsimp [g]; positivity)
  have hB : |iteratedDeriv 1 φ (logExpSum p h) * logExpSumD2 p h| ≤
      (|K| * C₀ * g) * (2 * (m : ℝ) ^ 2) := by
    rw [abs_mul]
    apply mul_le_mul (hgb 1 (by norm_num)) (logExpSumD2_abs_le hp hsum h)
      (abs_nonneg _)
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (by dsimp [C₀]; positivity))
      (by dsimp [g]; positivity)
  have hsec : |fieldD2 φ p h| ≤ |K| * (3 * (m : ℝ) ^ 2) * C₀ * g := by
    calc
      |fieldD2 φ p h| ≤
          |iteratedDeriv 2 φ (logExpSum p h) * (logExpSumD p h) ^ 2| +
            |iteratedDeriv 1 φ (logExpSum p h) * logExpSumD2 p h| := by
        rw [fieldD2]
        exact abs_add_le _ _
      _ ≤ (|K| * C₀ * g) * (m : ℝ) ^ 2 +
          (|K| * C₀ * g) * (2 * (m : ℝ) ^ 2) := add_le_add hA hB
      _ = |K| * (3 * (m : ℝ) ^ 2) * C₀ * g := by ring
  change |fieldD φ p h| + |fieldD2 φ p h| ≤
    |K| * ((m : ℝ) + 3 * (m : ℝ) ^ 2) * C₀ * g
  calc
    |fieldD φ p h| + |fieldD2 φ p h| ≤
        |K| * (m : ℝ) * C₀ * g + |K| * (3 * (m : ℝ) ^ 2) * C₀ * g :=
      add_le_add hder hsec
    _ = |K| * ((m : ℝ) + 3 * (m : ℝ) ^ 2) * C₀ * g := by ring


private theorem one_add_rpow_le {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    (1 + t) ^ s ≤ (2 : ℝ) ^ s * (1 + t ^ s) := by
  have htwo : 0 ≤ (2 : ℝ) ^ s := Real.rpow_nonneg (by norm_num) _
  rcases le_total t 1 with ht1 | ht1
  · have h₁ : (1 + t) ^ s ≤ (2 : ℝ) ^ s := by
      have h := Real.rpow_le_rpow (x := 1 + t) (y := 1 + 1) (z := s)
        (by positivity) (by linarith) hs
      norm_num at h
      exact h
    have h₂ : (2 : ℝ) ^ s ≤ (2 : ℝ) ^ s * (1 + t ^ s) := by
      apply le_mul_of_one_le_right htwo
      have := Real.rpow_nonneg ht s
      linarith
    exact h₁.trans h₂
  · calc
      (1 + t) ^ s ≤ (2 * t) ^ s := Real.rpow_le_rpow (by positivity) (by linarith) hs
      _ = (2 : ℝ) ^ s * t ^ s := Real.mul_rpow (by norm_num) ht
      _ ≤ (2 : ℝ) ^ s * (1 + t ^ s) := by
        apply mul_le_mul_of_nonneg_left _ htwo
        have := Real.rpow_nonneg ht s
        linarith

private theorem integrable_exp_log_g {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {q : Ω → ℝ} (hq : AEMeasurable q ν)
    (hqpos : ∀ᵐ x ∂ν, 0 < q x) (hqint : Integrable q ν)
    {θ a s : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hs : 0 ≤ s) :
    Integrable (fun x => Real.exp (θ * Real.log (q x)) *
      (1 + |Real.log (q x) - a|) ^ s) ν := by
  have hi := integrable_rpow_abs_log_sub_of ν hq hqpos hqint (a := a) hθ hθ1 hs
  have hi0 : Integrable (fun x => q x ^ θ) ν := by
    simpa only [Real.rpow_zero, mul_one] using
      integrable_rpow_abs_log_sub_of ν hq hqpos hqint (a := a) hθ hθ1 (s := 0) (le_refl 0)
  have hmeas := show AEMeasurable (fun x => Real.exp (θ * Real.log (q x)) *
      (1 + |Real.log (q x) - a|) ^ s) ν by fun_prop
  apply ((hi0.add hi).const_mul ((2 : ℝ) ^ s)).mono' hmeas.aestronglyMeasurable
  filter_upwards [hqpos] with x hx
  have hexp : Real.exp (θ * Real.log (q x)) = q x ^ θ := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le
    (Real.rpow_nonneg (by positivity) _)), hexp]
  calc
    q x ^ θ * (1 + |Real.log (q x) - a|) ^ s ≤
        q x ^ θ * ((2 : ℝ) ^ s * (1 + |Real.log (q x) - a| ^ s)) :=
      mul_le_mul_of_nonneg_left (one_add_rpow_le (abs_nonneg _) hs)
        (Real.rpow_nonneg hx.le _)
    _ = (2 : ℝ) ^ s * (q x ^ θ + q x ^ θ * |Real.log (q x) - a| ^ s) := by ring


/-- A finite positive exponential sum has an integrable logarithmic envelope and
its first two field derivatives pass through the expectation.  This proves
`DiamondPinning.field_envelope` (in `DiamondPinning.Statements.Response`). -/
theorem field_envelope_aux {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {m : ℕ} (p : Fin (m + 1) → Ω → ℝ) (hp : ∀ k, Integrable (p k) ν)
    (hp0 : ∀ᵐ e ∂ν, (∀ k, 0 ≤ p k e) ∧ 0 < ∑ k, p k e)
    {θ a s h₀ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hs : 0 ≤ s) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 3 φ)
    (hg : ∃ K : ℝ, ∀ i ≤ (3 : ℕ), ∀ x : ℝ,
      |iteratedDeriv i φ x| ≤ K * Real.exp (θ * x) * (1 + |x - a|) ^ s) :
    let x := fun (e : Ω) (h : ℝ) => Real.log (∑ k, p k e * Real.exp ((k.val : ℝ) * h))
    let f := fun (e : Ω) (h : ℝ) => φ (x e h)
    let g := fun e => Real.exp (θ * x e h₀) * (1 + |x e h₀ - a|) ^ s
    Integrable g ν ∧
      (∃ C : ℝ, ∀ᵐ e ∂ν, ∀ h : ℝ, |h - h₀| ≤ 1 →
        |deriv (f e) h| + |iteratedDeriv 2 (f e) h| ≤ C * g e) ∧
      ∀ i < (2 : ℕ), HasDerivAt (fieldMean ν (fun e => iteratedDeriv i (f e)))
        (fieldMean ν (fun e => iteratedDeriv (i + 1) (f e)) h₀) h₀ := by
  dsimp only
  obtain ⟨K, hg⟩ := hg
  let q : Ω → ℝ := fun e => expSum (fun k => p k e) 0 h₀
  let G : Ω → ℝ := fun e => Real.exp (θ * logExpSum (fun k => p k e) h₀) *
    (1 + |logExpSum (fun k => p k e) h₀ - a|) ^ s
  let C : ℝ := |K| * ((m : ℝ) + 3 * (m : ℝ) ^ 2) *
    (Real.exp (θ * (m : ℝ)) * (1 + (m : ℝ)) ^ s)
  have hq : AEMeasurable q ν := measurable_expSum (fun k => (hp k).aemeasurable) 0 h₀
  have hqint : Integrable q ν := by
    simp only [q, expSum, pow_zero, mul_one]
    exact integrable_finsetSum _ (fun k _ => (hp k).mul_const _)
  have hqpos : ∀ᵐ e ∂ν, 0 < q e := by
    filter_upwards [hp0] with e he
    exact expSum_zero_pos he.1 he.2 h₀
  have hG : Integrable G ν := by
    exact integrable_exp_log_g ν hq hqpos hqint hθ hθ1 hs
  have hbound : ∀ᵐ e ∂ν, ∀ h : ℝ, |h - h₀| ≤ 1 →
      |fieldD φ (fun k => p k e) h| + |fieldD2 φ (fun k => p k e) h| ≤ C * G e := by
    filter_upwards [hp0] with e he
    intro h hh
    exact field_envelope_pointwise he.1 he.2 hθ hs hg hh
  have hfint : Integrable
      (fun e => φ (logExpSum (fun k => p k e) h₀)) ν := by
    apply (hG.const_mul K).mono'
      (measurable_field (fun k => (hp k).aemeasurable) hφ h₀).aestronglyMeasurable
    filter_upwards with e
    rw [Real.norm_eq_abs]
    change |φ (logExpSum (fun k => p k e) h₀)| ≤ K * G e
    dsimp only [G]
    rw [← mul_assoc]
    exact hg 0 (by norm_num) _
  have hDint : Integrable (fun e => fieldD φ (fun k => p k e) h₀) ν := by
    apply (hG.const_mul C).mono'
      (measurable_fieldD (fun k => (hp k).aemeasurable) hφ h₀).aestronglyMeasurable
    filter_upwards [hbound] with e he
    rw [Real.norm_eq_abs]
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans (he h₀ (by simp))
  have H0 : HasDerivAt (fun h => ∫ e, φ (logExpSum (fun k => p k e) h) ∂ν)
      (∫ e, fieldD φ (fun k => p k e) h₀ ∂ν) h₀ := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.closedBall_mem_nhds h₀ (by norm_num : (0 : ℝ) < 1))
      (Filter.Eventually.of_forall (fun h =>
        (measurable_field (fun k => (hp k).aemeasurable) hφ h).aestronglyMeasurable))
      hfint
      (measurable_fieldD (fun k => (hp k).aemeasurable) hφ h₀).aestronglyMeasurable
      (bound := fun e => C * G e) ?_ (hG.const_mul C) ?_).2
    · filter_upwards [hbound] with e he
      intro h hh
      rw [Real.norm_eq_abs]
      apply (le_add_of_nonneg_right (abs_nonneg _)).trans
      apply he h
      rwa [Metric.mem_closedBall, Real.dist_eq] at hh
    · filter_upwards [hp0] with e he
      intro h _
      exact hasDerivAt_field he.1 he.2 hφ h
  have H1 : HasDerivAt (fun h => ∫ e, fieldD φ (fun k => p k e) h ∂ν)
      (∫ e, fieldD2 φ (fun k => p k e) h₀ ∂ν) h₀ := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.closedBall_mem_nhds h₀ (by norm_num : (0 : ℝ) < 1))
      (Filter.Eventually.of_forall (fun h =>
        (measurable_fieldD (fun k => (hp k).aemeasurable) hφ h).aestronglyMeasurable))
      hDint
      (measurable_fieldD2 (fun k => (hp k).aemeasurable) hφ h₀).aestronglyMeasurable
      (bound := fun e => C * G e) ?_ (hG.const_mul C) ?_).2
    · filter_upwards [hbound] with e he
      intro h hh
      rw [Real.norm_eq_abs]
      apply (le_add_of_nonneg_left (abs_nonneg _)).trans
      apply he h
      rwa [Metric.mem_closedBall, Real.dist_eq] at hh
    · filter_upwards [hp0] with e he
      intro h _
      exact hasDerivAt_fieldD he.1 he.2 hφ h
  refine ⟨?_, ⟨C, ?_⟩, ?_⟩
  · simpa only [G, logExpSum, expSum, pow_zero, mul_one] using hG
  · filter_upwards [hbound, hp0] with e he hpe
    intro h hh
    have hx : (fun h' : ℝ => Real.log (∑ k, p k e * Real.exp ((k.val : ℝ) * h'))) =
        logExpSum (fun k => p k e) := by
      funext h'
      simp only [logExpSum, expSum, pow_zero, mul_one]
    have hfx : (fun h' : ℝ => φ (Real.log (∑ k, p k e * Real.exp ((k.val : ℝ) * h')))) =
        (fun h' => φ (logExpSum (fun k => p k e) h')) := by
      funext h'
      rw [congrFun hx h']
    rw [hfx, deriv_field hpe.1 hpe.2 hφ]
    have hi2 : iteratedDeriv 2 (fun h' => φ (logExpSum (fun k => p k e) h')) =
        fieldD2 φ (fun k => p k e) := by
      rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one,
        deriv_field hpe.1 hpe.2 hφ, deriv_fieldD hpe.1 hpe.2 hφ]
    rw [hi2]
    simpa only [G, logExpSum, expSum, pow_zero, mul_one] using he h hh
  · intro i hi
    have hi_cases : i = 0 ∨ i = 1 := by omega
    rcases hi_cases with rfl | rfl
    · simp only [iteratedDeriv_zero, zero_add, iteratedDeriv_one, fieldMean]
      convert H0 using 1
      · funext h
        apply integral_congr_ae
        filter_upwards with e
        simp only [logExpSum, expSum, pow_zero, mul_one]
      · apply integral_congr_ae
        filter_upwards [hp0] with e he
        have hx : (fun h' : ℝ => Real.log (∑ k, p k e * Real.exp ((k.val : ℝ) * h'))) =
            logExpSum (fun k => p k e) := by
          funext h'
          simp only [logExpSum, expSum, pow_zero, mul_one]
        have hfx : (fun h' : ℝ => φ (Real.log (∑ k, p k e * Real.exp ((k.val : ℝ) * h')))) =
            (fun h' => φ (logExpSum (fun k => p k e) h')) := by
          funext h'
          rw [congrFun hx h']
        rw [hfx]
        exact (hasDerivAt_field he.1 he.2 hφ h₀).deriv
    · simp only [iteratedDeriv_one, one_add_one_eq_two, fieldMean]
      convert H1 using 1
      · funext h
        apply integral_congr_ae
        filter_upwards [hp0] with e he
        have hx : (fun h' : ℝ => Real.log (∑ k, p k e * Real.exp ((k.val : ℝ) * h'))) =
            logExpSum (fun k => p k e) := by
          funext h'
          simp only [logExpSum, expSum, pow_zero, mul_one]
        have hfx : (fun h' : ℝ => φ (Real.log (∑ k, p k e * Real.exp ((k.val : ℝ) * h')))) =
            (fun h' => φ (logExpSum (fun k => p k e) h')) := by
          funext h'
          rw [congrFun hx h']
        rw [hfx]
        exact (hasDerivAt_field he.1 he.2 hφ h).deriv
      · apply integral_congr_ae
        filter_upwards [hp0] with e he
        have hx : (fun h' : ℝ => Real.log (∑ k, p k e * Real.exp ((k.val : ℝ) * h'))) =
            logExpSum (fun k => p k e) := by
          funext h'
          simp only [logExpSum, expSum, pow_zero, mul_one]
        have hfx : (fun h' : ℝ => φ (Real.log (∑ k, p k e * Real.exp ((k.val : ℝ) * h')))) =
            (fun h' => φ (logExpSum (fun k => p k e) h')) := by
          funext h'
          rw [congrFun hx h']
        rw [hfx]
        rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one,
          deriv_field he.1 he.2 hφ, deriv_fieldD he.1 he.2 hφ]


/-- The response kernel `kernelPsi` is integrable under the product law at
positive height.  This proves `DiamondPinning.integrable_kernelPsi` (in
`DiamondPinning.Statements.Response`). -/
theorem integrable_kernelPsi_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (kernelPsi B) (productLaw μ B h n) := by
  -- The statement includes this positive-height hypothesis.
  have _ := hn
  let : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  let : IsProbabilityMeasure (productLaw μ B h n) := by
    rw [productLaw]
    infer_instance
  have hi := integrable_lawR_of hpos hmean hB h n
  have hs : Integrable (fun s : ℝ => s) (productLaw μ B h n) := by
    rw [productLaw]
    apply (integrable_map_measure measurable_id.aestronglyMeasurable (by fun_prop)).2
    exact hi.mul_prod hi
  have hsplus : Integrable (fun s : ℝ => s + (B - 1)) (productLaw μ B h n) :=
    hs.add (integrable_const _)
  have hspos : ∀ᵐ s ∂(productLaw μ B h n), 0 < s := by
    rw [productLaw, ae_map_iff (by fun_prop) measurableSet_Ioi]
    have hp : ∀ᵐ p : ℝ × ℝ ∂((lawR μ B h n).prod (lawR μ B h n)),
        0 < p.1 ∧ 0 < p.2 := by
      rw [Measure.ae_prod_iff_ae_ae (by measurability)]
      filter_upwards [ae_pos_lawR hpos hB h n] with x hx
      filter_upwards [ae_pos_lawR hpos hB h n] with y hy
      exact ⟨hx, hy⟩
    filter_upwards [hp] with p hp
    exact mul_pos hp.1 hp.2
  have hpluspos : ∀ᵐ s ∂(productLaw μ B h n), 0 < s + (B - 1) := by
    filter_upwards [hspos] with s hs0
    linarith
  obtain ⟨C₁, hC₁⟩ := exists_rpow_abs_log_sub_bound (theta_pos hB) (theta_lt_one hB)
    (a := 2 * Real.log B) (s := 1) (by norm_num)
  obtain ⟨C₂, hC₂⟩ := exists_rpow_abs_log_sub_bound (theta_pos hB) (theta_lt_one hB)
    (a := 2 * Real.log B) (s := 1) (by norm_num)
  have hdom : Integrable (fun s : ℝ => C₁ * (1 + (s + (B - 1))) + C₂ * (1 + s))
      (productLaw μ B h n) :=
    (((integrable_const 1).add hsplus).const_mul C₁).add
      (((integrable_const 1).add hs).const_mul C₂)
  apply hdom.mono'
  · have hmeas : Measurable (kernelPsi B) := by
      unfold kernelPsi
      fun_prop
    exact hmeas.aestronglyMeasurable
  filter_upwards [hspos, hpluspos] with s hs0 hsc
  have hlog₁ : Real.log ((s + (B - 1)) / B ^ 2) =
      Real.log (s + (B - 1)) - 2 * Real.log B := by
    rw [Real.log_div hsc.ne' (by positivity), Real.log_pow]
    norm_num
  have hlog₂ : Real.log (s / B ^ 2) = Real.log s - 2 * Real.log B := by
    rw [Real.log_div hs0.ne' (by positivity), Real.log_pow]
    norm_num
  have h₁ : |(s + (B - 1)) ^ theta B * Real.log ((s + (B - 1)) / B ^ 2)| ≤
      C₁ * (1 + (s + (B - 1))) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hsc.le _), hlog₁]
    simpa only [Real.rpow_one] using hC₁ (s + (B - 1)) hsc
  have h₂ : |s ^ theta B * Real.log (s / B ^ 2)| ≤ C₂ * (1 + s) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _), hlog₂]
    simpa only [Real.rpow_one] using hC₂ s hs0
  rw [Real.norm_eq_abs, kernelPsi]
  have htri : |(s + (B - 1)) ^ theta B * Real.log ((s + (B - 1)) / B ^ 2) -
      s ^ theta B * Real.log (s / B ^ 2)| ≤
      |(s + (B - 1)) ^ theta B * Real.log ((s + (B - 1)) / B ^ 2)| +
        |s ^ theta B * Real.log (s / B ^ 2)| := by
    simpa using abs_sub_le ((s + (B - 1)) ^ theta B * Real.log ((s + (B - 1)) / B ^ 2))
      0 (s ^ theta B * Real.log (s / B ^ 2))
  exact htri.trans (add_le_add h₁ h₂)


/-! ### Bounded Gibbs means -/

private theorem gibbsMean_abs_le {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ}
    {e : Env n} (he : Env.Pos n e) (f : ℕ → ℝ) {M : ℝ}
    (hf : ∀ k ∈ Finset.range (2 ^ n + 1), |f k| ≤ M) :
    |gibbsMean B h n e f| ≤ M := by
  calc
    |gibbsMean B h n e f| ≤ ∑ k ∈ Finset.range (2 ^ n + 1),
        |gibbsWeight B h n e k * f k| := by
      rw [gibbsMean]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ Finset.range (2 ^ n + 1), gibbsWeight B h n e k * |f k| := by
      apply Finset.sum_congr rfl
      intro k _
      rw [abs_mul, abs_of_nonneg]
      unfold gibbsWeight
      rw [eval_contactPoly_one]
      exact div_nonneg (contactPoly_coeff_nonneg (by linarith) h n e he k)
        (evalR_pos_aux (by linarith) h n he).le
    _ ≤ ∑ k ∈ Finset.range (2 ^ n + 1), gibbsWeight B h n e k * M := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left (hf k hk)
      unfold gibbsWeight
      rw [eval_contactPoly_one]
      exact div_nonneg (contactPoly_coeff_nonneg (by linarith) h n e he k)
        (evalR_pos_aux (by linarith) h n he).le
    _ = M := by
      rw [← Finset.sum_mul, (contact_gibbsWeight_isProb (by linarith) h n e he).2.2,
        one_mul]

private theorem gibbsMean_abs_le_exp {B : ℝ} (hB : 2 < B) (h u : ℝ) {n : ℕ}
    {e : Env n} (he : Env.Pos n e) :
    |gibbsMean B h n e (fun j => Real.exp (u * j) - 1)| ≤
      Real.exp (|u| * (2 : ℝ) ^ n) + 1 := by
  apply gibbsMean_abs_le hB h he (f := fun j => Real.exp (u * (j : ℝ)) - 1)
    (M := Real.exp (|u| * (2 : ℝ) ^ n) + 1)
  intro k hk
  have hk' : k < 2 ^ n + 1 := Finset.mem_range.mp hk
  have hkR : (k : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast (Nat.lt_succ_iff.mp hk')
  have hku : u * (k : ℝ) ≤ |u| * (2 : ℝ) ^ n := by
    calc
      u * (k : ℝ) ≤ |u| * (k : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self u) (Nat.cast_nonneg _)
      _ ≤ |u| * (2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left hkR (abs_nonneg _)
  have htri : |Real.exp (u * (k : ℝ)) - 1| ≤ Real.exp (u * (k : ℝ)) + 1 := by
    simpa using abs_sub_le (Real.exp (u * (k : ℝ))) 0 1
  exact htri.trans (by nlinarith [Real.exp_le_exp.mpr hku])

private theorem measurable_contactPoly_coeff (B h : ℝ) :
    ∀ (n : ℕ) (k : ℕ), Measurable (fun e : Env n => (contactPoly B h n e).coeff k) := by
  intro n
  induction n with
  | zero =>
      intro k
      cases k with
      | zero => simp [contactPoly]
      | succ k =>
          cases k with
          | zero =>
              simp only [contactPoly, Polynomial.coeff_C_mul, Polynomial.coeff_X]
              fun_prop
          | succ k => simp [contactPoly]
  | succ n ih =>
      intro k
      have hm : Measurable (fun e : Env (n + 1) =>
          ((contactPoly B h n e.1 * contactPoly B h n e.2).coeff k)) := by
        simp only [Polynomial.coeff_mul]
        apply Finset.measurable_sum
        intro ij _
        exact ((ih ij.1).comp measurable_fst).mul ((ih ij.2).comp measurable_snd)
      simp only [contactPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add,
        Polynomial.coeff_C]
      exact (hm.add (by split_ifs <;> fun_prop)).const_mul _

private theorem measurable_gibbsMean (B h : ℝ) (n : ℕ) (f : ℕ → ℝ) :
    Measurable (fun e : Env n => gibbsMean B h n e f) := by
  simp only [gibbsMean, gibbsWeight, eval_contactPoly_one]
  apply Finset.measurable_sum
  intro k _
  exact ((measurable_contactPoly_coeff B h n k).div (measurable_evalR B h n)).mul_const _

private theorem integrable_evalR_rpow {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : Integrable (fun e => evalR B h n e ^ theta B) (envMeasure μ n) := by
  have hi : Integrable (fun x : ℝ => x ^ theta B) (lawR μ B h n) := by
    simpa only [Real.rpow_zero, mul_one] using
      integrable_absTiltedLogRpow_aux hpos hmean hB h n (s := 0) (le_refl 0)
  rw [← map_evalR_envMeasure_aux μ B h n] at hi
  simpa only [Function.comp_def] using
    (integrable_map_measure hi.aestronglyMeasurable (measurable_evalR B h n).aemeasurable).mp hi


/-- Every polynomial Gibbs contact moment has a finite tilted environment
moment.  This proves `DiamondPinning.integrable_contactMoment` (in
`DiamondPinning.Statements.Response`). -/
theorem integrable_contactMoment_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) (k n : ℕ) :
    Integrable (fun e => evalR B h n e ^ theta B * gibbsMean B h n e (fun j => (j : ℝ) ^ k))
      (envMeasure μ n) := by
  let M : ℝ := ((2 : ℝ) ^ n) ^ k
  have hm : Measurable (fun e : Env n =>
      evalR B h n e ^ theta B * gibbsMean B h n e (fun j => (j : ℝ) ^ k)) :=
    ((Real.continuous_rpow_const (theta_pos hB).le).measurable.comp
      (measurable_evalR B h n)).mul (measurable_gibbsMean B h n _)
  apply ((integrable_evalR_rpow hpos hmean hB h n).const_mul M).mono' hm.aestronglyMeasurable
  filter_upwards [ae_envPos_aux hpos n] with e he
  have hgm : |gibbsMean B h n e (fun j => (j : ℝ) ^ k)| ≤ M := by
    apply gibbsMean_abs_le hB h he (f := fun j => (j : ℝ) ^ k) (M := M)
    intro j hj
    have hj' : j < 2 ^ n + 1 := Finset.mem_range.mp hj
    have hjR : (j : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast (Nat.lt_succ_iff.mp hj')
    rw [abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
    change (j : ℝ) ^ k ≤ ((2 : ℝ) ^ n) ^ k
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hjR k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (evalR_pos_aux (B := B)
    (by linarith) h n he).le _)]
  calc
    evalR B h n e ^ theta B * |gibbsMean B h n e _| ≤ evalR B h n e ^ theta B * M :=
      mul_le_mul_of_nonneg_left hgm (Real.rpow_nonneg (evalR_pos_aux (B := B)
        (by linarith) h n he).le _)
    _ = M * evalR B h n e ^ theta B := mul_comm _ _

/-- The centered exponential Gibbs contact observable has a finite tilted
environment moment.  This proves `DiamondPinning.integrable_contactExpMoment` (in
`DiamondPinning.Statements.Response`). -/
theorem integrable_contactExpMoment_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h u : ℝ) (n : ℕ) :
    Integrable (fun e => evalR B h n e ^ theta B *
      gibbsMean B h n e (fun j => Real.exp (u * j) - 1)) (envMeasure μ n) := by
  let M : ℝ := Real.exp (|u| * (2 : ℝ) ^ n) + 1
  have hm : Measurable (fun e : Env n => evalR B h n e ^ theta B *
      gibbsMean B h n e (fun j => Real.exp (u * j) - 1)) :=
    ((Real.continuous_rpow_const (theta_pos hB).le).measurable.comp
      (measurable_evalR B h n)).mul (measurable_gibbsMean B h n _)
  apply ((integrable_evalR_rpow hpos hmean hB h n).const_mul M).mono' hm.aestronglyMeasurable
  filter_upwards [ae_envPos_aux hpos n] with e he
  have hgm : |gibbsMean B h n e (fun j => Real.exp (u * j) - 1)| ≤ M :=
    gibbsMean_abs_le_exp hB h u he
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (evalR_pos_aux (B := B)
    (by linarith) h n he).le _)]
  calc
    evalR B h n e ^ theta B * |gibbsMean B h n e _| ≤ evalR B h n e ^ theta B * M :=
      mul_le_mul_of_nonneg_left hgm (Real.rpow_nonneg (evalR_pos_aux (B := B)
        (by linarith) h n he).le _)
    _ = M * evalR B h n e ^ theta B := mul_comm _ _


/-! ### Size-biased laws and the spine -/

/-- The tilted normalizing mass is strictly positive. -/
theorem tiltedMass_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : 0 < tiltedMass μ B h n := by
  let : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
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

/-- Normalizing by the positive tilted mass makes `tiltedLaw` a probability
measure. -/
theorem isProbabilityMeasure_tiltedLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (j : ℕ) : IsProbabilityMeasure (tiltedLaw μ B h j) := by
  have hi : Integrable (fun x : ℝ => x ^ theta B) (lawR μ B h j) := by
    simpa only [Real.rpow_zero, mul_one] using
      integrable_absTiltedLogRpow_aux hpos hmean hB h j (s := 0) (le_refl 0)
  have hA := tiltedMass_pos hpos hmean hB h j
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

/-- The size-biased law is almost surely supported on the positive reals,
provided the original disorder is almost surely positive. -/
theorem ae_pos_tiltedLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (j : ℕ) :
    ∀ᵐ x ∂(tiltedLaw μ B h j), 0 < x := by
  rw [tiltedLaw, ae_withDensity_iff
    (((Real.continuous_rpow_const (theta_pos hB).le).measurable.div_const _).ennreal_ofReal)]
  filter_upwards [ae_pos_lawR hpos hB h j] with x hx
  intro _
  exact hx

/-- The logarithm is integrable under the size-biased law whenever the original
mean-one disorder has the required positive support. -/
theorem integrable_log_tiltedLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (j : ℕ) : Integrable Real.log (tiltedLaw μ B h j) := by
  let : IsProbabilityMeasure (lawR μ B h j) := isProbabilityMeasure_lawR B h j
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
    (tiltedMass_pos hpos hmean hB h j).le)]
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (Real.rpow_nonneg hx.le _),
    abs_of_nonneg (le_of_lt (tiltedMass_pos hpos hmean hB h j)), Real.rpow_one]
  exact le_of_eq (by ring)

private theorem integrable_log_spine_fst {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ × (Fin n → ℝ) => Real.log x.1) (spineMeasure μ B h n) := by
  let : IsProbabilityMeasure (Measure.pi fun j : Fin n => tiltedLaw μ B h j) := by
    let (j : Fin n) : IsProbabilityMeasure (tiltedLaw μ B h j) :=
      isProbabilityMeasure_tiltedLaw hpos hmean hB h j
    infer_instance
  let : IsProbabilityMeasure (tiltedLaw μ B h 0) :=
    isProbabilityMeasure_tiltedLaw hpos hmean hB h 0
  rw [spineMeasure]
  exact (integrable_log_tiltedLaw hpos hmean hB h 0).comp_fst _

private theorem integrable_log_spine_eval {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) (j : Fin n) :
    Integrable (fun x : ℝ × (Fin n → ℝ) => Real.log (x.2 j)) (spineMeasure μ B h n) := by
  let : IsProbabilityMeasure (Measure.pi fun j : Fin n => tiltedLaw μ B h j) := by
    let (j : Fin n) : IsProbabilityMeasure (tiltedLaw μ B h j) :=
      isProbabilityMeasure_tiltedLaw hpos hmean hB h j
    infer_instance
  let : IsProbabilityMeasure (tiltedLaw μ B h 0) :=
    isProbabilityMeasure_tiltedLaw hpos hmean hB h 0
  let : IsProbabilityMeasure (spineMeasure μ B h n) := by
    rw [spineMeasure]
    infer_instance
  let : IsProbabilityMeasure (tiltedLaw μ B h j) :=
    isProbabilityMeasure_tiltedLaw hpos hmean hB h j
  let (i : Fin n) : IsProbabilityMeasure (tiltedLaw μ B h i) :=
    isProbabilityMeasure_tiltedLaw hpos hmean hB h i
  let (i : Fin n) : IsFiniteMeasure (tiltedLaw μ B h i) := inferInstance
  have hi : Integrable (fun u : Fin n → ℝ => Real.log (u j))
      (Measure.pi fun j : Fin n => tiltedLaw μ B h j) :=
    integrable_comp_eval (i := j) (integrable_log_tiltedLaw hpos hmean hB h j)
  rw [spineMeasure]
  exact hi.comp_snd _

private theorem integrable_spineWalkTerm {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) (j : Fin n) :
    Integrable (fun x : ℝ × (Fin n → ℝ) => Real.log (x.2 j) - Real.log B)
      (spineMeasure μ B h n) := by
  let : IsProbabilityMeasure (spineMeasure μ B h n) := by
    let : IsProbabilityMeasure (tiltedLaw μ B h 0) :=
      isProbabilityMeasure_tiltedLaw hpos hmean hB h 0
    let (i : Fin n) : IsProbabilityMeasure (tiltedLaw μ B h i) :=
      isProbabilityMeasure_tiltedLaw hpos hmean hB h i
    rw [spineMeasure]
    infer_instance
  exact (integrable_log_spine_eval hpos hmean hB h n j).sub (integrable_const _)


private noncomputable def spineBase (B : ℝ) (n : ℕ) (r : ℝ) (u : Fin n → ℝ) : ℝ :=
  1 + (B - 1) / (B * r) * ∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B u k)

private theorem one_le_spineBase {B : ℝ} (hB : 2 < B) {n : ℕ} {r : ℝ}
    (hr : 0 < r) (u : Fin n → ℝ) : 1 ≤ spineBase B n r u := by
  have hnon : 0 ≤ (B - 1) / (B * r) *
      ∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B u k) := by
    apply mul_nonneg
    · exact div_nonneg (by linarith) (mul_pos (by linarith) hr).le
    · exact Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  dsimp [spineBase]
  linarith

private theorem spineBase_pos {B : ℝ} (hB : 2 < B) {n : ℕ} {r : ℝ}
    (hr : 0 < r) (u : Fin n → ℝ) : 0 < spineBase B n r u :=
  zero_lt_one.trans_le (one_le_spineBase hB hr u)

private theorem spineW_pos {B : ℝ} (hB : 2 < B) {n : ℕ} {r : ℝ}
    (hr : 0 < r) (u : Fin n → ℝ) : 0 < spineW B n r u := by
  rw [spineW, show 1 + (B - 1) / (B * r) *
    ∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B u k) = spineBase B n r u from rfl]
  exact Real.rpow_pos_of_pos (spineBase_pos hB hr u) _

private theorem spineW_le_one {B : ℝ} (hB : 2 < B) {n : ℕ} {r : ℝ}
    (hr : 0 < r) (u : Fin n → ℝ) : spineW B n r u ≤ 1 := by
  rw [spineW, show 1 + (B - 1) / (B * r) *
    ∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B u k) = spineBase B n r u from rfl]
  apply Real.rpow_le_one_of_one_le_of_nonpos (one_le_spineBase hB hr u)
  linarith [theta_pos hB, theta_lt_one hB]

private theorem spineW_eq_inv {B : ℝ} (hB : 2 < B) {n : ℕ} {r : ℝ}
    (hr : 0 < r) (u : Fin n → ℝ) :
    spineW B n r u = (spineBase B n r u ^ (1 - theta B))⁻¹ := by
  rw [spineW, show 1 + (B - 1) / (B * r) *
    ∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B u k) = spineBase B n r u from rfl,
    Real.rpow_neg (spineBase_pos hB hr u).le]

private theorem spineW_rpow_neg_inv {B : ℝ} (hB : 2 < B) {n : ℕ} {r : ℝ}
    (hr : 0 < r) (u : Fin n → ℝ) :
    spineW B n r u ^ (-(1 / (1 - theta B))) = spineBase B n r u := by
  have hp : 0 < 1 - theta B := sub_pos.mpr (theta_lt_one hB)
  rw [spineW, show 1 + (B - 1) / (B * r) *
    ∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B u k) = spineBase B n r u from rfl]
  rw [← Real.rpow_mul (spineBase_pos hB hr u).le]
  convert Real.rpow_one (spineBase B n r u) using 2
  field_simp [hp.ne']

private theorem log_spineT {B : ℝ} (hB : 2 < B) {n : ℕ} {r : ℝ}
    (hr : 0 < r) (u : Fin n → ℝ) :
    Real.log (spineT B n r u) = Real.log r + spineWalk B u n + Real.log (spineBase B n r u) := by
  rw [spineT, spineW_rpow_neg_inv hB hr u]
  rw [Real.log_mul (mul_ne_zero hr.ne' (Real.exp_ne_zero _)) (spineBase_pos hB hr u).ne',
    Real.log_mul hr.ne' (Real.exp_ne_zero _), Real.log_exp]

private theorem measurable_spineBase (B : ℝ) (n : ℕ) :
    Measurable (fun x : ℝ × (Fin n → ℝ) => spineBase B n x.1 x.2) := by
  unfold spineBase spineWalk
  fun_prop

private theorem measurable_spineWInv {B : ℝ} (hB : 2 < B) (n : ℕ) :
    Measurable (fun x : ℝ × (Fin n → ℝ) => (spineBase B n x.1 x.2 ^ (1 - theta B))⁻¹) := by
  exact ((Real.continuous_rpow_const (sub_pos.mpr (theta_lt_one hB)).le).measurable.comp
    (measurable_spineBase B n)).inv

private theorem ae_spine_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    ∀ᵐ x : ℝ × (Fin n → ℝ) ∂(spineMeasure μ B h n),
      0 < x.1 ∧ ∀ j, 0 < x.2 j := by
  let (j : Fin n) : IsProbabilityMeasure (tiltedLaw μ B h j) := by
    apply isProbabilityMeasure_tiltedLaw hpos (hmean) hB h j
  rw [spineMeasure, Measure.ae_prod_iff_ae_ae (by measurability)]
  filter_upwards [ae_pos_tiltedLaw hpos hB h 0] with r hr
  have hu : ∀ᵐ u : Fin n → ℝ ∂(Measure.pi fun j : Fin n => tiltedLaw μ B h j),
      ∀ j, 0 < u j := by
    rw [ae_all_iff]
    intro j
    exact Measure.tendsto_eval_ae_ae.eventually (ae_pos_tiltedLaw hpos hB h j)
  filter_upwards [hu] with u hu
  exact ⟨hr, hu⟩

private theorem integrable_spineWalk {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ × (Fin n → ℝ) => spineWalk B x.2 n) (spineMeasure μ B h n) := by
  let : IsProbabilityMeasure (spineMeasure μ B h n) := by
    let : IsProbabilityMeasure (tiltedLaw μ B h 0) :=
      isProbabilityMeasure_tiltedLaw hpos hmean hB h 0
    let (j : Fin n) : IsProbabilityMeasure (tiltedLaw μ B h j) :=
      isProbabilityMeasure_tiltedLaw hpos hmean hB h j
    rw [spineMeasure]
    infer_instance
  simp only [spineWalk]
  apply integrable_finsetSum
  intro j _
  by_cases hj : (j : ℕ) < n
  · simp only [hj, ↓reduceIte]
    exact integrable_spineWalkTerm hpos hmean hB h n j
  · simp only [hj, ↓reduceIte]
    exact integrable_const 0

private theorem spineW_log_base_le {B : ℝ} (hB : 2 < B) {n : ℕ} {r : ℝ}
    (hr : 0 < r) (u : Fin n → ℝ) :
    |spineW B n r u * Real.log (spineBase B n r u)| ≤ (1 - theta B)⁻¹ := by
  let p := 1 - theta B
  have hp : 0 < p := sub_pos.mpr (theta_lt_one hB)
  have hw0 := spineW_pos hB hr u
  have hw1 := spineW_le_one hB hr u
  have hbpos := spineBase_pos hB hr u
  have hlogw : Real.log (spineW B n r u) = -p * Real.log (spineBase B n r u) := by
    rw [spineW, show 1 + (B - 1) / (B * r) *
      ∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B u k) = spineBase B n r u from rfl]
    exact Real.log_rpow hbpos _
  have habs := Real.abs_log_mul_self_lt (spineW B n r u) hw0 hw1
  have heq : |Real.log (spineW B n r u) * spineW B n r u| =
      p * |spineW B n r u * Real.log (spineBase B n r u)| := by
    rw [hlogw, abs_mul, abs_mul, abs_neg, abs_of_pos hp, abs_of_pos hw0]
    simp only [abs_mul, abs_of_pos hw0,
      abs_of_nonneg (Real.log_nonneg (one_le_spineBase hB hr u))]
    dsimp [p]
    ring
  calc
    |spineW B n r u * Real.log (spineBase B n r u)| =
        p⁻¹ * |Real.log (spineW B n r u) * spineW B n r u| := by
      rw [heq]
      field_simp [hp.ne']
    _ ≤ p⁻¹ * 1 := mul_le_mul_of_nonneg_left habs.le (inv_nonneg.mpr hp.le)
    _ = p⁻¹ := mul_one _

/-- The spine weight and its logarithmically tilted variant are integrable
under `spineMeasure`.  This proves `DiamondPinning.integrable_spine` (in
`DiamondPinning.Statements.Response`). -/
theorem integrable_spine_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ × (Fin n → ℝ) => spineW B n x.1 x.2) (spineMeasure μ B h n) ∧
    Integrable (fun x : ℝ × (Fin n → ℝ) => spineW B n x.1 x.2 *
      (Real.log (spineT B n x.1 x.2) + (1 / theta B - Real.log B))) (spineMeasure μ B h n) := by
  let : IsProbabilityMeasure (spineMeasure μ B h n) := by
    let : IsProbabilityMeasure (tiltedLaw μ B h 0) :=
      isProbabilityMeasure_tiltedLaw hpos hmean hB h 0
    let (j : Fin n) : IsProbabilityMeasure (tiltedLaw μ B h j) :=
      isProbabilityMeasure_tiltedLaw hpos hmean hB h j
    rw [spineMeasure]
    infer_instance
  let p := 1 - theta B
  have hp : 0 < p := sub_pos.mpr (theta_lt_one hB)
  have hfirst : Integrable (fun x : ℝ × (Fin n → ℝ) => spineW B n x.1 x.2)
      (spineMeasure μ B h n) := by
    have halt : Integrable (fun x : ℝ × (Fin n → ℝ) =>
        (spineBase B n x.1 x.2 ^ (1 - theta B))⁻¹) (spineMeasure μ B h n) := by
      apply (integrable_const 1).mono' (measurable_spineWInv hB n).aestronglyMeasurable
      filter_upwards [ae_spine_pos hpos hmean hB h n] with x hx
      have hbpos := spineBase_pos hB hx.1 x.2
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.rpow_pos_of_pos hbpos _))]
      exact inv_le_one_of_one_le₀ (Real.one_le_rpow (one_le_spineBase hB hx.1 x.2)
        (sub_nonneg.mpr (theta_lt_one hB).le))
    apply halt.congr
    filter_upwards [ae_spine_pos hpos hmean hB h n] with x hx
    rw [spineW_eq_inv hB hx.1 x.2]
  refine ⟨hfirst, ?_⟩
  have hS := integrable_spineWalk hpos hmean hB h n
  have hlog := integrable_log_spine_fst hpos hmean hB h n
  have hdom : Integrable (fun x : ℝ × (Fin n → ℝ) =>
      |Real.log x.1| + |spineWalk B x.2 n| + p⁻¹ + |1 / theta B - Real.log B|)
      (spineMeasure μ B h n) := by
    exact ((hlog.norm.add hS.norm).add (integrable_const p⁻¹)).add
      (integrable_const |1 / theta B - Real.log B|)
  have halt : Integrable (fun x : ℝ × (Fin n → ℝ) =>
      (spineBase B n x.1 x.2 ^ (1 - theta B))⁻¹ *
        (Real.log x.1 + spineWalk B x.2 n + Real.log (spineBase B n x.1 x.2) +
          (1 / theta B - Real.log B))) (spineMeasure μ B h n) := by
    have hmeas : Measurable (fun x : ℝ × (Fin n → ℝ) =>
        (spineBase B n x.1 x.2 ^ (1 - theta B))⁻¹ *
          (Real.log x.1 + spineWalk B x.2 n + Real.log (spineBase B n x.1 x.2) +
            (1 / theta B - Real.log B))) := by
      exact (measurable_spineWInv hB n).mul (by
        exact (((Real.measurable_log.comp measurable_fst).add
          (by unfold spineWalk; fun_prop)).add
          (Real.measurable_log.comp (measurable_spineBase B n))).add_const _)
    apply hdom.mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_spine_pos hpos hmean hB h n] with x hx
    have hw0 := spineW_pos hB hx.1 x.2
    have hw1 := spineW_le_one hB hx.1 x.2
    have hwlog := spineW_log_base_le hB hx.1 x.2
    rw [spineW_eq_inv hB hx.1 x.2] at hw0 hw1 hwlog
    have hpart (y : ℝ) : |(spineBase B n x.1 x.2 ^ (1 - theta B))⁻¹ * y| ≤ |y| := by
      rw [abs_mul, abs_of_pos hw0]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hw1 (abs_nonneg y)
    calc
      |(spineBase B n x.1 x.2 ^ (1 - theta B))⁻¹ *
          (Real.log x.1 + spineWalk B x.2 n + Real.log (spineBase B n x.1 x.2) +
            (1 / theta B - Real.log B))| ≤
          |(spineBase B n x.1 x.2 ^ (1 - theta B))⁻¹ * Real.log x.1| +
            |(spineBase B n x.1 x.2 ^ (1 - theta B))⁻¹ * spineWalk B x.2 n| +
            |(spineBase B n x.1 x.2 ^ (1 - theta B))⁻¹ * Real.log (spineBase B n x.1 x.2)| +
            |(spineBase B n x.1 x.2 ^ (1 - theta B))⁻¹ * (1 / theta B - Real.log B)| := by
        rw [mul_add, mul_add, mul_add]
        exact (abs_add_le _ _).trans (add_le_add_left (abs_add_three _ _ _) _)
      _ ≤ |Real.log x.1| + |spineWalk B x.2 n| + p⁻¹ + |1 / theta B - Real.log B| := by
        exact add_le_add (add_le_add (add_le_add (hpart _) (hpart _)) hwlog) (hpart _)
  apply halt.congr
  filter_upwards [ae_spine_pos hpos hmean hB h n] with x hx
  rw [spineW_eq_inv hB hx.1 x.2, log_spineT hB hx.1 x.2]

end DiamondPinning
