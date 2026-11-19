module

public import DiamondPinning.Proofs.ContactsProof
public import DiamondPinning.Proofs.IntegrabilityProof
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Field differentiation of tilted moments

This file differentiates the tilted logarithmic moments and the product-kernel
mean by expanding partition functions as finite contact polynomials.  It proves
the derivative formulas used by the spine identities in `source/response.tex`,
lines 62–96, and by the convergence argument at lines 175–196.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology

/-- The exponential-polynomial functions used by the field envelope are
smooth. -/
theorem contDiff_exp_mul_pow (θ a : ℝ) (k : ℕ) :
    ContDiff ℝ 3 (fun x : ℝ => Real.exp (θ * x) * (x - a) ^ k) := by
  fun_prop

/-- First derivative of the exponential-polynomial envelope function. -/
theorem hasDerivAt_exp_mul_pow (θ a : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (θ * x) * (x - a) ^ k)
      (Real.exp (θ * x) * (θ * (x - a) ^ k + k * (x - a) ^ (k - 1))) x := by
  have hlin : HasDerivAt (fun x : ℝ => θ * x) θ x := by
    simpa using (hasDerivAt_id x).const_mul θ
  have hsub : HasDerivAt (fun x : ℝ => x - a) 1 x := by
    simpa using (hasDerivAt_id x).sub_const a
  convert hlin.exp.mul (hsub.pow k) using 1
  all_goals simp only [Pi.pow_apply]
  all_goals ring

/-- Leibniz formula for derivatives of the exponential-polynomial envelope
function. -/
theorem iteratedDeriv_exp_mul_pow (i : ℕ) (θ a : ℝ) (k : ℕ) (x : ℝ) :
    iteratedDeriv i (fun x : ℝ => Real.exp (θ * x) * (x - a) ^ k) x =
      ∑ j ∈ Finset.range (i + 1),
        (i.choose j : ℝ) * θ ^ j * (k.descFactorial (i - j) : ℝ) *
          Real.exp (θ * x) * (x - a) ^ (k - (i - j)) := by
  rw [show (fun x : ℝ => Real.exp (θ * x) * (x - a) ^ k) =
    (fun x => Real.exp (θ * x)) * (fun x => (x - a) ^ k) by rfl]
  rw [iteratedDeriv_mul (n := i) (x := x)
    (f := fun x : ℝ => Real.exp (θ * x)) (g := fun x : ℝ => (x - a) ^ k)
    (by fun_prop) (by fun_prop)]
  simp_rw [iteratedDeriv_exp_const_mul]
  have hshift (r : ℕ) : iteratedDeriv r (fun x : ℝ => (x - a) ^ k) x =
      (k.descFactorial r : ℝ) * (x - a) ^ (k - r) := by
    have hs := congrFun (iteratedDeriv_comp_sub_const (n := r)
      (f := fun y : ℝ => y ^ k) a) x
    change iteratedDeriv r (fun z : ℝ => (z - a) ^ k) x = _
    rw [hs, iteratedDeriv_pow]
  simp_rw [hshift]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The first three derivatives of the exponential-polynomial envelope
function have the domination required by `field_envelope_aux`. -/
theorem exists_iteratedDeriv_exp_mul_pow_bound (θ a : ℝ) (k : ℕ) :
    ∃ K : ℝ, ∀ i ≤ (3 : ℕ), ∀ x : ℝ,
      |iteratedDeriv i (fun x : ℝ => Real.exp (θ * x) * (x - a) ^ k) x| ≤
        K * Real.exp (θ * x) * (1 + |x - a|) ^ (k : ℝ) := by
  refine ⟨32 * (1 + |θ|) ^ 3 * (1 + (k : ℝ)) ^ 3, ?_⟩
  intro i hi x
  rw [iteratedDeriv_exp_mul_pow]
  have hterm (j : ℕ) (hj : j ∈ Finset.range (i + 1)) :
      |(i.choose j : ℝ) * θ ^ j * (k.descFactorial (i - j) : ℝ) *
          Real.exp (θ * x) * (x - a) ^ (k - (i - j))| ≤
        8 * (1 + |θ|) ^ 3 * (1 + (k : ℝ)) ^ 3 *
          Real.exp (θ * x) * (1 + |x - a|) ^ k := by
    have hji : j ≤ i := by exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hchoose : (i.choose j : ℝ) ≤ 8 := by
      have h := Nat.choose_le_two_pow i j
      have hi' : 2 ^ i ≤ (8 : ℕ) := by
        have : 2 ^ i ≤ 2 ^ 3 := Nat.pow_le_pow_right (by omega) hi
        norm_num at this ⊢
        exact this
      exact_mod_cast h.trans hi'
    have hθpow : |θ| ^ j ≤ (1 + |θ|) ^ 3 := by
      calc
        _ ≤ (1 + |θ|) ^ j := pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg θ]) _
        _ ≤ (1 + |θ|) ^ 3 := pow_le_pow_right₀ (by linarith [abs_nonneg θ]) (hji.trans hi)
    have hdesc : (k.descFactorial (i - j) : ℝ) ≤ (1 + (k : ℝ)) ^ 3 := by
      have hd := Nat.descFactorial_le_pow k (i - j)
      have hd' : k ^ (i - j) ≤ (1 + k) ^ 3 := by
        calc
          k ^ (i - j) ≤ (1 + k) ^ (i - j) :=
            Nat.pow_le_pow_left (by omega) _
          _ ≤ (1 + k) ^ 3 := Nat.pow_le_pow_right (by omega) ((Nat.sub_le _ _).trans hi)
      exact_mod_cast hd.trans hd'
    have hxpow : |x - a| ^ (k - (i - j)) ≤ (1 + |x - a|) ^ k := by
      calc
        |x - a| ^ (k - (i - j)) ≤ (1 + |x - a|) ^ (k - (i - j)) :=
          pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg (x - a)]) _
        _ ≤ (1 + |x - a|) ^ k :=
          pow_le_pow_right₀ (by linarith [abs_nonneg (x - a)]) (Nat.sub_le _ _)
    have hxpow' : |(x - a) ^ (k - (i - j))| ≤ (1 + |x - a|) ^ k := by
      rw [abs_pow]
      exact hxpow
    rw [abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (i.choose j : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.descFactorial (i - j) : ℝ)),
      abs_of_nonneg (Real.exp_pos _).le, abs_pow]
    have hcommon : (0 : ℝ) ≤ Real.exp (θ * x) * (1 + |x - a|) ^ k := by positivity
    gcongr
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum hterm).trans
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Real.rpow_natCast]
  have hi' : (i + 1 : ℝ) ≤ 4 := by exact_mod_cast (show i + 1 ≤ 4 by omega)
  have hp : (0 : ℝ) ≤ 8 * (1 + |θ|) ^ 3 * (1 + (k : ℝ)) ^ 3 *
      Real.exp (θ * x) * (1 + |x - a|) ^ k := by positivity
  norm_num [Nat.cast_add, Nat.cast_one]
  convert mul_le_mul_of_nonneg_right hi' hp using 1
  all_goals ring

section ContactPolynomial

open Polynomial

/-- The finite contact-polynomial expansion of the partition function. -/
theorem sum_contactPoly_coeff_exp (B h : ℝ) (n : ℕ) (e : Env n) :
    (∑ k : Fin (2 ^ n + 1),
      (contactPoly B 0 n e).coeff k.val * Real.exp ((k.val : ℝ) * h)) = evalR B h n e := by
  rw [← zero_add h, ← eval_contactPoly_exp B 0 n e h,
    eval_eq_sum_range' (Nat.lt_succ_of_le (contactPoly_natDegree_le B 0 n e)),
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Real.exp_nat_mul]
  ring_nf

/-- The sum of the contact coefficients is the partition function at field
zero. -/
private theorem sum_contactPoly_coeff (B : ℝ) (n : ℕ) (e : Env n) :
    (∑ k : Fin (2 ^ n + 1), (contactPoly B 0 n e).coeff k.val) = evalR B 0 n e := by
  simpa using sum_contactPoly_coeff_exp B 0 n e


/-- Measurability of a contact-polynomial coefficient. -/
theorem measurable_contactPoly_coeff_field (B h : ℝ) :
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

/-- The first moment of the evaluator is integrable in the environment. -/
theorem integrable_evalR_env {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : Integrable (evalR B h n) (envMeasure μ n) := by
  have hi := integrable_lawR_of hpos hmean hB h n
  rw [← map_evalR_envMeasure_aux μ B h n] at hi
  simpa only [Function.comp_def, id_eq] using
    (integrable_map_measure (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable
      (measurable_evalR B h n).aemeasurable).mp hi

/-- Every contact coefficient is integrable with respect to the environment
law. -/
theorem integrable_contactPoly_coeff {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (n : ℕ) (k : Fin (2 ^ n + 1)) :
    Integrable (fun e => (contactPoly B 0 n e).coeff k.val) (envMeasure μ n) := by
  have hR := integrable_evalR_env hpos hmean hB 0 n
  apply hR.mono' (measurable_contactPoly_coeff_field B 0 n k.val).aestronglyMeasurable
  filter_upwards [ae_envPos_aux hpos n] with e he
  rw [Real.norm_eq_abs, abs_of_nonneg (contactPoly_coeff_nonneg (by linarith) 0 n e he k.val)]
  rw [← sum_contactPoly_coeff B n e]
  exact Finset.single_le_sum
    (fun j _ => contactPoly_coeff_nonneg (by linarith) 0 n e he j.val) (Finset.mem_univ k)

/-- The field envelope specialized to the contact polynomial of `evalR`. -/
theorem contact_field_envelope {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (k n : ℕ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 3 φ)
    (hg : ∃ K : ℝ, ∀ i ≤ (3 : ℕ), ∀ x : ℝ,
      |iteratedDeriv i φ x| ≤ K * Real.exp (theta B * x) *
        (1 + |x - Real.log B|) ^ (k : ℝ)) :
    ∀ i < (2 : ℕ),
      HasDerivAt
        (fieldMean (envMeasure μ n)
          (fun e => iteratedDeriv i (fun h'' => φ (Real.log (evalR B h'' n e)))))
        (fieldMean (envMeasure μ n)
          (fun e => iteratedDeriv (i + 1) (fun h'' => φ (Real.log (evalR B h'' n e)))) h) h := by
  have hp0 : ∀ᵐ e ∂(envMeasure μ n),
      (∀ k : Fin (2 ^ n + 1), 0 ≤ (contactPoly B 0 n e).coeff k.val) ∧
        0 < ∑ k : Fin (2 ^ n + 1), (contactPoly B 0 n e).coeff k.val := by
    filter_upwards [ae_envPos_aux hpos n] with e he
    refine ⟨fun k => contactPoly_coeff_nonneg (by linarith) 0 n e he k.val, ?_⟩
    rw [sum_contactPoly_coeff]
    exact evalR_pos_aux (by linarith) 0 n he
  have H := (field_envelope_aux (envMeasure μ n) (h₀ := h)
    (fun (k : Fin (2 ^ n + 1)) (e : Env n) => (contactPoly B 0 n e).coeff k.val)
    (integrable_contactPoly_coeff hpos hmean hB n) hp0
    (theta_pos hB) (theta_lt_one hB) (Nat.cast_nonneg k) φ hφ hg).2.2
  simpa only [sum_contactPoly_coeff_exp] using H


/-- Transfer of a tilted logarithmic moment to the environment. -/
theorem tiltedLogMoment_eq_env {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (k n : ℕ) :
    tiltedLogMoment μ B h k n = ∫ e, Real.exp (theta B * Real.log (evalR B h n e)) *
      (Real.log (evalR B h n e) - Real.log B) ^ k ∂(envMeasure μ n) := by
  rw [tiltedLogMoment, ← map_evalR_envMeasure_aux μ B h n,
    integral_map (measurable_evalR B h n).aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [ae_envPos_aux hpos n] with e he
  rw [Real.rpow_def_of_pos (evalR_pos_aux (by linarith) h n he)]
  congr 2
  ring

/-- The derivative of a tilted logarithmic moment, transferred to the
environment and identified pointwise with the chain-rule derivative. -/
theorem tiltedLogMomentDeriv_eq_env {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (k n : ℕ) :
    tiltedLogMomentDeriv μ B h k n = ∫ e,
      deriv (fun h' => Real.exp (theta B * Real.log (evalR B h' n e)) *
        (Real.log (evalR B h' n e) - Real.log B) ^ k) h ∂(envMeasure μ n) := by
  rw [tiltedLogMomentDeriv]
  apply integral_congr_ae
  filter_upwards [ae_envPos_aux hpos n] with e he
  have hlog := contact_hasDerivAt_log_evalR (by linarith) h n e he
  have hd := (hasDerivAt_exp_mul_pow (theta B) (Real.log B) k
    (Real.log (evalR B h n e))).comp h hlog
  have hd' : HasDerivAt (fun h' => Real.exp (theta B * Real.log (evalR B h' n e)) *
      (Real.log (evalR B h' n e) - Real.log B) ^ k)
      (Real.exp (theta B * Real.log (evalR B h n e)) *
        (theta B * (Real.log (evalR B h n e) - Real.log B) ^ k +
          k * (Real.log (evalR B h n e) - Real.log B) ^ (k - 1)) *
        gibbsMean B h n e (fun j => (j : ℝ))) h := by
    simpa only [Function.comp_def] using hd
  rw [hd'.deriv, Real.rpow_def_of_pos (evalR_pos_aux (by linarith) h n he)]
  ring

/-- The derivative of a tilted logarithmic moment is the corresponding Gibbs
contact expression.  This proves the frozen `hasDerivAt_tiltedLogMoment`. -/
theorem hasDerivAt_tiltedLogMoment_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    (k n : ℕ) :
    HasDerivAt (fun h' => tiltedLogMoment μ B h' k n) (tiltedLogMomentDeriv μ B h k n) h := by
  let φ : ℝ → ℝ := fun x => Real.exp (theta B * x) * (x - Real.log B) ^ k
  have H := contact_field_envelope hpos hmean hB h k n φ
    (contDiff_exp_mul_pow (theta B) (Real.log B) k)
    (exists_iteratedDeriv_exp_mul_pow_bound (theta B) (Real.log B) k) 0 (by norm_num)
  simp only [iteratedDeriv_zero, zero_add, iteratedDeriv_one, fieldMean] at H
  rw [show (fun h' => tiltedLogMoment μ B h' k n) = (fun h' => ∫ e,
      φ (Real.log (evalR B h' n e)) ∂(envMeasure μ n)) by
    funext h'
    exact tiltedLogMoment_eq_env hpos hB h' k n]
  rw [tiltedLogMomentDeriv_eq_env hpos hB h k n]
  exact H

/-- The tilted normalizing mass has derivative `theta B` times the first
contact moment.  This proves the frozen `hasDerivAt_tiltedMass`. -/
theorem hasDerivAt_tiltedMass_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    (n : ℕ) :
    HasDerivAt (fun h' => tiltedMass μ B h' n) (theta B * contactMoment μ B h 1 n) h := by
  have H := hasDerivAt_tiltedLogMoment_aux hpos hmean hB h 0 n
  have hfun : (fun h' => tiltedMass μ B h' n) = (fun h' => tiltedLogMoment μ B h' 0 n) := by
    funext h'
    simp [tiltedMass, tiltedLogMoment]
  rw [hfun]
  convert H using 1
  rw [tiltedLogMomentDeriv, contactMoment]
  simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero, mul_one, pow_one]
  rw [integral_mul_const]
  ring

/-- The derivative of the first tilted logarithmic moment is differentiable.
This proves the frozen `differentiableAt_deriv_tiltedLogMoment_one`. -/
theorem differentiableAt_deriv_tiltedLogMoment_one_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    (n : ℕ) :
    DifferentiableAt ℝ (deriv fun h' => tiltedLogMoment μ B h' 1 n) h := by
  have hderiv : (deriv fun h' => tiltedLogMoment μ B h' 1 n) =
      (fun h' => tiltedLogMomentDeriv μ B h' 1 n) := by
    funext h'
    exact (hasDerivAt_tiltedLogMoment_aux hpos hmean hB h' 1 n).deriv
  rw [hderiv]
  let φ : ℝ → ℝ := fun x => Real.exp (theta B * x) * (x - Real.log B) ^ (1 : ℕ)
  have H := contact_field_envelope hpos hmean hB h 1 n φ
    (contDiff_exp_mul_pow (theta B) (Real.log B) 1)
    (exists_iteratedDeriv_exp_mul_pow_bound (theta B) (Real.log B) 1) 1 (by norm_num)
  simp only [iteratedDeriv_one, one_add_one_eq_two, fieldMean] at H
  have hfun : (fun h' => tiltedLogMomentDeriv μ B h' 1 n) = (fun h' => ∫ e,
      deriv (fun h'' => φ (Real.log (evalR B h'' n e))) h' ∂(envMeasure μ n)) := by
    funext h'
    exact tiltedLogMomentDeriv_eq_env hpos hB h' 1 n
  rw [hfun]
  exact H.differentiableAt


/-- The product contact polynomial, with an optional additive constant. -/
noncomputable def pairContactPoly (B c : ℝ) (n : ℕ) (e : Env n × Env n) : ℝ[X] :=
  contactPoly B 0 n e.1 * contactPoly B 0 n e.2 + C c

/-- The pair evaluator represented by `pairContactPoly`. -/
noncomputable def pairEval (B c : ℝ) (h : ℝ) (n : ℕ) (e : Env n × Env n) : ℝ :=
  evalR B h n e.1 * evalR B h n e.2 + c

/-- Degree bound for the shifted product contact polynomial. -/
theorem pairContactPoly_natDegree_le (B c : ℝ) (n : ℕ) (e : Env n × Env n) :
    (pairContactPoly B c n e).natDegree ≤ 2 ^ (n + 1) := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply natDegree_mul_le.trans
    have h₁ := contactPoly_natDegree_le B 0 n e.1
    have h₂ := contactPoly_natDegree_le B 0 n e.2
    rw [pow_succ]
    omega
  · exact (natDegree_C c).le.trans (Nat.zero_le _)

/-- Evaluation of the shifted product contact polynomial at an exponential. -/
theorem pairContactPoly_eval_exp (B c h : ℝ) (n : ℕ) (e : Env n × Env n) :
    (pairContactPoly B c n e).eval (Real.exp h) = pairEval B c h n e := by
  simp [pairContactPoly, pairEval, eval_contactPoly_exp]

/-- The exponential-polynomial expansion of `pairEval`. -/
theorem sum_pairContactPoly_coeff_exp (B c h : ℝ) (n : ℕ) (e : Env n × Env n) :
    (∑ k : Fin (2 ^ (n + 1) + 1),
      (pairContactPoly B c n e).coeff k.val * Real.exp ((k.val : ℝ) * h)) =
        pairEval B c h n e := by
  rw [← pairContactPoly_eval_exp,
    eval_eq_sum_range' (Nat.lt_succ_of_le (pairContactPoly_natDegree_le B c n e)),
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Real.exp_nat_mul]

/-- Nonnegativity of the shifted product coefficients on positive
environments. -/
theorem pairContactPoly_coeff_nonneg {B c : ℝ} (hB : 1 < B) (hc : 0 ≤ c)
    (n : ℕ) (e : Env n × Env n) (he : Env.Pos n e.1 ∧ Env.Pos n e.2) (k : ℕ) :
    0 ≤ (pairContactPoly B c n e).coeff k := by
  simp only [pairContactPoly, coeff_add, coeff_mul, coeff_C]
  apply add_nonneg
  · exact Finset.sum_nonneg fun ij _ => mul_nonneg
      (contactPoly_coeff_nonneg hB 0 n e.1 he.1 ij.1)
      (contactPoly_coeff_nonneg hB 0 n e.2 he.2 ij.2)
  · split_ifs
    · exact hc
    · exact le_rfl

/-- Measurability of the shifted product coefficients. -/
theorem measurable_pairContactPoly_coeff (B c : ℝ) (n : ℕ) (k : ℕ) :
    Measurable (fun e : Env n × Env n => (pairContactPoly B c n e).coeff k) := by
  have hm : Measurable (fun e : Env n × Env n =>
      ((contactPoly B 0 n e.1 * contactPoly B 0 n e.2).coeff k)) := by
    simp only [Polynomial.coeff_mul]
    apply Finset.measurable_sum
    intro ij _
    exact ((measurable_contactPoly_coeff_field B 0 n ij.1).comp measurable_fst).mul
      ((measurable_contactPoly_coeff_field B 0 n ij.2).comp measurable_snd)
  simp only [pairContactPoly, coeff_add, coeff_C]
  exact hm.add (by split_ifs <;> fun_prop)

/-- Integrability of every shifted product coefficient. -/
theorem integrable_pairContactPoly_coeff {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (k : Fin (2 ^ (n + 1) + 1)) :
    Integrable (fun e : Env n × Env n => (pairContactPoly B c n e).coeff k.val)
      ((envMeasure μ n).prod (envMeasure μ n)) := by
  let ν := (envMeasure μ n).prod (envMeasure μ n)
  have hR := integrable_evalR_env hpos hmean hB 0 n
  have hq : Integrable (fun e : Env n × Env n => pairEval B c 0 n e) ν := by
    exact (hR.mul_prod hR).add (integrable_const c)
  apply hq.mono' (measurable_pairContactPoly_coeff B c n k.val).aestronglyMeasurable
  have hepos : ∀ᵐ e : Env n × Env n ∂ν, Env.Pos n e.1 ∧ Env.Pos n e.2 := by
    change ∀ᵐ e ∂(envMeasure μ (n + 1)), Env.Pos (n + 1) e
    exact ae_envPos_aux hpos (n + 1)
  filter_upwards [hepos] with e he
  rw [Real.norm_eq_abs, abs_of_nonneg
    (pairContactPoly_coeff_nonneg (B := B) (c := c) (by linarith) hc n e he k.val)]
  have hsum : (∑ j : Fin (2 ^ (n + 1) + 1), (pairContactPoly B c n e).coeff j.val) =
      pairEval B c 0 n e := by
    simpa using sum_pairContactPoly_coeff_exp B c 0 n e
  rw [← hsum]
  exact Finset.single_le_sum
    (fun j _ => pairContactPoly_coeff_nonneg (B := B) (c := c) (by linarith) hc n e he
      j.val) (Finset.mem_univ k)

/-- First-order field envelope for a shifted product of two partition
functions. -/
theorem pair_field_envelope {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {c : ℝ} (hc : 0 ≤ c) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 3 φ)
    (hg : ∃ K : ℝ, ∀ i ≤ (3 : ℕ), ∀ x : ℝ,
      |iteratedDeriv i φ x| ≤ K * Real.exp (theta B * x) *
        (1 + |x - 2 * Real.log B|) ^ (1 : ℝ)) :
    Integrable (fun e : Env n × Env n => φ (Real.log (pairEval B c h n e)))
        ((envMeasure μ n).prod (envMeasure μ n)) ∧
      HasDerivAt
        (fun h' => ∫ e : Env n × Env n, φ (Real.log (pairEval B c h' n e))
          ∂((envMeasure μ n).prod (envMeasure μ n)))
        (∫ e : Env n × Env n, deriv (fun h'' => φ (Real.log (pairEval B c h'' n e))) h
          ∂((envMeasure μ n).prod (envMeasure μ n))) h := by
  let ν := (envMeasure μ n).prod (envMeasure μ n)
  have hepos : ∀ᵐ e : Env n × Env n ∂ν, Env.Pos n e.1 ∧ Env.Pos n e.2 := by
    change ∀ᵐ e ∂(envMeasure μ (n + 1)), Env.Pos (n + 1) e
    exact ae_envPos_aux hpos (n + 1)
  have hp0 : ∀ᵐ e ∂ν,
      (∀ k : Fin (2 ^ (n + 1) + 1), 0 ≤ (pairContactPoly B c n e).coeff k.val) ∧
        0 < ∑ k : Fin (2 ^ (n + 1) + 1), (pairContactPoly B c n e).coeff k.val := by
    filter_upwards [hepos] with e he
    refine ⟨fun k => pairContactPoly_coeff_nonneg (B := B) (c := c) (by linarith) hc n e he
      k.val, ?_⟩
    have hsum : (∑ k : Fin (2 ^ (n + 1) + 1), (pairContactPoly B c n e).coeff k.val) =
        pairEval B c 0 n e := by simpa using sum_pairContactPoly_coeff_exp B c 0 n e
    rw [hsum]
    have h₁ := evalR_pos_aux (B := B) (by linarith) 0 n he.1
    have h₂ := evalR_pos_aux (B := B) (by linarith) 0 n he.2
    exact add_pos_of_pos_of_nonneg (mul_pos h₁ h₂) hc
  obtain ⟨K, hK⟩ := hg
  have H := field_envelope_aux ν (h₀ := h)
    (fun (k : Fin (2 ^ (n + 1) + 1)) (e : Env n × Env n) =>
      (pairContactPoly B c n e).coeff k.val)
    (integrable_pairContactPoly_coeff hpos hmean hB hc n) hp0
    (theta_pos hB) (theta_lt_one hB) (by norm_num) φ hφ ⟨K, hK⟩
  have hfun (h' : ℝ) : (fun e : Env n × Env n => φ (Real.log (pairEval B c h' n e))) =
      (fun e => φ (Real.log (∑ k : Fin (2 ^ (n + 1) + 1),
        (pairContactPoly B c n e).coeff k.val * Real.exp ((k.val : ℝ) * h')))) := by
    funext e
    rw [sum_pairContactPoly_coeff_exp]
  have hmeas : Measurable (pairEval B c h n) := by
    exact (((measurable_evalR B h n).comp measurable_fst).mul
      ((measurable_evalR B h n).comp measurable_snd)).add_const c
  refine ⟨?_, ?_⟩
  · apply (H.1.const_mul K).mono'
    · exact (hφ.continuous.measurable.comp (Real.measurable_log.comp hmeas)).aestronglyMeasurable
    · filter_upwards with e
      rw [Real.norm_eq_abs, ← sum_pairContactPoly_coeff_exp B c h n e]
      exact (hK 0 (by norm_num) _).trans_eq (by ring)
  · have H0 := H.2.2 0 (by norm_num)
    simp only [iteratedDeriv_zero, zero_add, iteratedDeriv_one, fieldMean,
      sum_pairContactPoly_coeff_exp] at H0
    exact H0

/-- The law of the pair product is `productLaw`. -/
theorem map_pairEval_envMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B h : ℝ) (n : ℕ) :
    (((envMeasure μ n).prod (envMeasure μ n)).map
      (fun e => evalR B h n e.1 * evalR B h n e.2)) = productLaw μ B h n := by
  let f : Env n × Env n → ℝ × ℝ :=
    fun e => (evalR B h n e.1, evalR B h n e.2)
  let g : ℝ × ℝ → ℝ := fun p => p.1 * p.2
  have hf : Measurable f := by
    exact ((measurable_evalR B h n).comp measurable_fst).prodMk
      ((measurable_evalR B h n).comp measurable_snd)
  have hg : Measurable g := by fun_prop
  change (((envMeasure μ n).prod (envMeasure μ n)).map (g ∘ f)) = productLaw μ B h n
  calc
    (((envMeasure μ n).prod (envMeasure μ n)).map (g ∘ f)) =
        ((((envMeasure μ n).prod (envMeasure μ n)).map f).map g) := by
      rw [← Measure.map_map hg hf]
    _ = (((envMeasure μ n).map (evalR B h n)).prod
        ((envMeasure μ n).map (evalR B h n))).map g := by
      congr 1
      rw [Measure.map_prod_map (envMeasure μ n) (envMeasure μ n)
        (measurable_evalR B h n) (measurable_evalR B h n)]
      rfl
    _ = productLaw μ B h n := by
      rw [map_evalR_envMeasure_aux]
      rfl

/-- Measurability of the kernel function. -/
theorem measurable_kernelPsi {B : ℝ} (hB : 2 < B) : Measurable (kernelPsi B) := by
  apply Measurable.sub
  · apply Measurable.mul
    · exact (Real.continuous_rpow_const (theta_pos hB).le).measurable.comp
        (measurable_id.add_const (B - 1))
    · exact Real.measurable_log.comp ((measurable_id.add_const (B - 1)).div_const (B ^ 2))
  · apply Measurable.mul
    · exact (Real.continuous_rpow_const (theta_pos hB).le).measurable.comp measurable_id
    · exact Real.measurable_log.comp (measurable_id.div_const (B ^ 2))

/-- Transfer of the kernel expectation to the pair environment. -/
theorem kernelMean_eq_env {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    kernelMean μ B h n = ∫ e : Env n × Env n,
      (Real.exp (theta B * Real.log (pairEval B (B - 1) h n e)) *
          (Real.log (pairEval B (B - 1) h n e) - 2 * Real.log B) -
        Real.exp (theta B * Real.log (pairEval B 0 h n e)) *
          (Real.log (pairEval B 0 h n e) - 2 * Real.log B))
      ∂((envMeasure μ n).prod (envMeasure μ n)) := by
  have hpair : Measurable (fun e : Env n × Env n =>
      evalR B h n e.1 * evalR B h n e.2) :=
    ((measurable_evalR B h n).comp measurable_fst).mul
      ((measurable_evalR B h n).comp measurable_snd)
  rw [kernelMean, ← map_pairEval_envMeasure μ B h n,
    integral_map hpair.aemeasurable (measurable_kernelPsi hB).aestronglyMeasurable]
  apply integral_congr_ae
  have hepos : ∀ᵐ e : Env n × Env n ∂((envMeasure μ n).prod (envMeasure μ n)),
      Env.Pos n e.1 ∧ Env.Pos n e.2 := by
    change ∀ᵐ e ∂(envMeasure μ (n + 1)), Env.Pos (n + 1) e
    exact ae_envPos_aux hpos (n + 1)
  filter_upwards [hepos] with e he
  have h₁ := evalR_pos_aux (B := B) (by linarith) h n he.1
  have h₂ := evalR_pos_aux (B := B) (by linarith) h n he.2
  have hs : 0 < evalR B h n e.1 * evalR B h n e.2 := mul_pos h₁ h₂
  have hsc : 0 < evalR B h n e.1 * evalR B h n e.2 + (B - 1) := by linarith
  simp only [pairEval, add_zero, kernelPsi]
  rw [Real.rpow_def_of_pos hs, Real.rpow_def_of_pos hsc,
    Real.log_div hs.ne' (pow_ne_zero 2 (by linarith : B ≠ 0)),
    Real.log_div hsc.ne' (pow_ne_zero 2 (by linarith : B ≠ 0)), Real.log_pow]
  ring

/-- The product-kernel mean is differentiable in the field.  This proves the
frozen `differentiableAt_kernelMean`. -/
theorem differentiableAt_kernelMean_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    (n : ℕ) :
    DifferentiableAt ℝ (fun h' => kernelMean μ B h' n) h := by
  let φ : ℝ → ℝ := fun x => Real.exp (theta B * x) * (x - 2 * Real.log B) ^ (1 : ℕ)
  have hφ := contDiff_exp_mul_pow (theta B) (2 * Real.log B) 1
  have hg := exists_iteratedDeriv_exp_mul_pow_bound (theta B) (2 * Real.log B) 1
  have hg' : ∃ K : ℝ, ∀ i ≤ (3 : ℕ), ∀ x : ℝ,
      |iteratedDeriv i φ x| ≤ K * Real.exp (theta B * x) *
        (1 + |x - 2 * Real.log B|) ^ (1 : ℝ) := by
    simpa only [φ, Nat.cast_one] using hg
  have H0 (h' : ℝ) := pair_field_envelope hpos hmean hB h' n (c := 0) (le_refl 0) φ hφ hg'
  have Hc (h' : ℝ) := pair_field_envelope hpos hmean hB h' n (c := B - 1) (by linarith) φ hφ hg'
  have hfun : (fun h' => kernelMean μ B h' n) = fun h' =>
      (∫ e : Env n × Env n, φ (Real.log (pairEval B (B - 1) h' n e))
        ∂((envMeasure μ n).prod (envMeasure μ n))) -
      (∫ e : Env n × Env n, φ (Real.log (pairEval B 0 h' n e))
        ∂((envMeasure μ n).prod (envMeasure μ n))) := by
    funext h'
    rw [kernelMean_eq_env hpos hB h' n]
    simp only [φ, pow_one]
    rw [integral_sub (by simpa only [φ, pow_one] using (Hc h').1)
      (by simpa only [φ, pow_one] using (H0 h').1)]
  rw [hfun]
  exact ((Hc h).2.sub (H0 h).2).differentiableAt

end ContactPolynomial

end DiamondPinning
