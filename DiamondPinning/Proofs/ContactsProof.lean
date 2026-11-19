module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Model.Contacts
public import DiamondPinning.Proofs.Env
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Contact-polynomial identities

This file proves positivity and evaluation formulas for contact polynomials,
constructs the Gibbs contact law, and differentiates the logarithmic partition
function.  It covers the contact representation and change-of-field identities
in `source/response.tex`, lines 205–242.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Polynomial

/-- At a positive environment, every coefficient of the contact polynomial is
nonnegative. -/
theorem contactPoly_coeff_nonneg {B : ℝ} (hB : 1 < B) (h : ℝ) :
    ∀ (n : ℕ) (e : Env n), Env.Pos n e → ∀ k, 0 ≤ (contactPoly B h n e).coeff k := by
  intro n
  induction n with
  | zero =>
      intro e he k
      change 0 < (show ℝ from e) at he
      have ha : 0 ≤ Real.exp h * (show ℝ from e) := (mul_pos (Real.exp_pos h) he).le
      rw [contactPoly, coeff_C_mul_X]
      split_ifs
      · exact ha
      · exact le_rfl
  | succ n ih =>
      intro e he k
      have he₁ : Env.Pos n e.1 := he.1
      have he₂ : Env.Pos n e.2 := he.2
      simp only [contactPoly, coeff_C_mul, coeff_add]
      apply mul_nonneg (inv_nonneg.mpr (by linarith))
      apply add_nonneg
      · rw [coeff_mul]
        exact Finset.sum_nonneg fun ij _ => mul_nonneg (ih e.1 he₁ ij.1) (ih e.2 he₂ ij.2)
      · rw [coeff_C]
        split_ifs
        · linarith
        · exact le_rfl

/-- The contact polynomial has degree at most the number `2^n` of leaves. -/
theorem contactPoly_natDegree_le (B h : ℝ) :
    ∀ (n : ℕ) (e : Env n), (contactPoly B h n e).natDegree ≤ 2 ^ n := by
  intro n
  induction n with
  | zero =>
      intro e
      exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  | succ n ih =>
      intro e
      have hmul : (contactPoly B h n e.1 * contactPoly B h n e.2).natDegree ≤ 2 ^ (n + 1) :=
        natDegree_mul_le.trans (by
          have h₁ := ih e.1
          have h₂ := ih e.2
          rw [pow_succ]
          omega)
      calc
        (contactPoly B h (n + 1) e).natDegree
            ≤ (contactPoly B h n e.1 * contactPoly B h n e.2 + C (B - 1)).natDegree :=
          natDegree_C_mul_le _ _
        _ ≤ max (contactPoly B h n e.1 * contactPoly B h n e.2).natDegree
            (C (B - 1) : ℝ[X]).natDegree := natDegree_add_le _ _
        _ ≤ 2 ^ (n + 1) := max_le hmul ((natDegree_C (B - 1)).le.trans (Nat.zero_le _))

/-- Evaluation at one gives the partition function at the same field. -/
theorem eval_contactPoly_one (B h : ℝ) :
    ∀ (n : ℕ) (e : Env n), (contactPoly B h n e).eval 1 = evalR B h n e := by
  intro n
  induction n with
  | zero => intro e; simp [contactPoly]
  | succ n ih =>
      intro e
      simp only [contactPoly, eval_mul, eval_C, eval_add, evalR_succ, ih]
      ring

/-- Evaluation at `exp u` shifts the field by `u`. -/
theorem eval_contactPoly_exp (B h : ℝ) :
    ∀ (n : ℕ) (e : Env n) (u : ℝ),
      (contactPoly B h n e).eval (Real.exp u) = evalR B (h + u) n e := by
  intro n
  induction n with
  | zero =>
      intro e u
      simp only [contactPoly, eval_mul, eval_C, eval_X, evalR_zero]
      rw [Real.exp_add]
      ac_rfl
  | succ n ih =>
      intro e u
      simp only [contactPoly, eval_mul, eval_C, eval_add, evalR_succ, ih]
      ring

/-- At height zero the Gibbs contact law is concentrated on one contact.
This proves the frozen `gibbsWeight_zero`. -/
theorem gibbsWeight_zero_aux {B : ℝ} (h : ℝ) {w : Env 0} (hw : Env.Pos 0 w) (k : ℕ) :
    gibbsWeight B h 0 w k = if k = 1 then 1 else 0 := by
  have ha : Real.exp h * (show ℝ from w) ≠ 0 :=
    mul_ne_zero (Real.exp_ne_zero h) (ne_of_gt hw)
  by_cases hk : k = 1
  · subst k
    simp [gibbsWeight, contactPoly, ha]
  · simp only [gibbsWeight, contactPoly, coeff_C_mul_X, zero_div, ite_eq_right hk]

/-- The contact weights are a probability law on a positive environment. -/
theorem contact_gibbsWeight_isProb {B : ℝ} (hB : 1 < B) (h : ℝ) :
    ∀ (n : ℕ) (e : Env n), Env.Pos n e →
      (∀ k, 0 ≤ gibbsWeight B h n e k) ∧ (∀ k, 2 ^ n < k → gibbsWeight B h n e k = 0) ∧
        ∑ k ∈ Finset.range (2 ^ n + 1), gibbsWeight B h n e k = 1 := by
  intro n e he
  have hp : 0 < evalR B h n e := evalR_pos_aux hB h n he
  have heval : (contactPoly B h n e).eval 1 ≠ 0 := by
    rw [eval_contactPoly_one]
    exact ne_of_gt hp
  have heval_nonneg : 0 ≤ (contactPoly B h n e).eval 1 := by
    rw [eval_contactPoly_one]
    exact hp.le
  refine ⟨fun k => div_nonneg (contactPoly_coeff_nonneg hB h n e he k) heval_nonneg, ?_, ?_⟩
  · intro k hk
    apply div_eq_zero_iff.mpr
    left
    exact coeff_eq_zero_of_natDegree_lt ((contactPoly_natDegree_le B h n e).trans_lt hk)
  · simp only [gibbsWeight, ← Finset.sum_div]
    have hsum : ∑ k ∈ Finset.range (2 ^ n + 1), (contactPoly B h n e).coeff k =
        (contactPoly B h n e).eval 1 := by
      rw [eval_eq_sum_range' (Nat.lt_succ_of_le (contactPoly_natDegree_le B h n e))]
      simp
    rw [hsum, div_self heval]

/-- The root choice in the contact representation, on a positive environment. -/
theorem contact_gibbsWeight_succ {B : ℝ} (hB : 1 < B) (h : ℝ) {n : ℕ} {e : Env (n + 1)}
    (he : Env.Pos (n + 1) e) (k : ℕ) :
    gibbsWeight B h (n + 1) e k =
      evalR B h n e.1 * evalR B h n e.2 / (evalR B h n e.1 * evalR B h n e.2 + (B - 1)) *
        ∑ ij ∈ Finset.antidiagonal k, gibbsWeight B h n e.1 ij.1 * gibbsWeight B h n e.2 ij.2 +
      if k = 0 then
        (B - 1) / (evalR B h n e.1 * evalR B h n e.2 + (B - 1)) else 0 := by
  have hp₁ : 0 < evalR B h n e.1 := evalR_pos_aux hB h n he.1
  have hp₂ : 0 < evalR B h n e.2 := evalR_pos_aux hB h n he.2
  have hden : evalR B h n e.1 * evalR B h n e.2 + (B - 1) ≠ 0 :=
    ne_of_gt (by nlinarith [mul_pos hp₁ hp₂])
  have hsum :
      (∑ ij ∈ Finset.antidiagonal k,
          (contactPoly B h n e.1).coeff ij.1 * (contactPoly B h n e.2).coeff ij.2) /
          (evalR B h n e.1 * evalR B h n e.2 + (B - 1)) =
        evalR B h n e.1 * evalR B h n e.2 /
          (evalR B h n e.1 * evalR B h n e.2 + (B - 1)) *
        ∑ ij ∈ Finset.antidiagonal k,
          ((contactPoly B h n e.1).coeff ij.1 / evalR B h n e.1) *
            ((contactPoly B h n e.2).coeff ij.2 / evalR B h n e.2) := by
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ij hij
    field_simp
  simp only [gibbsWeight]
  rw [show contactPoly B h (n + 1) e =
    C B⁻¹ * (contactPoly B h n e.1 * contactPoly B h n e.2 + C (B - 1)) from rfl]
  rw [coeff_C_mul, coeff_add, coeff_mul]
  simp only [coeff_C, eval_mul, eval_C, eval_add, eval_contactPoly_one]
  have hcancel :
      B⁻¹ * ((∑ ij ∈ Finset.antidiagonal k,
          (contactPoly B h n e.1).coeff ij.1 * (contactPoly B h n e.2).coeff ij.2) +
        if k = 0 then B - 1 else 0) /
        (B⁻¹ * (evalR B h n e.1 * evalR B h n e.2 + (B - 1))) =
      ((∑ ij ∈ Finset.antidiagonal k,
          (contactPoly B h n e.1).coeff ij.1 * (contactPoly B h n e.2).coeff ij.2) +
        if k = 0 then B - 1 else 0) /
        (evalR B h n e.1 * evalR B h n e.2 + (B - 1)) := by
    field_simp
  rw [hcancel, add_div, hsum]
  split_ifs <;> simp

/-- The root choice decomposes the successor Gibbs weights into contact and
non-contact contributions.  This proves the frozen `gibbsWeight_succ`. -/
theorem gibbsWeight_succ_aux {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ} {e : Env (n + 1)}
    (he : Env.Pos (n + 1) e) (k : ℕ) :
    gibbsWeight B h (n + 1) e k =
      evalR B h n e.1 * evalR B h n e.2 / (evalR B h n e.1 * evalR B h n e.2 + (B - 1)) *
        ∑ ij ∈ Finset.antidiagonal k, gibbsWeight B h n e.1 ij.1 * gibbsWeight B h n e.2 ij.2 +
      if k = 0 then
        (B - 1) / (evalR B h n e.1 * evalR B h n e.2 + (B - 1)) else 0 := by
  exact contact_gibbsWeight_succ (by linarith) h he k

/-- The contact polynomial changes the base field by a Gibbs exponential
expectation. -/
theorem contact_evalR_add_eq_gibbsMean {B : ℝ} (hB : 1 < B) (h : ℝ) (n : ℕ)
    (e : Env n) (he : Env.Pos n e) (u : ℝ) :
    evalR B (h + u) n e = evalR B h n e * gibbsMean B h n e (fun j => Real.exp (u * j)) := by
  have hp : evalR B h n e ≠ 0 := ne_of_gt (evalR_pos_aux hB h n he)
  have hevalp : (contactPoly B h n e).eval 1 ≠ 0 := by
    rw [eval_contactPoly_one]
    exact hp
  calc
    evalR B (h + u) n e = (contactPoly B h n e).eval (Real.exp u) :=
      (eval_contactPoly_exp B h n e u).symm
    _ = ∑ k ∈ Finset.range (2 ^ n + 1),
        (contactPoly B h n e).coeff k * Real.exp u ^ k :=
      eval_eq_sum_range' (Nat.lt_succ_of_le (contactPoly_natDegree_le B h n e)) _
    _ = ∑ k ∈ Finset.range (2 ^ n + 1),
        (contactPoly B h n e).coeff k * Real.exp (u * k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [show u * (k : ℝ) = (k : ℝ) * u by ring, Real.exp_nat_mul]
    _ = evalR B h n e * gibbsMean B h n e (fun j => Real.exp (u * j)) := by
      simp only [gibbsMean, gibbsWeight, Finset.mul_sum]
      rw [← eval_contactPoly_one B h n e]
      apply Finset.sum_congr rfl
      intro k hk
      field_simp [hevalp]

/-- Almost surely, shifting the field multiplies the partition function by the
Gibbs exponential contact mean.  This proves the frozen
`evalR_add_eq_gibbsMean`. -/
theorem evalR_add_eq_gibbsMean_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    ∀ᵐ e ∂(envMeasure μ n), ∀ u : ℝ,
      evalR B (h + u) n e = evalR B h n e * gibbsMean B h n e (fun j => Real.exp (u * j)) := by
  filter_upwards [ae_envPos_aux hpos n] with e he
  exact contact_evalR_add_eq_gibbsMean (by linarith) h n e he

/-- The polynomial derivative at one is the unnormalized first contact
moment, truncated at the number of leaves. -/
theorem contactPoly_derivative_eval_one (B h : ℝ) (n : ℕ) (e : Env n) :
    (contactPoly B h n e).derivative.eval 1 =
      ∑ k ∈ Finset.range (2 ^ n + 1), (contactPoly B h n e).coeff k * (k : ℝ) := by
  rw [derivative_eval]
  rw [(contactPoly B h n e).sum_over_range' (fun k => by simp) (2 ^ n + 1)
    (Nat.lt_succ_of_le (contactPoly_natDegree_le B h n e))]
  apply Finset.sum_congr rfl
  intro k hk
  simp

/-- The derivative of the logarithmic partition function is the Gibbs first
moment on a positive environment. -/
theorem contact_hasDerivAt_log_evalR {B : ℝ} (hB : 1 < B) (h : ℝ) (n : ℕ)
    (e : Env n) (he : Env.Pos n e) :
    HasDerivAt (fun h' => Real.log (evalR B h' n e))
      (gibbsMean B h n e (fun j => (j : ℝ))) h := by
  have hp : evalR B h n e ≠ 0 := ne_of_gt (evalR_pos_aux hB h n he)
  have hexp : HasDerivAt (fun h' : ℝ => Real.exp (h' - h)) 1 h := by
    simpa using ((hasDerivAt_id h).sub_const h).exp
  have hpder : HasDerivAt (fun h' => (contactPoly B h n e).eval (Real.exp (h' - h)))
      (∑ k ∈ Finset.range (2 ^ n + 1), (contactPoly B h n e).coeff k * (k : ℝ)) h := by
    rw [show (fun h' => (contactPoly B h n e).eval (Real.exp (h' - h))) =
      (fun h' => ∑ k ∈ Finset.range (2 ^ n + 1),
        (contactPoly B h n e).coeff k * Real.exp (h' - h) ^ k) by
      funext h'
      exact eval_eq_sum_range' (Nat.lt_succ_of_le (contactPoly_natDegree_le B h n e)) _]
    have hsum := HasDerivAt.fun_sum (u := Finset.range (2 ^ n + 1))
      (fun k hk => (((hasDerivAt_pow k (Real.exp (h - h))).comp h hexp).const_mul
        ((contactPoly B h n e).coeff k)))
    simpa using hsum
  have hfun : (fun h' => evalR B h' n e) =
      (fun h' => (contactPoly B h n e).eval (Real.exp (h' - h))) := by
    funext h'
    calc
      evalR B h' n e = evalR B (h + (h' - h)) n e := by congr 2; ring
      _ = (contactPoly B h n e).eval (Real.exp (h' - h)) :=
        (eval_contactPoly_exp B h n e (h' - h)).symm
  have hevalR : HasDerivAt (fun h' => evalR B h' n e)
      (∑ k ∈ Finset.range (2 ^ n + 1), (contactPoly B h n e).coeff k * (k : ℝ)) h := by
    rw [hfun]
    exact hpder
  have hmean : (∑ k ∈ Finset.range (2 ^ n + 1),
        (contactPoly B h n e).coeff k * (k : ℝ)) / evalR B h n e =
      gibbsMean B h n e (fun j => (j : ℝ)) := by
    simp only [gibbsMean, gibbsWeight, eval_contactPoly_one]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [← hmean]
  exact hevalR.log hp

/-- Almost surely, the derivative of the logarithmic partition function is the
Gibbs first contact moment.  This proves the frozen `hasDerivAt_log_evalR`. -/
theorem hasDerivAt_log_evalR_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    ∀ᵐ e ∂(envMeasure μ n),
      HasDerivAt (fun h' => Real.log (evalR B h' n e))
        (gibbsMean B h n e (fun j => (j : ℝ))) h := by
  filter_upwards [ae_envPos_aux hpos n] with e he
  exact contact_hasDerivAt_log_evalR (by linarith) h n e he

/-- Almost surely, the Gibbs contact weights form a probability law on
`{0, …, 2^n}`.  This proves the frozen `gibbsWeight_isProb`. -/
theorem gibbsWeight_isProb_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    ∀ᵐ e ∂(envMeasure μ n),
      (∀ k, 0 ≤ gibbsWeight B h n e k) ∧ (∀ k, 2 ^ n < k → gibbsWeight B h n e k = 0) ∧
        ∑ k ∈ Finset.range (2 ^ n + 1), gibbsWeight B h n e k = 1 := by
  filter_upwards [ae_envPos_aux hpos n] with e he
  exact contact_gibbsWeight_isProb (by linarith) h n e he

end DiamondPinning
