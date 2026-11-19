module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Proofs.ContactsProof
public import DiamondPinning.Proofs.FieldDerivProof
public import DiamondPinning.Proofs.CriticalMoments
public import DiamondPinning.Statements.Env
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Asymptotics.Theta

/-!
# `prop:contact-moments` (`response.tex` lines 221–265)

The contact recursion `contactMoment_succ`, the factorial induction
`contact_factorial_induction` (constants chosen before `k` and `n`), the
exponential moment by summation of the exponential series, and the field
increment `A_n(h + u) - A_n(h) ≤ E[R_n^θ ⟨e^{u C_n} - 1⟩_n]` (from
`R_n(h + u) = R_n(h) ⟨e^{u C_n}⟩_n` and `x^θ ≤ x` for `x ≥ 1`). The final
theorem `contactMoments_of` takes the conclusions of `th:product`
(`criticalProduct`) and `response:linear` (`response_linear`) as hypotheses.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Asymptotics
open scoped BigOperators

/-- Reindex a finite sum over all antidiagonals as a rectangular sum. -/
private theorem sum_range_antidiagonal {N m : ℕ}
    (hN : ∀ i < m, ∀ j < m, i + j < N) (f : ℕ → ℕ → ℕ → ℝ)
    (hf : ∀ k i j, m ≤ i ∨ m ≤ j → f k i j = 0) :
    ∑ k ∈ Finset.range N, ∑ ij ∈ Finset.antidiagonal k, f k ij.1 ij.2 =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, f (i + j) i j := by
  classical
  let t := (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 < N)
  have hsigma :
      (∑ k ∈ Finset.range N, ∑ ij ∈ Finset.antidiagonal k, f k ij.1 ij.2) =
        ∑ p ∈ t, f (p.1 + p.2) p.1 p.2 := by
    rw [Finset.sum_sigma' (Finset.range N) (fun k => Finset.antidiagonal k)
      (fun k ij => f k ij.1 ij.2)]
    apply Finset.sum_bij (fun x _ => x.snd)
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      have hxa := Finset.mem_antidiagonal.mp hx.2
      simp only [t, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      have hi : x.snd.1 < N := by omega
      have hj : x.snd.2 < N := by omega
      exact ⟨⟨hi, hj⟩, by omega⟩
    · intro x hx y hy hxy
      simp only [Finset.mem_sigma, Finset.mem_range] at hx hy
      have hxa := Finset.mem_antidiagonal.mp hx.2
      have hya := Finset.mem_antidiagonal.mp hy.2
      cases x with | mk k ij =>
      cases y with | mk l kl =>
      dsimp at hxy
      cases hxy
      dsimp at hxa hya
      have hkl : k = l := by omega
      subst l
      exact Sigma.ext hkl HEq.rfl
    · intro p hp
      simp only [t, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      refine ⟨⟨p.1 + p.2, p⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal]
      exact ⟨hp.2, by simp⟩
    · intro x hx
      have hxa := Finset.mem_antidiagonal.mp (Finset.mem_sigma.mp hx).2
      exact congrArg (fun d => f d x.snd.1 x.snd.2) hxa.symm
  rw [hsigma]
  symm
  change (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      (fun p : ℕ × ℕ => f (p.1 + p.2) p.1 p.2) (i, j)) = _
  rw [← Finset.sum_product (Finset.range m) (Finset.range m)
    (fun p : ℕ × ℕ => f (p.1 + p.2) p.1 p.2)]
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    simp only [t, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    have hs := hN p.1 hp.1 p.2 hp.2
    refine ⟨⟨?_, ?_⟩, hs⟩ <;> omega
  · intro p hp hpm
    simp only [Finset.mem_product, Finset.mem_range] at hpm
    push_neg at hpm
    exact hf (p.1 + p.2) p.1 p.2 (by omega)

/-- The root recursion, summed against a positive power of the contact count. -/
private theorem gibbsMean_pow_succ_rect {B : ℝ} (hB : 2 < B) (h : ℝ)
    {n : ℕ} {e : Env (n + 1)} (he : Env.Pos (n + 1) e) {k : ℕ} (hk : 1 ≤ k) :
    gibbsMean B h (n + 1) e (fun j => (j : ℝ) ^ k) =
      (evalR B h n e.1 * evalR B h n e.2 /
        (evalR B h n e.1 * evalR B h n e.2 + (B - 1))) *
      ∑ i ∈ Finset.range (2 ^ n + 1), ∑ j ∈ Finset.range (2 ^ n + 1),
        gibbsWeight B h n e.1 i * gibbsWeight B h n e.2 j * ((i + j : ℕ) : ℝ) ^ k := by
  classical
  let p := evalR B h n e.1 * evalR B h n e.2 /
    (evalR B h n e.1 * evalR B h n e.2 + (B - 1))
  have hN : ∀ i < 2 ^ n + 1, ∀ j < 2 ^ n + 1, i + j < 2 ^ (n + 1) + 1 := by
    intro i hi j hj
    rw [pow_succ]
    omega
  have hzero (x : Env n) (hx : Env.Pos n x) (a b : ℕ)
      (hab : 2 ^ n + 1 ≤ a ∨ 2 ^ n + 1 ≤ b) :
      gibbsWeight B h n x a * gibbsWeight B h n x b = 0 := by
    rcases hab with ha | hb
    · rw [(contact_gibbsWeight_isProb (by linarith) h n x hx).2.1 a (by omega), zero_mul]
    · rw [(contact_gibbsWeight_isProb (by linarith) h n x hx).2.1 b (by omega), mul_zero]
  calc
    gibbsMean B h (n + 1) e (fun j => (j : ℝ) ^ k) =
        ∑ a ∈ Finset.range (2 ^ (n + 1) + 1), p *
          ∑ ij ∈ Finset.antidiagonal a,
            gibbsWeight B h n e.1 ij.1 * gibbsWeight B h n e.2 ij.2 * (a : ℝ) ^ k := by
      unfold gibbsMean
      apply Finset.sum_congr rfl
      intro a ha
      rw [gibbsWeight_succ_aux hB h he]
      by_cases ha0 : a = 0
      · subst a
        simp [p, zero_pow (by omega : k ≠ 0)]
      · simp only [ha0, ↓reduceIte, add_zero]
        change (p * ∑ ij ∈ Finset.antidiagonal a,
          gibbsWeight B h n e.1 ij.1 * gibbsWeight B h n e.2 ij.2) * (a : ℝ) ^ k = _
        rw [mul_assoc, Finset.sum_mul]
    _ = p * ∑ a ∈ Finset.range (2 ^ (n + 1) + 1),
          ∑ ij ∈ Finset.antidiagonal a,
            gibbsWeight B h n e.1 ij.1 * gibbsWeight B h n e.2 ij.2 * (a : ℝ) ^ k := by
      rw [Finset.mul_sum]
    _ = p * ∑ i ∈ Finset.range (2 ^ n + 1), ∑ j ∈ Finset.range (2 ^ n + 1),
          gibbsWeight B h n e.1 i * gibbsWeight B h n e.2 j * ((i + j : ℕ) : ℝ) ^ k := by
      congr 1
      apply sum_range_antidiagonal hN (fun a i j =>
        gibbsWeight B h n e.1 i * gibbsWeight B h n e.2 j * (a : ℝ) ^ k)
      intro a i j hij
      by_cases hi : 2 ^ n + 1 ≤ i
      · rw [(contact_gibbsWeight_isProb (by linarith) h n e.1 he.1).2.1 i (by omega)]
        simp
      · have hj : 2 ^ n + 1 ≤ j := by omega
        rw [(contact_gibbsWeight_isProb (by linarith) h n e.2 he.2).2.1 j (by omega)]
        simp
    _ = _ := rfl

/-- A finite rectangular sum of a binomial power is a binomial convolution. -/
private theorem rectangle_add_pow (a b : ℕ → ℝ) (m k : ℕ) :
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, a i * b j * ((i + j : ℕ) : ℝ) ^ k =
      ∑ l ∈ Finset.antidiagonal k, (k.choose l.1 : ℝ) *
        (∑ i ∈ Finset.range m, a i * (i : ℝ) ^ l.1) *
          (∑ j ∈ Finset.range m, b j * (j : ℝ) ^ l.2) := by
  classical
  calc
    _ = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, ∑ l ∈ Finset.antidiagonal k,
        (k.choose l.1 : ℝ) * (a i * (i : ℝ) ^ l.1) * (b j * (j : ℝ) ^ l.2) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.cast_add, add_pow]
      rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun l r => (i : ℝ) ^ l * (j : ℝ) ^ r * (k.choose l : ℝ))]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = ∑ l ∈ Finset.antidiagonal k, ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
        (k.choose l.1 : ℝ) * (a i * (i : ℝ) ^ l.1) * (b j * (j : ℝ) ^ l.2) := by
      conv_lhs => enter [2, i]; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      calc
        (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
            (k.choose l.1 : ℝ) * (a i * (i : ℝ) ^ l.1) * (b j * (j : ℝ) ^ l.2)) =
            ∑ i ∈ Finset.range m,
              ((k.choose l.1 : ℝ) * (a i * (i : ℝ) ^ l.1)) *
                ∑ j ∈ Finset.range m, b j * (j : ℝ) ^ l.2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
        _ = (∑ i ∈ Finset.range m, (k.choose l.1 : ℝ) * (a i * (i : ℝ) ^ l.1)) *
              ∑ j ∈ Finset.range m, b j * (j : ℝ) ^ l.2 := by
          rw [Finset.sum_mul]
        _ = _ := by
          congr 1
          rw [Finset.mul_sum]

/-- The Gibbs moments at a node are the binomial convolution of the subtree moments. -/
private theorem gibbsMean_pow_succ {B : ℝ} (hB : 2 < B) (h : ℝ)
    {n : ℕ} {e : Env (n + 1)} (he : Env.Pos (n + 1) e) {k : ℕ} (hk : 1 ≤ k) :
    gibbsMean B h (n + 1) e (fun j => (j : ℝ) ^ k) =
      (evalR B h n e.1 * evalR B h n e.2 /
        (evalR B h n e.1 * evalR B h n e.2 + (B - 1))) *
      ∑ l ∈ Finset.antidiagonal k, (k.choose l.1 : ℝ) *
        gibbsMean B h n e.1 (fun j => (j : ℝ) ^ l.1) *
          gibbsMean B h n e.2 (fun j => (j : ℝ) ^ l.2) := by
  rw [gibbsMean_pow_succ_rect hB h he hk, rectangle_add_pow]
  rfl

/-- The root-weight estimate in the contact recursion. -/
private theorem root_weight_rpow_le {S c θ : ℝ} (hS : 0 < S) (hc : 0 ≤ c) (hθ : θ < 1) :
    (S + c) ^ θ * (S / (S + c)) ≤ S ^ θ := by
  have hSc : 0 < S + c := by linarith
  have hmono : (S + c) ^ (θ - 1) ≤ S ^ (θ - 1) :=
    Real.rpow_le_rpow_of_nonpos hS (by linarith) (by linarith)
  calc
    (S + c) ^ θ * (S / (S + c)) = S * (S + c) ^ (θ - 1) := by
      rw [show θ = (θ - 1) + 1 by ring, Real.rpow_add hSc, Real.rpow_one]
      field_simp
      ring
    _ ≤ S * S ^ (θ - 1) := mul_le_mul_of_nonneg_left hmono hS.le
    _ = S ^ θ := by
      calc
        S * S ^ (θ - 1) = S ^ (1 : ℝ) * S ^ (θ - 1) := by rw [Real.rpow_one]
        _ = S ^ ((1 : ℝ) + (θ - 1)) := (Real.rpow_add hS _ _).symm
        _ = S ^ θ := by ring_nf

private theorem gibbsMean_nonneg {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ}
    {e : Env n} (he : Env.Pos n e) (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    0 ≤ gibbsMean B h n e f := by
  unfold gibbsMean
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg ((contact_gibbsWeight_isProb (by linarith) h n e he).1 j) (hf j)

/-- The pointwise weighted moment recursion before integration. -/
private theorem weighted_gibbsMean_pow_succ_le {B : ℝ} (hB : 2 < B) (h : ℝ)
    {n : ℕ} {e : Env (n + 1)} (he : Env.Pos (n + 1) e) {k : ℕ} (hk : 1 ≤ k) :
    evalR B h (n + 1) e ^ theta B * gibbsMean B h (n + 1) e (fun j => (j : ℝ) ^ k) ≤
      (evalR B h n e.1 * evalR B h n e.2) ^ theta B / B ^ theta B *
        ∑ l ∈ Finset.antidiagonal k, (k.choose l.1 : ℝ) *
          gibbsMean B h n e.1 (fun j => (j : ℝ) ^ l.1) *
            gibbsMean B h n e.2 (fun j => (j : ℝ) ^ l.2) := by
  let x := evalR B h n e.1
  let y := evalR B h n e.2
  let T := ∑ l ∈ Finset.antidiagonal k, (k.choose l.1 : ℝ) *
    gibbsMean B h n e.1 (fun j => (j : ℝ) ^ l.1) *
      gibbsMean B h n e.2 (fun j => (j : ℝ) ^ l.2)
  have hx : 0 < x := evalR_pos_aux (by linarith) h n he.1
  have hy : 0 < y := evalR_pos_aux (by linarith) h n he.2
  have hT : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro l hl
    have hg1 := gibbsMean_nonneg hB h he.1 (fun j => (j : ℝ) ^ l.1)
      (fun j => pow_nonneg (Nat.cast_nonneg j) _)
    have hg2 := gibbsMean_nonneg hB h he.2 (fun j => (j : ℝ) ^ l.2)
      (fun j => pow_nonneg (Nat.cast_nonneg j) _)
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hg1) hg2
  have hr := root_weight_rpow_le (S := x * y) (c := B - 1) (θ := theta B)
    (mul_pos hx hy) (by linarith) (theta_lt_one hB)
  have hBθ : 0 < B ^ theta B := Real.rpow_pos_of_pos (by linarith) _
  rw [gibbsMean_pow_succ hB h he hk]
  change ((x * y + (B - 1)) / B) ^ theta B * ((x * y / (x * y + (B - 1))) * T) ≤
    (x * y) ^ theta B / B ^ theta B * T
  calc
    _ = (((x * y + (B - 1)) ^ theta B * (x * y / (x * y + (B - 1)))) /
        B ^ theta B) * T := by
      rw [Real.div_rpow (add_nonneg (mul_nonneg hx.le hy.le) (by linarith)) (by linarith : 0 ≤ B)]
      ring
    _ ≤ ((x * y) ^ theta B / B ^ theta B) * T := by
      exact mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hBθ).2 hr) hT

private theorem B_rpow_theta_contact {B : ℝ} (hB : 2 < B) : B ^ theta B = 2 := by
  have hb : 0 < B := by linarith
  have hl := Real.log_pos (show 1 < B by linarith)
  rw [Real.rpow_def_of_pos hb, theta, ← mul_div_assoc, mul_div_cancel_left₀ _ hl.ne',
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Integration of the root recursion over the two independent subtrees. -/
private theorem contactMoment_succ {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    contactMoment μ B h k (n + 1) ≤ (2 : ℝ)⁻¹ *
      ∑ l ∈ Finset.antidiagonal k, (k.choose l.1 : ℝ) *
        contactMoment μ B h l.1 n * contactMoment μ B h l.2 n := by
  let ν := envMeasure μ n
  let F : ℕ × ℕ → Env n × Env n → ℝ := fun l e =>
    (evalR B h n e.1 ^ theta B * gibbsMean B h n e.1 (fun j => (j : ℝ) ^ l.1)) *
      (evalR B h n e.2 ^ theta B * gibbsMean B h n e.2 (fun j => (j : ℝ) ^ l.2))
  have hFi (l : ℕ × ℕ) : Integrable (F l) (ν.prod ν) :=
    (integrable_contactMoment_aux hpos hmean hB h l.1 n).mul_prod
      (integrable_contactMoment_aux hpos hmean hB h l.2 n)
  have hsum : Integrable (fun e => ∑ l ∈ Finset.antidiagonal k, (k.choose l.1 : ℝ) * F l e)
      (ν.prod ν) := by
    apply integrable_finset_sum
    intro l hl
    exact (hFi l).const_mul _
  have hpoint : ∀ᵐ e : Env (n + 1) ∂(envMeasure μ (n + 1)),
      evalR B h (n + 1) e ^ theta B * gibbsMean B h (n + 1) e (fun j => (j : ℝ) ^ k) ≤
        (B ^ theta B)⁻¹ * ∑ l ∈ Finset.antidiagonal k, (k.choose l.1 : ℝ) * F l e := by
    filter_upwards [ae_envPos_aux hpos (n + 1)] with e he
    calc
      _ ≤ (evalR B h n e.1 * evalR B h n e.2) ^ theta B / B ^ theta B *
          ∑ l ∈ Finset.antidiagonal k, (k.choose l.1 : ℝ) *
            gibbsMean B h n e.1 (fun j => (j : ℝ) ^ l.1) *
              gibbsMean B h n e.2 (fun j => (j : ℝ) ^ l.2) :=
        weighted_gibbsMean_pow_succ_le hB h he hk
      _ = (B ^ theta B)⁻¹ *
          ((evalR B h n e.1 ^ theta B * evalR B h n e.2 ^ theta B) *
            ∑ l ∈ Finset.antidiagonal k, (k.choose l.1 : ℝ) *
              gibbsMean B h n e.1 (fun j => (j : ℝ) ^ l.1) *
                gibbsMean B h n e.2 (fun j => (j : ℝ) ^ l.2)) := by
        rw [Real.mul_rpow (evalR_pos_aux (by linarith) h n he.1).le
          (evalR_pos_aux (by linarith) h n he.2).le]
        ring
      _ = _ := by
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro l hl
        dsimp [F]
        ring
  have hInt := integral_mono_ae
    (integrable_contactMoment_aux hpos hmean hB h k (n + 1))
    (hsum.const_mul (B ^ theta B)⁻¹) hpoint
  change contactMoment μ B h k (n + 1) ≤ _ at hInt
  calc
    contactMoment μ B h k (n + 1) ≤
        ∫ e, (B ^ theta B)⁻¹ * ∑ l ∈ Finset.antidiagonal k, (k.choose l.1 : ℝ) * F l e
          ∂(envMeasure μ (n + 1)) := hInt
    _ = (B ^ theta B)⁻¹ * ∑ l ∈ Finset.antidiagonal k, (k.choose l.1 : ℝ) *
        contactMoment μ B h l.1 n * contactMoment μ B h l.2 n := by
      change (∫ e, (B ^ theta B)⁻¹ * ∑ l ∈ Finset.antidiagonal k,
        (k.choose l.1 : ℝ) * F l e ∂(ν.prod ν)) = _
      rw [integral_const_mul]
      congr 1
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro l hl
        rw [integral_const_mul]
        change (k.choose l.1 : ℝ) * (∫ e, F l e ∂(ν.prod ν)) = _
        have hp : (∫ e, F l e ∂(ν.prod ν)) =
            contactMoment μ B h l.1 n * contactMoment μ B h l.2 n := by
          dsimp [F]
          exact integral_prod_mul
            (fun x : Env n => evalR B h n x ^ theta B *
              gibbsMean B h n x (fun j => (j : ℝ) ^ l.1))
            (fun y : Env n => evalR B h n y ^ theta B *
              gibbsMean B h n y (fun j => (j : ℝ) ^ l.2))
        rw [hp]
        ring
      · intro l hl
        exact (hFi l).const_mul _
    _ = _ := by rw [B_rpow_theta_contact hB]

private theorem tiltedMass_eq_env {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) :
    tiltedMass μ B h n = ∫ e, evalR B h n e ^ theta B ∂(envMeasure μ n) := by
  have hi : Integrable (fun x : ℝ => x ^ theta B) (lawR μ B h n) := by
    simpa only [Real.rpow_zero, mul_one] using
      integrable_absTiltedLogRpow_aux hpos hmean hB h n (s := 0) (le_refl 0)
  unfold tiltedMass
  rw [← map_evalR_envMeasure μ B h n] at hi ⊢
  exact integral_map (measurable_evalR B h n).aemeasurable hi.aestronglyMeasurable

private theorem contactMoment_zero_order {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : contactMoment μ B h 0 n = tiltedMass μ B h n := by
  rw [tiltedMass_eq_env hpos hmean hB h]
  unfold contactMoment
  apply integral_congr_ae
  filter_upwards [ae_envPos_aux hpos n] with e he
  have hg : gibbsMean B h n e (fun j => (j : ℝ) ^ 0) = 1 := by
    unfold gibbsMean
    simpa only [pow_zero, mul_one] using
      (contact_gibbsWeight_isProb (by linarith) h n e he).2.2
  rw [hg, mul_one]

private theorem contactMoment_height_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (k : ℕ) : contactMoment μ B h k 0 = tiltedMass μ B h 0 := by
  rw [tiltedMass_eq_env hpos hmean hB h]
  unfold contactMoment
  apply integral_congr_ae
  filter_upwards [ae_envPos_aux hpos 0] with e he
  have hg : gibbsMean B h 0 e (fun j => (j : ℝ) ^ k) = 1 := by
    unfold gibbsMean
    rw [show 2 ^ 0 + 1 = 2 by norm_num, Finset.sum_range_succ, Finset.sum_range_one]
    simp [gibbsWeight_zero_aux h he]
  rw [hg, mul_one]

private theorem sum_antidiagonal_endpoints {k : ℕ} (hk : 1 ≤ k) (f : ℕ × ℕ → ℝ) :
    ∑ l ∈ Finset.antidiagonal k, f l = f (0, k) + f (k, 0) +
      ∑ l ∈ (Finset.antidiagonal k).erase (0, k) |>.erase (k, 0), f l := by
  classical
  let s := Finset.antidiagonal k
  have h0 : (0, k) ∈ s := by simp [s, Finset.mem_antidiagonal]
  have hk0 : (k, 0) ∈ s := by simp [s, Finset.mem_antidiagonal]
  have hne : (k, 0) ≠ (0, k) := by
    intro heq
    have := congrArg Prod.fst heq
    simp at this
    omega
  have hk1 : (k, 0) ∈ s.erase (0, k) := Finset.mem_erase.mpr ⟨hne, hk0⟩
  calc
    ∑ l ∈ s, f l = (∑ l ∈ s.erase (0, k), f l) + f (0, k) :=
      (Finset.sum_erase_add s f h0).symm
    _ = ((∑ l ∈ (s.erase (0, k)).erase (k, 0), f l) + f (k, 0)) + f (0, k) := by
      rw [Finset.sum_erase_add (s.erase (0, k)) f hk1]
    _ = _ := by dsimp [s]; ring

/-- The moment recursion with its two endpoint terms separated. -/
private theorem contactMoment_succ_split {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    contactMoment μ B h k (n + 1) ≤
      tiltedMass μ B h n * contactMoment μ B h k n + (2 : ℝ)⁻¹ *
        ∑ l ∈ (Finset.antidiagonal k).erase (0, k) |>.erase (k, 0),
          (k.choose l.1 : ℝ) * contactMoment μ B h l.1 n * contactMoment μ B h l.2 n := by
  have hr := contactMoment_succ hpos hmean hB h n hk
  rw [sum_antidiagonal_endpoints hk] at hr
  rw [contactMoment_zero_order hpos hmean hB h n] at hr
  simp only [Prod.fst, Prod.snd, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul] at hr
  have heq : (2 : ℝ)⁻¹ *
      (tiltedMass μ B h n * contactMoment μ B h k n +
        contactMoment μ B h k n * tiltedMass μ B h n +
        ∑ l ∈ (Finset.antidiagonal k).erase (0, k) |>.erase (k, 0),
          (k.choose l.1 : ℝ) * contactMoment μ B h l.1 n * contactMoment μ B h l.2 n) =
      tiltedMass μ B h n * contactMoment μ B h k n + (2 : ℝ)⁻¹ *
        ∑ l ∈ (Finset.antidiagonal k).erase (0, k) |>.erase (k, 0),
          (k.choose l.1 : ℝ) * contactMoment μ B h l.1 n * contactMoment μ B h l.2 n := by
    ring
  exact hr.trans_eq heq

/-- The first binomial gap bound, in a telescoping-friendly form. -/
private theorem mul_pow_le_add_one_pow_sub (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    (m : ℝ) * x ^ (m - 1) ≤ (x + 1) ^ m - x ^ m := by
  cases m with
  | zero => simp
  | succ m =>
      rw [← geom_sum₂_mul (x + 1) x (m + 1), add_sub_cancel_left, mul_one]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      calc
        ((m : ℝ) + 1) * x ^ m = ∑ i ∈ Finset.range (m + 1), x ^ m := by simp
        _ ≤ ∑ i ∈ Finset.range (m + 1), (x + 1) ^ i * x ^ (m - i) := by
          apply Finset.sum_le_sum
          intro i hi
          have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          calc
            x ^ m = x ^ i * x ^ (m - i) := by
              rw [← pow_add]
              congr 1
              omega
            _ ≤ (x + 1) ^ i * x ^ (m - i) := by
              exact mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ hx (by linarith) i) (pow_nonneg hx _)

/-- Bound the internal binomial convolution using all strictly smaller moments. -/
private theorem internal_convolution_bound (m : ℕ → ℕ → ℝ) (M L : ℝ)
    (hM : 0 ≤ M) (hL1 : 1 ≤ L) (hm_nonneg : ∀ q n, 0 ≤ m q n)
    {k : ℕ} (hk : 2 ≤ k)
    (hbound : ∀ q < k, 1 ≤ q → ∀ n : ℕ,
      m q n ≤ (q.factorial : ℝ) * M * L ^ (q - 1) * ((n : ℝ) + 1) ^ (2 * q - 1))
    (n : ℕ) :
    ∑ l ∈ (Finset.antidiagonal k).erase (0, k) |>.erase (k, 0),
        (k.choose l.1 : ℝ) * m l.1 n * m l.2 n ≤
      ((k - 1 : ℕ) : ℝ) * ((k.factorial : ℝ) * M ^ 2 * L ^ (k - 2) *
        ((n : ℝ) + 1) ^ (2 * k - 2)) := by
  classical
  let s := (Finset.antidiagonal k).erase (0, k) |>.erase (k, 0)
  let C := (k.factorial : ℝ) * M ^ 2 * L ^ (k - 2) * ((n : ℝ) + 1) ^ (2 * k - 2)
  have h0 : (0, k) ∈ Finset.antidiagonal k := by simp [Finset.mem_antidiagonal]
  have hne : (k, 0) ≠ (0, k) := by
    intro heq
    have heq' := congrArg Prod.fst heq
    simp at heq'
    omega
  have hk0 : (k, 0) ∈ Finset.antidiagonal k := by simp [Finset.mem_antidiagonal]
  have hk1 : (k, 0) ∈ (Finset.antidiagonal k).erase (0, k) :=
    Finset.mem_erase.mpr ⟨hne, hk0⟩
  have hcard : s.card = k - 1 := by
    dsimp [s]
    rw [Finset.card_erase_of_mem hk1, Finset.card_erase_of_mem h0]
    simp
  have hpoint : ∀ l ∈ s, (k.choose l.1 : ℝ) * m l.1 n * m l.2 n ≤ C := by
    intro l hl
    have hl0 : l ≠ (0, k) := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    have hlk : l ≠ (k, 0) := (Finset.mem_erase.mp hl).1
    have hlk0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).2
    have hsum : l.1 + l.2 = k := Finset.mem_antidiagonal.mp hlk0
    have hl1 : 1 ≤ l.1 := by
      by_contra hn
      have hz : l.1 = 0 := by omega
      have hz2 : l.2 = k := by omega
      apply hl0
      exact Prod.ext hz hz2
    have hl2 : 1 ≤ l.2 := by
      by_contra hn
      have hz : l.2 = 0 := by omega
      have hz1 : l.1 = k := by omega
      apply hlk
      exact Prod.ext hz1 hz
    have hlt1 : l.1 < k := by omega
    have hlt2 : l.2 < k := by omega
    have h1 := hbound l.1 hlt1 hl1 n
    have h2 := hbound l.2 hlt2 hl2 n
    have hfac : (k.choose l.1 : ℝ) * (l.1.factorial : ℝ) * (l.2.factorial : ℝ) =
        (k.factorial : ℝ) := by
      have hfac_nat : k.choose l.1 * l.1.factorial * l.2.factorial = k.factorial := by
        have hsub : k - l.1 = l.2 := by omega
        simpa [hsub] using Nat.choose_mul_factorial_mul_factorial
          (n := k) (k := l.1) (by omega)
      exact_mod_cast hfac_nat
    have hLpow : L ^ (l.1 - 1) * L ^ (l.2 - 1) = L ^ (k - 2) := by
      rw [← pow_add]
      congr 1
      omega
    have hxpow : ((n : ℝ) + 1) ^ (2 * l.1 - 1) * ((n : ℝ) + 1) ^ (2 * l.2 - 1) =
        ((n : ℝ) + 1) ^ (2 * k - 2) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      (k.choose l.1 : ℝ) * m l.1 n * m l.2 n ≤
          (k.choose l.1 : ℝ) *
            ((l.1.factorial : ℝ) * M * L ^ (l.1 - 1) * ((n : ℝ) + 1) ^ (2 * l.1 - 1)) *
            ((l.2.factorial : ℝ) * M * L ^ (l.2 - 1) * ((n : ℝ) + 1) ^ (2 * l.2 - 1)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
        · exact h2
        · exact hm_nonneg _ _
        · exact mul_nonneg (Nat.cast_nonneg _) (le_trans (hm_nonneg _ _) h1)
      _ = ((k.choose l.1 : ℝ) * (l.1.factorial : ℝ) * (l.2.factorial : ℝ)) *
          (M * M) * (L ^ (l.1 - 1) * L ^ (l.2 - 1)) *
          (((n : ℝ) + 1) ^ (2 * l.1 - 1) * ((n : ℝ) + 1) ^ (2 * l.2 - 1)) := by ring
      _ = C := by rw [hfac, hLpow, hxpow]; dsimp [C]; ring
  calc
    _ ≤ ∑ _l ∈ s, C := Finset.sum_le_sum hpoint
    _ = s.card • C := by rw [Finset.sum_const]
    _ = ((k - 1 : ℕ) : ℝ) * C := by rw [hcard, nsmul_eq_mul]
    _ = _ := rfl

/-- Factorial induction for a product-normalized quadratic recursion. -/
private theorem contact_factorial_induction
    (A P : ℕ → ℝ) (m : ℕ → ℕ → ℝ) (K M L C₁ : ℝ)
    (hK : 1 ≤ K) (hM : 1 ≤ M) (hL : K ^ 3 * M ≤ L) (hC₁ : C₁ ≤ M)
    (hP0 : P 0 = 1) (hPsucc : ∀ n, P (n + 1) = A n * P n)
    (hPpos : ∀ n, 0 < P n) (hApos : ∀ n, 0 < A n)
    (hPlower : ∀ n : ℕ, ((n : ℝ) + 2) ^ 2 / K ≤ P (n + 1))
    (hPupper : ∀ n, 1 ≤ n → P n ≤ K * ((n : ℝ) + 1) ^ 2)
    (hm0 : ∀ k, m k 0 = A 0) (hmA0 : A 0 ≤ M)
    (hm_nonneg : ∀ k n, 0 ≤ m k n)
    (hm1 : ∀ n, m 1 n ≤ C₁ * ((n : ℝ) + 1))
    (hrec : ∀ k, 1 ≤ k → ∀ n, m k (n + 1) ≤ A n * m k n + (2 : ℝ)⁻¹ *
      ∑ l ∈ (Finset.antidiagonal k).erase (0, k) |>.erase (k, 0),
        (k.choose l.1 : ℝ) * m l.1 n * m l.2 n) :
    ∀ k n, 1 ≤ k →
      m k n ≤ K * M * (k.factorial : ℝ) * L ^ (k - 1) * ((n : ℝ) + 1) ^ (2 * k - 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro n hk
      by_cases hk1 : k = 1
      · subst k
        have hKM : C₁ ≤ K * M := by
          apply hC₁.trans
          calc
            M = 1 * M := by ring
            _ ≤ K * M := mul_le_mul_of_nonneg_right hK (by linarith)
        specialize hm1 n
        simpa using hm1.trans (mul_le_mul_of_nonneg_right hKM (by positivity : 0 ≤ (n : ℝ) + 1))
      have hk2 : 2 ≤ k := by omega
      have hMpos : 0 < M := by linarith
      have hK0 : 0 < K := by linarith
      have hL1 : 1 ≤ L := by
        have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK
        have hKM1 : 1 ≤ K ^ 3 * M := by
          calc
            1 = 1 * 1 := by norm_num
            _ ≤ K ^ 3 * M := mul_le_mul hK3 hM (by norm_num) (by positivity)
        linarith
      have hL0 : 0 < L := by linarith
      have hfac0 : 0 ≤ (k.factorial : ℝ) := by positivity
      have hnorm : ∀ n : ℕ, m k n ≤
          (k.factorial : ℝ) * P n * (M * L ^ (k - 1)) * ((n : ℝ) + 1) ^ (2 * k - 3) := by
        intro j
        induction j with
        | zero =>
            have hLpow : 1 ≤ L ^ (k - 1) := one_le_pow₀ hL1
            have hfac1 : 1 ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
            rw [hm0, hP0]
            norm_num
            have hMD : M ≤ M * L ^ (k - 1) := by
              nth_rewrite 1 [← mul_one M]
              exact mul_le_mul_of_nonneg_left hLpow hMpos.le
            exact (hmA0.trans hMD).trans (by
              have := mul_le_mul_of_nonneg_right hMD hfac0
              nlinarith)
        | succ j hj =>
            let x := (j : ℝ) + 1
            let y := (j : ℝ) + 2
            let p := 2 * k - 3
            have hx1 : 1 ≤ x := by dsimp [x]; norm_num
            have hx0 : 0 ≤ x := by linarith
            have hxy : x ≤ y := by dsimp [x, y]; linarith
            have hy0 : 0 ≤ y := by linarith
            have hgap : ((k - 1 : ℕ) : ℝ) * x ^ (2 * k - 4) ≤ y ^ p - x ^ p := by
              have hkp : ((k - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
                exact_mod_cast (show k - 1 ≤ p by dsimp [p]; omega)
              calc
                ((k - 1 : ℕ) : ℝ) * x ^ (2 * k - 4) ≤ (p : ℝ) * x ^ (p - 1) := by
                  convert mul_le_mul_of_nonneg_right hkp (pow_nonneg hx0 _) using 1 <;>
                    congr 2 <;> dsimp [p] <;> omega
                _ ≤ y ^ p - x ^ p := by
                    convert mul_pow_le_add_one_pow_sub x hx0 p using 1 <;> dsimp [x, y] <;> ring
            have hyx : x ^ (2 * k - 2) ≤ y ^ 2 * x ^ (2 * k - 4) := by
              calc
                x ^ (2 * k - 2) = x ^ 2 * x ^ (2 * k - 4) := by
                  rw [← pow_add]
                  congr 1
                  omega
                _ ≤ y ^ 2 * x ^ (2 * k - 4) := by
                  exact mul_le_mul_of_nonneg_right
                    (pow_le_pow_left₀ hx0 hxy 2) (pow_nonneg hx0 _)
            have hLdecomp : L ^ (k - 1) = L * L ^ (k - 2) := by
              rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
              ring
            have hML : (K * M) ^ 2 * L ^ (k - 2) ≤ M * L ^ (k - 1) / K := by
              apply (le_div_iff₀ hK0).2
              calc
                ((K * M) ^ 2 * L ^ (k - 2)) * K =
                    (K ^ 3 * M) * (M * L ^ (k - 2)) := by ring
                _ ≤ L * (M * L ^ (k - 2)) := by
                  exact mul_le_mul_of_nonneg_right hL (by positivity)
                _ = M * L ^ (k - 1) := by rw [hLdecomp]; ring
            have hcross : (2 : ℝ)⁻¹ *
                ∑ l ∈ (Finset.antidiagonal k).erase (0, k) |>.erase (k, 0),
                  (k.choose l.1 : ℝ) * m l.1 j * m l.2 j ≤
                (k.factorial : ℝ) * P (j + 1) * (M * L ^ (k - 1)) * (y ^ p - x ^ p) := by
              have hS := internal_convolution_bound m (K * M) L (by positivity) hL1 hm_nonneg hk2
                (fun q hq hq1 n => by
                  have hh := ih q hq n hq1
                  convert hh using 1 <;> ring) j
              have hPlo := hPlower j
              change ((j : ℝ) + 2) ^ 2 / K ≤ P (j + 1) at hPlo
              have hconst : (K * M) ^ 2 * L ^ (k - 2) * x ^ (2 * k - 2) ≤
                  (M * L ^ (k - 1)) * (y ^ 2 / K) * x ^ (2 * k - 4) := by
                calc
                  (K * M) ^ 2 * L ^ (k - 2) * x ^ (2 * k - 2) ≤
                      (K * M) ^ 2 * L ^ (k - 2) * (y ^ 2 * x ^ (2 * k - 4)) := by
                    exact mul_le_mul_of_nonneg_left hyx (by positivity)
                  _ ≤ (M * L ^ (k - 1) / K) * y ^ 2 * x ^ (2 * k - 4) := by
                    convert mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_right hML (pow_nonneg hy0 2))
                      (pow_nonneg hx0 (2 * k - 4)) using 1 <;> ring
                  _ = (M * L ^ (k - 1)) * (y ^ 2 / K) * x ^ (2 * k - 4) := by ring
              have hkey : (k.factorial : ℝ) * (((k - 1 : ℕ) : ℝ) *
                  ((K * M) ^ 2 * L ^ (k - 2) * x ^ (2 * k - 2))) ≤
                  (k.factorial : ℝ) * P (j + 1) * (M * L ^ (k - 1)) * (y ^ p - x ^ p) := by
                calc
                  _ ≤ (k.factorial : ℝ) * (((k - 1 : ℕ) : ℝ) *
                      ((M * L ^ (k - 1)) * (y ^ 2 / K) * x ^ (2 * k - 4))) := by
                    exact mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_left hconst (by positivity)) hfac0
                  _ = (k.factorial : ℝ) * (y ^ 2 / K) * (M * L ^ (k - 1)) *
                      (((k - 1 : ℕ) : ℝ) * x ^ (2 * k - 4)) := by ring
                  _ ≤ (k.factorial : ℝ) * P (j + 1) * (M * L ^ (k - 1)) * (y ^ p - x ^ p) := by
                    have hP' : 0 ≤ P (j + 1) := (hPpos _).le
                    have hML0 : 0 ≤ M * L ^ (k - 1) := by positivity
                    have hgap0 : 0 ≤ y ^ p - x ^ p := by
                      exact sub_nonneg.mpr (pow_le_pow_left₀ hx0 hxy _)
                    have hyK0 : 0 ≤ y ^ 2 / K := by positivity
                    have hp1 : (k.factorial : ℝ) * (y ^ 2 / K) * (M * L ^ (k - 1)) ≤
                        (k.factorial : ℝ) * P (j + 1) * (M * L ^ (k - 1)) :=
                      mul_le_mul_of_nonneg_right
                        (mul_le_mul_of_nonneg_left hPlo hfac0) hML0
                    exact mul_le_mul hp1 hgap (by positivity) (by positivity)
              calc
                _ ≤ (2 : ℝ)⁻¹ * (((k - 1 : ℕ) : ℝ) *
                    ((k.factorial : ℝ) * (K * M) ^ 2 * L ^ (k - 2) * x ^ (2 * k - 2))) := by
                  exact mul_le_mul_of_nonneg_left hS (by norm_num)
                _ = (2 : ℝ)⁻¹ * ((k.factorial : ℝ) * (((k - 1 : ℕ) : ℝ) *
                    ((K * M) ^ 2 * L ^ (k - 2) * x ^ (2 * k - 2)))) := by ring
                _ ≤ (2 : ℝ)⁻¹ * ((k.factorial : ℝ) * P (j + 1) *
                    (M * L ^ (k - 1)) * (y ^ p - x ^ p)) :=
                  mul_le_mul_of_nonneg_left hkey (by norm_num)
                _ ≤ _ := by
                  have hp : 0 ≤ (k.factorial : ℝ) * P (j + 1) *
                    (M * L ^ (k - 1)) * (y ^ p - x ^ p) :=
                    mul_nonneg (mul_nonneg (mul_nonneg hfac0 (hPpos _).le) (by positivity))
                      (sub_nonneg.mpr (pow_le_pow_left₀ hx0 hxy _))
                  linarith
            have hfirst : A j * m k j ≤
                (k.factorial : ℝ) * P (j + 1) * (M * L ^ (k - 1)) * x ^ p := by
              calc
                A j * m k j ≤ A j *
                    ((k.factorial : ℝ) * P j * (M * L ^ (k - 1)) * x ^ p) := by
                  exact mul_le_mul_of_nonneg_left hj (hApos _).le
                _ = _ := by rw [hPsucc]; ring
            calc
              m k (j + 1) ≤ A j * m k j + (2 : ℝ)⁻¹ *
                  ∑ l ∈ (Finset.antidiagonal k).erase (0, k) |>.erase (k, 0),
                    (k.choose l.1 : ℝ) * m l.1 j * m l.2 j := hrec k (by omega) j
              _ ≤ (k.factorial : ℝ) * P (j + 1) * (M * L ^ (k - 1)) * x ^ p +
                  (k.factorial : ℝ) * P (j + 1) * (M * L ^ (k - 1)) * (y ^ p - x ^ p) :=
                add_le_add hfirst hcross
              _ = _ := by dsimp [x, y, p]; simp only [Nat.cast_add, Nat.cast_one]; ring
      by_cases hn0 : n = 0
      · subst n
        have hout := hnorm 0
        rw [hP0] at hout
        norm_num at hout
        have hfac1 : 1 ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
        have hg : (k.factorial : ℝ) * (M * L ^ (k - 1)) ≤
            K * ((k.factorial : ℝ) * (M * L ^ (k - 1))) := by
          have hnonneg : 0 ≤ (k.factorial : ℝ) * (M * L ^ (k - 1)) := by positivity
          nlinarith
        convert hout.trans hg using 1 <;> ring
      · have hn : 1 ≤ n := by omega
        calc
          m k n ≤ (k.factorial : ℝ) * P n * (M * L ^ (k - 1)) *
              ((n : ℝ) + 1) ^ (2 * k - 3) := hnorm n
          _ ≤ (k.factorial : ℝ) * (K * ((n : ℝ) + 1) ^ 2) * (M * L ^ (k - 1)) *
              ((n : ℝ) + 1) ^ (2 * k - 3) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hPupper n hn) hfac0)
                (by positivity)) (by positivity)
          _ = K * M * (k.factorial : ℝ) * L ^ (k - 1) * ((n : ℝ) + 1) ^ (2 * k - 1) := by
            rw [show 2 * k - 1 = (2 * k - 3) + 2 by omega, pow_add]
            ring

private theorem contactMoment_nonneg {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (k n : ℕ) :
    0 ≤ contactMoment μ B h k n := by
  unfold contactMoment
  apply integral_nonneg_of_ae
  filter_upwards [ae_envPos_aux hpos n] with e he
  exact mul_nonneg (Real.rpow_nonneg (evalR_pos_aux (by linarith) h n he).le _)
    (gibbsMean_nonneg hB h he _ (fun j => pow_nonneg (Nat.cast_nonneg j) _))

/-- The factorial contact-moment bounds obtained from the product and linear estimates. -/
private theorem contactMoment_bounds_of_product_linear {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hPi : ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) ^ 2 / D ≤ tiltedProduct μ B (criticalPoint μ B) n ∧
      tiltedProduct μ B (criticalPoint μ B) n ≤ D * ((n : ℝ) + 1) ^ 2)
    (hLin : ∃ C : ℝ, ∀ n : ℕ,
      deriv (fun h => tiltedMass μ B h n) (criticalPoint μ B) ≤ C * ((n : ℝ) + 1)) :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ ∀ k n : ℕ, 1 ≤ k →
      contactMoment μ B (criticalPoint μ B) k n ≤
        (k.factorial : ℝ) * M * L ^ (k - 1) * ((n : ℝ) + 1) ^ (2 * k - 1) := by
  rcases hPi with ⟨D, hD, hDb⟩
  rcases hLin with ⟨C, hC⟩
  let K := max D 1
  let C₁ := max (C / theta B) 0
  let M := max 1 (max (tiltedMass μ B (criticalPoint μ B) 0) C₁)
  let L := K ^ 3 * M
  have hKD : D ≤ K := le_max_left _ _
  have hK : 1 ≤ K := le_max_right _ _
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := by linarith
  have hMA : tiltedMass μ B (criticalPoint μ B) 0 ≤ M :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hMC : C₁ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hC1 : ∀ n, contactMoment μ B (criticalPoint μ B) 1 n ≤ C₁ * ((n : ℝ) + 1) := by
    intro n
    have hd := (hasDerivAt_tiltedMass_aux hpos hmean hB (criticalPoint μ B) n).deriv
    have hc := hC n
    rw [hd] at hc
    have hθ := theta_pos hB
    calc
      contactMoment μ B (criticalPoint μ B) 1 n ≤ (C * ((n : ℝ) + 1)) / theta B := by
        apply (le_div_iff₀ hθ).2
        simpa [mul_comm] using hc
      _ = (C / theta B) * ((n : ℝ) + 1) := by ring
      _ ≤ C₁ * ((n : ℝ) + 1) := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hP0 : tiltedProduct μ B (criticalPoint μ B) 0 = 1 := by simp [tiltedProduct]
  have hPsucc : ∀ n, tiltedProduct μ B (criticalPoint μ B) (n + 1) =
      tiltedMass μ B (criticalPoint μ B) n * tiltedProduct μ B (criticalPoint μ B) n := by
    intro n
    simp [tiltedProduct, Finset.prod_range_succ, mul_comm]
  have hPlower : ∀ n : ℕ, ((n : ℝ) + 2) ^ 2 / K ≤
      tiltedProduct μ B (criticalPoint μ B) (n + 1) := by
    intro n
    have hb := (hDb (n + 1) (by omega)).1
    calc
      ((n : ℝ) + 2) ^ 2 / K ≤ ((n : ℝ) + 2) ^ 2 / D := by
        exact div_le_div_of_nonneg_left (by positivity) hD hKD
      _ ≤ tiltedProduct μ B (criticalPoint μ B) (n + 1) := by
        convert hb using 1 <;> push_cast <;> ring
  have hPupper : ∀ n, 1 ≤ n → tiltedProduct μ B (criticalPoint μ B) n ≤
      K * ((n : ℝ) + 1) ^ 2 := by
    intro n hn
    exact (hDb n hn).2.trans (mul_le_mul_of_nonneg_right hKD (by positivity))
  have hPpos : ∀ n, 0 < tiltedProduct μ B (criticalPoint μ B) n := by
    intro n
    cases n with
    | zero => simp [tiltedProduct]
    | succ n =>
        have hb := (hDb (n + 1) (by omega)).1
        have hp : 0 < (((n + 1 : ℕ) : ℝ) + 1) ^ 2 / D := by positivity
        exact hp.trans_le hb
  have hApos : ∀ n, 0 < tiltedMass μ B (criticalPoint μ B) n := by
    intro n
    apply pos_of_mul_pos_left (b := tiltedProduct μ B (criticalPoint μ B) n)
    · rw [← hPsucc n]
      exact hPpos (n + 1)
    · exact (hPpos n).le
  refine ⟨K * M, L, mul_nonneg hK0.le hM0.le, mul_nonneg (pow_nonneg hK0.le 3) hM0.le, ?_⟩
  have H := contact_factorial_induction
    (fun n => tiltedMass μ B (criticalPoint μ B) n)
    (fun n => tiltedProduct μ B (criticalPoint μ B) n)
    (fun k n => contactMoment μ B (criticalPoint μ B) k n) K M L C₁
    hK hM (by dsimp [L]; rfl) hMC hP0 hPsucc hPpos hApos hPlower hPupper
    (fun k => contactMoment_height_zero hpos hmean hB (criticalPoint μ B) k) hMA
    (fun k n => contactMoment_nonneg hpos hB (criticalPoint μ B) k n) hC1
    (fun k hk n => contactMoment_succ_split hpos hmean hB (criticalPoint μ B) n hk)
  intro k n hk
  simpa [mul_assoc, mul_comm, mul_left_comm] using H k n hk

/-! ### The exponential clause -/

/-- The Gibbs mean of a finite linear combination. -/
private theorem gibbsMean_finset_sum {B h : ℝ} {n : ℕ} (e : Env n) (s : Finset ℕ)
    (c : ℕ → ℝ) (f : ℕ → ℕ → ℝ) :
    gibbsMean B h n e (fun j => ∑ k ∈ s, c k * f k j) =
      ∑ k ∈ s, c k * gibbsMean B h n e (f k) := by
  unfold gibbsMean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Monotonicity of the Gibbs mean. -/
private theorem gibbsMean_mono {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ}
    {e : Env n} (he : Env.Pos n e) {f g : ℕ → ℝ} (hfg : ∀ j, f j ≤ g j) :
    gibbsMean B h n e f ≤ gibbsMean B h n e g := by
  unfold gibbsMean
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hfg j)
    ((contact_gibbsWeight_isProb (by linarith) h n e he).1 j)

/-- The shifted partial sums of the exponential series converge to `e^y - 1`. -/
private theorem tendsto_expSeries_sub_one (y : ℝ) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, y ^ (k + 1) / ((k + 1).factorial : ℝ)) atTop
      (𝓝 (Real.exp y - 1)) := by
  have hs : HasSum (fun k => y ^ k / (k.factorial : ℝ)) (Real.exp y) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp y
  have h1 := (hasSum_nat_add_iff' 1).2 hs
  rw [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h1
  exact h1.tendsto_sum_nat

/-- The shifted partial sums of the exponential series lie in `[0, e^y - 1]` for `y ≥ 0`. -/
private theorem expSeries_sub_one_bounds {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    0 ≤ ∑ k ∈ Finset.range N, y ^ (k + 1) / ((k + 1).factorial : ℝ) ∧
      ∑ k ∈ Finset.range N, y ^ (k + 1) / ((k + 1).factorial : ℝ) ≤ Real.exp y - 1 := by
  refine ⟨Finset.sum_nonneg fun k _ => by positivity, ?_⟩
  have h := Real.sum_le_exp_of_nonneg hy (N + 1)
  rw [Finset.sum_range_succ'] at h
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  linarith

/-- The exponential contact moment from the factorial moment bounds. -/
private theorem contactExpMoment_le_of_moments {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hk : ∀ k n : ℕ, 1 ≤ k → contactMoment μ B h k n ≤
      (k.factorial : ℝ) * M * L ^ (k - 1) * ((n : ℝ) + 1) ^ (2 * k - 1))
    (n : ℕ) {u : ℝ} (hu : 0 ≤ u) (hr : L * u * ((n : ℝ) + 1) ^ 2 < 1) :
    contactExpMoment μ B h u n ≤
      M * u * ((n : ℝ) + 1) / (1 - L * u * ((n : ℝ) + 1) ^ 2) := by
  let ν := envMeasure μ n
  let x : ℝ := (n : ℝ) + 1
  let r : ℝ := L * u * x ^ 2
  have hx0 : 0 ≤ x := by positivity
  have hr0 : 0 ≤ r := by positivity
  have hr1 : 0 < 1 - r := by
    show 0 < 1 - L * u * ((n : ℝ) + 1) ^ 2
    linarith
  let c : ℕ → ℝ := fun k => u ^ (k + 1) / ((k + 1).factorial : ℝ)
  let G : ℕ → Env n → ℝ := fun k e =>
    evalR B h n e ^ theta B * gibbsMean B h n e (fun j => (j : ℝ) ^ (k + 1))
  let F : ℕ → Env n → ℝ := fun N e => ∑ k ∈ Finset.range N, c k * G k e
  let f : Env n → ℝ := fun e =>
    evalR B h n e ^ theta B * gibbsMean B h n e (fun j => Real.exp (u * j) - 1)
  have hGint : ∀ k, Integrable (G k) ν := fun k =>
    integrable_contactMoment_aux hpos hmean hB h (k + 1) n
  have hFint : ∀ N, Integrable (F N) ν := fun N =>
    integrable_finsetSum _ fun k _ => (hGint k).const_mul _
  have hfint : Integrable f ν := integrable_contactExpMoment_aux hpos hmean hB h u n
  -- `F N` is the weighted Gibbs mean of a partial sum of `e^{u j} - 1`
  have hFeq : ∀ N e, F N e = evalR B h n e ^ theta B * gibbsMean B h n e
      (fun j => ∑ k ∈ Finset.range N, (u * (j : ℝ)) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
    intro N e
    have hfun : (fun j : ℕ => ∑ k ∈ Finset.range N,
        (u * (j : ℝ)) ^ (k + 1) / ((k + 1).factorial : ℝ)) =
        fun j => ∑ k ∈ Finset.range N, c k * (fun k (j : ℕ) => (j : ℝ) ^ (k + 1)) k j := by
      funext j
      apply Finset.sum_congr rfl
      intro k _
      simp only [c]
      rw [mul_pow]
      ring
    rw [hfun, gibbsMean_finset_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [G]
    ring
  have hIF : ∀ N, ∫ e, F N e ∂ν =
      ∑ k ∈ Finset.range N, c k * contactMoment μ B h (k + 1) n := by
    intro N
    simp only [F]
    rw [integral_finsetSum _ fun k _ => (hGint k).const_mul _]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul]
    rfl
  have hlim : Tendsto (fun N => ∫ e, F N e ∂ν) atTop (𝓝 (∫ e, f e ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence f
      (fun N => (hFint N).aestronglyMeasurable) hfint
    · intro N
      filter_upwards [ae_envPos_aux hpos n] with e he
      have hR : 0 ≤ evalR B h n e ^ theta B :=
        Real.rpow_nonneg (evalR_pos_aux (show (1 : ℝ) < B by linarith) h n he).le _
      have hb := fun j : ℕ =>
        expSeries_sub_one_bounds (mul_nonneg hu (Nat.cast_nonneg j : (0 : ℝ) ≤ j)) N
      rw [hFeq, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg hR (gibbsMean_nonneg hB h he _ fun j => (hb j).1))]
      exact mul_le_mul_of_nonneg_left (gibbsMean_mono hB h he fun j => (hb j).2) hR
    · refine Filter.Eventually.of_forall fun e => ?_
      simp only [hFeq]
      apply Tendsto.const_mul
      unfold gibbsMean
      apply tendsto_finsetSum
      intro j _
      exact (tendsto_expSeries_sub_one (u * j)).const_mul _
  have hbound : ∀ N, ∫ e, F N e ∂ν ≤ M * u * x / (1 - r) := by
    intro N
    rw [hIF]
    have hterm : ∀ k ∈ Finset.range N, c k * contactMoment μ B h (k + 1) n ≤
        M * u * x * r ^ k := by
      intro k _
      have hkb := hk (k + 1) n (by omega)
      rw [show k + 1 - 1 = k by omega, show 2 * (k + 1) - 1 = 2 * k + 1 by omega] at hkb
      have hc0 : 0 ≤ c k := by positivity
      have hfac : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      calc
        c k * contactMoment μ B h (k + 1) n ≤
            c k * (((k + 1).factorial : ℝ) * M * L ^ k * ((n : ℝ) + 1) ^ (2 * k + 1)) :=
          mul_le_mul_of_nonneg_left hkb hc0
        _ = u ^ (k + 1) * M * L ^ k * x ^ (2 * k + 1) := by
          simp only [c, x]
          field_simp
        _ = M * u * x * r ^ k := by
          have key : ∀ a b c d : ℝ,
              a ^ (k + 1) * b * c ^ k * d ^ (2 * k + 1) = b * a * d * (c * a * d ^ 2) ^ k := by
            intro a b c d
            rw [mul_pow, mul_pow, ← pow_mul, pow_succ, pow_succ]
            ring
          exact key u M L x
    have hgeom : ∑ k ∈ Finset.range N, r ^ k ≤ 1 / (1 - r) := by
      rw [le_div_iff₀ hr1]
      have := geom_sum_mul_neg r N
      have := pow_nonneg hr0 N
      linarith
    calc
      _ ≤ ∑ k ∈ Finset.range N, M * u * x * r ^ k := Finset.sum_le_sum hterm
      _ = M * u * x * ∑ k ∈ Finset.range N, r ^ k := by rw [Finset.mul_sum]
      _ ≤ M * u * x * (1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = M * u * x / (1 - r) := by ring
  exact le_of_tendsto' hlim hbound

/-! ### The field increment -/

private theorem integrable_evalR_rpow_theta {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) :
    Integrable (fun e => evalR B h n e ^ theta B) (envMeasure μ n) := by
  have hi : Integrable (fun x : ℝ => x ^ theta B) (lawR μ B h n) := by
    simpa only [Real.rpow_zero, mul_one] using
      integrable_absTiltedLogRpow_aux hpos hmean hB h n (s := 0) (le_refl 0)
  rw [← map_evalR_envMeasure μ B h n] at hi
  exact hi.comp_measurable (measurable_evalR B h n)

/-- `A_n(h + u) - A_n(h) ≤ E[R_n(h)^θ ⟨e^{u C_n} - 1⟩_n]` for `u ≥ 0`. -/
private theorem tiltedMass_add_sub_le_contactExpMoment {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ}
    (hB : 2 < B) (h : ℝ) (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    tiltedMass μ B (h + u) n - tiltedMass μ B h n ≤ contactExpMoment μ B h u n := by
  have hI := integrable_evalR_rpow_theta hpos hmean hB
  rw [tiltedMass_eq_env hpos hmean hB (h + u), tiltedMass_eq_env hpos hmean hB h,
    ← integral_sub (hI (h + u) n) (hI h n)]
  unfold contactExpMoment
  apply integral_mono_ae ((hI (h + u) n).sub (hI h n))
    (integrable_contactExpMoment_aux hpos hmean hB h u n)
  filter_upwards [ae_envPos_aux hpos n, evalR_add_eq_gibbsMean_aux hpos hB h n]
    with e he hadd
  rw [Pi.sub_apply, hadd u]
  have hR := evalR_pos_aux (show (1 : ℝ) < B by linarith) h n he
  have hw := contact_gibbsWeight_isProb (show (1 : ℝ) < B by linarith) h n e he
  have hsub : gibbsMean B h n e (fun j => Real.exp (u * j) - 1) =
      gibbsMean B h n e (fun j => Real.exp (u * j)) - 1 := by
    unfold gibbsMean
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hw.2.2]
  have hge : 0 ≤ gibbsMean B h n e (fun j => Real.exp (u * j) - 1) :=
    gibbsMean_nonneg hB h he _ fun j =>
      sub_nonneg.2 (Real.one_le_exp (mul_nonneg hu (Nat.cast_nonneg j)))
  rw [hsub] at hge ⊢
  have hg1 : 1 ≤ gibbsMean B h n e (fun j => Real.exp (u * j)) := by linarith
  rw [Real.mul_rpow hR.le (by linarith)]
  have hle := Real.rpow_le_self_of_one_le hg1 (theta_lt_one hB).le
  have hRθ : 0 ≤ evalR B h n e ^ theta B := Real.rpow_nonneg hR.le _
  have := mul_le_mul_of_nonneg_left hle hRθ
  rw [mul_sub, mul_one]
  linarith

/-! ### `prop:contact-moments` -/

/-- `prop:contact-moments` (`response.tex` lines 227–237), with the conclusions
of `th:product` (`criticalProduct`) and `response:linear` (`response_linear`) as
hypotheses. -/
theorem contactMoments_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B)
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
    (hLinear : ∃ C : ℝ, ∀ n : ℕ,
      deriv (fun h => tiltedMass μ B h n) (criticalPoint μ B) ≤ C * ((n : ℝ) + 1)) :
    ∃ M L : ℝ,
      (∀ k n : ℕ, 1 ≤ k →
        contactMoment μ B (criticalPoint μ B) k n ≤
          (k.factorial : ℝ) * M * L ^ (k - 1) * ((n : ℝ) + 1) ^ (2 * k - 1)) ∧
      ∀ (n : ℕ) (u : ℝ), 0 ≤ u → L * u * ((n : ℝ) + 1) ^ 2 < 1 →
        contactExpMoment μ B (criticalPoint μ B) u n ≤
            M * u * ((n : ℝ) + 1) / (1 - L * u * ((n : ℝ) + 1) ^ 2) ∧
          tiltedMass μ B (criticalPoint μ B + u) n - tiltedMass μ B (criticalPoint μ B) n ≤
            M * u * ((n : ℝ) + 1) / (1 - L * u * ((n : ℝ) + 1) ^ 2) := by
  -- `hshift` is consumed by `criticalProduct` and `response_linear`, whose
  -- conclusions are the hypotheses `hProd` and `hLinear` here.
  have _ := hshift
  obtain ⟨C, hC, hCb, -⟩ := hProd
  obtain ⟨M, L, hM, hL, hbd⟩ := contactMoment_bounds_of_product_linear hpos hmean hB
    ⟨C, hC, fun n hn => ⟨(hCb n hn).1, (hCb n hn).2.1⟩⟩ hLinear
  have hexp := contactExpMoment_le_of_moments hpos hmean hB (criticalPoint μ B) hM hL hbd
  refine ⟨M, L, hbd, fun n u hu hr => ⟨hexp n hu hr, ?_⟩⟩
  exact (tiltedMass_add_sub_le_contactExpMoment hpos hmean hB _ n hu).trans (hexp n hu hr)

end DiamondPinning
