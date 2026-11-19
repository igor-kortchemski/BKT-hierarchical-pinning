module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Proofs.ContactMomentsProof
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `prop:window-moments` (`response.tex` lines 267–342)

The uniform field estimates in the window `0 ≤ v (n+1)² ≤ η` above `h_c`.

All quantities at the field `h₀ + v` are written through the contact polynomial
based at `h₀`: with `p_k` its coefficients (nonnegative) and
`S_d(v) = ∑_k p_k k^d e^{v k}`, one has `R_n(h₀ + v) = S_0(v)`,
`∂_h R_n = S_1`, `∂_h² R_n = S_2`, and `S_0(v) / R_n(h₀) = 1 + ⟨e^{v C_n} - 1⟩`.
For `s > 0`, `k^d e^{v k} ≤ (d!/s^d) (e^{(s+v) k} - 1)` (`d = 1, 2`), so the
contact factors of the field derivatives at `h₀ + v` are bounded by the
exponential contact moment `⟨e^{σ C_n} - 1⟩` at `h₀` with `σ = s + v`, and the
log-factors at `h₀ + v` by those at `h₀` plus `⟨e^{σ C_n} - 1⟩`
(`log R_n(h₀ + v) - log R_n(h₀) ≤ ⟨e^{v C_n}⟩ - 1`). Elementary weighted
AM–GM inequalities then reduce every integrand to a combination of
`R_n^θ ⟨e^{jσ C_n} - 1⟩` (`j = 1, 2, 4, 8`, controlled by the exponential clause
of `prop:contact-moments` with `s = η/(n+1)²`) and `R_n^θ Z_n^2`, `R_n^θ Z_n^4`
at `h₀` (controlled by `th:product`: `K_n ≤ C (n+1)`, `L_n ≤ C (n+1)³`).

This gives the derivative bounds (`window_derivBounds_of`); the window moments
(`windowMoments_of`) follow by the mean value theorem, except the `7/2` moment,
which is bounded directly by the same reduction (the weighted AM–GM step
`ε b^{7/2} ≤ b⁴/√t + t^{7/2} ε⁸` replaces the Hölder interpolation between the
second and fourth moments, which would need the fourth moment at `h₀ + v`), and
the product ratio, which is bounded factor by factor from the bound on `A_j'`.

Both theorems take the conclusions of `th:product` (`criticalProduct`) and of
`prop:contact-moments` (`contactMoments`) as hypotheses.
-/

set_option linter.style.longFile 1700

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Asymptotics
open scoped BigOperators

namespace WindowProof

/-! ### Elementary inequalities -/

/-- `X^m Y ≤ X^(m+1) + Y^(m+1)` for `X, Y ≥ 0`. -/
theorem pow_mul_le_pow_add_pow {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (m : ℕ) :
    X ^ m * Y ≤ X ^ (m + 1) + Y ^ (m + 1) := by
  rcases le_total X Y with hXY | hXY
  · have h1 : X ^ m * Y ≤ Y ^ m * Y :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hX hXY m) hY
    have h2 : 0 ≤ X ^ (m + 1) := pow_nonneg hX _
    rw [pow_succ Y]
    linarith
  · have h1 : X ^ m * Y ≤ X ^ m * X := mul_le_mul_of_nonneg_left hXY (pow_nonneg hX m)
    have h2 : 0 ≤ Y ^ (m + 1) := pow_nonneg hY _
    rw [pow_succ X]
    linarith

/-- `e^S - 1 ≤ S e^S`. -/
theorem exp_sub_one_le_mul_exp (S : ℝ) : Real.exp S - 1 ≤ S * Real.exp S := by
  have h := Real.add_one_le_exp (-S)
  have h2 : Real.exp (-S) * Real.exp S = 1 := by rw [← Real.exp_add]; simp
  have h3 := mul_le_mul_of_nonneg_right h (Real.exp_pos S).le
  nlinarith

/-- `|∏ (1 + δ_j) - 1| ≤ ∏ (1 + |δ_j|) - 1`. -/
theorem abs_prod_one_add_sub_one_le (δ : ℕ → ℝ) (n : ℕ) :
    |∏ j ∈ Finset.range n, (1 + δ j) - 1| ≤ ∏ j ∈ Finset.range n, (1 + |δ j|) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have hQ : 0 ≤ ∏ j ∈ Finset.range n, (1 + |δ j|) - 1 := le_trans (abs_nonneg _) ih
    have e : (∏ j ∈ Finset.range n, (1 + δ j)) * (1 + δ n) - 1 =
        ((∏ j ∈ Finset.range n, (1 + δ j)) - 1) * (1 + δ n) + δ n := by ring
    rw [e]
    have h1 : |1 + δ n| ≤ 1 + |δ n| := by
      calc |1 + δ n| ≤ |1| + |δ n| := abs_add_le _ _
        _ = 1 + |δ n| := by rw [abs_one]
    calc |((∏ j ∈ Finset.range n, (1 + δ j)) - 1) * (1 + δ n) + δ n|
        ≤ |(∏ j ∈ Finset.range n, (1 + δ j)) - 1| * |1 + δ n| + |δ n| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ ((∏ j ∈ Finset.range n, (1 + |δ j|)) - 1) * (1 + |δ n|) + |δ n| :=
          add_le_add (mul_le_mul ih h1 (abs_nonneg _) hQ) le_rfl
      _ = (∏ j ∈ Finset.range n, (1 + |δ j|)) * (1 + |δ n|) - 1 := by ring

/-- `∏ (1 + |δ_j|) ≤ exp (∑ |δ_j|)`. -/
theorem prod_one_add_abs_le_exp (δ : ℕ → ℝ) (n : ℕ) :
    ∏ j ∈ Finset.range n, (1 + |δ j|) ≤ Real.exp (∑ j ∈ Finset.range n, |δ j|) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro j _; positivity
  · intro j _; linarith [Real.add_one_le_exp (|δ j|)]

/-- The mean value theorem in the window `[h₀, h₀ + u]`. -/
theorem mvt_window {f f' : ℝ → ℝ} {h₀ u D : ℝ} (hu : 0 ≤ u)
    (hf : ∀ v, 0 ≤ v → v ≤ u → HasDerivAt f (f' (h₀ + v)) (h₀ + v))
    (hD : ∀ v, 0 ≤ v → v ≤ u → |f' (h₀ + v)| ≤ D) : |f (h₀ + u) - f h₀| ≤ D * u := by
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (f' := f') (C := D)
    (a := h₀) (b := h₀ + u)
    (fun x hx => by
      have h := hf (x - h₀) (by linarith [hx.1]) (by linarith [hx.2])
      have e : h₀ + (x - h₀) = x := by ring
      rw [e] at h
      exact h.hasDerivWithinAt)
    (fun x hx => by
      have h := hD (x - h₀) (by linarith [hx.1]) (by linarith [hx.2])
      have e : h₀ + (x - h₀) = x := by ring
      rw [e] at h
      rwa [Real.norm_eq_abs])
    (h₀ + u) ⟨by linarith, le_rfl⟩
  rw [Real.norm_eq_abs] at key
  have e : h₀ + u - h₀ = u := by ring
  rwa [e] at key

/-! ### Weighted exponential sums -/

/-- The weighted exponential sum `∑_{k < N} p_k k^d e^{u k}`. -/
noncomputable def wSum (p : ℕ → ℝ) (N d : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, p k * (k : ℝ) ^ d * Real.exp (u * k)

theorem hasDerivAt_wSum (p : ℕ → ℝ) (N d : ℕ) (u : ℝ) :
    HasDerivAt (wSum p N d) (wSum p N (d + 1) u) u := by
  have H : ∀ k ∈ Finset.range N, HasDerivAt (fun u : ℝ => p k * (k : ℝ) ^ d * Real.exp (u * k))
      (p k * (k : ℝ) ^ (d + 1) * Real.exp (u * k)) u := by
    intro k _
    have h1 : HasDerivAt (fun u : ℝ => u * (k : ℝ)) (k : ℝ) u := by
      simpa using (hasDerivAt_id u).mul_const (k : ℝ)
    convert h1.exp.const_mul (p k * (k : ℝ) ^ d) using 1
    ring
  unfold wSum
  exact HasDerivAt.fun_sum H

theorem hasDerivAt_wSum_sub (p : ℕ → ℝ) (N d : ℕ) (h₀ h : ℝ) :
    HasDerivAt (fun h => wSum p N d (h - h₀)) (wSum p N (d + 1) (h - h₀)) h := by
  have := (hasDerivAt_wSum p N d (h - h₀)).comp h ((hasDerivAt_id' h).sub_const h₀)
  rw [mul_one] at this
  exact this

theorem wSum_nonneg {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k) (N d : ℕ) (u : ℝ) : 0 ≤ wSum p N d u :=
  Finset.sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (hp k) (pow_nonneg (Nat.cast_nonneg k) d)) (Real.exp_pos _).le

theorem wSum_zero_mono {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k) (N : ℕ) {u v : ℝ} (huv : u ≤ v) :
    wSum p N 0 u ≤ wSum p N 0 v := by
  unfold wSum
  apply Finset.sum_le_sum
  intro k _
  have h : Real.exp (u * k) ≤ Real.exp (v * k) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right huv (Nat.cast_nonneg k))
  simp only [pow_zero, mul_one]
  exact mul_le_mul_of_nonneg_left h (hp k)

theorem wSum_zero_sub_eq (p : ℕ → ℝ) (N : ℕ) (σ : ℝ) :
    wSum p N 0 σ - wSum p N 0 0 = ∑ k ∈ Finset.range N, p k * (Real.exp (σ * k) - 1) := by
  unfold wSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [pow_zero, mul_one, zero_mul, Real.exp_zero]
  ring

/-- `s S_1(v) ≤ S_0(s + v) - S_0(0)`. -/
theorem wSum_one_le {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k) (N : ℕ) {s v : ℝ}
    (hv : 0 ≤ v) : s * wSum p N 1 v ≤ wSum p N 0 (s + v) - wSum p N 0 0 := by
  rw [wSum_zero_sub_eq]
  unfold wSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 := Real.add_one_le_exp (s * k)
  have h2 : 1 ≤ Real.exp (v * k) := Real.one_le_exp (mul_nonneg hv hk)
  have h3 : Real.exp ((s + v) * k) = Real.exp (s * k) * Real.exp (v * k) := by
    rw [← Real.exp_add]; ring_nf
  rw [h3, pow_one]
  have hp' := hp k
  have h4 : 0 ≤ p k * ((Real.exp (s * k) - (s * k + 1)) * Real.exp (v * k)) :=
    mul_nonneg hp' (mul_nonneg (by linarith) (by linarith))
  have h5 : 0 ≤ p k * (Real.exp (v * k) - 1) := mul_nonneg hp' (by linarith)
  nlinarith

/-- `s² S_2(v) ≤ 2 (S_0(s + v) - S_0(0))`. -/
theorem wSum_two_le {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k) (N : ℕ) {s v : ℝ} (hs : 0 ≤ s)
    (hv : 0 ≤ v) : s ^ 2 * wSum p N 2 v ≤ 2 * (wSum p N 0 (s + v) - wSum p N 0 0) := by
  rw [wSum_zero_sub_eq]
  unfold wSum
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hsk : 0 ≤ s * k := mul_nonneg hs hk
  have h1 := Real.quadratic_le_exp_of_nonneg hsk
  have h2 : 1 ≤ Real.exp (v * k) := Real.one_le_exp (mul_nonneg hv hk)
  have h3 : Real.exp ((s + v) * k) = Real.exp (s * k) * Real.exp (v * k) := by
    rw [← Real.exp_add]; ring_nf
  rw [h3]
  have hp' := hp k
  have h4 : 0 ≤ p k * ((Real.exp (s * k) - (1 + s * k + (s * k) ^ 2 / 2)) * Real.exp (v * k)) :=
    mul_nonneg hp' (mul_nonneg (by linarith) (by linarith))
  have h5 : 0 ≤ p k * (Real.exp (v * k) - 1) := mul_nonneg hp' (by linarith)
  have h6 : 0 ≤ p k * (s * k) * Real.exp (v * k) :=
    mul_nonneg (mul_nonneg hp' hsk) (by linarith)
  nlinarith

/-- Cauchy–Schwarz: `S_1² ≤ S_0 S_2`. -/
theorem wSum_one_sq_le {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k) (N : ℕ) (u : ℝ) :
    wSum p N 1 u ^ 2 ≤ wSum p N 0 u * wSum p N 2 u := by
  unfold wSum
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro k _
    exact mul_nonneg (mul_nonneg (hp k) (pow_nonneg (Nat.cast_nonneg k) _)) (Real.exp_pos _).le
  · intro k _
    exact mul_nonneg (mul_nonneg (hp k) (pow_nonneg (Nat.cast_nonneg k) _)) (Real.exp_pos _).le
  · intro k _
    apply le_of_eq
    ring

/-- `(S_0(σ) - S_0(0))² ≤ S_0(0) (S_0(2σ) - S_0(0))`. -/
theorem wSum_sub_sq_le {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k) (N : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    (wSum p N 0 σ - wSum p N 0 0) ^ 2 ≤ wSum p N 0 0 * (wSum p N 0 (2 * σ) - wSum p N 0 0) := by
  have e0 : wSum p N 0 0 = ∑ k ∈ Finset.range N, p k := by simp [wSum]
  rw [wSum_zero_sub_eq, wSum_zero_sub_eq, e0]
  calc (∑ k ∈ Finset.range N, p k * (Real.exp (σ * k) - 1)) ^ 2
      ≤ (∑ k ∈ Finset.range N, p k) *
          ∑ k ∈ Finset.range N, p k * (Real.exp (σ * k) - 1) ^ 2 :=
        Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun k _ => hp k)
          (fun k _ => mul_nonneg (hp k) (sq_nonneg _)) (fun k _ => le_of_eq (by ring))
    _ ≤ (∑ k ∈ Finset.range N, p k) *
          ∑ k ∈ Finset.range N, p k * (Real.exp (2 * σ * k) - 1) := by
        apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun k _ => hp k)
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_left _ (hp k)
        have hy : 1 ≤ Real.exp (σ * k) := Real.one_le_exp (mul_nonneg hσ (Nat.cast_nonneg k))
        have e : Real.exp (2 * σ * k) = Real.exp (σ * k) ^ 2 := by
          rw [sq, ← Real.exp_add]; ring_nf
        rw [e]
        nlinarith

/-! ### The contact polynomial based at `h₀` -/

/-- The coefficients of the contact polynomial of `e` at the base field `h₀`. -/
noncomputable def cpc (B h₀ : ℝ) (n : ℕ) (e : Env n) : ℕ → ℝ :=
  fun k => (contactPoly B h₀ n e).coeff k

/-- `R_n(h₀)^θ`. -/
noncomputable def wRho (B h₀ : ℝ) (n : ℕ) (e : Env n) : ℝ := evalR B h₀ n e ^ theta B

/-- `Z_n = log R_n(h₀) - a`. -/
noncomputable def wZ (B h₀ : ℝ) (n : ℕ) (e : Env n) : ℝ := Real.log (evalR B h₀ n e) - Real.log B

/-- `⟨e^{σ C_n} - 1⟩` at the base field `h₀`. -/
noncomputable def expG (B h₀ : ℝ) (n : ℕ) (e : Env n) (σ : ℝ) : ℝ :=
  gibbsMean B h₀ n e (fun j => Real.exp (σ * j) - 1)

theorem cpc_nonneg {B : ℝ} (hB : 2 < B) (h₀ : ℝ) {n : ℕ} {e : Env n} (he : Env.Pos n e) :
    ∀ k, 0 ≤ cpc B h₀ n e k :=
  contactPoly_coeff_nonneg (by linarith) h₀ n e he

theorem evalR_eq_wSum (B h₀ : ℝ) (n : ℕ) (e : Env n) (h : ℝ) :
    evalR B h n e = wSum (cpc B h₀ n e) (2 ^ n + 1) 0 (h - h₀) := by
  have e1 : evalR B h n e = evalR B (h₀ + (h - h₀)) n e := by ring_nf
  rw [e1, ← eval_contactPoly_exp B h₀ n e (h - h₀),
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (contactPoly_natDegree_le B h₀ n e))]
  simp only [wSum, cpc]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Real.exp_nat_mul, pow_zero, mul_one, mul_comm ((k : ℝ)) (h - h₀)]

theorem evalR_eq_wSum_zero (B h₀ : ℝ) (n : ℕ) (e : Env n) :
    evalR B h₀ n e = wSum (cpc B h₀ n e) (2 ^ n + 1) 0 0 := by
  rw [evalR_eq_wSum B h₀ n e h₀, sub_self]

theorem hasDerivAt_evalR_wSum (B h₀ : ℝ) (n : ℕ) (e : Env n) (h : ℝ) :
    HasDerivAt (fun h' => evalR B h' n e) (wSum (cpc B h₀ n e) (2 ^ n + 1) 1 (h - h₀)) h := by
  have hfun : (fun h' => evalR B h' n e) =
      fun h' => wSum (cpc B h₀ n e) (2 ^ n + 1) 0 (h' - h₀) := by
    funext h'; exact evalR_eq_wSum B h₀ n e h'
  rw [hfun]
  exact hasDerivAt_wSum_sub _ _ 0 h₀ h

theorem gibbsMean_eq_sum_div (B h₀ : ℝ) (n : ℕ) (e : Env n) (f : ℕ → ℝ) :
    gibbsMean B h₀ n e f =
      (∑ k ∈ Finset.range (2 ^ n + 1), cpc B h₀ n e k * f k) / evalR B h₀ n e := by
  simp only [gibbsMean, gibbsWeight, cpc, eval_contactPoly_one, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem expG_eq (B h₀ : ℝ) (n : ℕ) (e : Env n) (σ : ℝ) :
    expG B h₀ n e σ =
      (wSum (cpc B h₀ n e) (2 ^ n + 1) 0 σ - evalR B h₀ n e) / evalR B h₀ n e := by
  rw [expG, gibbsMean_eq_sum_div]
  congr 1
  rw [evalR_eq_wSum_zero B h₀ n e, wSum_zero_sub_eq]

theorem wRho_nonneg {B : ℝ} (hB : 2 < B) (h₀ : ℝ) {n : ℕ} {e : Env n} (he : Env.Pos n e) :
    0 ≤ wRho B h₀ n e :=
  Real.rpow_nonneg (evalR_pos_aux (by linarith) h₀ n he).le _

theorem expG_nonneg {B : ℝ} (hB : 2 < B) (h₀ : ℝ) {n : ℕ} {e : Env n} (he : Env.Pos n e)
    {σ : ℝ} (hσ : 0 ≤ σ) : 0 ≤ expG B h₀ n e σ := by
  rw [expG_eq, evalR_eq_wSum_zero B h₀ n e]
  exact div_nonneg (sub_nonneg.mpr (wSum_zero_mono (cpc_nonneg hB h₀ he) _ hσ))
    (wSum_nonneg (cpc_nonneg hB h₀ he) _ _ _)

theorem expG_sq_le {B : ℝ} (hB : 2 < B) (h₀ : ℝ) {n : ℕ} {e : Env n} (he : Env.Pos n e)
    {σ : ℝ} (hσ : 0 ≤ σ) : expG B h₀ n e σ ^ 2 ≤ expG B h₀ n e (2 * σ) := by
  have hR₀ : 0 < evalR B h₀ n e := evalR_pos_aux (by linarith) h₀ n he
  have hW : 0 < wSum (cpc B h₀ n e) (2 ^ n + 1) 0 0 := by
    rw [← evalR_eq_wSum_zero B h₀ n e]; exact hR₀
  have key := wSum_sub_sq_le (cpc_nonneg hB h₀ he) (2 ^ n + 1) hσ
  rw [expG_eq, expG_eq, evalR_eq_wSum_zero B h₀ n e, div_pow,
    div_le_div_iff₀ (by positivity) hW]
  have := mul_le_mul_of_nonneg_right key hW.le
  nlinarith

theorem expG_pow4_le {B : ℝ} (hB : 2 < B) (h₀ : ℝ) {n : ℕ} {e : Env n} (he : Env.Pos n e)
    {σ : ℝ} (hσ : 0 ≤ σ) : expG B h₀ n e σ ^ 4 ≤ expG B h₀ n e (4 * σ) := by
  have h1 := expG_sq_le hB h₀ he hσ
  have h2 := expG_sq_le hB h₀ he (by linarith : 0 ≤ 2 * σ)
  rw [show 2 * (2 * σ) = 4 * σ by ring] at h2
  calc expG B h₀ n e σ ^ 4 = (expG B h₀ n e σ ^ 2) ^ 2 := by ring
    _ ≤ expG B h₀ n e (2 * σ) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ ≤ _ := h2

theorem expG_pow8_le {B : ℝ} (hB : 2 < B) (h₀ : ℝ) {n : ℕ} {e : Env n} (he : Env.Pos n e)
    {σ : ℝ} (hσ : 0 ≤ σ) : expG B h₀ n e σ ^ 8 ≤ expG B h₀ n e (8 * σ) := by
  have h1 := expG_pow4_le hB h₀ he hσ
  have h2 := expG_sq_le hB h₀ he (by linarith : 0 ≤ 4 * σ)
  rw [show 2 * (4 * σ) = 8 * σ by ring] at h2
  calc expG B h₀ n e σ ^ 8 = (expG B h₀ n e σ ^ 4) ^ 2 := by ring
    _ ≤ expG B h₀ n e (4 * σ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    _ ≤ _ := h2

/-- The basic comparisons between the fields `h₀ + v` and `h₀`, for `s, v ≥ 0`. -/
theorem env_shift_facts {B : ℝ} (hB : 2 < B) (h₀ : ℝ) {n : ℕ} {e : Env n} (he : Env.Pos n e)
    {s v : ℝ} (hs : 0 ≤ s) (hv : 0 ≤ v) :
    evalR B h₀ n e ≤ evalR B (h₀ + v) n e ∧
    evalR B (h₀ + v) n e / evalR B h₀ n e - 1 ≤ expG B h₀ n e (s + v) ∧
    s * wSum (cpc B h₀ n e) (2 ^ n + 1) 1 v ≤ evalR B h₀ n e * expG B h₀ n e (s + v) ∧
    s ^ 2 * wSum (cpc B h₀ n e) (2 ^ n + 1) 2 v ≤
      2 * (evalR B h₀ n e * expG B h₀ n e (s + v)) := by
  have hp := cpc_nonneg hB h₀ he
  have hR₀ : 0 < evalR B h₀ n e := evalR_pos_aux (by linarith) h₀ n he
  have hRv : evalR B (h₀ + v) n e = wSum (cpc B h₀ n e) (2 ^ n + 1) 0 v := by
    rw [evalR_eq_wSum B h₀ n e (h₀ + v)]; ring_nf
  have hR0 := evalR_eq_wSum_zero B h₀ n e
  have hmulE : evalR B h₀ n e * expG B h₀ n e (s + v) =
      wSum (cpc B h₀ n e) (2 ^ n + 1) 0 (s + v) - evalR B h₀ n e := by
    rw [expG_eq]; field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hRv, hR0]; exact wSum_zero_mono hp _ hv
  · rw [expG_eq, hRv, div_sub_one hR₀.ne']
    apply (div_le_div_iff_of_pos_right hR₀).mpr
    have := wSum_zero_mono hp (2 ^ n + 1) (show v ≤ s + v by linarith)
    linarith
  · rw [hmulE, hR0]; exact wSum_one_le hp _ hv
  · rw [hmulE, hR0]; exact wSum_two_le hp _ hs hv

/-! ### Field derivatives of `e^{θ x} (x - a)^k`, `x = log R` -/

theorem hasDerivAt_tilt_comp {T0 : ℝ → ℝ} {T1 h : ℝ} (θ a : ℝ) (k : ℕ)
    (hT : HasDerivAt T0 T1 h) (hpos : 0 < T0 h) :
    HasDerivAt (fun h' => Real.exp (θ * Real.log (T0 h')) * (Real.log (T0 h') - a) ^ k)
      (Real.exp (θ * Real.log (T0 h)) *
        (θ * (Real.log (T0 h) - a) ^ k + k * (Real.log (T0 h) - a) ^ (k - 1)) * (T1 / T0 h)) h := by
  have := (hasDerivAt_exp_mul_pow θ a k (Real.log (T0 h))).comp h (hT.log hpos.ne')
  simpa only [Function.comp_def] using this

/-- The first field derivative of `e^{θ x} (x - a)`, `x = log T0`. -/
noncomputable def tiltD1 (θ a : ℝ) (T0 T1 : ℝ → ℝ) (h : ℝ) : ℝ :=
  Real.exp (θ * Real.log (T0 h)) * (θ * (Real.log (T0 h) - a) + 1) * (T1 h / T0 h)

/-- The second field derivative of `e^{θ x} (x - a)`, `x = log T0`. -/
noncomputable def tiltD2 (θ a : ℝ) (T0 T1 T2 : ℝ → ℝ) (h : ℝ) : ℝ :=
  Real.exp (θ * Real.log (T0 h)) * (θ * (θ * (Real.log (T0 h) - a) + 1) + θ) *
      (T1 h / T0 h) * (T1 h / T0 h) +
    Real.exp (θ * Real.log (T0 h)) * (θ * (Real.log (T0 h) - a) + 1) *
      ((T2 h * T0 h - T1 h * T1 h) / T0 h ^ 2)

theorem hasDerivAt_tiltD1 {T0 T1 T2 : ℝ → ℝ} {h : ℝ} (θ a : ℝ)
    (h0 : HasDerivAt T0 (T1 h) h) (h1 : HasDerivAt T1 (T2 h) h) (hpos : 0 < T0 h) :
    HasDerivAt (tiltD1 θ a T0 T1) (tiltD2 θ a T0 T1 T2 h) h := by
  have hP : ∀ y : ℝ, HasDerivAt (fun y => Real.exp (θ * y) * (θ * (y - a) + 1))
      (Real.exp (θ * y) * (θ * (θ * (y - a) + 1) + θ)) y := by
    intro y
    have hlin : HasDerivAt (fun y : ℝ => θ * y) θ y := by
      simpa using (hasDerivAt_id y).const_mul θ
    have hq : HasDerivAt (fun y : ℝ => θ * (y - a) + 1) θ y := by
      simpa using (((hasDerivAt_id y).sub_const a).const_mul θ).add_const 1
    convert hlin.exp.mul hq using 1
    ring
  have hPx := (hP (Real.log (T0 h))).comp h (h0.log hpos.ne')
  have hdiv := h1.div h0 hpos.ne'
  have H := hPx.mul hdiv
  simp only [Function.comp_def, Pi.div_apply] at H
  unfold tiltD1 tiltD2
  refine H.congr_deriv ?_
  ring

theorem iteratedDeriv_two_tilt {T0 T1 T2 : ℝ → ℝ} (θ a : ℝ)
    (h0 : ∀ h, HasDerivAt T0 (T1 h) h) (h1 : ∀ h, HasDerivAt T1 (T2 h) h)
    (hpos : ∀ h, 0 < T0 h) (h : ℝ) :
    iteratedDeriv 2 (fun h' => Real.exp (θ * Real.log (T0 h')) * (Real.log (T0 h') - a) ^ 1) h =
      tiltD2 θ a T0 T1 T2 h := by
  have hd : deriv (fun h' => Real.exp (θ * Real.log (T0 h')) * (Real.log (T0 h') - a) ^ 1) =
      tiltD1 θ a T0 T1 := by
    funext h'
    rw [(hasDerivAt_tilt_comp θ a 1 (h0 h') (hpos h')).deriv, tiltD1]
    simp
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
  exact (hasDerivAt_tiltD1 θ a (h0 h) (h1 h) (hpos h)).deriv

/-! ### Pointwise real bounds -/

theorem exp_theta_log_div_le {θ R₀ R : ℝ} (hθ1 : θ ≤ 1) (hR₀ : 0 < R₀) (hRR : R₀ ≤ R) :
    Real.exp (θ * Real.log R) / R ≤ Real.exp (θ * Real.log R₀) / R₀ := by
  have hR : 0 < R := lt_of_lt_of_le hR₀ hRR
  have e1 : Real.exp (θ * Real.log R) / R = Real.exp ((θ - 1) * Real.log R) := by
    rw [sub_mul, one_mul, Real.exp_sub, Real.exp_log hR]
  have e2 : Real.exp (θ * Real.log R₀) / R₀ = Real.exp ((θ - 1) * Real.log R₀) := by
    rw [sub_mul, one_mul, Real.exp_sub, Real.exp_log hR₀]
  rw [e1, e2, Real.exp_le_exp]
  have := Real.log_le_log hR₀ hRR
  nlinarith

theorem abs_tiltDk_le {θ a R₀ R T1 : ℝ} (k : ℕ) (hθ : 0 < θ) (hθ1 : θ < 1) (hR₀ : 0 < R₀)
    (hRR : R₀ ≤ R) (hT1 : 0 ≤ T1) :
    |Real.exp (θ * Real.log R) * (θ * (Real.log R - a) ^ k + k * (Real.log R - a) ^ (k - 1)) *
        (T1 / R)| ≤
      Real.exp (θ * Real.log R₀) / R₀ * T1 *
        (|Real.log R - a| ^ k + k * |Real.log R - a| ^ (k - 1)) := by
  have hR : 0 < R := lt_of_lt_of_le hR₀ hRR
  have hdiv := exp_theta_log_div_le hθ1.le hR₀ hRR
  have hpoly : |θ * (Real.log R - a) ^ k + k * (Real.log R - a) ^ (k - 1)| ≤
      |Real.log R - a| ^ k + k * |Real.log R - a| ^ (k - 1) := by
    calc _ ≤ |θ * (Real.log R - a) ^ k| + |(k : ℝ) * (Real.log R - a) ^ (k - 1)| := abs_add_le _ _
      _ = θ * |Real.log R - a| ^ k + k * |Real.log R - a| ^ (k - 1) := by
        rw [abs_mul, abs_mul, abs_of_pos hθ, abs_pow, abs_pow, Nat.abs_cast]
      _ ≤ _ := by
        have : 0 ≤ |Real.log R - a| ^ k := pow_nonneg (abs_nonneg _) _
        nlinarith
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (div_nonneg hT1 hR.le)]
  calc Real.exp (θ * Real.log R) * |θ * (Real.log R - a) ^ k + k * (Real.log R - a) ^ (k - 1)| *
        (T1 / R)
      = (Real.exp (θ * Real.log R) / R * T1) *
          |θ * (Real.log R - a) ^ k + k * (Real.log R - a) ^ (k - 1)| := by ring
    _ ≤ (Real.exp (θ * Real.log R₀) / R₀ * T1) *
          (|Real.log R - a| ^ k + k * |Real.log R - a| ^ (k - 1)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hdiv hT1) hpoly (abs_nonneg _)
          (mul_nonneg (div_nonneg (Real.exp_pos _).le hR₀.le) hT1)

theorem abs_tiltD2_le {θ a R₀ R T1 T2 : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hR₀ : 0 < R₀)
    (hRR : R₀ ≤ R) (hT1 : 0 ≤ T1) (hT2 : 0 ≤ T2) (hCS : T1 ^ 2 ≤ R * T2) :
    |Real.exp (θ * Real.log R) * (θ * (θ * (Real.log R - a) + 1) + θ) * (T1 / R) * (T1 / R) +
      Real.exp (θ * Real.log R) * (θ * (Real.log R - a) + 1) * ((T2 * R - T1 * T1) / R ^ 2)| ≤
    3 * (|Real.log R - a| + 2) * (Real.exp (θ * Real.log R₀) / R₀ * T2) := by
  have hR : 0 < R := lt_of_lt_of_le hR₀ hRR
  have hdiv := exp_theta_log_div_le hθ1.le hR₀ hRR
  have hm : 0 ≤ T1 / R := div_nonneg hT1 hR.le
  have hw : 0 ≤ T2 / R := div_nonneg hT2 hR.le
  have hmw : (T1 / R) ^ 2 ≤ T2 / R := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hR]
    nlinarith
  have hvar : (T2 * R - T1 * T1) / R ^ 2 = T2 / R - (T1 / R) ^ 2 := by
    field_simp
  rw [hvar]
  set Z := Real.log R - a with hZ
  set ρ := Real.exp (θ * Real.log R) with hρdef
  have hρ : 0 < ρ := Real.exp_pos _
  set m := T1 / R with hmdef
  set w := T2 / R with hwdef
  have hA : |θ * (θ * Z + 1) + θ| ≤ |Z| + 2 := by
    rw [abs_le]
    have h1 := mul_nonneg (sq_nonneg θ) (sub_nonneg.mpr (le_abs_self Z))
    have h2 := mul_nonneg (sq_nonneg θ) (sub_nonneg.mpr (neg_abs_le Z))
    have h3 : 0 ≤ (1 - θ ^ 2) * |Z| := mul_nonneg (by nlinarith) (abs_nonneg Z)
    constructor <;> nlinarith
  have hB : |θ * Z + 1| ≤ |Z| + 1 := by
    rw [abs_le]
    have h1 := mul_nonneg hθ.le (sub_nonneg.mpr (le_abs_self Z))
    have h2 := mul_nonneg hθ.le (sub_nonneg.mpr (neg_abs_le Z))
    have h3 : 0 ≤ (1 - θ) * |Z| := mul_nonneg (by linarith) (abs_nonneg Z)
    constructor <;> nlinarith
  have hC : |w - m ^ 2| ≤ w + m ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith
  have key : |ρ * (θ * (θ * Z + 1) + θ) * m * m + ρ * (θ * Z + 1) * (w - m ^ 2)| ≤
      3 * (|Z| + 2) * (ρ * w) := by
    calc _ ≤ |ρ * (θ * (θ * Z + 1) + θ) * m * m| + |ρ * (θ * Z + 1) * (w - m ^ 2)| :=
          abs_add_le _ _
      _ = ρ * |θ * (θ * Z + 1) + θ| * m ^ 2 + ρ * |θ * Z + 1| * |w - m ^ 2| := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hρ, abs_of_nonneg hm]
          ring
      _ ≤ ρ * (|Z| + 2) * m ^ 2 + ρ * (|Z| + 1) * (w + m ^ 2) := by
          have e1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hρ.le)
            (sq_nonneg m)
          have e2 := mul_le_mul (mul_le_mul_of_nonneg_left hB hρ.le) hC (abs_nonneg _)
            (mul_nonneg hρ.le (by positivity))
          linarith
      _ ≤ 3 * (|Z| + 2) * (ρ * w) := by
          have hZ0 := abs_nonneg Z
          have e1 := mul_le_mul_of_nonneg_left hmw (mul_nonneg hρ.le (by linarith : 0 ≤ |Z| + 2))
          nlinarith [mul_nonneg hρ.le hw, mul_nonneg (mul_nonneg hρ.le hw) hZ0,
            mul_nonneg (mul_nonneg hρ.le (sq_nonneg m)) hZ0]
  have hρw : ρ * w ≤ Real.exp (θ * Real.log R₀) / R₀ * T2 := by
    calc ρ * w = ρ / R * T2 := by simp only [hwdef]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hdiv hT2
  calc _ ≤ 3 * (|Z| + 2) * (ρ * w) := key
    _ ≤ _ := mul_le_mul_of_nonneg_left hρw (by positivity)

theorem abs_log_sub_le_shift {a R₀ R ε : ℝ} (hR₀ : 0 < R₀) (hRR : R₀ ≤ R)
    (hε : R / R₀ - 1 ≤ ε) : |Real.log R - a| ≤ |Real.log R₀ - a| + ε := by
  have hR : 0 < R := lt_of_lt_of_le hR₀ hRR
  have h1 : Real.log R - Real.log R₀ ≤ ε := by
    rw [← Real.log_div hR.ne' hR₀.ne']
    exact (Real.log_le_sub_one_of_pos (div_pos hR hR₀)).trans hε
  have h2 : 0 ≤ Real.log R - Real.log R₀ := sub_nonneg.mpr (Real.log_le_log hR₀ hRR)
  calc |Real.log R - a| = |(Real.log R₀ - a) + (Real.log R - Real.log R₀)| := by
        congr 1; ring
    _ ≤ |Real.log R₀ - a| + |Real.log R - Real.log R₀| := abs_add_le _ _
    _ ≤ _ := by rw [abs_of_nonneg h2]; linarith

theorem polyK_le {a ε t w : ℝ} (hε : 0 ≤ ε) (htw : t * w = 1) :
    ε * ((a + ε) ^ 2 + 2 * (a + ε)) ≤
      ε + (2 * t ^ 2 + 4) * ε ^ 2 + 4 * ε ^ 4 + 2 * w ^ 2 * a ^ 4 := by
  have hb2 : (a + ε) ^ 2 + 2 * (a + ε) ≤ 1 + 4 * a ^ 2 + 4 * ε ^ 2 := by
    nlinarith [sq_nonneg (a + ε - 1), sq_nonneg (a - ε)]
  have h1 := mul_le_mul_of_nonneg_left hb2 hε
  have h2 : t * w * (ε * a ^ 2) = ε * a ^ 2 := by rw [htw, one_mul]
  have h3 := sq_nonneg (t * ε - w * a ^ 2)
  have h4 := sq_nonneg (ε - ε ^ 2)
  nlinarith [sq_nonneg ε, pow_nonneg hε 4]

theorem polyJ_le {a ε t w : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε) (ht : 0 ≤ t) (hw : 0 ≤ w)
    (htw : t * w = 1) :
    ε * ((a + ε) ^ 3 + 3 * (a + ε) ^ 2) ≤
      (3 * t ^ 2 + 6) * ε ^ 2 + (4 * t ^ 3 + 10) * ε ^ 4 + (4 * w + 3 * w ^ 2) * a ^ 4 := by
  have hb3 : (a + ε) ^ 3 ≤ 4 * a ^ 3 + 4 * ε ^ 3 := by
    nlinarith [mul_nonneg (add_nonneg ha hε) (sq_nonneg (a - ε))]
  have hb2 : (a + ε) ^ 2 ≤ 2 * a ^ 2 + 2 * ε ^ 2 := by nlinarith [sq_nonneg (a - ε)]
  have h1 : ε * ((a + ε) ^ 3 + 3 * (a + ε) ^ 2) ≤
      ε * (4 * a ^ 3 + 4 * ε ^ 3 + 3 * (2 * a ^ 2 + 2 * ε ^ 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) hε
  have hY := pow_mul_le_pow_add_pow ha (mul_nonneg ht hε) 3
  have hY' := mul_le_mul_of_nonneg_left hY hw
  have e1 : w * (a ^ 3 * (t * ε)) = ε * a ^ 3 := by
    calc w * (a ^ 3 * (t * ε)) = (t * w) * (ε * a ^ 3) := by ring
      _ = ε * a ^ 3 := by rw [htw, one_mul]
  have e2 : w * (a ^ (3 + 1) + (t * ε) ^ (3 + 1)) = w * a ^ 4 + t ^ 3 * ε ^ 4 := by
    calc w * (a ^ (3 + 1) + (t * ε) ^ (3 + 1)) = w * a ^ 4 + (t * w) * (t ^ 3 * ε ^ 4) := by ring
      _ = _ := by rw [htw, one_mul]
  rw [e1, e2] at hY'
  have h2 : t * w * (ε * a ^ 2) = ε * a ^ 2 := by rw [htw, one_mul]
  have h3 := sq_nonneg (t * ε - w * a ^ 2)
  have h4 := sq_nonneg (ε - ε ^ 2)
  nlinarith [sq_nonneg ε, pow_nonneg hε 4, pow_nonneg ha 4, sq_nonneg w]

theorem polyH_le {a ε t w : ℝ} (ht : 0 ≤ t) (htw : t * w = 1) :
    (a + ε + 2) * ε ≤ w / 2 * a ^ 2 + (t / 2 + 1) * ε ^ 2 + 2 * ε := by
  have h1 := mul_nonneg ht (sq_nonneg (w * a - ε))
  have e1 : t * (w * a - ε) ^ 2 = (t * w) * (w * a ^ 2) - 2 * (t * w) * (a * ε) + t * ε ^ 2 := by
    ring
  rw [e1, htw] at h1
  nlinarith

theorem rpow_seven_halves {b : ℝ} (hb : 0 ≤ b) : b ^ ((7 : ℝ) / 2) = Real.sqrt b ^ 7 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hb]
  norm_num

theorem poly72_le {b ε r : ℝ} (hb : 0 ≤ b) (hε : 0 ≤ ε) (hr : 0 < r) :
    (1 + ε) * b ^ ((7 : ℝ) / 2) ≤ r ^ 3 * b ^ 2 + 2 * b ^ 4 / r + r ^ 7 * ε ^ 8 := by
  obtain ⟨q, hq0, rfl⟩ : ∃ q, 0 ≤ q ∧ b = q ^ 2 :=
    ⟨Real.sqrt b, Real.sqrt_nonneg b, (Real.sq_sqrt hb).symm⟩
  rw [rpow_seven_halves hb, Real.sqrt_sq hq0]
  have h1 := pow_mul_le_pow_add_pow hq0 hr.le 3
  have h2 := pow_mul_le_pow_add_pow hq0 (mul_nonneg hr.le hε) 7
  have h1' := mul_le_mul_of_nonneg_left h1 (pow_nonneg hq0 4)
  simp only [Nat.reduceAdd] at h1 h2 h1'
  have hr' := hr.ne'
  have e : r * (2 * (q ^ 2) ^ 4 / r) = 2 * (q ^ 2) ^ 4 := by field_simp
  refine le_of_mul_le_mul_left ?_ hr
  nlinarith

/-! ### Pointwise bounds on the environment -/

theorem env_derivK_bound {B : ℝ} (hB : 2 < B) (h₀ : ℝ) {n : ℕ} {e : Env n} (he : Env.Pos n e)
    (k : ℕ) {s v : ℝ} (hs : 0 < s) (hv : 0 ≤ v) :
    |deriv (fun h' => Real.exp (theta B * Real.log (evalR B h' n e)) *
        (Real.log (evalR B h' n e) - Real.log B) ^ k) (h₀ + v)| ≤
      wRho B h₀ n e * (expG B h₀ n e (s + v) / s) *
        ((|wZ B h₀ n e| + expG B h₀ n e (s + v)) ^ k +
          k * (|wZ B h₀ n e| + expG B h₀ n e (s + v)) ^ (k - 1)) := by
  obtain ⟨hRR, hε, hT1s, -⟩ := env_shift_facts hB h₀ he hs.le hv
  have hp := cpc_nonneg hB h₀ he
  have hR₀ : 0 < evalR B h₀ n e := evalR_pos_aux (by linarith) h₀ n he
  have hposh : ∀ h, 0 < evalR B h n e := fun h => evalR_pos_aux (by linarith) h n he
  have hder := hasDerivAt_evalR_wSum B h₀ n e (h₀ + v)
  have ev : h₀ + v - h₀ = v := by ring
  rw [ev] at hder
  rw [(hasDerivAt_tilt_comp (theta B) (Real.log B) k hder (hposh _)).deriv]
  have hT1 : 0 ≤ wSum (cpc B h₀ n e) (2 ^ n + 1) 1 v := wSum_nonneg hp _ _ _
  refine (abs_tiltDk_le k (theta_pos hB) (theta_lt_one hB) hR₀ hRR hT1).trans ?_
  have hρ : Real.exp (theta B * Real.log (evalR B h₀ n e)) = wRho B h₀ n e := by
    rw [wRho, Real.rpow_def_of_pos hR₀, mul_comm]
  have hρ0 : 0 ≤ wRho B h₀ n e := wRho_nonneg hB h₀ he
  rw [hρ]
  have hZ : |Real.log (evalR B (h₀ + v) n e) - Real.log B| ≤
      |wZ B h₀ n e| + expG B h₀ n e (s + v) :=
    abs_log_sub_le_shift hR₀ hRR hε
  have hε0 : 0 ≤ expG B h₀ n e (s + v) := expG_nonneg hB h₀ he (by linarith)
  apply mul_le_mul
  · calc wRho B h₀ n e / evalR B h₀ n e * wSum (cpc B h₀ n e) (2 ^ n + 1) 1 v
        = wRho B h₀ n e * (wSum (cpc B h₀ n e) (2 ^ n + 1) 1 v / evalR B h₀ n e) := by ring
      _ ≤ wRho B h₀ n e * (expG B h₀ n e (s + v) / s) := by
        apply mul_le_mul_of_nonneg_left _ hρ0
        rw [div_le_div_iff₀ hR₀ hs]
        linarith
  · gcongr
  · positivity
  · exact mul_nonneg hρ0 (div_nonneg hε0 hs.le)

theorem env_deriv2_bound {B : ℝ} (hB : 2 < B) (h₀ : ℝ) {n : ℕ} {e : Env n} (he : Env.Pos n e)
    {s v : ℝ} (hs : 0 < s) (hv : 0 ≤ v) :
    |iteratedDeriv 2 (fun h' => Real.exp (theta B * Real.log (evalR B h' n e)) *
        (Real.log (evalR B h' n e) - Real.log B) ^ 1) (h₀ + v)| ≤
      wRho B h₀ n e * (6 / s ^ 2) *
        ((|wZ B h₀ n e| + expG B h₀ n e (s + v) + 2) * expG B h₀ n e (s + v)) := by
  obtain ⟨hRR, hε, -, hT2s⟩ := env_shift_facts hB h₀ he hs.le hv
  have hp := cpc_nonneg hB h₀ he
  have hR₀ : 0 < evalR B h₀ n e := evalR_pos_aux (by linarith) h₀ n he
  have hposh : ∀ h, 0 < evalR B h n e := fun h => evalR_pos_aux (by linarith) h n he
  have h2 := iteratedDeriv_two_tilt (T0 := fun h => evalR B h n e)
    (T1 := fun h => wSum (cpc B h₀ n e) (2 ^ n + 1) 1 (h - h₀))
    (T2 := fun h => wSum (cpc B h₀ n e) (2 ^ n + 1) 2 (h - h₀)) (theta B) (Real.log B)
    (fun h => hasDerivAt_evalR_wSum B h₀ n e h) (fun h => hasDerivAt_wSum_sub _ _ 1 h₀ h)
    hposh (h₀ + v)
  have ev : h₀ + v - h₀ = v := by ring
  rw [h2, tiltD2, ev]
  have hT1 : 0 ≤ wSum (cpc B h₀ n e) (2 ^ n + 1) 1 v := wSum_nonneg hp _ _ _
  have hT2 : 0 ≤ wSum (cpc B h₀ n e) (2 ^ n + 1) 2 v := wSum_nonneg hp _ _ _
  have hCS : wSum (cpc B h₀ n e) (2 ^ n + 1) 1 v ^ 2 ≤
      evalR B (h₀ + v) n e * wSum (cpc B h₀ n e) (2 ^ n + 1) 2 v := by
    rw [evalR_eq_wSum B h₀ n e (h₀ + v), ev]; exact wSum_one_sq_le hp _ _
  refine (abs_tiltD2_le (theta_pos hB) (theta_lt_one hB) hR₀ hRR hT1 hT2 hCS).trans ?_
  have hZ : |Real.log (evalR B (h₀ + v) n e) - Real.log B| ≤
      |wZ B h₀ n e| + expG B h₀ n e (s + v) :=
    abs_log_sub_le_shift hR₀ hRR hε
  have hε0 : 0 ≤ expG B h₀ n e (s + v) := expG_nonneg hB h₀ he (by linarith)
  have hρ : Real.exp (theta B * Real.log (evalR B h₀ n e)) = wRho B h₀ n e := by
    rw [wRho, Real.rpow_def_of_pos hR₀, mul_comm]
  have hρ0 : 0 ≤ wRho B h₀ n e := wRho_nonneg hB h₀ he
  rw [hρ]
  have hT2' : wRho B h₀ n e / evalR B h₀ n e * wSum (cpc B h₀ n e) (2 ^ n + 1) 2 v ≤
      wRho B h₀ n e * (2 * expG B h₀ n e (s + v) / s ^ 2) := by
    calc wRho B h₀ n e / evalR B h₀ n e * wSum (cpc B h₀ n e) (2 ^ n + 1) 2 v
        = wRho B h₀ n e * (wSum (cpc B h₀ n e) (2 ^ n + 1) 2 v / evalR B h₀ n e) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hρ0
        rw [div_le_div_iff₀ hR₀ (by positivity)]
        nlinarith
  have hZ0 := abs_nonneg (wZ B h₀ n e)
  calc 3 * (|Real.log (evalR B (h₀ + v) n e) - Real.log B| + 2) *
        (wRho B h₀ n e / evalR B h₀ n e * wSum (cpc B h₀ n e) (2 ^ n + 1) 2 v)
      ≤ 3 * (|wZ B h₀ n e| + expG B h₀ n e (s + v) + 2) *
          (wRho B h₀ n e * (2 * expG B h₀ n e (s + v) / s ^ 2)) := by
        apply mul_le_mul _ hT2' (mul_nonneg (div_nonneg hρ0 hR₀.le) hT2) (by linarith)
        linarith
    _ = _ := by ring

theorem env_seven_halves_bound {B : ℝ} (hB : 2 < B) (h₀ : ℝ) {n : ℕ} {e : Env n}
    (he : Env.Pos n e) {u r : ℝ} (hu : 0 ≤ u) (hr : 0 < r) :
    evalR B (h₀ + u) n e ^ theta B *
        |Real.log (evalR B (h₀ + u) n e) - Real.log B| ^ ((7 : ℝ) / 2) ≤
      wRho B h₀ n e * (r ^ 3 * (|wZ B h₀ n e| + expG B h₀ n e u) ^ 2 +
        2 * (|wZ B h₀ n e| + expG B h₀ n e u) ^ 4 / r + r ^ 7 * expG B h₀ n e u ^ 8) := by
  obtain ⟨hRR, hε, -, -⟩ := env_shift_facts hB h₀ he (le_refl 0) hu
  rw [zero_add] at hε
  have hR₀ : 0 < evalR B h₀ n e := evalR_pos_aux (by linarith) h₀ n he
  have hR : 0 < evalR B (h₀ + u) n e := lt_of_lt_of_le hR₀ hRR
  have hε0 : 0 ≤ expG B h₀ n e u := expG_nonneg hB h₀ he hu
  have hZ : |Real.log (evalR B (h₀ + u) n e) - Real.log B| ≤ |wZ B h₀ n e| + expG B h₀ n e u :=
    abs_log_sub_le_shift hR₀ hRR hε
  have hratio : 1 ≤ evalR B (h₀ + u) n e / evalR B h₀ n e := by
    rw [le_div_iff₀ hR₀]; linarith
  have hρ0 : 0 ≤ wRho B h₀ n e := wRho_nonneg hB h₀ he
  have hRθ : evalR B (h₀ + u) n e ^ theta B ≤ wRho B h₀ n e * (1 + expG B h₀ n e u) := by
    have hne := (Real.rpow_pos_of_pos hR₀ (theta B)).ne'
    have e1 : evalR B (h₀ + u) n e ^ theta B =
        wRho B h₀ n e * (evalR B (h₀ + u) n e / evalR B h₀ n e) ^ theta B := by
      rw [wRho, Real.div_rpow hR.le hR₀.le]
      field_simp
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ hρ0
    calc _ ≤ evalR B (h₀ + u) n e / evalR B h₀ n e :=
          Real.rpow_le_self_of_one_le hratio (theta_lt_one hB).le
      _ ≤ _ := by linarith
  have hpow : |Real.log (evalR B (h₀ + u) n e) - Real.log B| ^ ((7 : ℝ) / 2) ≤
      (|wZ B h₀ n e| + expG B h₀ n e u) ^ ((7 : ℝ) / 2) :=
    Real.rpow_le_rpow (abs_nonneg _) hZ (by norm_num)
  have hpoly := poly72_le (add_nonneg (abs_nonneg (wZ B h₀ n e)) hε0) hε0 hr
  calc _ ≤ wRho B h₀ n e * (1 + expG B h₀ n e u) *
        (|wZ B h₀ n e| + expG B h₀ n e u) ^ ((7 : ℝ) / 2) :=
        mul_le_mul hRθ hpow (Real.rpow_nonneg (abs_nonneg _) _)
          (mul_nonneg hρ0 (by linarith))
    _ = wRho B h₀ n e * ((1 + expG B h₀ n e u) *
          (|wZ B h₀ n e| + expG B h₀ n e u) ^ ((7 : ℝ) / 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpoly hρ0

/-! ### Integrals over the environment -/

theorem integrable_tiltLog_env {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) (k n : ℕ) :
    Integrable (fun e => wRho B h n e * wZ B h n e ^ k) (envMeasure μ n) := by
  have hi : Integrable (fun x : ℝ => x ^ theta B * (Real.log x - Real.log B) ^ k)
      (lawR μ B h n) := by
    refine (integrable_absTiltedLogRpow_aux hpos hmean hB h n (s := (k : ℝ))
      (Nat.cast_nonneg k)).mono' (by fun_prop) ?_
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _), abs_pow,
      Real.rpow_natCast]
  rw [← map_evalR_envMeasure_aux μ B h n] at hi
  exact hi.comp_measurable (measurable_evalR B h n)

theorem integral_tiltLog_env {μ : Measure ℝ} [IsProbabilityMeasure μ] (B h : ℝ) (k n : ℕ) :
    ∫ e, wRho B h n e * wZ B h n e ^ k ∂(envMeasure μ n) = tiltedLogMoment μ B h k n := by
  simp only [wRho, wZ]
  rw [tiltedLogMoment, ← map_evalR_envMeasure_aux μ B h n,
    integral_map (measurable_evalR B h n).aemeasurable (by fun_prop)]

theorem absTilted_eq_env {μ : Measure ℝ} [IsProbabilityMeasure μ] (B h : ℝ) (n : ℕ) :
    absTiltedLogRpowMoment μ B h (7 / 2) n = ∫ e, evalR B h n e ^ theta B *
      |Real.log (evalR B h n e) - Real.log B| ^ ((7 : ℝ) / 2) ∂(envMeasure μ n) := by
  rw [absTiltedLogRpowMoment, ← map_evalR_envMeasure_aux μ B h n,
    integral_map (measurable_evalR B h n).aemeasurable (by fun_prop)]

/-- The reduction: an integrand dominated by a combination of
`R^θ ⟨e^{jσ C} - 1⟩` (`j = 1, 2, 4, 8`) and `R^θ Z^2`, `R^θ Z^4` at `h₀`. -/
theorem master_integral_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h₀ : ℝ) (n : ℕ)
    (σ c₁ c₂ c₄ c₈ d₂ d₄ : ℝ) {F : Env n → ℝ}
    (hF : ∀ᵐ e ∂(envMeasure μ n), |F e| ≤
      c₁ * (wRho B h₀ n e * expG B h₀ n e σ) + c₂ * (wRho B h₀ n e * expG B h₀ n e (2 * σ)) +
      c₄ * (wRho B h₀ n e * expG B h₀ n e (4 * σ)) +
      c₈ * (wRho B h₀ n e * expG B h₀ n e (8 * σ)) +
      d₂ * (wRho B h₀ n e * wZ B h₀ n e ^ 2) + d₄ * (wRho B h₀ n e * wZ B h₀ n e ^ 4)) :
    |∫ e, F e ∂(envMeasure μ n)| ≤
      c₁ * contactExpMoment μ B h₀ σ n + c₂ * contactExpMoment μ B h₀ (2 * σ) n +
      c₄ * contactExpMoment μ B h₀ (4 * σ) n + c₈ * contactExpMoment μ B h₀ (8 * σ) n +
      d₂ * tiltedLogMoment μ B h₀ 2 n + d₄ * tiltedLogMoment μ B h₀ 4 n := by
  have I : ∀ τ, Integrable (fun e => wRho B h₀ n e * expG B h₀ n e τ) (envMeasure μ n) :=
    fun τ => integrable_contactExpMoment_aux hpos hmean hB h₀ τ n
  have IZ : ∀ k, Integrable (fun e => wRho B h₀ n e * wZ B h₀ n e ^ k) (envMeasure μ n) :=
    fun k => integrable_tiltLog_env hpos hmean hB h₀ k n
  have J1 : Integrable (fun e => c₁ * (wRho B h₀ n e * expG B h₀ n e σ) +
      c₂ * (wRho B h₀ n e * expG B h₀ n e (2 * σ))) (envMeasure μ n) :=
    ((I σ).const_mul c₁).add ((I (2 * σ)).const_mul c₂)
  have J2 : Integrable (fun e => c₁ * (wRho B h₀ n e * expG B h₀ n e σ) +
      c₂ * (wRho B h₀ n e * expG B h₀ n e (2 * σ)) +
      c₄ * (wRho B h₀ n e * expG B h₀ n e (4 * σ))) (envMeasure μ n) :=
    J1.add ((I (4 * σ)).const_mul c₄)
  have J3 : Integrable (fun e => c₁ * (wRho B h₀ n e * expG B h₀ n e σ) +
      c₂ * (wRho B h₀ n e * expG B h₀ n e (2 * σ)) +
      c₄ * (wRho B h₀ n e * expG B h₀ n e (4 * σ)) +
      c₈ * (wRho B h₀ n e * expG B h₀ n e (8 * σ))) (envMeasure μ n) :=
    J2.add ((I (8 * σ)).const_mul c₈)
  have J4 : Integrable (fun e => c₁ * (wRho B h₀ n e * expG B h₀ n e σ) +
      c₂ * (wRho B h₀ n e * expG B h₀ n e (2 * σ)) +
      c₄ * (wRho B h₀ n e * expG B h₀ n e (4 * σ)) +
      c₈ * (wRho B h₀ n e * expG B h₀ n e (8 * σ)) +
      d₂ * (wRho B h₀ n e * wZ B h₀ n e ^ 2)) (envMeasure μ n) :=
    J3.add ((IZ 2).const_mul d₂)
  have J5 : Integrable (fun e => c₁ * (wRho B h₀ n e * expG B h₀ n e σ) +
      c₂ * (wRho B h₀ n e * expG B h₀ n e (2 * σ)) +
      c₄ * (wRho B h₀ n e * expG B h₀ n e (4 * σ)) +
      c₈ * (wRho B h₀ n e * expG B h₀ n e (8 * σ)) +
      d₂ * (wRho B h₀ n e * wZ B h₀ n e ^ 2) + d₄ * (wRho B h₀ n e * wZ B h₀ n e ^ 4))
      (envMeasure μ n) :=
    J4.add ((IZ 4).const_mul d₄)
  have hle := norm_integral_le_of_norm_le J5 (hF.mono fun e he => by rwa [Real.norm_eq_abs])
  rw [Real.norm_eq_abs] at hle
  refine hle.trans (le_of_eq ?_)
  rw [integral_add J4 ((IZ 4).const_mul d₄), integral_add J3 ((IZ 2).const_mul d₂),
    integral_add J2 ((I (8 * σ)).const_mul c₈), integral_add J1 ((I (4 * σ)).const_mul c₄),
    integral_add ((I σ).const_mul c₁) ((I (2 * σ)).const_mul c₂)]
  simp only [integral_const_mul]
  rw [integral_tiltLog_env B h₀ 2 n, integral_tiltLog_env B h₀ 4 n]
  rfl

theorem deriv_tiltedLogMoment_eq_integral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) (k n : ℕ) :
    deriv (fun h' => tiltedLogMoment μ B h' k n) h =
      ∫ e, deriv (fun h' => Real.exp (theta B * Real.log (evalR B h' n e)) *
        (Real.log (evalR B h' n e) - Real.log B) ^ k) h ∂(envMeasure μ n) := by
  rw [(hasDerivAt_tiltedLogMoment_aux hpos hmean hB h k n).deriv,
    tiltedLogMomentDeriv_eq_env hpos hB h k n]

theorem deriv_deriv_H_eq_integral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    deriv (deriv fun h' => tiltedLogMoment μ B h' 1 n) h =
      ∫ e, iteratedDeriv 2 (fun h' => Real.exp (theta B * Real.log (evalR B h' n e)) *
        (Real.log (evalR B h' n e) - Real.log B) ^ 1) h ∂(envMeasure μ n) := by
  have hderiv : (deriv fun h' => tiltedLogMoment μ B h' 1 n) = fun h' => ∫ e,
      deriv (fun h'' => Real.exp (theta B * Real.log (evalR B h'' n e)) *
        (Real.log (evalR B h'' n e) - Real.log B) ^ 1) h' ∂(envMeasure μ n) := by
    funext h'
    exact deriv_tiltedLogMoment_eq_integral hpos hmean hB h' 1 n
  have H := contact_field_envelope hpos hmean hB h 1 n
    (fun x => Real.exp (theta B * x) * (x - Real.log B) ^ (1 : ℕ))
    (contDiff_exp_mul_pow (theta B) (Real.log B) 1)
    (exists_iteratedDeriv_exp_mul_pow_bound (theta B) (Real.log B) 1) 1 (by norm_num)
  simp only [iteratedDeriv_one, one_add_one_eq_two, fieldMean] at H
  rw [hderiv]
  exact H.deriv

theorem tiltedMass_fun_eq (μ : Measure ℝ) (B : ℝ) (n : ℕ) :
    (fun h => tiltedMass μ B h n) = fun h => tiltedLogMoment μ B h 0 n := by
  funext h
  simp [tiltedMass, tiltedLogMoment]

/-! ### The window constants -/

/-- From the exponential clause of `prop:contact-moments`: a window size `η`
and a constant `Mx` with `E[R_n^θ ⟨e^{σ C_n} - 1⟩] ≤ Mx σ (n+1)` whenever
`0 ≤ σ (n+1)² ≤ 16 η`. -/
theorem window_setup {μ : Measure ℝ} {B h₀ : ℝ}
    (hContact : ∃ M L : ℝ,
      (∀ k n : ℕ, 1 ≤ k →
        contactMoment μ B h₀ k n ≤
          (k.factorial : ℝ) * M * L ^ (k - 1) * ((n : ℝ) + 1) ^ (2 * k - 1)) ∧
      ∀ (n : ℕ) (u : ℝ), 0 ≤ u → L * u * ((n : ℝ) + 1) ^ 2 < 1 →
        contactExpMoment μ B h₀ u n ≤
            M * u * ((n : ℝ) + 1) / (1 - L * u * ((n : ℝ) + 1) ^ 2) ∧
          tiltedMass μ B (h₀ + u) n - tiltedMass μ B h₀ n ≤
            M * u * ((n : ℝ) + 1) / (1 - L * u * ((n : ℝ) + 1) ^ 2)) :
    ∃ η Mx : ℝ, 0 < η ∧ 0 ≤ Mx ∧ ∀ (n : ℕ) (σ : ℝ), 0 ≤ σ → σ * ((n : ℝ) + 1) ^ 2 ≤ 16 * η →
      contactExpMoment μ B h₀ σ n ≤ Mx * σ * ((n : ℝ) + 1) := by
  obtain ⟨M, L, -, hexp⟩ := hContact
  have hL1 : 1 ≤ max L 1 := le_max_right _ _
  have hLL : L ≤ max L 1 := le_max_left _ _
  have hL0 : max L 1 ≠ 0 := by positivity
  refine ⟨1 / (64 * max L 1), 2 * max M 0, div_pos one_pos (by linarith),
    mul_nonneg zero_le_two (le_max_right _ _), ?_⟩
  intro n σ hσ hσt
  have ht2 : 0 ≤ ((n : ℝ) + 1) ^ 2 := by positivity
  have hx : 0 ≤ σ * ((n : ℝ) + 1) ^ 2 := mul_nonneg hσ ht2
  have hq : L * σ * ((n : ℝ) + 1) ^ 2 ≤ 1 / 4 := by
    have h1 : L * σ * ((n : ℝ) + 1) ^ 2 ≤ max L 1 * (σ * ((n : ℝ) + 1) ^ 2) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hLL hx
    have h2 : max L 1 * (σ * ((n : ℝ) + 1) ^ 2) ≤ max L 1 * (16 * (1 / (64 * max L 1))) :=
      mul_le_mul_of_nonneg_left hσt (by linarith)
    have h3 : max L 1 * (16 * (1 / (64 * max L 1))) = 1 / 4 := by
      rw [show max L 1 * (16 * (1 / (64 * max L 1))) = (max L 1 / max L 1) / 4 by ring,
        div_self hL0]
    linarith
  have hden : 0 < 1 - L * σ * ((n : ℝ) + 1) ^ 2 := by linarith
  refine (hexp n σ hσ (by linarith)).1.trans ?_
  rw [div_le_iff₀ hden]
  have ht0 : 0 ≤ σ * ((n : ℝ) + 1) := mul_nonneg hσ (by positivity)
  have hM : M * σ * ((n : ℝ) + 1) ≤ max M 0 * σ * ((n : ℝ) + 1) := by
    rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) ht0
  have hM0 : 0 ≤ max M 0 * σ * ((n : ℝ) + 1) := by
    rw [mul_assoc]; exact mul_nonneg (le_max_right _ _) ht0
  nlinarith [mul_nonneg hM0 (by linarith : (0 : ℝ) ≤ 1 / 4 - L * σ * ((n : ℝ) + 1) ^ 2)]

/-- In the window, with `s = η/t²`: `(t²/η) E[R^θ ⟨e^{c(s+v) C} - 1⟩] ≤ 2 c Mx t`
for `0 ≤ c ≤ 8`. -/
theorem window_exp_S {μ : Measure ℝ} {B h₀ η Mx : ℝ} (hη : 0 < η) (hMx : 0 ≤ Mx)
    (hE : ∀ (n : ℕ) (σ : ℝ), 0 ≤ σ → σ * ((n : ℝ) + 1) ^ 2 ≤ 16 * η →
      contactExpMoment μ B h₀ σ n ≤ Mx * σ * ((n : ℝ) + 1))
    {n : ℕ} {t : ℝ} (ht : (n : ℝ) + 1 = t) {v : ℝ} (hv : 0 ≤ v) (hvη : v * t ^ 2 ≤ η)
    {c : ℝ} (hc0 : 0 ≤ c) (hc8 : c ≤ 8) :
    t ^ 2 / η * contactExpMoment μ B h₀ (c * (η / t ^ 2 + v)) n ≤ 2 * c * Mx * t := by
  have ht0 : 0 < t := by rw [← ht]; positivity
  have ht2 : 0 < t ^ 2 := by positivity
  obtain ⟨s, hs_def⟩ : ∃ s, s = η / t ^ 2 := ⟨_, rfl⟩
  rw [← hs_def]
  have hs : 0 < s := by rw [hs_def]; exact div_pos hη ht2
  have hst : s * t ^ 2 = η := by rw [hs_def]; exact div_mul_cancel₀ η ht2.ne'
  have hvs : v ≤ s := by
    have h1 : v * t ^ 2 ≤ s * t ^ 2 := by rw [hst]; exact hvη
    exact le_of_mul_le_mul_right h1 ht2
  have hσ : 0 ≤ c * (s + v) := mul_nonneg hc0 (by linarith)
  have h2 : 0 ≤ (s + v) * t ^ 2 := mul_nonneg (by linarith) ht2.le
  have hσt : c * (s + v) * t ^ 2 ≤ 16 * η := by
    have h1 : (s + v) * t ^ 2 ≤ 2 * η := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) h2]
  have hX := hE n _ hσ (by rw [ht]; exact hσt)
  rw [ht] at hX
  have hX' : contactExpMoment μ B h₀ (c * (s + v)) n ≤ 2 * c * Mx * t * s := by
    calc _ ≤ Mx * (c * (s + v)) * t := hX
      _ ≤ Mx * (c * (2 * s)) * t := by
          apply mul_le_mul_of_nonneg_right _ ht0.le
          apply mul_le_mul_of_nonneg_left _ hMx
          apply mul_le_mul_of_nonneg_left _ hc0
          linarith
      _ = 2 * c * Mx * t * s := by ring
  have hSs : t ^ 2 / η * s = 1 := by
    rw [hs_def]; field_simp
  calc t ^ 2 / η * contactExpMoment μ B h₀ (c * (s + v)) n
      ≤ t ^ 2 / η * (2 * c * Mx * t * s) :=
        mul_le_mul_of_nonneg_left hX' (div_nonneg ht2.le hη.le)
    _ = 2 * c * Mx * t * (t ^ 2 / η * s) := by ring
    _ = 2 * c * Mx * t := by rw [hSs, mul_one]

/-! ### The derivative bounds in the window -/

/-- `|A_n'(h₀ + v)| ≤ 2 Mx (n+1)` in the window (no restriction on `n`). -/
theorem window_dA {μ : Measure ℝ} [IsProbabilityMeasure μ] (hpos : ∀ᵐ w ∂μ, 0 < w)
    (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) {h₀ η Mx : ℝ} (hη : 0 < η) (hMx : 0 ≤ Mx)
    (hE : ∀ (n : ℕ) (σ : ℝ), 0 ≤ σ → σ * ((n : ℝ) + 1) ^ 2 ≤ 16 * η →
      contactExpMoment μ B h₀ σ n ≤ Mx * σ * ((n : ℝ) + 1))
    {n : ℕ} {t : ℝ} (ht : (n : ℝ) + 1 = t) {v : ℝ} (hv : 0 ≤ v) (hvη : v * t ^ 2 ≤ η) :
    |deriv (fun h => tiltedMass μ B h n) (h₀ + v)| ≤ 2 * Mx * t := by
  have ht0 : 0 < t := by rw [← ht]; positivity
  obtain ⟨s, hs_def⟩ : ∃ s, s = η / t ^ 2 := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hs_def]; exact div_pos hη (by positivity)
  have hηne := hη.ne'
  have htne := ht0.ne'
  have hSε : ∀ x : ℝ, x / s = t ^ 2 / η * x := by
    intro x; rw [hs_def]; field_simp
  have hX1 := window_exp_S hη hMx hE ht hv hvη (c := 1) zero_le_one (by norm_num)
  rw [← hs_def, one_mul] at hX1
  rw [tiltedMass_fun_eq, deriv_tiltedLogMoment_eq_integral hpos hmean hB]
  have hmaster := master_integral_bound hpos hmean hB h₀ n (s + v) (t ^ 2 / η) 0 0 0 0 0
    (F := fun e => deriv (fun h' => Real.exp (theta B * Real.log (evalR B h' n e)) *
      (Real.log (evalR B h' n e) - Real.log B) ^ 0) (h₀ + v)) ?_
  · refine hmaster.trans ?_
    simp only [zero_mul, add_zero]
    linarith
  · filter_upwards [ae_envPos_aux hpos n] with e he
    have hb := env_derivK_bound hB h₀ he 0 hs hv
    refine hb.trans (le_of_eq ?_)
    rw [hSε]
    simp only [pow_zero, Nat.cast_zero, zero_mul, add_zero, mul_one]
    ring

/-- `|K_n'(h₀ + v)| ≤ C (n+1)³` in the window. -/
theorem window_dK {μ : Measure ℝ} [IsProbabilityMeasure μ] (hpos : ∀ᵐ w ∂μ, 0 < w)
    (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) {h₀ η Mx : ℝ} (hη : 0 < η) (hMx : 0 ≤ Mx)
    (hE : ∀ (n : ℕ) (σ : ℝ), 0 ≤ σ → σ * ((n : ℝ) + 1) ^ 2 ≤ 16 * η →
      contactExpMoment μ B h₀ σ n ≤ Mx * σ * ((n : ℝ) + 1))
    {n : ℕ} {t : ℝ} (ht : (n : ℝ) + 1 = t) {C₀ : ℝ}
    (hL : tiltedLogMoment μ B h₀ 4 n ≤ C₀ * t ^ 3) {v : ℝ} (hv : 0 ≤ v) (hvη : v * t ^ 2 ≤ η) :
    |deriv (fun h => tiltedLogMoment μ B h 2 n) (h₀ + v)| ≤
      (58 * Mx + 2 * C₀ * η⁻¹) * t ^ 3 := by
  have ht0 : 0 < t := by rw [← ht]; positivity
  have ht1 : 1 ≤ t := by rw [← ht]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  obtain ⟨s, hs_def⟩ : ∃ s, s = η / t ^ 2 := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hs_def]; exact div_pos hη (by positivity)
  have hηne := hη.ne'
  have htne := ht0.ne'
  have hSε : ∀ x : ℝ, x / s = t ^ 2 / η * x := by
    intro x; rw [hs_def]; field_simp
  have htw : t * t⁻¹ = 1 := mul_inv_cancel₀ htne
  have hS0 : 0 ≤ t ^ 2 / η := div_nonneg (by positivity) hη.le
  have hX1 := window_exp_S hη hMx hE ht hv hvη (c := 1) zero_le_one (by norm_num)
  have hX2 := window_exp_S hη hMx hE ht hv hvη (c := 2) (by norm_num) (by norm_num)
  have hX4 := window_exp_S hη hMx hE ht hv hvη (c := 4) (by norm_num) (by norm_num)
  rw [← hs_def, one_mul] at hX1
  rw [← hs_def] at hX2 hX4
  rw [deriv_tiltedLogMoment_eq_integral hpos hmean hB]
  have hmaster := master_integral_bound hpos hmean hB h₀ n (s + v) (t ^ 2 / η)
    ((2 * t ^ 2 + 4) * (t ^ 2 / η)) (4 * (t ^ 2 / η)) 0 0 (2 * t⁻¹ ^ 2 * (t ^ 2 / η))
    (F := fun e => deriv (fun h' => Real.exp (theta B * Real.log (evalR B h' n e)) *
      (Real.log (evalR B h' n e) - Real.log B) ^ 2) (h₀ + v)) ?_
  · refine hmaster.trans ?_
    have h1 := mul_le_mul_of_nonneg_left hX2 (by positivity : (0 : ℝ) ≤ 2 * t ^ 2 + 4)
    have h2 := mul_le_mul_of_nonneg_left hL
      (by positivity : (0 : ℝ) ≤ 2 * t⁻¹ ^ 2 * (t ^ 2 / η))
    have q : 2 * t⁻¹ ^ 2 * (t ^ 2 / η) * (C₀ * t ^ 3) = 2 * C₀ * η⁻¹ * t ^ 3 := by
      field_simp
    have h3 : t ≤ t ^ 3 := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 hMx
    nlinarith
  · filter_upwards [ae_envPos_aux hpos n] with e he
    have hb := env_derivK_bound hB h₀ he 2 hs hv
    have hε0 : 0 ≤ expG B h₀ n e (s + v) := expG_nonneg hB h₀ he (by linarith)
    have hE2 := expG_sq_le hB h₀ he (by linarith : 0 ≤ s + v)
    have hE4 := expG_pow4_le hB h₀ he (by linarith : 0 ≤ s + v)
    have hρ0 := wRho_nonneg hB h₀ he
    have hpoly := polyK_le (a := |wZ B h₀ n e|) hε0 htw
    have ha4 : |wZ B h₀ n e| ^ 4 = wZ B h₀ n e ^ 4 := Even.pow_abs ⟨2, rfl⟩ _
    have hk : ((2 : ℕ) : ℝ) * (|wZ B h₀ n e| + expG B h₀ n e (s + v)) ^ (2 - 1) =
        2 * (|wZ B h₀ n e| + expG B h₀ n e (s + v)) := by norm_num
    rw [hk, hSε] at hb
    refine hb.trans ?_
    rw [ha4] at hpoly
    have hSρ : 0 ≤ t ^ 2 / η * wRho B h₀ n e := mul_nonneg hS0 hρ0
    have step : expG B h₀ n e (s + v) * ((|wZ B h₀ n e| + expG B h₀ n e (s + v)) ^ 2 +
        2 * (|wZ B h₀ n e| + expG B h₀ n e (s + v))) ≤
        expG B h₀ n e (s + v) + (2 * t ^ 2 + 4) * expG B h₀ n e (2 * (s + v)) +
          4 * expG B h₀ n e (4 * (s + v)) + 2 * t⁻¹ ^ 2 * wZ B h₀ n e ^ 4 := by
      have h1 := mul_le_mul_of_nonneg_left hE2 (by positivity : (0 : ℝ) ≤ 2 * t ^ 2 + 4)
      have h2 := mul_le_mul_of_nonneg_left hE4 (by norm_num : (0 : ℝ) ≤ 4)
      linarith
    calc wRho B h₀ n e * (t ^ 2 / η * expG B h₀ n e (s + v)) *
          ((|wZ B h₀ n e| + expG B h₀ n e (s + v)) ^ 2 +
            2 * (|wZ B h₀ n e| + expG B h₀ n e (s + v)))
        = t ^ 2 / η * wRho B h₀ n e * (expG B h₀ n e (s + v) *
          ((|wZ B h₀ n e| + expG B h₀ n e (s + v)) ^ 2 +
            2 * (|wZ B h₀ n e| + expG B h₀ n e (s + v)))) := by ring
      _ ≤ t ^ 2 / η * wRho B h₀ n e * (expG B h₀ n e (s + v) +
          (2 * t ^ 2 + 4) * expG B h₀ n e (2 * (s + v)) +
          4 * expG B h₀ n e (4 * (s + v)) + 2 * t⁻¹ ^ 2 * wZ B h₀ n e ^ 4) :=
        mul_le_mul_of_nonneg_left step hSρ
      _ = _ := by ring

/-- `|J_n'(h₀ + v)| ≤ C (n+1)⁴` in the window. -/
theorem window_dJ {μ : Measure ℝ} [IsProbabilityMeasure μ] (hpos : ∀ᵐ w ∂μ, 0 < w)
    (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) {h₀ η Mx : ℝ} (hη : 0 < η) (hMx : 0 ≤ Mx)
    (hE : ∀ (n : ℕ) (σ : ℝ), 0 ≤ σ → σ * ((n : ℝ) + 1) ^ 2 ≤ 16 * η →
      contactExpMoment μ B h₀ σ n ≤ Mx * σ * ((n : ℝ) + 1))
    {n : ℕ} {t : ℝ} (ht : (n : ℝ) + 1 = t) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hL : tiltedLogMoment μ B h₀ 4 n ≤ C₀ * t ^ 3) {v : ℝ} (hv : 0 ≤ v) (hvη : v * t ^ 2 ≤ η) :
    |deriv (fun h => tiltedLogMoment μ B h 3 n) (h₀ + v)| ≤
      (148 * Mx + 7 * C₀ * η⁻¹) * t ^ 4 := by
  have ht0 : 0 < t := by rw [← ht]; positivity
  have ht1 : 1 ≤ t := by rw [← ht]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  obtain ⟨s, hs_def⟩ : ∃ s, s = η / t ^ 2 := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hs_def]; exact div_pos hη (by positivity)
  have hηne := hη.ne'
  have htne := ht0.ne'
  have hSε : ∀ x : ℝ, x / s = t ^ 2 / η * x := by
    intro x; rw [hs_def]; field_simp
  have htw : t * t⁻¹ = 1 := mul_inv_cancel₀ htne
  have hS0 : 0 ≤ t ^ 2 / η := div_nonneg (by positivity) hη.le
  have hX2 := window_exp_S hη hMx hE ht hv hvη (c := 2) (by norm_num) (by norm_num)
  have hX4 := window_exp_S hη hMx hE ht hv hvη (c := 4) (by norm_num) (by norm_num)
  rw [← hs_def] at hX2 hX4
  rw [deriv_tiltedLogMoment_eq_integral hpos hmean hB]
  have hmaster := master_integral_bound hpos hmean hB h₀ n (s + v) 0
    ((3 * t ^ 2 + 6) * (t ^ 2 / η)) ((4 * t ^ 3 + 10) * (t ^ 2 / η)) 0 0
    ((4 * t⁻¹ + 3 * t⁻¹ ^ 2) * (t ^ 2 / η))
    (F := fun e => deriv (fun h' => Real.exp (theta B * Real.log (evalR B h' n e)) *
      (Real.log (evalR B h' n e) - Real.log B) ^ 3) (h₀ + v)) ?_
  · refine hmaster.trans ?_
    have h1 := mul_le_mul_of_nonneg_left hX2 (by positivity : (0 : ℝ) ≤ 3 * t ^ 2 + 6)
    have h1' := mul_le_mul_of_nonneg_left hX4 (by positivity : (0 : ℝ) ≤ 4 * t ^ 3 + 10)
    have h2 := mul_le_mul_of_nonneg_left hL
      (by positivity : (0 : ℝ) ≤ (4 * t⁻¹ + 3 * t⁻¹ ^ 2) * (t ^ 2 / η))
    have q : (4 * t⁻¹ + 3 * t⁻¹ ^ 2) * (t ^ 2 / η) * (C₀ * t ^ 3) =
        4 * C₀ * η⁻¹ * t ^ 4 + 3 * C₀ * η⁻¹ * t ^ 3 := by
      field_simp
    have h3 : t ≤ t ^ 4 := by nlinarith [pow_le_pow_right₀ ht1 (show 1 ≤ 3 by norm_num)]
    have h3' : t ^ 3 ≤ t ^ 4 := pow_le_pow_right₀ ht1 (by norm_num)
    have h4 := mul_le_mul_of_nonneg_left h3 hMx
    have h4' := mul_le_mul_of_nonneg_left h3' hMx
    have h5 := mul_le_mul_of_nonneg_left h3' (mul_nonneg hC₀ (inv_nonneg.mpr hη.le))
    nlinarith
  · filter_upwards [ae_envPos_aux hpos n] with e he
    have hb := env_derivK_bound hB h₀ he 3 hs hv
    have hε0 : 0 ≤ expG B h₀ n e (s + v) := expG_nonneg hB h₀ he (by linarith)
    have hE2 := expG_sq_le hB h₀ he (by linarith : 0 ≤ s + v)
    have hE4 := expG_pow4_le hB h₀ he (by linarith : 0 ≤ s + v)
    have hρ0 := wRho_nonneg hB h₀ he
    have hpoly := polyJ_le (abs_nonneg (wZ B h₀ n e)) hε0 ht0.le (inv_nonneg.mpr ht0.le) htw
    have ha4 : |wZ B h₀ n e| ^ 4 = wZ B h₀ n e ^ 4 := Even.pow_abs ⟨2, rfl⟩ _
    have hk : ((3 : ℕ) : ℝ) * (|wZ B h₀ n e| + expG B h₀ n e (s + v)) ^ (3 - 1) =
        3 * (|wZ B h₀ n e| + expG B h₀ n e (s + v)) ^ 2 := by norm_num
    rw [hk, hSε] at hb
    refine hb.trans ?_
    rw [ha4] at hpoly
    have hSρ : 0 ≤ t ^ 2 / η * wRho B h₀ n e := mul_nonneg hS0 hρ0
    have step : expG B h₀ n e (s + v) * ((|wZ B h₀ n e| + expG B h₀ n e (s + v)) ^ 3 +
        3 * (|wZ B h₀ n e| + expG B h₀ n e (s + v)) ^ 2) ≤
        (3 * t ^ 2 + 6) * expG B h₀ n e (2 * (s + v)) +
          (4 * t ^ 3 + 10) * expG B h₀ n e (4 * (s + v)) +
          (4 * t⁻¹ + 3 * t⁻¹ ^ 2) * wZ B h₀ n e ^ 4 := by
      have h1 := mul_le_mul_of_nonneg_left hE2 (by positivity : (0 : ℝ) ≤ 3 * t ^ 2 + 6)
      have h2 := mul_le_mul_of_nonneg_left hE4 (by positivity : (0 : ℝ) ≤ 4 * t ^ 3 + 10)
      linarith
    calc wRho B h₀ n e * (t ^ 2 / η * expG B h₀ n e (s + v)) *
          ((|wZ B h₀ n e| + expG B h₀ n e (s + v)) ^ 3 +
            3 * (|wZ B h₀ n e| + expG B h₀ n e (s + v)) ^ 2)
        = t ^ 2 / η * wRho B h₀ n e * (expG B h₀ n e (s + v) *
          ((|wZ B h₀ n e| + expG B h₀ n e (s + v)) ^ 3 +
            3 * (|wZ B h₀ n e| + expG B h₀ n e (s + v)) ^ 2)) := by ring
      _ ≤ t ^ 2 / η * wRho B h₀ n e * ((3 * t ^ 2 + 6) * expG B h₀ n e (2 * (s + v)) +
          (4 * t ^ 3 + 10) * expG B h₀ n e (4 * (s + v)) +
          (4 * t⁻¹ + 3 * t⁻¹ ^ 2) * wZ B h₀ n e ^ 4) :=
        mul_le_mul_of_nonneg_left step hSρ
      _ = _ := by ring

/-- `|H_n''(h₀ + v)| ≤ C (n+1)⁴` in the window. -/
theorem window_dH {μ : Measure ℝ} [IsProbabilityMeasure μ] (hpos : ∀ᵐ w ∂μ, 0 < w)
    (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) {h₀ η Mx : ℝ} (hη : 0 < η) (hMx : 0 ≤ Mx)
    (hE : ∀ (n : ℕ) (σ : ℝ), 0 ≤ σ → σ * ((n : ℝ) + 1) ^ 2 ≤ 16 * η →
      contactExpMoment μ B h₀ σ n ≤ Mx * σ * ((n : ℝ) + 1))
    {n : ℕ} {t : ℝ} (ht : (n : ℝ) + 1 = t) {C₀ : ℝ}
    (hK : tiltedLogMoment μ B h₀ 2 n ≤ C₀ * t) {v : ℝ} (hv : 0 ≤ v) (hvη : v * t ^ 2 ≤ η) :
    |deriv (deriv fun h => tiltedLogMoment μ B h 1 n) (h₀ + v)| ≤
      (60 * Mx * η⁻¹ + 3 * C₀ * η⁻¹ ^ 2) * t ^ 4 := by
  have ht0 : 0 < t := by rw [← ht]; positivity
  have ht1 : 1 ≤ t := by rw [← ht]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  obtain ⟨s, hs_def⟩ : ∃ s, s = η / t ^ 2 := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hs_def]; exact div_pos hη (by positivity)
  have hηne := hη.ne'
  have htne := ht0.ne'
  have htw : t * t⁻¹ = 1 := mul_inv_cancel₀ htne
  have hS0 : 0 ≤ t ^ 2 / η := div_nonneg (by positivity) hη.le
  have hX1 := window_exp_S hη hMx hE ht hv hvη (c := 1) zero_le_one (by norm_num)
  have hX2 := window_exp_S hη hMx hE ht hv hvη (c := 2) (by norm_num) (by norm_num)
  rw [← hs_def, one_mul] at hX1
  rw [← hs_def] at hX2
  rw [deriv_deriv_H_eq_integral hpos hmean hB]
  have hmaster := master_integral_bound hpos hmean hB h₀ n (s + v) (12 * (t ^ 2 / η) ^ 2)
    (6 * (t ^ 2 / η) ^ 2 * (t / 2 + 1)) 0 0 (3 * t⁻¹ * (t ^ 2 / η) ^ 2) 0
    (F := fun e => iteratedDeriv 2 (fun h' => Real.exp (theta B * Real.log (evalR B h' n e)) *
      (Real.log (evalR B h' n e) - Real.log B) ^ 1) (h₀ + v)) ?_
  · refine hmaster.trans ?_
    have a1 := mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ 12 * (t ^ 2 / η))
    have a2 := mul_le_mul_of_nonneg_left hX2
      (mul_nonneg (by positivity : (0 : ℝ) ≤ 6 * (t ^ 2 / η)) (by linarith : (0 : ℝ) ≤ t / 2 + 1))
    have a3 := mul_le_mul_of_nonneg_left hK
      (by positivity : (0 : ℝ) ≤ 3 * t⁻¹ * (t ^ 2 / η) ^ 2)
    have q1 : 12 * (t ^ 2 / η) * (2 * 1 * Mx * t) = 24 * Mx * η⁻¹ * t ^ 3 := by ring
    have q2 : 6 * (t ^ 2 / η) * (t / 2 + 1) * (2 * 2 * Mx * t) =
        12 * Mx * η⁻¹ * t ^ 4 + 24 * Mx * η⁻¹ * t ^ 3 := by ring
    have q3 : 3 * t⁻¹ * (t ^ 2 / η) ^ 2 * (C₀ * t) = 3 * C₀ * η⁻¹ ^ 2 * t ^ 4 := by
      field_simp
    have h3' : t ^ 3 ≤ t ^ 4 := pow_le_pow_right₀ ht1 (by norm_num)
    have a4 := mul_le_mul_of_nonneg_left h3' (mul_nonneg hMx (inv_nonneg.mpr hη.le))
    nlinarith
  · filter_upwards [ae_envPos_aux hpos n] with e he
    have hb := env_deriv2_bound hB h₀ he hs hv
    have hE2 := expG_sq_le hB h₀ he (by linarith : 0 ≤ s + v)
    have hρ0 := wRho_nonneg hB h₀ he
    have hpoly := polyH_le (a := |wZ B h₀ n e|) (ε := expG B h₀ n e (s + v)) ht0.le htw
    have ha2 : |wZ B h₀ n e| ^ 2 = wZ B h₀ n e ^ 2 := sq_abs _
    rw [ha2] at hpoly
    have hS2 : 6 / s ^ 2 = 6 * (t ^ 2 / η) ^ 2 := by rw [hs_def]; field_simp
    rw [hS2] at hb
    refine hb.trans ?_
    have step : (|wZ B h₀ n e| + expG B h₀ n e (s + v) + 2) * expG B h₀ n e (s + v) ≤
        t⁻¹ / 2 * wZ B h₀ n e ^ 2 + (t / 2 + 1) * expG B h₀ n e (2 * (s + v)) +
          2 * expG B h₀ n e (s + v) := by
      have h1 := mul_le_mul_of_nonneg_left hE2 (by linarith : (0 : ℝ) ≤ t / 2 + 1)
      linarith
    calc wRho B h₀ n e * (6 * (t ^ 2 / η) ^ 2) *
          ((|wZ B h₀ n e| + expG B h₀ n e (s + v) + 2) * expG B h₀ n e (s + v))
        ≤ wRho B h₀ n e * (6 * (t ^ 2 / η) ^ 2) * (t⁻¹ / 2 * wZ B h₀ n e ^ 2 +
          (t / 2 + 1) * expG B h₀ n e (2 * (s + v)) + 2 * expG B h₀ n e (s + v)) :=
          mul_le_mul_of_nonneg_left step (mul_nonneg hρ0 (by positivity))
      _ = _ := by ring

/-- `E[R_n(h₀+u)^θ |log R_n(h₀+u) - a|^{7/2}] ≤ C (n+1)^{5/2}` in the window, with
`r = √(n+1)`. -/
theorem window_seven_halves {μ : Measure ℝ} [IsProbabilityMeasure μ] (hpos : ∀ᵐ w ∂μ, 0 < w)
    (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) {h₀ η Mx : ℝ} (hη : 0 < η) (hMx : 0 ≤ Mx)
    (hE : ∀ (n : ℕ) (σ : ℝ), 0 ≤ σ → σ * ((n : ℝ) + 1) ^ 2 ≤ 16 * η →
      contactExpMoment μ B h₀ σ n ≤ Mx * σ * ((n : ℝ) + 1))
    {n : ℕ} {r : ℝ} (hr1 : 1 ≤ r) (ht : (n : ℝ) + 1 = r ^ 2) {C₀ : ℝ}
    (hK : tiltedLogMoment μ B h₀ 2 n ≤ C₀ * r ^ 2)
    (hL : tiltedLogMoment μ B h₀ 4 n ≤ C₀ * (r ^ 2) ^ 3)
    {u : ℝ} (hu : 0 ≤ u) (huη : u * (r ^ 2) ^ 2 ≤ η) :
    absTiltedLogRpowMoment μ B (h₀ + u) (7 / 2) n ≤ (76 * Mx * η + 18 * C₀) * r ^ 5 := by
  have hr : 0 < r := by linarith
  have hX : ∀ c : ℝ, 0 ≤ c → c ≤ 8 →
      contactExpMoment μ B h₀ (c * u) n ≤ Mx * (c * u) * r ^ 2 := by
    intro c hc0 hc8
    have hcu : 0 ≤ u * (r ^ 2) ^ 2 := mul_nonneg hu (by positivity)
    have h := hE n (c * u) (mul_nonneg hc0 hu) (by
      rw [ht]; nlinarith [mul_le_mul_of_nonneg_right hc8 hcu])
    rwa [ht] at h
  rw [absTilted_eq_env]
  have hmaster := master_integral_bound hpos hmean hB h₀ n u 0 (2 * r ^ 3) (16 / r) (r ^ 7)
    (2 * r ^ 3) (16 / r)
    (F := fun e => evalR B (h₀ + u) n e ^ theta B *
      |Real.log (evalR B (h₀ + u) n e) - Real.log B| ^ ((7 : ℝ) / 2)) ?_
  · refine (le_abs_self _).trans (hmaster.trans ?_)
    have hX2 := hX 2 (by norm_num) (by norm_num)
    have hX4 := hX 4 (by norm_num) (by norm_num)
    have hX8 := hX 8 (by norm_num) (by norm_num)
    have hr5 : 1 ≤ r ^ 5 := one_le_pow₀ hr1
    have hrr5 : r ≤ r ^ 5 := by
      calc r = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ 5 := pow_le_pow_right₀ hr1 (by norm_num)
    have hrr4 : r ≤ r ^ 4 := by
      calc r = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ 4 := pow_le_pow_right₀ hr1 (by norm_num)
    have hur : u * r ^ 4 ≤ η := by
      have e : (r ^ 2) ^ 2 = r ^ 4 := by ring
      rw [e] at huη; exact huη
    have hMxη : 0 ≤ Mx * η := mul_nonneg hMx hη.le
    have T2 : 2 * r ^ 3 * contactExpMoment μ B h₀ (2 * u) n ≤ 4 * Mx * η * r ^ 5 := by
      have h1 := mul_le_mul_of_nonneg_left hX2 (by positivity : (0 : ℝ) ≤ 2 * r ^ 3)
      have h2 := mul_le_mul_of_nonneg_left hur
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hMx) hr.le)
      have h3 := mul_le_mul_of_nonneg_left hrr5 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hMxη)
      nlinarith
    have T4 : 16 / r * contactExpMoment μ B h₀ (4 * u) n ≤ 64 * Mx * η * r ^ 5 := by
      have h1 := mul_le_mul_of_nonneg_left hX4 (div_nonneg (by norm_num : (0 : ℝ) ≤ 16) hr.le)
      have e : 16 / r * (Mx * (4 * u) * r ^ 2) = 64 * Mx * (u * r) := by
        rw [div_mul_eq_mul_div, div_eq_iff hr.ne']; ring
      have h2 : u * r ≤ η := le_trans (mul_le_mul_of_nonneg_left hrr4 hu) hur
      have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) hMx)
      have h4 := mul_le_mul_of_nonneg_left hr5 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) hMxη)
      nlinarith
    have T8 : r ^ 7 * contactExpMoment μ B h₀ (8 * u) n ≤ 8 * Mx * η * r ^ 5 := by
      have h1 := mul_le_mul_of_nonneg_left hX8 (by positivity : (0 : ℝ) ≤ r ^ 7)
      have h2 := mul_le_mul_of_nonneg_left hur
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hMx) (by positivity : (0 : ℝ) ≤ r ^ 5))
      nlinarith
    have TK : 2 * r ^ 3 * tiltedLogMoment μ B h₀ 2 n ≤ 2 * C₀ * r ^ 5 := by
      have h1 := mul_le_mul_of_nonneg_left hK (by positivity : (0 : ℝ) ≤ 2 * r ^ 3)
      nlinarith
    have TL : 16 / r * tiltedLogMoment μ B h₀ 4 n ≤ 16 * C₀ * r ^ 5 := by
      have h1 := mul_le_mul_of_nonneg_left hL (div_nonneg (by norm_num : (0 : ℝ) ≤ 16) hr.le)
      have e : 16 / r * (C₀ * (r ^ 2) ^ 3) = 16 * C₀ * r ^ 5 := by
        rw [div_mul_eq_mul_div, div_eq_iff hr.ne']; ring
      linarith
    nlinarith
  · filter_upwards [ae_envPos_aux hpos n] with e he
    have hR : 0 < evalR B (h₀ + u) n e := evalR_pos_aux (by linarith) _ n he
    have hF0 : 0 ≤ evalR B (h₀ + u) n e ^ theta B *
        |Real.log (evalR B (h₀ + u) n e) - Real.log B| ^ ((7 : ℝ) / 2) :=
      mul_nonneg (Real.rpow_nonneg hR.le _) (Real.rpow_nonneg (abs_nonneg _) _)
    rw [abs_of_nonneg hF0]
    refine (env_seven_halves_bound hB h₀ he hu hr).trans ?_
    have hε0 := expG_nonneg hB h₀ he hu
    have hE2 := expG_sq_le hB h₀ he hu
    have hE4 := expG_pow4_le hB h₀ he hu
    have hE8 := expG_pow8_le hB h₀ he hu
    have hρ0 := wRho_nonneg hB h₀ he
    have ha2 : |wZ B h₀ n e| ^ 2 = wZ B h₀ n e ^ 2 := sq_abs _
    have ha4 : |wZ B h₀ n e| ^ 4 = wZ B h₀ n e ^ 4 := Even.pow_abs ⟨2, rfl⟩ _
    have ha0 := abs_nonneg (wZ B h₀ n e)
    have hb2 : (|wZ B h₀ n e| + expG B h₀ n e u) ^ 2 ≤
        2 * |wZ B h₀ n e| ^ 2 + 2 * expG B h₀ n e u ^ 2 := by
      nlinarith [sq_nonneg (|wZ B h₀ n e| - expG B h₀ n e u)]
    have hb4 : (|wZ B h₀ n e| + expG B h₀ n e u) ^ 4 ≤
        8 * |wZ B h₀ n e| ^ 4 + 8 * expG B h₀ n e u ^ 4 := by
      have := pow_le_pow_left₀ (sq_nonneg _) hb2 2
      nlinarith [sq_nonneg (|wZ B h₀ n e| ^ 2 - expG B h₀ n e u ^ 2)]
    rw [ha2] at hb2
    rw [ha4] at hb4
    have hr3 : 0 ≤ r ^ 3 := (pow_pos hr 3).le
    have hr7 : 0 ≤ r ^ 7 := (pow_pos hr 7).le
    have h16 : 0 ≤ 16 / r := div_nonneg (by norm_num) hr.le
    have step : r ^ 3 * (|wZ B h₀ n e| + expG B h₀ n e u) ^ 2 +
        2 * (|wZ B h₀ n e| + expG B h₀ n e u) ^ 4 / r + r ^ 7 * expG B h₀ n e u ^ 8 ≤
        2 * r ^ 3 * expG B h₀ n e (2 * u) + 16 / r * expG B h₀ n e (4 * u) +
          r ^ 7 * expG B h₀ n e (8 * u) + 2 * r ^ 3 * wZ B h₀ n e ^ 2 +
          16 / r * wZ B h₀ n e ^ 4 := by
      have e1 : 2 * (|wZ B h₀ n e| + expG B h₀ n e u) ^ 4 / r =
          2 / r * (|wZ B h₀ n e| + expG B h₀ n e u) ^ 4 := by ring
      rw [e1]
      have h1 := mul_le_mul_of_nonneg_left hb2 hr3
      have h2 := mul_le_mul_of_nonneg_left hb4 (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr.le)
      have h3 := mul_le_mul_of_nonneg_left hE2 hr3
      have h4 := mul_le_mul_of_nonneg_left hE4 h16
      have h5 := mul_le_mul_of_nonneg_left hE8 hr7
      have e2 : 2 / r * (8 * wZ B h₀ n e ^ 4 + 8 * expG B h₀ n e u ^ 4) =
          16 / r * wZ B h₀ n e ^ 4 + 16 / r * expG B h₀ n e u ^ 4 := by ring
      linarith
    calc wRho B h₀ n e * (r ^ 3 * (|wZ B h₀ n e| + expG B h₀ n e u) ^ 2 +
          2 * (|wZ B h₀ n e| + expG B h₀ n e u) ^ 4 / r + r ^ 7 * expG B h₀ n e u ^ 8)
        ≤ wRho B h₀ n e * (2 * r ^ 3 * expG B h₀ n e (2 * u) + 16 / r * expG B h₀ n e (4 * u) +
          r ^ 7 * expG B h₀ n e (8 * u) + 2 * r ^ 3 * wZ B h₀ n e ^ 2 +
          16 / r * wZ B h₀ n e ^ 4) :=
          mul_le_mul_of_nonneg_left step hρ0
      _ = _ := by ring

/-! ### The product ratio -/

theorem K_le_of {K P C₀ t : ℝ} (hC₀ : 0 < C₀) (ht : 0 ≤ t) (hP : P ≤ C₀ * t ^ 2)
    (hK : K ^ 2 ≤ C₀ * P) : K ≤ C₀ * t := by
  have h1 : K ^ 2 ≤ (C₀ * t) ^ 2 := by nlinarith
  nlinarith [mul_nonneg hC₀.le ht]

theorem tiltedMass_lower {μ : Measure ℝ} {B h₀ C₀ : ℝ} (hC₀ : 0 < C₀)
    (hb : ∀ n : ℕ, 1 ≤ n → ((n : ℝ) + 1) ^ 2 / C₀ ≤ tiltedProduct μ B h₀ n ∧
      tiltedProduct μ B h₀ n ≤ C₀ * ((n : ℝ) + 1) ^ 2) (j : ℕ) :
    min (4 / C₀) (1 / C₀ ^ 2) ≤ tiltedMass μ B h₀ j := by
  have hsucc : tiltedProduct μ B h₀ (j + 1) = tiltedProduct μ B h₀ j * tiltedMass μ B h₀ j :=
    Finset.prod_range_succ _ _
  have hs := (hb (j + 1) (by omega)).1
  rw [hsucc] at hs
  push_cast at hs
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have h0 : tiltedProduct μ B h₀ 0 = 1 := Finset.prod_range_zero _
    rw [h0, one_mul] at hs
    apply min_le_of_left_le
    norm_num at hs
    linarith
  · obtain ⟨hlo, hhi⟩ := hb j hj
    apply min_le_of_right_le
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hPpos : 0 < tiltedProduct μ B h₀ j := lt_of_lt_of_le (div_pos (by positivity) hC₀) hlo
    have hs' : ((j : ℝ) + 1 + 1) ^ 2 ≤ C₀ * (tiltedProduct μ B h₀ j * tiltedMass μ B h₀ j) := by
      rw [div_le_iff₀ hC₀] at hs; linarith
    have hApos : 0 < tiltedMass μ B h₀ j := by
      by_contra hneg
      have h1 := mul_le_mul_of_nonneg_left (not_lt.mp hneg) hPpos.le
      have h2 := mul_le_mul_of_nonneg_left h1 hC₀.le
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    have h3 := mul_le_mul_of_nonneg_left hhi (mul_nonneg hC₀.le hApos.le)
    nlinarith [mul_pos hj1 hj1]

theorem prod_ratio_bound {A A' : ℕ → ℝ} {c₀ CA u t η : ℝ} (hc₀ : 0 < c₀) (hCA : 0 ≤ CA)
    (hu : 0 ≤ u) {n : ℕ} (ht : (n : ℝ) + 1 = t)
    (hA0 : ∀ j, c₀ ≤ A j) (hdA : ∀ j < n, |A' j - A j| ≤ CA * ((j : ℝ) + 1) * u)
    (hwin : u * t ^ 2 ≤ η) :
    |(∏ j ∈ Finset.range n, A' j) / (∏ j ∈ Finset.range n, A j) - 1| ≤
      CA / c₀ * Real.exp (CA / c₀ * η) * u * t ^ 2 := by
  have hApos : ∀ j, 0 < A j := fun j => lt_of_lt_of_le hc₀ (hA0 j)
  have ht0 : 0 ≤ t := by rw [← ht]; positivity
  have hκ : 0 ≤ CA / c₀ := div_nonneg hCA hc₀.le
  rw [← Finset.prod_div_distrib]
  have hrat : ∀ j, A' j / A j = 1 + (A' j - A j) / A j := by
    intro j; rw [one_add_div (hApos j).ne']; congr 1; ring
  simp_rw [hrat]
  refine (abs_prod_one_add_sub_one_le (fun j => (A' j - A j) / A j) n).trans ?_
  refine (sub_le_sub_right (prod_one_add_abs_le_exp (fun j => (A' j - A j) / A j) n) 1).trans ?_
  have hδb : ∀ j ∈ Finset.range n, |(A' j - A j) / A j| ≤ CA / c₀ * u * t := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [abs_div, abs_of_pos (hApos j), div_le_iff₀ (hApos j)]
    have h1 := hdA j hj'
    have h2 : (j : ℝ) + 1 ≤ t := by
      rw [← ht]
      have : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj'
      linarith
    have h3 : CA * ((j : ℝ) + 1) * u ≤ CA * t * u :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hCA) hu
    have h4 : CA * t * u = CA / c₀ * c₀ * t * u := by rw [div_mul_cancel₀ CA hc₀.ne']
    have h5 : CA / c₀ * c₀ * t * u ≤ CA / c₀ * A j * t * u := by
      have h6 := mul_le_mul_of_nonneg_left (hA0 j) hκ
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h6 ht0) hu
    nlinarith
  have hS : ∑ j ∈ Finset.range n, |(A' j - A j) / A j| ≤ CA / c₀ * u * t ^ 2 := by
    calc _ ≤ ∑ j ∈ Finset.range n, CA / c₀ * u * t := Finset.sum_le_sum hδb
      _ = n * (CA / c₀ * u * t) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ t * (CA / c₀ * u * t) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (mul_nonneg hκ hu) ht0)
          rw [← ht]; linarith
      _ = _ := by ring
  have hSη : ∑ j ∈ Finset.range n, |(A' j - A j) / A j| ≤ CA / c₀ * η := by
    refine hS.trans ?_
    have := mul_le_mul_of_nonneg_left hwin hκ
    linarith
  calc Real.exp (∑ j ∈ Finset.range n, |(A' j - A j) / A j|) - 1
      ≤ (∑ j ∈ Finset.range n, |(A' j - A j) / A j|) *
          Real.exp (∑ j ∈ Finset.range n, |(A' j - A j) / A j|) := exp_sub_one_le_mul_exp _
    _ ≤ (CA / c₀ * u * t ^ 2) * Real.exp (CA / c₀ * η) :=
        mul_le_mul hS (Real.exp_le_exp.mpr hSη) (Real.exp_pos _).le
          (mul_nonneg (mul_nonneg hκ hu) (sq_nonneg t))
    _ = _ := by ring

end WindowProof

open WindowProof

/-- Proof of `prop:window-moments`, the derivative bounds (`response.tex` lines
323–326), with the conclusions of `th:product` (`criticalProduct`) and
`prop:contact-moments` (`contactMoments`) as hypotheses. -/
theorem window_derivBounds_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
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
    (hContact : ∃ M L : ℝ,
      (∀ k n : ℕ, 1 ≤ k →
        contactMoment μ B (criticalPoint μ B) k n ≤
          (k.factorial : ℝ) * M * L ^ (k - 1) * ((n : ℝ) + 1) ^ (2 * k - 1)) ∧
      ∀ (n : ℕ) (u : ℝ), 0 ≤ u → L * u * ((n : ℝ) + 1) ^ 2 < 1 →
        contactExpMoment μ B (criticalPoint μ B) u n ≤
            M * u * ((n : ℝ) + 1) / (1 - L * u * ((n : ℝ) + 1) ^ 2) ∧
          tiltedMass μ B (criticalPoint μ B + u) n - tiltedMass μ B (criticalPoint μ B) n ≤
            M * u * ((n : ℝ) + 1) / (1 - L * u * ((n : ℝ) + 1) ^ 2)) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ v : ℝ, 0 ≤ v →
      v * ((n : ℝ) + 1) ^ 2 ≤ η →
      |deriv (fun h => tiltedMass μ B h n) (criticalPoint μ B + v)| ≤ C * ((n : ℝ) + 1) ∧
        |deriv (deriv fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B + v)| ≤
          C * ((n : ℝ) + 1) ^ 4 ∧
        |deriv (fun h => tiltedLogMoment μ B h 2 n) (criticalPoint μ B + v)| ≤
          C * ((n : ℝ) + 1) ^ 3 ∧
        |deriv (fun h => tiltedLogMoment μ B h 3 n) (criticalPoint μ B + v)| ≤
          C * ((n : ℝ) + 1) ^ 4 := by
  -- `hshift` is consumed by `criticalProduct` and `contactMoments`, whose
  -- conclusions are the hypotheses `hProd` and `hContact` here.
  have _ := hshift
  obtain ⟨C₀, hC₀, hb, -⟩ := hProd
  obtain ⟨η, Mx, hη, hMx, hE⟩ := window_setup hContact
  refine ⟨η, max 1 (max (2 * Mx) (max (60 * Mx * η⁻¹ + 3 * C₀ * η⁻¹ ^ 2)
    (max (58 * Mx + 2 * C₀ * η⁻¹) (148 * Mx + 7 * C₀ * η⁻¹)))), hη,
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro n hn v hv hvη
  have ht0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hK : tiltedLogMoment μ B (criticalPoint μ B) 2 n ≤ C₀ * ((n : ℝ) + 1) :=
    K_le_of hC₀ ht0 (hb n hn).2.1 (hb n hn).2.2.1
  have hL := (hb n hn).2.2.2
  have hA := window_dA hpos hmean hB hη hMx hE rfl hv hvη
  have hH := window_dH hpos hmean hB hη hMx hE rfl hK hv hvη
  have hKd := window_dK hpos hmean hB hη hMx hE rfl hL hv hvη
  have hJd := window_dJ hpos hmean hB hη hMx hE rfl hC₀.le hL hv hvη
  refine ⟨hA.trans ?_, hH.trans ?_, hKd.trans ?_, hJd.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) ht0
  · exact mul_le_mul_of_nonneg_right
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))) (by positivity)
  · exact mul_le_mul_of_nonneg_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
      (by positivity)
  · exact mul_le_mul_of_nonneg_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))))
      (by positivity)

/-- `prop:window-moments` (`response.tex` lines 273–284), with the conclusions of
`th:product` (`criticalProduct`) and `prop:contact-moments` (`contactMoments`) as
hypotheses. -/
theorem windowMoments_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
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
    (hContact : ∃ M L : ℝ,
      (∀ k n : ℕ, 1 ≤ k →
        contactMoment μ B (criticalPoint μ B) k n ≤
          (k.factorial : ℝ) * M * L ^ (k - 1) * ((n : ℝ) + 1) ^ (2 * k - 1)) ∧
      ∀ (n : ℕ) (u : ℝ), 0 ≤ u → L * u * ((n : ℝ) + 1) ^ 2 < 1 →
        contactExpMoment μ B (criticalPoint μ B) u n ≤
            M * u * ((n : ℝ) + 1) / (1 - L * u * ((n : ℝ) + 1) ^ 2) ∧
          tiltedMass μ B (criticalPoint μ B + u) n - tiltedMass μ B (criticalPoint μ B) n ≤
            M * u * ((n : ℝ) + 1) / (1 - L * u * ((n : ℝ) + 1) ^ 2)) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ u : ℝ, 0 ≤ u →
      u * ((n : ℝ) + 1) ^ 2 ≤ η →
      |tiltedMass μ B (criticalPoint μ B + u) n - tiltedMass μ B (criticalPoint μ B) n| ≤
          C * u * ((n : ℝ) + 1) ∧
        |tiltedLogMoment μ B (criticalPoint μ B + u) 1 n -
            tiltedLogMoment μ B (criticalPoint μ B) 1 n -
            u * deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B)| ≤
          C * u ^ 2 * ((n : ℝ) + 1) ^ 4 ∧
        |tiltedLogMoment μ B (criticalPoint μ B + u) 2 n -
            tiltedLogMoment μ B (criticalPoint μ B) 2 n| ≤ C * u * ((n : ℝ) + 1) ^ 3 ∧
        |tiltedLogMoment μ B (criticalPoint μ B + u) 3 n -
            tiltedLogMoment μ B (criticalPoint μ B) 3 n| ≤ C * u * ((n : ℝ) + 1) ^ 4 ∧
        absTiltedLogRpowMoment μ B (criticalPoint μ B + u) (7 / 2) n ≤
          C * ((n : ℝ) + 1) ^ ((5 : ℝ) / 2) ∧
        |tiltedProduct μ B (criticalPoint μ B + u) n /
            tiltedProduct μ B (criticalPoint μ B) n - 1| ≤ C * u * ((n : ℝ) + 1) ^ 2 := by
  -- `hshift` is consumed by `criticalProduct` and `contactMoments`, whose
  -- conclusions are the hypotheses `hProd` and `hContact` here.
  have _ := hshift
  obtain ⟨C₀, hC₀, hb, -⟩ := hProd
  obtain ⟨η, Mx, hη, hMx, hE⟩ := window_setup hContact
  have hc₀ : 0 < min (4 / C₀) (1 / C₀ ^ 2) :=
    lt_min (div_pos (by norm_num) hC₀) (div_pos one_pos (by positivity))
  have hA0 := tiltedMass_lower hC₀ (fun n hn => ⟨(hb n hn).1, (hb n hn).2.1⟩)
  set c₀ := min (4 / C₀) (1 / C₀ ^ 2) with hc₀def
  set CP := 2 * Mx / c₀ * Real.exp (2 * Mx / c₀ * η) with hCPdef
  set CH := 60 * Mx * η⁻¹ + 3 * C₀ * η⁻¹ ^ 2 with hCHdef
  set CK := 58 * Mx + 2 * C₀ * η⁻¹ with hCKdef
  set CJ := 148 * Mx + 7 * C₀ * η⁻¹ with hCJdef
  set C7 := 76 * Mx * η + 18 * C₀ with hC7def
  refine ⟨η, max 1 (max (2 * Mx) (max CH (max CK (max CJ (max C7 CP))))), hη,
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro n hn u hu huη
  set C := max 1 (max (2 * Mx) (max CH (max CK (max CJ (max C7 CP))))) with hCdef
  have hC1 : 2 * Mx ≤ C := le_max_of_le_right (le_max_left _ _)
  have hCH : CH ≤ C := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hCK : CK ≤ C :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hCJ : CJ ≤ C := le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_left _ _))))
  have hC7 : C7 ≤ C := le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))
  have hCP : CP ≤ C := le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))))
  have ht0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have ht1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hK : tiltedLogMoment μ B (criticalPoint μ B) 2 n ≤ C₀ * ((n : ℝ) + 1) :=
    K_le_of hC₀ ht0.le (hb n hn).2.1 (hb n hn).2.2.1
  have hL := (hb n hn).2.2.2
  have hwin : ∀ v, 0 ≤ v → v ≤ u → v * ((n : ℝ) + 1) ^ 2 ≤ η := fun v _ hvu =>
    le_trans (mul_le_mul_of_nonneg_right hvu (by positivity)) huη
  have hCH0 : 0 ≤ CH := add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hMx) (inv_nonneg.mpr hη.le))
    (mul_nonneg (mul_nonneg (by norm_num) hC₀.le) (sq_nonneg _))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `A_n`
    have cA := mvt_window (f := fun h => tiltedMass μ B h n)
      (f' := deriv (fun h => tiltedMass μ B h n)) (h₀ := criticalPoint μ B)
      (D := 2 * Mx * ((n : ℝ) + 1)) hu
      (fun v _ _ => (hasDerivAt_tiltedMass_aux hpos hmean hB _ n).differentiableAt.hasDerivAt)
      (fun v hv0 hvu => window_dA hpos hmean hB hη hMx hE rfl hv0 (hwin v hv0 hvu))
    refine cA.trans ?_
    calc 2 * Mx * ((n : ℝ) + 1) * u ≤ C * ((n : ℝ) + 1) * u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 ht0.le) hu
      _ = C * u * ((n : ℝ) + 1) := by ring
  · -- `H_n`, by the mean value theorem twice
    have step1 : ∀ v, 0 ≤ v → v ≤ u →
        |deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B + v) -
          deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B)| ≤
          CH * ((n : ℝ) + 1) ^ 4 * u := by
      intro v hv0 hvu
      have c1 := mvt_window (f := deriv (fun h => tiltedLogMoment μ B h 1 n))
        (f' := deriv (deriv (fun h => tiltedLogMoment μ B h 1 n))) (h₀ := criticalPoint μ B)
        (D := CH * ((n : ℝ) + 1) ^ 4) hv0
        (fun w _ _ =>
          (differentiableAt_deriv_tiltedLogMoment_one_aux hpos hmean hB _ n).hasDerivAt)
        (fun w hw0 hwv => window_dH hpos hmean hB hη hMx hE rfl hK hw0
          (hwin w hw0 (hwv.trans hvu)))
      refine c1.trans ?_
      exact mul_le_mul_of_nonneg_left hvu (mul_nonneg hCH0 (by positivity))
    have c2 := mvt_window
      (f := fun x => tiltedLogMoment μ B x 1 n -
        x * deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B))
      (f' := fun x => deriv (fun h => tiltedLogMoment μ B h 1 n) x -
        deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B))
      (h₀ := criticalPoint μ B) (D := CH * ((n : ℝ) + 1) ^ 4 * u) hu
      (fun v _ _ => by
        have h1 := (hasDerivAt_tiltedLogMoment_aux hpos hmean hB (criticalPoint μ B + v) 1
          n).differentiableAt.hasDerivAt
        have h2 := (hasDerivAt_id' (criticalPoint μ B + v)).mul_const
          (deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B))
        exact (h1.sub h2).congr_deriv (by rw [one_mul]))
      step1
    have e : tiltedLogMoment μ B (criticalPoint μ B + u) 1 n -
          (criticalPoint μ B + u) * deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) -
        (tiltedLogMoment μ B (criticalPoint μ B) 1 n -
          criticalPoint μ B * deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B)) =
        tiltedLogMoment μ B (criticalPoint μ B + u) 1 n -
          tiltedLogMoment μ B (criticalPoint μ B) 1 n -
          u * deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) := by ring
    rw [e] at c2
    refine c2.trans ?_
    calc CH * ((n : ℝ) + 1) ^ 4 * u * u ≤ C * ((n : ℝ) + 1) ^ 4 * u * u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCH (by positivity)) hu) hu
      _ = C * u ^ 2 * ((n : ℝ) + 1) ^ 4 := by ring
  · -- `K_n`
    have cK := mvt_window (f := fun h => tiltedLogMoment μ B h 2 n)
      (f' := deriv (fun h => tiltedLogMoment μ B h 2 n)) (h₀ := criticalPoint μ B)
      (D := CK * ((n : ℝ) + 1) ^ 3) hu
      (fun v _ _ =>
        (hasDerivAt_tiltedLogMoment_aux hpos hmean hB _ 2 n).differentiableAt.hasDerivAt)
      (fun v hv0 hvu => window_dK hpos hmean hB hη hMx hE rfl hL hv0 (hwin v hv0 hvu))
    refine cK.trans ?_
    calc CK * ((n : ℝ) + 1) ^ 3 * u ≤ C * ((n : ℝ) + 1) ^ 3 * u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCK (by positivity)) hu
      _ = C * u * ((n : ℝ) + 1) ^ 3 := by ring
  · -- `J_n`
    have cJ := mvt_window (f := fun h => tiltedLogMoment μ B h 3 n)
      (f' := deriv (fun h => tiltedLogMoment μ B h 3 n)) (h₀ := criticalPoint μ B)
      (D := CJ * ((n : ℝ) + 1) ^ 4) hu
      (fun v _ _ =>
        (hasDerivAt_tiltedLogMoment_aux hpos hmean hB _ 3 n).differentiableAt.hasDerivAt)
      (fun v hv0 hvu => window_dJ hpos hmean hB hη hMx hE rfl hC₀.le hL hv0 (hwin v hv0 hvu))
    refine cJ.trans ?_
    calc CJ * ((n : ℝ) + 1) ^ 4 * u ≤ C * ((n : ℝ) + 1) ^ 4 * u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCJ (by positivity)) hu
      _ = C * u * ((n : ℝ) + 1) ^ 4 := by ring
  · -- the `7/2` moment
    set r := Real.sqrt ((n : ℝ) + 1) with hr
    have hr2 : r ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt ht0.le
    have hr1 : 1 ≤ r := by
      have h := Real.sqrt_le_sqrt ht1
      rwa [Real.sqrt_one] at h
    have h7 := window_seven_halves hpos hmean hB hη hMx hE hr1 hr2.symm
      (by rw [hr2]; exact hK) (by rw [hr2]; exact hL) hu (by rw [hr2]; exact huη)
    have hpow : ((n : ℝ) + 1) ^ ((5 : ℝ) / 2) = r ^ 5 := by
      rw [hr, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
      norm_num
    rw [hpow]
    refine h7.trans ?_
    exact mul_le_mul_of_nonneg_right hC7 (by positivity)
  · -- the product ratio
    have hdA : ∀ j < n, |tiltedMass μ B (criticalPoint μ B + u) j -
        tiltedMass μ B (criticalPoint μ B) j| ≤ 2 * Mx * ((j : ℝ) + 1) * u := by
      intro j hj
      have hjn : ((j : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
        have : (j : ℝ) ≤ n := by exact_mod_cast hj.le
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        nlinarith
      exact mvt_window (f := fun h => tiltedMass μ B h j)
        (f' := deriv (fun h => tiltedMass μ B h j)) (h₀ := criticalPoint μ B)
        (D := 2 * Mx * ((j : ℝ) + 1)) hu
        (fun v _ _ => (hasDerivAt_tiltedMass_aux hpos hmean hB _ j).differentiableAt.hasDerivAt)
        (fun v hv0 hvu => window_dA hpos hmean hB hη hMx hE rfl hv0
          (le_trans (mul_le_mul_of_nonneg_left hjn hv0) (hwin v hv0 hvu)))
    have hP := prod_ratio_bound (A := fun j => tiltedMass μ B (criticalPoint μ B) j)
      (A' := fun j => tiltedMass μ B (criticalPoint μ B + u) j) hc₀
      (mul_nonneg zero_le_two hMx) hu (n := n) rfl hA0 hdA huη
    unfold tiltedProduct
    refine hP.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCP hu) (by positivity)

end DiamondPinning
