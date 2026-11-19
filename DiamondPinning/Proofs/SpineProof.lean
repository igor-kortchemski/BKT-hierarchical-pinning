module

public import DiamondPinning.Proofs.FieldDerivProof
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The spine identities

This file proves `response:spine-identities` (`source/response.tex`, lines
62–96).  The route is the induction master identity
`E[R_n^θ Q_n g(R_n)] = Π_n A_0 Ê[w_n g(T_n)]` for bounded measurable `g`,
using the height-zero change of measure and the successor decomposition.
Logarithmic cutoffs and dominated convergence then give the mixed spine
identity.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology
open scoped BigOperators

private noncomputable abbrev spineQ (B h : ℝ) (n : ℕ) (e : Env n) : ℝ :=
  gibbsMean B h n e (fun j => (j : ℝ))

private abbrev spineAppend {n : ℕ} (u : Fin n → ℝ) (y : ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc u y

private theorem theta_mul_log_B {B : ℝ} (hB : 2 < B) :
    theta B * Real.log B = Real.log 2 := by
  rw [theta, div_mul_cancel₀]
  exact Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)

private theorem one_inv_theta_sub_log_B_pos {B : ℝ} (hB : 2 < B) :
    0 < 1 / theta B - Real.log B := by
  have hlB : 0 < Real.log B := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 < 1 := by
    nlinarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)]
  rw [theta, one_div, inv_div]
  have hpos : 0 < Real.log B * (1 / Real.log 2 - 1) :=
    mul_pos hlB (sub_pos.mpr (one_lt_one_div hl2 hl21))
  convert hpos using 1
  field_simp

@[simp] private theorem spineAppend_castSucc {n : ℕ} (u : Fin n → ℝ) (y : ℝ)
    (j : Fin n) : spineAppend u y j.castSucc = u j := by
  simp [spineAppend]

@[simp] private theorem spineAppend_last {n : ℕ} (u : Fin n → ℝ) (y : ℝ) :
    spineAppend u y (Fin.last n) = y := by
  simp [spineAppend]

private theorem spineWalk_append_succ {B : ℝ} {n : ℕ} (u : Fin n → ℝ) (y : ℝ) :
    spineWalk B (spineAppend u y) (n + 1) =
      spineWalk B u n + (Real.log y - Real.log B) := by
  simp only [spineWalk]
  rw [Fin.sum_univ_castSucc]
  simp only [spineAppend_castSucc, Fin.val_castSucc, Fin.val_last,
    spineAppend_last, Nat.lt_succ_self, ↓reduceIte, Fin.is_lt,
    Nat.lt_succ_of_lt]

private theorem spineWalk_append_of_le {B : ℝ} {n k : ℕ} (u : Fin n → ℝ) (y : ℝ)
    (hk : k ≤ n) : spineWalk B (spineAppend u y) k = spineWalk B u k := by
  simp only [spineWalk]
  rw [Fin.sum_univ_castSucc]
  simp only [spineAppend_castSucc, Fin.val_castSucc]
  have hlast : ¬ (n : ℕ) < k := Nat.not_lt.mpr hk
  simp only [Fin.val_last, hlast, ↓reduceIte, add_zero]

private theorem spineWalk_append_exp_sum {B : ℝ} {n : ℕ} (u : Fin n → ℝ) (y : ℝ) :
    (∑ k ∈ Finset.Icc 1 (n + 1), Real.exp (-spineWalk B (spineAppend u y) k)) =
      (∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B u k)) +
        Real.exp (-spineWalk B (spineAppend u y) (n + 1)) := by
  rw [Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [spineWalk_append_of_le u y (Finset.mem_Icc.mp hk).2]

private noncomputable def spineBase (B : ℝ) (n : ℕ) (r : ℝ) (u : Fin n → ℝ) : ℝ :=
  1 + (B - 1) / (B * r) * ∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B u k)

private theorem spineBase_append {B : ℝ} {n : ℕ} (r y : ℝ) (u : Fin n → ℝ) :
    spineBase B (n + 1) r (spineAppend u y) = spineBase B n r u +
      (B - 1) / (B * r) * Real.exp (-spineWalk B (spineAppend u y) (n + 1)) := by
  rw [spineBase, spineBase, spineWalk_append_exp_sum]
  ring

private theorem spineBase_pos {B : ℝ} (hB : 2 < B) {n : ℕ} {r : ℝ}
    (hr : 0 < r) (u : Fin n → ℝ) : 0 < spineBase B n r u := by
  have hc : 0 ≤ (B - 1) / (B * r) := div_nonneg (by linarith) (mul_pos (by linarith) hr).le
  have hs : 0 ≤ ∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B u k) := by positivity
  dsimp [spineBase]
  nlinarith [mul_nonneg hc hs]

private theorem spineW_eq_base {B : ℝ} (n : ℕ) (r : ℝ) (u : Fin n → ℝ) :
    spineW B n r u = spineBase B n r u ^ (-(1 - theta B)) := rfl

private theorem spineT_eq_base {B : ℝ} (hB : 2 < B) {n : ℕ} {r : ℝ}
    (hr : 0 < r) (u : Fin n → ℝ) :
    spineT B n r u = r * Real.exp (spineWalk B u n) * spineBase B n r u := by
  have hp : 1 - theta B ≠ 0 := ne_of_gt (sub_pos.mpr (theta_lt_one hB))
  have hb : 0 ≤ spineBase B n r u := (spineBase_pos hB hr u).le
  rw [spineT, spineW_eq_base, ← Real.rpow_mul hb]
  have he : (-(1 - theta B)) * (-(1 / (1 - theta B))) = 1 := by
    field_simp
  rw [he, Real.rpow_one]

private theorem exp_spineWalk_append {B : ℝ} {n : ℕ} (y : ℝ) (u : Fin n → ℝ)
    (hB : 0 < B) (hy : 0 < y) :
    Real.exp (spineWalk B (spineAppend u y) (n + 1)) =
      Real.exp (spineWalk B u n) * y / B := by
  rw [spineWalk_append_succ, Real.exp_add, Real.exp_sub, Real.exp_log hy,
    Real.exp_log hB]
  ring

private theorem spineT_append_base {B : ℝ} (hB : 2 < B) {n : ℕ} {r y : ℝ}
    (hr : 0 < r) (hy : 0 < y) (u : Fin n → ℝ) :
    spineT B (n + 1) r (spineAppend u y) =
      spineT B n r u * y * spineBase B (n + 1) r (spineAppend u y) /
        (B * spineBase B n r u) := by
  rw [spineT_eq_base hB hr, spineT_eq_base hB hr, exp_spineWalk_append y u
    (by linarith) hy]
  have hb := (spineBase_pos hB hr u).ne'
  field_simp

private theorem spineT_append {B : ℝ} (hB : 2 < B) {n : ℕ} {r y : ℝ}
    (hr : 0 < r) (hy : 0 < y) (u : Fin n → ℝ) :
    (spineT B n r u * y + (B - 1)) / B = spineT B (n + 1) r (spineAppend u y) := by
  have hb : 0 < B := by linarith
  have hbold := spineBase_pos hB hr u
  rw [spineT_eq_base hB hr u, spineT_eq_base hB hr (spineAppend u y),
    spineBase_append, spineWalk_append_succ]
  rw [show Real.exp (-(spineWalk B u n + (Real.log y - Real.log B))) =
      B * Real.exp (-spineWalk B u n) / y by
    rw [neg_add, Real.exp_add, neg_sub, Real.exp_sub, Real.exp_log hy,
      Real.exp_log hb]
    field_simp]
  have hE : Real.exp (-spineWalk B u n) = (Real.exp (spineWalk B u n))⁻¹ := by
    rw [Real.exp_neg]
  have hE0 : Real.exp (spineWalk B u n) ≠ 0 := Real.exp_ne_zero _
  rw [hE, Real.exp_add, Real.exp_sub, Real.exp_log hy, Real.exp_log hb]
  field_simp [hb.ne', hr.ne', hy.ne', hE0]

private theorem spine_weight_append {B : ℝ} (hB : 2 < B) {n : ℕ} {r y : ℝ}
    (hr : 0 < r) (hy : 0 < y) (u : Fin n → ℝ) :
    (2 / B) * spineW B n r u * spineT B n r u ^ (1 - theta B) *
        y ^ (1 - theta B) * spineT B (n + 1) r (spineAppend u y) ^ (theta B - 1) =
      spineW B (n + 1) r (spineAppend u y) := by
  have hb : 0 < B := by linarith
  have hp : 0 < 1 - theta B := sub_pos.mpr (theta_lt_one hB)
  have hbold := spineBase_pos hB hr u
  have hbnew := spineBase_pos hB hr (spineAppend u y)
  have hTold : 0 < spineT B n r u := by
    rw [spineT_eq_base hB hr]
    positivity
  have hTnew : 0 < spineT B (n + 1) r (spineAppend u y) := by
    rw [← spineT_append hB hr hy]
    exact div_pos (by have := mul_pos hTold hy; linarith) hb
  rw [spineW_eq_base, spineW_eq_base]
  apply Real.log_injOn_pos
    (show _ ∈ Set.Ioi (0 : ℝ) by change 0 < _; positivity)
    (show _ ∈ Set.Ioi (0 : ℝ) by change 0 < _; positivity)
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hb.ne',
    Real.log_rpow hbold, Real.log_rpow hTold,
    Real.log_rpow hy, Real.log_rpow hTnew, Real.log_rpow hbnew]
  rw [← theta_mul_log_B hB]
  have hTbase := spineT_append_base hB hr hy u
  have hlog : Real.log (spineT B (n + 1) r (spineAppend u y)) =
      Real.log (spineT B n r u) + Real.log y +
        Real.log (spineBase B (n + 1) r (spineAppend u y)) -
        Real.log B - Real.log (spineBase B n r u) := by
    rw [hTbase, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul hb.ne' hbold.ne']
    ring
  rw [hlog]
  ring


private theorem integral_tiltedLaw_apply {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (j : ℕ) (g : ℝ → ℝ) :
    (∫ x, g x ∂tiltedLaw μ B h j) =
      ∫ x, (x ^ theta B / tiltedMass μ B h j) * g x ∂lawR μ B h j := by
  rw [tiltedLaw, integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_pos_lawR hpos hB h j] with x hx
  rw [ENNReal.toReal_ofReal (div_nonneg (Real.rpow_nonneg hx.le _)
    (tiltedMass_pos hpos hmean hB h j).le)]
  rfl

private theorem integral_law_eq_tiltedMass_mul_tiltedLaw {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1)
    {B : ℝ} (hB : 2 < B) (h : ℝ) (j : ℕ) (g : ℝ → ℝ) :
    (∫ x, g x ∂lawR μ B h j) = tiltedMass μ B h j *
      ∫ x, x ^ (-theta B) * g x ∂tiltedLaw μ B h j := by
  have hA := tiltedMass_pos hpos hmean hB h j
  rw [integral_tiltedLaw_apply hpos hmean hB h]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_pos_lawR hpos hB h j] with x hx
  have hxpow : x ^ theta B * x ^ (-theta B) = 1 := by
    rw [← Real.rpow_add hx]
    simp
  calc
    g x = g x * (x ^ theta B * x ^ (-theta B)) := by rw [hxpow, mul_one]
    _ = tiltedMass μ B h j *
        (x ^ theta B / tiltedMass μ B h j * (x ^ (-theta B) * g x)) := by
      field_simp [hA.ne']

private theorem spineQ_eval_deriv {B : ℝ} (hB : 1 < B) (h : ℝ) (n : ℕ)
    {e : Env n} (he : Env.Pos n e) :
    HasDerivAt (fun h' => evalR B h' n e)
      (evalR B h n e * spineQ B h n e) h := by
  have hd := (contact_hasDerivAt_log_evalR hB h n e he).exp
  have heq : (fun h' => Real.exp (Real.log (evalR B h' n e))) =
      (fun h' => evalR B h' n e) := by
    funext h'
    exact Real.exp_log (evalR_pos_aux hB h' n he)
  rw [heq, Real.exp_log (evalR_pos_aux hB h n he)] at hd
  exact hd

private theorem spineQ_succ_mul {B : ℝ} (hB : 1 < B) (h : ℝ) (n : ℕ)
    {e : Env (n + 1)} (he : Env.Pos (n + 1) e) :
    evalR B h (n + 1) e * spineQ B h (n + 1) e =
      (evalR B h n e.1 * spineQ B h n e.1 * evalR B h n e.2 +
        evalR B h n e.1 * (evalR B h n e.2 * spineQ B h n e.2)) / B := by
  have hroot := spineQ_eval_deriv hB h (n + 1) he
  have h₁ := spineQ_eval_deriv hB h n he.1
  have h₂ := spineQ_eval_deriv hB h n he.2
  have hrec := ((h₁.mul h₂).add_const (B - 1)).div_const B
  exact hroot.unique (by simpa only [evalR_succ, Pi.mul_apply] using hrec)

private noncomputable def spineBranch (B : ℝ) (g : ℝ → ℝ) (y x : ℝ) : ℝ :=
  x ^ (1 - theta B) * y *
    (((x * y + (B - 1)) / B) ^ (theta B - 1)) * g ((x * y + (B - 1)) / B)

private theorem spineBranch_factor {B : ℝ} (hB : 2 < B) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) :
    x ^ (1 - theta B) * (((x * y + (B - 1)) / B) ^ (theta B - 1)) =
      (x / ((x * y + (B - 1)) / B)) ^ (1 - theta B) := by
  have hR : 0 < (x * y + (B - 1)) / B := div_pos (by nlinarith [mul_pos hx hy]) (by linarith)
  have hp : 0 ≤ 1 - theta B := sub_nonneg.mpr (theta_lt_one hB).le
  rw [Real.div_rpow hx.le hR.le]
  rw [show theta B - 1 = -(1 - theta B) by ring, Real.rpow_neg hR.le]
  field_simp

private theorem spineBranch_base_le {B : ℝ} (hB : 2 < B) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) : x / ((x * y + (B - 1)) / B) ≤ B / y := by
  have hR : 0 < (x * y + (B - 1)) / B := div_pos (by nlinarith [mul_pos hx hy]) (by linarith)
  rw [div_le_div_iff₀ hR hy]
  have hxy : 0 ≤ x * y := (mul_pos hx hy).le
  field_simp
  nlinarith

private theorem spineBranch_bounded {B : ℝ} (hB : 2 < B) (g : ℝ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hgC : ∀ z, 0 < z → |g z| ≤ C) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |spineBranch B g y x| ≤ max y B * C := by
  have hp : 0 ≤ 1 - theta B := sub_nonneg.mpr (theta_lt_one hB).le
  have hp1 : 1 - theta B ≤ 1 := by
    have := (theta_pos hB).le
    linarith
  have hfac := spineBranch_factor hB hx hy
  have hR : 0 < (x*y+(B-1))/B := div_pos (by nlinarith [mul_pos hx hy]) (by linarith)
  have hbase : 0 ≤ x / ((x*y+(B-1))/B) := div_nonneg hx.le hR.le
  have hle := spineBranch_base_le hB hx hy
  have hfac_le : (x / ((x*y+(B-1))/B)) ^ (1-theta B) * y ≤ max y B := by
    by_cases hBy : B / y ≤ 1
    · have hpow : (x / ((x*y+(B-1))/B)) ^ (1-theta B) ≤ 1 := by
        apply (Real.rpow_le_one hbase _ hp)
        exact hle.trans hBy
      calc
        _ ≤ 1 * y := mul_le_mul_of_nonneg_right hpow hy.le
        _ ≤ max y B := by simp
    · have hBy1 : 1 ≤ B / y := le_of_not_ge hBy
      have hpow : (x / ((x*y+(B-1))/B)) ^ (1-theta B) ≤ B / y := by
        calc
          _ ≤ (B / y) ^ (1-theta B) := Real.rpow_le_rpow hbase hle hp
          _ ≤ (B / y) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hBy1 hp1
          _ = B / y := Real.rpow_one _
      calc
        _ ≤ (B / y) * y := mul_le_mul_of_nonneg_right hpow hy.le
        _ = B := div_mul_cancel₀ _ hy.ne'
        _ ≤ max y B := le_max_right _ _
  have hfac_nonneg : 0 ≤ x ^ (1 - theta B) * (((x*y+(B-1))/B)^(theta B-1)) := by
    rw [hfac]
    positivity
  unfold spineBranch
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _),
    abs_of_pos hy, abs_of_nonneg (Real.rpow_nonneg hR.le _)]
  calc
    x ^ (1-theta B) * y * ((x*y+(B-1))/B) ^ (theta B-1) *
        |g ((x*y+(B-1))/B)| =
      (x ^ (1-theta B) * ((x*y+(B-1))/B) ^ (theta B-1)) * y *
        |g ((x*y+(B-1))/B)| := by ring
    _ = (x / ((x*y+(B-1))/B)) ^ (1-theta B) * y * |g ((x*y+(B-1))/B)| := by
      rw [hfac]
    _ ≤ (x / ((x*y+(B-1))/B)) ^ (1-theta B) * y * C := by
      gcongr
      exact hgC _ hR
    _ ≤ max y B * C := mul_le_mul_of_nonneg_right hfac_le hC

private theorem measurable_spineBranch (B : ℝ) (g : ℝ → ℝ)
    (hg : Measurable g) (y : ℝ) : Measurable (spineBranch B g y) := by
  unfold spineBranch
  fun_prop

private theorem spine_rpow_cancel {θ x y R G Q : ℝ}
    (hx : x ^ θ * x ^ (1 - θ) = x) :
    x ^ θ * Q * (x ^ (1 - θ) * y * R * G) = x * Q * (y * R * G) := by
  calc
    _ = (x ^ θ * x ^ (1 - θ)) * Q * (y * R * G) := by ring
    _ = _ := by rw [hx]

private theorem spineQ_succ_decompose {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ)
    (g : ℝ → ℝ) {e : Env (n + 1)} (he : Env.Pos (n + 1) e) :
    evalR B h (n + 1) e ^ theta B * spineQ B h (n + 1) e *
        g (evalR B h (n + 1) e) =
      (evalR B h n e.1 ^ theta B * spineQ B h n e.1 *
          spineBranch B g (evalR B h n e.2) (evalR B h n e.1) +
        evalR B h n e.2 ^ theta B * spineQ B h n e.2 *
          spineBranch B g (evalR B h n e.1) (evalR B h n e.2)) / B := by
  have hx := evalR_pos_aux (B := B) (by linarith) h n he.1
  have hy := evalR_pos_aux (B := B) (by linarith) h n he.2
  have hR := evalR_pos_aux (B := B) (by linarith) h (n + 1) he
  have hrec := spineQ_succ_mul (B := B) (by linarith) h n he
  have hxpow : evalR B h n e.1 ^ theta B * evalR B h n e.1 ^ (1 - theta B) =
      evalR B h n e.1 := by
    calc
      _ = evalR B h n e.1 ^ (theta B + (1 - theta B)) := (Real.rpow_add hx _ _).symm
      _ = evalR B h n e.1 ^ (1 : ℝ) := by ring_nf
      _ = _ := Real.rpow_one _
  have hypow : evalR B h n e.2 ^ theta B * evalR B h n e.2 ^ (1 - theta B) =
      evalR B h n e.2 := by
    calc
      _ = evalR B h n e.2 ^ (theta B + (1 - theta B)) := (Real.rpow_add hy _ _).symm
      _ = evalR B h n e.2 ^ (1 : ℝ) := by ring_nf
      _ = _ := Real.rpow_one _
  have hRpow : evalR B h (n + 1) e ^ (theta B - 1) *
      (evalR B h (n + 1) e * spineQ B h (n + 1) e) =
      evalR B h (n + 1) e ^ theta B * spineQ B h (n + 1) e := by
    calc
      _ = evalR B h (n + 1) e ^ (theta B - 1) *
          evalR B h (n + 1) e ^ (1 : ℝ) * spineQ B h (n + 1) e := by
        rw [Real.rpow_one]
        ring
      _ = evalR B h (n + 1) e ^ (theta B - 1 + 1) * spineQ B h (n + 1) e := by
        rw [Real.rpow_add hR]
      _ = _ := by ring_nf
  unfold spineBranch
  rw [evalR_succ] at hR hRpow hrec ⊢
  rw [← hRpow, hrec]
  rw [spine_rpow_cancel hxpow]
  rw [mul_comm (evalR B h n e.2) (evalR B h n e.1)]
  rw [spine_rpow_cancel hypow]
  ring

private theorem spineQ_zero {B : ℝ} (hB : 1 < B) (h : ℝ) {w : Env 0}
    (hw : Env.Pos 0 w) : spineQ B h 0 w = 1 := by
  have hp : evalR B h 0 w ≠ 0 := (evalR_pos_aux hB h 0 hw).ne'
  simp [spineQ, gibbsMean, gibbsWeight_zero_aux h hw]

private theorem spine_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ}
    (hB : 2 < B) (h : ℝ) (n : ℕ) : IsProbabilityMeasure (spineMeasure μ B h n) := by
  let : IsProbabilityMeasure (tiltedLaw μ B h 0) :=
    isProbabilityMeasure_tiltedLaw hpos hmean hB h 0
  let (j : Fin n) : IsProbabilityMeasure (tiltedLaw μ B h j) :=
    isProbabilityMeasure_tiltedLaw hpos hmean hB h j
  rw [spineMeasure]
  infer_instance

private theorem ae_spine_coordinates_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : ∀ᵐ x : ℝ × (Fin n → ℝ) ∂(spineMeasure μ B h n),
      0 < x.1 ∧ ∀ j, 0 < x.2 j := by
  let (j : Fin n) : IsProbabilityMeasure (tiltedLaw μ B h j) :=
    isProbabilityMeasure_tiltedLaw hpos hmean hB h j
  rw [spineMeasure, Measure.ae_prod_iff_ae_ae (by measurability)]
  filter_upwards [ae_pos_tiltedLaw hpos hB h 0] with r hr
  have hu : ∀ᵐ u : Fin n → ℝ ∂(Measure.pi fun j : Fin n => tiltedLaw μ B h j),
      ∀ j, 0 < u j := by
    rw [ae_all_iff]
    intro j
    exact Measure.tendsto_eval_ae_ae.eventually (ae_pos_tiltedLaw hpos hB h j)
  filter_upwards [hu] with u hu
  exact ⟨hr, hu⟩

private theorem spineMean_bounded_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) (g : ℝ → ℝ) (hg : Measurable g) {C : ℝ}
    (hgC : ∀ z, 0 < z → |g z| ≤ C) :
    Integrable (fun x : ℝ × (Fin n → ℝ) => spineW B n x.1 x.2 *
      g (spineT B n x.1 x.2)) (spineMeasure μ B h n) := by
  let : IsProbabilityMeasure (spineMeasure μ B h n) := spine_probability μ hpos hmean hB h n
  have hm : Measurable (fun x : ℝ × (Fin n → ℝ) => spineW B n x.1 x.2 *
      g (spineT B n x.1 x.2)) := by
    dsimp [spineW, spineT, spineWalk]
    fun_prop
  apply (integrable_spine_aux hpos hmean hB h n).1.const_mul C |>.mono'
    hm.aestronglyMeasurable
  filter_upwards [ae_spine_coordinates_pos hpos hmean hB h n] with x hx
  have hw : 0 ≤ spineW B n x.1 x.2 := by
    rw [spineW_eq_base]
    exact (Real.rpow_pos_of_pos (spineBase_pos hB hx.1 x.2) _).le
  change |spineW B n x.1 x.2 * g (spineT B n x.1 x.2)| ≤ C * spineW B n x.1 x.2
  rw [abs_mul, abs_of_nonneg hw]
  calc
    _ ≤ spineW B n x.1 x.2 * C := mul_le_mul_of_nonneg_left
      (hgC _ (by
        rw [spineT_eq_base hB hx.1]
        exact mul_pos (mul_pos hx.1 (Real.exp_pos _)) (spineBase_pos hB hx.1 x.2))) hw
    _ = _ := mul_comm _ _

private theorem spine_master_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ e, evalR B h 0 e ^ theta B * spineQ B h 0 e * g (evalR B h 0 e)
      ∂(envMeasure μ 0)) = tiltedProduct μ B h 0 * tiltedMass μ B h 0 *
      ∫ x, spineW B 0 x.1 x.2 * g (spineT B 0 x.1 x.2) ∂(spineMeasure μ B h 0) := by
  let (j : Fin 0) : IsProbabilityMeasure (tiltedLaw μ B h j) :=
    isProbabilityMeasure_tiltedLaw hpos hmean hB h j
  have hfst : (spineMeasure μ B h 0).map Prod.fst = tiltedLaw μ B h 0 := by
    rw [spineMeasure]
    exact measurePreserving_fst.map_eq
  have hsp : (∫ x, spineW B 0 x.1 x.2 * g (spineT B 0 x.1 x.2)
      ∂(spineMeasure μ B h 0)) = ∫ r, g r ∂(tiltedLaw μ B h 0) := by
    calc
      _ = ∫ x : ℝ × (Fin 0 → ℝ), g x.1 ∂(spineMeasure μ B h 0) := by
        apply integral_congr_ae
        filter_upwards with x
        simp [spineW, spineT, spineWalk]
      _ = ∫ r, g r ∂((spineMeasure μ B h 0).map Prod.fst) := by
        symm
        rw [integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable]
      _ = _ := by rw [hfst]
  rw [hsp, integral_tiltedLaw_apply hpos hmean hB h]
  rw [← map_evalR_envMeasure_aux μ B h 0,
    integral_map (measurable_evalR B h 0).aemeasurable (by fun_prop)]
  simp only [tiltedProduct, Finset.range_zero, Finset.prod_empty, one_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_envPos_aux hpos 0] with e he
  rw [spineQ_zero (by linarith) h he]
  field_simp [(tiltedMass_pos hpos hmean hB h 0).ne']

private noncomputable def spineSuccEquiv (n : ℕ) :
    (ℝ × (Fin (n + 1) → ℝ)) ≃ᵐ ℝ × (ℝ × (Fin n → ℝ)) :=
  ((MeasurableEquiv.refl ℝ).prodCongr
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n))).trans
    (MeasurableEquiv.prodAssoc.symm.trans
      (((MeasurableEquiv.prodComm).prodCongr (MeasurableEquiv.refl (Fin n → ℝ))).trans
        MeasurableEquiv.prodAssoc))

private theorem spineSuccEquiv_measurePreserving {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) :
    MeasurePreserving (spineSuccEquiv n) (spineMeasure μ B h (n + 1))
      ((tiltedLaw μ B h n).prod (spineMeasure μ B h n)) := by
  let : IsProbabilityMeasure (tiltedLaw μ B h 0) :=
    isProbabilityMeasure_tiltedLaw hpos hmean hB h 0
  let (j : Fin n) : IsProbabilityMeasure (tiltedLaw μ B h j) :=
    isProbabilityMeasure_tiltedLaw hpos hmean hB h j
  let : IsProbabilityMeasure (tiltedLaw μ B h n) :=
    isProbabilityMeasure_tiltedLaw hpos hmean hB h n
  let (j : Fin (n + 1)) : IsProbabilityMeasure (tiltedLaw μ B h j) :=
    isProbabilityMeasure_tiltedLaw hpos hmean hB h j
  have hpi := measurePreserving_piFinSuccAbove
    (fun j : Fin (n + 1) => tiltedLaw μ B h j) (Fin.last n)
  simp only [Fin.succAbove_last, Fin.val_last] at hpi
  have h₁ := (MeasurePreserving.id (μ := tiltedLaw μ B h 0)).prod hpi
  have h₂ := (measurePreserving_prodAssoc (tiltedLaw μ B h 0) (tiltedLaw μ B h n)
    (Measure.pi fun j : Fin n => tiltedLaw μ B h j)).symm
  have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
      ((tiltedLaw μ B h 0).prod (tiltedLaw μ B h n))
      ((tiltedLaw μ B h n).prod (tiltedLaw μ B h 0)) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  have h₃ := hswap.prod
    (MeasurePreserving.id (μ := Measure.pi fun j : Fin n => tiltedLaw μ B h j))
  have h₄ := measurePreserving_prodAssoc (tiltedLaw μ B h n) (tiltedLaw μ B h 0)
    (Measure.pi fun j : Fin n => tiltedLaw μ B h j)
  exact h₄.comp (h₃.comp (h₂.comp h₁))

private theorem spine_integral_succ {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) (g : ℝ → ℝ) (hg : Measurable g) {C : ℝ}
    (hgC : ∀ z, 0 < z → |g z| ≤ C) :
    (∫ x, spineW B (n + 1) x.1 x.2 * g (spineT B (n + 1) x.1 x.2)
      ∂(spineMeasure μ B h (n + 1))) =
      ∫ y, ∫ x, spineW B (n + 1) x.1 (spineAppend x.2 y) *
        g (spineT B (n + 1) x.1 (spineAppend x.2 y)) ∂(spineMeasure μ B h n)
        ∂(tiltedLaw μ B h n) := by
  let e := spineSuccEquiv n
  have he := spineSuccEquiv_measurePreserving hpos hmean hB h n
  let : IsProbabilityMeasure (spineMeasure μ B h n) :=
    spine_probability μ hpos hmean hB h n
  let : IsProbabilityMeasure (tiltedLaw μ B h n) :=
    isProbabilityMeasure_tiltedLaw hpos hmean hB h n
  let F : (ℝ × (Fin (n + 1) → ℝ)) → ℝ := fun x =>
    spineW B (n + 1) x.1 x.2 * g (spineT B (n + 1) x.1 x.2)
  let G : (ℝ × (ℝ × (Fin n → ℝ))) → ℝ := fun z =>
    spineW B (n + 1) z.2.1 (spineAppend z.2.2 z.1) *
      g (spineT B (n + 1) z.2.1 (spineAppend z.2.2 z.1))
  have he_apply (r : ℝ) (u : Fin (n + 1) → ℝ) :
      e (r, u) = (u (Fin.last n), (r, fun j => u j.castSucc)) := by
    change (spineSuccEquiv n) (r, u) = _
    unfold spineSuccEquiv
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext j
        rw [MeasurableEquiv.coe_trans, MeasurableEquiv.coe_trans, MeasurableEquiv.coe_trans]
        dsimp [MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc,
          MeasurableEquiv.prodComm, MeasurableEquiv.piFinSuccAbove,
          MeasurableEquiv.refl, Fin.insertNthEquiv, Equiv.prodAssoc, Equiv.prodComm,
          Equiv.prodCongr]
        simp [Equiv.coe_fn_mk, Prod.map, id]
        rfl
  have happend (u : Fin (n + 1) → ℝ) :
      spineAppend (fun j => u j.castSucc) (u (Fin.last n)) = u := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [spineAppend]
    · simp [spineAppend]
  have hGe : G ∘ e = F := by
    funext x
    rcases x with ⟨r, u⟩
    rw [Function.comp_apply, he_apply]
    dsimp [G, F]
    rw [happend]
  have hF : Integrable F (spineMeasure μ B h (n + 1)) :=
    spineMean_bounded_integrable hpos hmean hB h (n + 1) g hg hgC
  have hG : Integrable G ((tiltedLaw μ B h n).prod (spineMeasure μ B h n)) := by
    apply (he.integrable_comp_emb e.measurableEmbedding).mp
    change Integrable (G ∘ e) (spineMeasure μ B h (n + 1))
    rw [hGe]
    exact hF
  calc
    _ = ∫ z, G z ∂((tiltedLaw μ B h n).prod (spineMeasure μ B h n)) := by
      rw [← he.integral_comp' G]
      change (∫ x, F x ∂(spineMeasure μ B h (n + 1))) =
        ∫ x, (G ∘ (spineSuccEquiv n)) x ∂(spineMeasure μ B h (n + 1))
      rw [show G ∘ (spineSuccEquiv n) = F from hGe]
    _ = _ := integral_prod _ hG

private theorem measurable_spineBranch_pair (B : ℝ) (g : ℝ → ℝ)
    (hg : Measurable g) : Measurable (fun z : ℝ × ℝ => spineBranch B g z.2 z.1) := by
  unfold spineBranch
  fun_prop

private theorem measurable_spineQ (B h : ℝ) (n : ℕ) : Measurable (spineQ B h n) := by
  unfold spineQ gibbsMean gibbsWeight
  simp_rw [eval_contactPoly_one]
  apply Finset.measurable_sum
  intro k hk
  exact (measurable_contactPoly_coeff_field B h n k).div (measurable_evalR B h n) |>.mul_const _

private theorem spine_bias_branch {B : ℝ} (hB : 2 < B) {n : ℕ}
    (g : ℝ → ℝ) {r y : ℝ} (hr : 0 < r) (hy : 0 < y) (u : Fin n → ℝ) :
    y ^ (-theta B) * (spineW B n r u * spineBranch B g y (spineT B n r u)) =
      (B / 2) * (spineW B (n + 1) r (spineAppend u y) *
        g (spineT B (n + 1) r (spineAppend u y))) := by
  have hyy : y ^ (-theta B) * y = y ^ (1 - theta B) := by
    calc
      _ = y ^ (-theta B) * y ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = y ^ (-theta B + 1) := (Real.rpow_add hy _ _).symm
      _ = _ := by ring_nf
  have hw := spine_weight_append hB hr hy u
  unfold spineBranch
  rw [← spineT_append hB hr hy u]
  calc
    y ^ (-theta B) * (spineW B n r u *
        (spineT B n r u ^ (1 - theta B) * y *
          (((spineT B n r u * y + (B - 1)) / B) ^ (theta B - 1)) *
          g ((spineT B n r u * y + (B - 1)) / B))) =
      (B / 2) * (((2 / B) * spineW B n r u * spineT B n r u ^ (1 - theta B) *
        y ^ (1 - theta B) * (((spineT B n r u * y + (B - 1)) / B) ^ (theta B - 1)) *
        g ((spineT B n r u * y + (B - 1)) / B))) := by
      rw [← hyy]
      field_simp [show B ≠ 0 by linarith]
    _ = _ := by rw [spineT_append hB hr hy u, hw]

private theorem spine_master_bounded {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) (g : ℝ → ℝ) (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hgC : ∀ z, 0 < z → |g z| ≤ C) :
    (∫ e, evalR B h n e ^ theta B * spineQ B h n e * g (evalR B h n e)
      ∂(envMeasure μ n)) = tiltedProduct μ B h n * tiltedMass μ B h 0 *
      ∫ x, spineW B n x.1 x.2 * g (spineT B n x.1 x.2) ∂(spineMeasure μ B h n) := by
  induction n generalizing g C with
  | zero => exact spine_master_zero hpos hmean hB h g hg
  | succ n ih =>
    let : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
    have hθ0 : 0 ≤ theta B := (theta_pos hB).le
    have hθp : 0 ≤ 1 - theta B := sub_nonneg.mpr (theta_lt_one hB).le
    let f₀ : Env n × Env n → ℝ := fun e =>
      evalR B h (n + 1) e ^ theta B * spineQ B h (n + 1) e *
        g (evalR B h (n + 1) e)
    let f₁ : Env n × Env n → ℝ := fun e =>
      evalR B h n e.1 ^ theta B * spineQ B h n e.1 *
        spineBranch B g (evalR B h n e.2) (evalR B h n e.1)
    let f₂ : Env n × Env n → ℝ := fun e =>
      evalR B h n e.2 ^ theta B * spineQ B h n e.2 *
        spineBranch B g (evalR B h n e.1) (evalR B h n e.2)
    have hRint : Integrable (evalR B h n) (envMeasure μ n) := by
      have hi := integrable_lawR_of hpos hmean hB h n
      rw [← map_evalR_envMeasure_aux μ B h n] at hi
      simpa only [Function.comp_def, id_eq] using
        (integrable_map_measure hi.aestronglyMeasurable
          (measurable_evalR B h n).aemeasurable).mp hi
    have hmax : Integrable (fun e => max (evalR B h n e) B) (envMeasure μ n) :=
      hRint.sup (integrable_const B)
    have hc : Integrable (fun e => |evalR B h n e ^ theta B * spineQ B h n e|)
        (envMeasure μ n) := (by
      simpa only [pow_one, spineQ] using (integrable_contactMoment_aux hpos hmean hB h 1 n).abs)
    have hf₁ : Integrable f₁ ((envMeasure μ n).prod (envMeasure μ n)) := by
      apply (hc.mul_prod (hmax.const_mul C)).mono'
      · dsimp [f₁]
        exact (((Real.continuous_rpow_const hθ0).measurable.comp
          ((measurable_evalR B h n).comp measurable_fst)).mul
            ((measurable_spineQ B h n).comp measurable_fst)).mul
          ((measurable_spineBranch_pair B g hg).comp
            (((measurable_evalR B h n).comp measurable_fst).prodMk
              ((measurable_evalR B h n).comp measurable_snd))) |>.aestronglyMeasurable
      filter_upwards [ae_envPos_aux hpos (n + 1)] with e he
      have hb := spineBranch_bounded hB g hC hgC
        (evalR_pos_aux (B := B) (by linarith) h n he.1)
        (evalR_pos_aux (B := B) (by linarith) h n he.2)
      dsimp [f₁]
      change |evalR B h n e.1 ^ theta B * spineQ B h n e.1 *
        spineBranch B g (evalR B h n e.2) (evalR B h n e.1)| ≤ _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by
        calc
          _ ≤ max (evalR B h n e.2) B * C := hb
          _ = _ := mul_comm _ _) (abs_nonneg _)
    have hf₀ : Integrable f₀ ((envMeasure μ n).prod (envMeasure μ n)) := by
      apply (integrable_contactMoment_aux hpos hmean hB h 1 (n + 1)).abs.const_mul C |>.mono'
      · dsimp [f₀]
        exact (((Real.continuous_rpow_const (theta_pos hB).le).measurable.comp
          (measurable_evalR B h (n + 1))).mul (measurable_spineQ B h (n + 1))).mul
            (hg.comp (measurable_evalR B h (n + 1))) |>.aestronglyMeasurable
      filter_upwards [ae_envPos_aux hpos (n + 1)] with e he
      dsimp [f₀]
      rw [← evalR_succ]
      simp only [pow_one]
      change |evalR B h (n + 1) e ^ theta B * spineQ B h (n + 1) e *
        g (evalR B h (n + 1) e)| ≤ C * |evalR B h (n + 1) e ^ theta B *
          spineQ B h (n + 1) e|
      simp only [spineQ]
      rw [abs_mul]
      calc
        _ ≤ |evalR B h (n + 1) e ^ theta B * gibbsMean B h (n + 1) e (fun j => (j : ℝ))| * C :=
          mul_le_mul_of_nonneg_left
            (hgC _ (evalR_pos_aux (B := B) (by linarith) h (n + 1) he)) (abs_nonneg _)
        _ = _ := mul_comm _ _
    have hf₂ : Integrable f₂ ((envMeasure μ n).prod (envMeasure μ n)) := by
      apply (hf₀.const_mul B |>.sub hf₁).congr
      filter_upwards [ae_envPos_aux hpos (n + 1)] with e he
      dsimp [f₀, f₁, f₂]
      unfold spineBranch
      have hd := spineQ_succ_decompose hB h n g he
      dsimp [f₀, f₁, f₂, spineBranch] at hd ⊢
      simp only [mul_comm (evalR B h n e.2) (evalR B h n e.1)] at hd ⊢
      rw [hd]
      field_simp [show B ≠ 0 by linarith]
      ring
    have hsymm : (∫ e, f₂ e ∂((envMeasure μ n).prod (envMeasure μ n))) =
        ∫ e, f₁ e ∂((envMeasure μ n).prod (envMeasure μ n)) := by
      change (∫ e, f₁ e.swap ∂((envMeasure μ n).prod (envMeasure μ n))) = _
      exact integral_prod_swap f₁
    have hrec : (∫ e, f₀ e ∂((envMeasure μ n).prod (envMeasure μ n))) =
        (2 / B) * ∫ e, f₁ e ∂((envMeasure μ n).prod (envMeasure μ n)) := by
      rw [show (∫ e, f₀ e ∂((envMeasure μ n).prod (envMeasure μ n))) =
          ∫ e, (f₁ e + f₂ e) / B ∂((envMeasure μ n).prod (envMeasure μ n)) by
        apply integral_congr_ae
        filter_upwards [ae_envPos_aux hpos (n + 1)] with e he
        exact spineQ_succ_decompose hB h n g he]
      rw [integral_div, integral_add hf₁ hf₂, hsymm]
      ring
    rw [envMeasure_succ]
    change (∫ e, f₀ e ∂((envMeasure μ n).prod (envMeasure μ n))) = _
    rw [hrec]
    let fR : Env n × ℝ → ℝ := fun z =>
      evalR B h n z.1 ^ theta B * spineQ B h n z.1 * spineBranch B g z.2 (evalR B h n z.1)
    have hmp : MeasurePreserving (Prod.map id (evalR B h n))
        ((envMeasure μ n).prod (envMeasure μ n))
        ((envMeasure μ n).prod (lawR μ B h n)) :=
      (MeasurePreserving.id (μ := envMeasure μ n)).prod
        ⟨measurable_evalR B h n, map_evalR_envMeasure_aux μ B h n⟩
    have hfr : fR ∘ Prod.map id (evalR B h n) = f₁ := by
      ext e
      rfl
    have hfR : Integrable fR ((envMeasure μ n).prod (lawR μ B h n)) := by
      apply (hmp.integrable_comp (g := fR) (by
        dsimp [fR]
        exact (((Real.continuous_rpow_const hθ0).measurable.comp
          ((measurable_evalR B h n).comp measurable_fst)).mul
            ((measurable_spineQ B h n).comp measurable_fst)).mul
          ((measurable_spineBranch_pair B g hg).comp
            (((measurable_evalR B h n).comp measurable_fst).prodMk measurable_snd))
          |>.aestronglyMeasurable)).mp
      rwa [hfr]
    rw [show (∫ e, f₁ e ∂((envMeasure μ n).prod (envMeasure μ n))) =
        ∫ z, fR z ∂((envMeasure μ n).prod (lawR μ B h n)) by
      rw [← hmp.map_eq]
      symm
      rw [← hfr]
      exact
        (integral_map hmp.measurable.aemeasurable (f := fR) (by
          dsimp [fR]
          exact (((Real.continuous_rpow_const hθ0).measurable.comp
            ((measurable_evalR B h n).comp measurable_fst)).mul
              ((measurable_spineQ B h n).comp measurable_fst)).mul
            ((measurable_spineBranch_pair B g hg).comp
              (((measurable_evalR B h n).comp measurable_fst).prodMk measurable_snd))
          |>.aestronglyMeasurable))]
    rw [← integral_prod_swap fR]
    change (2 / B) * ∫ z, (fR ∘ Prod.swap) z ∂((lawR μ B h n).prod (envMeasure μ n)) = _
    rw [integral_prod _ hfR.swap]
    have htest : ∀ᵐ y ∂(lawR μ B h n),
        (∫ (x : Env n), evalR B h n x ^ theta B * spineQ B h n x *
          spineBranch B g y (evalR B h n x) ∂(envMeasure μ n)) =
        tiltedProduct μ B h n * tiltedMass μ B h 0 *
          ∫ z, spineW B n z.1 z.2 *
            spineBranch B g y (spineT B n z.1 z.2) ∂(spineMeasure μ B h n) := by
      filter_upwards [ae_pos_lawR hpos hB h n] with y hy
      exact ih (spineBranch B g y) (measurable_spineBranch B g hg y)
        (C := max y B * C) (mul_nonneg (hy.le.trans (le_max_left y B)) hC)
        (fun x hx => spineBranch_bounded hB g hC hgC hx hy)
    change (2 / B) * ∫ y, (∫ (x : Env n), evalR B h n x ^ theta B *
      spineQ B h n x * spineBranch B g y (evalR B h n x) ∂(envMeasure μ n))
      ∂(lawR μ B h n) = _
    rw [show (2 / B) * ∫ y, (∫ (x : Env n), evalR B h n x ^ theta B *
        spineQ B h n x * spineBranch B g y (evalR B h n x) ∂(envMeasure μ n))
        ∂(lawR μ B h n) =
      (2 / B) * ∫ y, (tiltedProduct μ B h n * tiltedMass μ B h 0 *
        ∫ z, spineW B n z.1 z.2 * spineBranch B g y (spineT B n z.1 z.2)
          ∂(spineMeasure μ B h n)) ∂(lawR μ B h n) by
      congr 1
      exact integral_congr_ae htest]
    rw [integral_law_eq_tiltedMass_mul_tiltedLaw hpos hmean hB h n]
    have hsp : ∀ᵐ y ∂(tiltedLaw μ B h n),
        y ^ (-theta B) * (tiltedProduct μ B h n * tiltedMass μ B h 0 *
          ∫ z, spineW B n z.1 z.2 * spineBranch B g y (spineT B n z.1 z.2)
            ∂(spineMeasure μ B h n)) =
        (B / 2) * tiltedProduct μ B h n * tiltedMass μ B h 0 *
          ∫ z, spineW B (n + 1) z.1 (spineAppend z.2 y) *
            g (spineT B (n + 1) z.1 (spineAppend z.2 y)) ∂(spineMeasure μ B h n) := by
      filter_upwards [ae_pos_tiltedLaw hpos hB h n] with y hy
      calc
        _ = tiltedProduct μ B h n * tiltedMass μ B h 0 *
            (y ^ (-theta B) * ∫ z, spineW B n z.1 z.2 *
              spineBranch B g y (spineT B n z.1 z.2) ∂(spineMeasure μ B h n)) := by ring
        _ = tiltedProduct μ B h n * tiltedMass μ B h 0 *
            (∫ z, y ^ (-theta B) * (spineW B n z.1 z.2 *
              spineBranch B g y (spineT B n z.1 z.2)) ∂(spineMeasure μ B h n)) := by
          rw [integral_const_mul]
        _ = tiltedProduct μ B h n * tiltedMass μ B h 0 *
            (∫ z, (B / 2) * (spineW B (n + 1) z.1 (spineAppend z.2 y) *
              g (spineT B (n + 1) z.1 (spineAppend z.2 y))) ∂(spineMeasure μ B h n)) := by
          congr 1
          apply integral_congr_ae
          filter_upwards [ae_spine_coordinates_pos hpos hmean hB h n] with z hz
          exact spine_bias_branch hB g hz.1 hy z.2
        _ = tiltedProduct μ B h n * tiltedMass μ B h 0 *
            ((B / 2) * ∫ z, spineW B (n + 1) z.1 (spineAppend z.2 y) *
              g (spineT B (n + 1) z.1 (spineAppend z.2 y)) ∂(spineMeasure μ B h n)) := by
          rw [integral_const_mul]
        _ = _ := by ring
    rw [show (∫ y, y ^ (-theta B) * (tiltedProduct μ B h n * tiltedMass μ B h 0 *
        ∫ z, spineW B n z.1 z.2 * spineBranch B g y (spineT B n z.1 z.2)
          ∂(spineMeasure μ B h n)) ∂(tiltedLaw μ B h n)) =
      (B / 2) * tiltedProduct μ B h n * tiltedMass μ B h 0 *
        ∫ y, ∫ z, spineW B (n + 1) z.1 (spineAppend z.2 y) *
          g (spineT B (n + 1) z.1 (spineAppend z.2 y)) ∂(spineMeasure μ B h n)
          ∂(tiltedLaw μ B h n) by
      calc
        _ = ∫ y, (B / 2) * tiltedProduct μ B h n * tiltedMass μ B h 0 *
            ∫ z, spineW B (n + 1) z.1 (spineAppend z.2 y) *
              g (spineT B (n + 1) z.1 (spineAppend z.2 y)) ∂(spineMeasure μ B h n)
            ∂(tiltedLaw μ B h n) := integral_congr_ae hsp
        _ = _ := by rw [integral_const_mul]]
    rw [← spine_integral_succ hpos hmean hB h n g hg hgC]
    rw [show tiltedProduct μ B h (n + 1) = tiltedProduct μ B h n * tiltedMass μ B h n by
      simp [tiltedProduct, Finset.prod_range_succ]]
    field_simp [show B ≠ 0 by linarith]

private theorem spine_gibbsMean_abs_le {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ}
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

private theorem spine_tiltedProduct_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : 0 < tiltedProduct μ B h n := by
  unfold tiltedProduct
  apply Finset.prod_pos
  intro j hj
  exact tiltedMass_pos hpos hmean hB h j

private noncomputable def spineLogTest (B : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  if |Real.log x + (1 / theta B - Real.log B)| ≤ (m : ℝ) then
    Real.log x + (1 / theta B - Real.log B) else 0

private theorem measurable_spineLogTest (B : ℝ) (m : ℕ) : Measurable (spineLogTest B m) := by
  unfold spineLogTest
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
    (by fun_prop) measurable_const

private theorem abs_spineLogTest_le (B : ℝ) (m : ℕ) {x : ℝ} :
    |spineLogTest B m x| ≤ (m : ℝ) := by
  unfold spineLogTest
  split_ifs with h
  · exact h
  · simp

private theorem abs_spineLogTest_le_abs (B : ℝ) (m : ℕ) (x : ℝ) :
    |spineLogTest B m x| ≤ |Real.log x + (1 / theta B - Real.log B)| := by
  unfold spineLogTest
  split_ifs
  · exact le_rfl
  · simp

private theorem tendsto_spineLogTest (B : ℝ) (x : ℝ) :
    Tendsto (fun m : ℕ => spineLogTest B m x) atTop
      (𝓝 (Real.log x + (1 / theta B - Real.log B))) := by
  obtain ⟨N, hN⟩ := exists_nat_ge |Real.log x + (1 / theta B - Real.log B)|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with m hm
  unfold spineLogTest
  rw [ite_eq_left]
  exact hN.trans (by exact_mod_cast hm)

private theorem spine_log_master {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) :
    (∫ e, evalR B h n e ^ theta B * spineQ B h n e *
      (Real.log (evalR B h n e) + (1 / theta B - Real.log B)) ∂(envMeasure μ n)) =
    tiltedProduct μ B h n * tiltedMass μ B h 0 * spineMeanWLog μ B h n := by
  let d := 1 / theta B - Real.log B
  have hd : 0 ≤ d := (one_inv_theta_sub_log_B_pos hB).le
  have hQ : ∀ᵐ e ∂(envMeasure μ n), |spineQ B h n e| ≤ (2 : ℝ) ^ n := by
    filter_upwards [ae_envPos_aux hpos n] with e he
    apply spine_gibbsMean_abs_le hB h he (fun j => (j : ℝ))
    intro k hk
    norm_cast
    exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hRint : Integrable (evalR B h n) (envMeasure μ n) := by
    have hi := integrable_lawR_of hpos hmean hB h n
    rw [← map_evalR_envMeasure_aux μ B h n] at hi
    simpa only [Function.comp_def, id_eq] using
      (integrable_map_measure hi.aestronglyMeasurable
        (measurable_evalR B h n).aemeasurable).mp hi
  have hlog_int : Integrable (fun e => evalR B h n e ^ theta B *
      |Real.log (evalR B h n e) - Real.log B|) (envMeasure μ n) := by
    have hi : Integrable (fun x : ℝ => x ^ theta B * |Real.log x - Real.log B| ^ (1 : ℝ))
        (lawR μ B h n) := integrable_absTiltedLogRpow_aux hpos hmean hB h n zero_le_one
    rw [← map_evalR_envMeasure_aux μ B h n] at hi
    simpa only [Function.comp_def, Real.rpow_one] using
      (integrable_map_measure (by fun_prop) (measurable_evalR B h n).aemeasurable).mp hi
  have hRtheta : Integrable (fun e => evalR B h n e ^ theta B) (envMeasure μ n) := by
    have hi : Integrable (fun x : ℝ => x ^ theta B) (lawR μ B h n) := by
      simpa using integrable_absTiltedLogRpow_aux hpos hmean hB h n (s := 0) (le_refl 0)
    rw [← map_evalR_envMeasure_aux μ B h n] at hi
    simpa only [Function.comp_def] using
      (integrable_map_measure hi.aestronglyMeasurable
        (measurable_evalR B h n).aemeasurable).mp hi
  have hdom_int : Integrable (fun e => (2 : ℝ) ^ n *
      (evalR B h n e ^ theta B * |Real.log (evalR B h n e) - Real.log B| +
        (1 / theta B) * evalR B h n e ^ theta B)) (envMeasure μ n) :=
    (hlog_int.add (hRtheta.const_mul (1 / theta B))).const_mul _
  have h_meas : ∀ m : ℕ, AEStronglyMeasurable (fun e : Env n =>
      evalR B h n e ^ theta B * spineQ B h n e * spineLogTest B m (evalR B h n e))
      (envMeasure μ n) := by
    intro m
    exact (((Real.continuous_rpow_const (theta_pos hB).le).measurable.comp
      (measurable_evalR B h n)).mul (measurable_spineQ B h n)).mul
      ((measurable_spineLogTest B m).comp (measurable_evalR B h n)) |>.aestronglyMeasurable
  have h_bound : ∀ m : ℕ, ∀ᵐ e ∂(envMeasure μ n),
      ‖evalR B h n e ^ theta B * spineQ B h n e * spineLogTest B m (evalR B h n e)‖ ≤
        (2 : ℝ) ^ n * (evalR B h n e ^ theta B *
          |Real.log (evalR B h n e) - Real.log B| + (1 / theta B) * evalR B h n e ^ theta B) := by
    intro m
    filter_upwards [ae_envPos_aux hpos n, hQ] with e he hq
    change |evalR B h n e ^ theta B * spineQ B h n e * spineLogTest B m (evalR B h n e)| ≤ _
    rw [abs_mul]
    have hR : 0 < evalR B h n e := evalR_pos_aux (B := B) (by linarith) h n he
    have hpow : 0 ≤ evalR B h n e ^ theta B := (Real.rpow_pos_of_pos hR _).le
    have hg : |spineLogTest B m (evalR B h n e)| ≤
        |Real.log (evalR B h n e) - Real.log B| + 1 / theta B := by
      calc
        _ ≤ |Real.log (evalR B h n e) + d| := abs_spineLogTest_le_abs B m _
        _ ≤ |Real.log (evalR B h n e) - Real.log B| + 1 / theta B := by
          rw [show Real.log (evalR B h n e) + d =
            (Real.log (evalR B h n e) - Real.log B) + 1 / theta B by dsimp [d]; ring]
          simpa only [abs_of_pos (one_div_pos.mpr (theta_pos hB))] using
            abs_add_le (Real.log (evalR B h n e) - Real.log B) (1 / theta B)
    calc
      |evalR B h n e ^ theta B * spineQ B h n e| * |spineLogTest B m (evalR B h n e)| ≤
          (evalR B h n e ^ theta B * (2 : ℝ) ^ n) *
            (|Real.log (evalR B h n e) - Real.log B| + 1 / theta B) := by
        rw [abs_mul, abs_of_nonneg hpow]
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hq hpow
        · exact hg
        · positivity
        · positivity
      _ = _ := by ring
  have h_lim : ∀ᵐ e ∂(envMeasure μ n), Tendsto (fun m : ℕ =>
      evalR B h n e ^ theta B * spineQ B h n e * spineLogTest B m (evalR B h n e)) atTop
      (𝓝 (evalR B h n e ^ theta B * spineQ B h n e *
        (Real.log (evalR B h n e) + (1 / theta B - Real.log B)))) := by
    filter_upwards with e
    exact (tendsto_spineLogTest B (evalR B h n e)).const_mul
      (evalR B h n e ^ theta B * spineQ B h n e)
  have hL := tendsto_integral_of_dominated_convergence _ h_meas hdom_int h_bound h_lim
  have hs_meas : ∀ m : ℕ, AEStronglyMeasurable (fun z : ℝ × (Fin n → ℝ) =>
      spineW B n z.1 z.2 * spineLogTest B m (spineT B n z.1 z.2))
      (spineMeasure μ B h n) := by
    intro m
    have hmW : Measurable (fun z : ℝ × (Fin n → ℝ) => spineW B n z.1 z.2) := by
      dsimp [spineW, spineWalk]
      fun_prop
    have hmT : Measurable (fun z : ℝ × (Fin n → ℝ) => spineT B n z.1 z.2) := by
      dsimp [spineW, spineT, spineWalk]
      fun_prop
    exact hmW.mul ((measurable_spineLogTest B m).comp hmT) |>.aestronglyMeasurable
  have hs_int : Integrable (fun z : ℝ × (Fin n → ℝ) =>
      |spineW B n z.1 z.2 * (Real.log (spineT B n z.1 z.2) +
        (1 / theta B - Real.log B))|) (spineMeasure μ B h n) :=
    (integrable_spine_aux hpos hmean hB h n).2.abs
  have hs_bound : ∀ m : ℕ, ∀ᵐ z ∂(spineMeasure μ B h n),
      ‖spineW B n z.1 z.2 * spineLogTest B m (spineT B n z.1 z.2)‖ ≤
        |spineW B n z.1 z.2 * (Real.log (spineT B n z.1 z.2) +
          (1 / theta B - Real.log B))| := by
    intro m
    filter_upwards with z
    change |spineW B n z.1 z.2 * spineLogTest B m (spineT B n z.1 z.2)| ≤ _
    calc
      _ = |spineW B n z.1 z.2| * |spineLogTest B m (spineT B n z.1 z.2)| := abs_mul _ _
      _ ≤ |spineW B n z.1 z.2| * |Real.log (spineT B n z.1 z.2) +
          (1 / theta B - Real.log B)| :=
        mul_le_mul_of_nonneg_left (abs_spineLogTest_le_abs B m _) (abs_nonneg _)
      _ = _ := (abs_mul _ _).symm
  have hs_lim : ∀ᵐ z ∂(spineMeasure μ B h n), Tendsto (fun m : ℕ =>
      spineW B n z.1 z.2 * spineLogTest B m (spineT B n z.1 z.2)) atTop
      (𝓝 (spineW B n z.1 z.2 * (Real.log (spineT B n z.1 z.2) +
        (1 / theta B - Real.log B)))) := by
    filter_upwards with z
    exact tendsto_const_nhds.mul (tendsto_spineLogTest B _)
  have hR := tendsto_integral_of_dominated_convergence _ hs_meas hs_int hs_bound hs_lim
  have hm : ∀ m : ℕ,
      (∫ e, evalR B h n e ^ theta B * spineQ B h n e * spineLogTest B m (evalR B h n e)
        ∂(envMeasure μ n)) = tiltedProduct μ B h n * tiltedMass μ B h 0 *
      ∫ z, spineW B n z.1 z.2 * spineLogTest B m (spineT B n z.1 z.2)
        ∂(spineMeasure μ B h n) := by
    intro m
    exact spine_master_bounded hpos hmean hB h n (spineLogTest B m)
      (measurable_spineLogTest B m) (Nat.cast_nonneg m) (fun x _ => abs_spineLogTest_le B m)
  have hR' : Tendsto (fun m : ℕ => ∫ e, evalR B h n e ^ theta B * spineQ B h n e *
      spineLogTest B m (evalR B h n e) ∂(envMeasure μ n)) atTop
      (𝓝 (tiltedProduct μ B h n * tiltedMass μ B h 0 * spineMeanWLog μ B h n)) := by
    simp_rw [hm]
    exact hR.const_mul (tiltedProduct μ B h n * tiltedMass μ B h 0)
  exact tendsto_nhds_unique hL hR'

/-- The field derivatives, normalized by `tiltedProduct`, are the two spine
expectations, and `1 / theta B - Real.log B` is positive.  This proves
`DiamondPinning.spine_identities` (in `DiamondPinning.Statements.Response`). -/
theorem spine_identities_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    (n : ℕ) :
    0 < 1 / theta B - Real.log B ∧
      deriv (fun h' => tiltedMass μ B h' n) h / tiltedProduct μ B h n =
        theta B * tiltedMass μ B h 0 * spineMeanW μ B h n ∧
      deriv (fun h' => tiltedLogMoment μ B h' 1 n) h / tiltedProduct μ B h n =
        theta B * tiltedMass μ B h 0 * spineMeanWLog μ B h n := by
  have hθ : 0 < theta B := theta_pos hB
  have hPi : 0 < tiltedProduct μ B h n := spine_tiltedProduct_pos hpos hmean hB h n
  refine ⟨one_inv_theta_sub_log_B_pos hB, ?_, ?_⟩
  · rw [(hasDerivAt_tiltedMass_aux hpos hmean hB h n).deriv]
    have hm := spine_master_bounded hpos hmean hB h n (fun _ => 1) measurable_const
      (C := 1) zero_le_one (fun _ _ => by simp)
    have hm' : contactMoment μ B h 1 n = tiltedProduct μ B h n * tiltedMass μ B h 0 *
        spineMeanW μ B h n := by
      simpa only [contactMoment, pow_one, spineMeanW, mul_one, spineQ] using hm
    rw [hm']
    field_simp [hPi.ne']
  · rw [(hasDerivAt_tiltedLogMoment_aux hpos hmean hB h 1 n).deriv]
    have hm := spine_log_master hpos hmean hB h n
    have hform : tiltedLogMomentDeriv μ B h 1 n = theta B *
        (∫ e, evalR B h n e ^ theta B * spineQ B h n e *
          (Real.log (evalR B h n e) + (1 / theta B - Real.log B)) ∂(envMeasure μ n)) := by
      rw [tiltedLogMomentDeriv, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_envPos_aux hpos n] with e he
      dsimp [spineQ]
      have hθne : theta B ≠ 0 := hθ.ne'
      simp only [pow_one, pow_zero, mul_one]
      field_simp [hθne]
      norm_num only [Nat.cast_one]
      ring
    rw [hform, hm]
    field_simp [hPi.ne']


end DiamondPinning
