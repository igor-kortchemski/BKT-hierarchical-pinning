module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Proofs.FieldDerivProof
public import DiamondPinning.Proofs.CriticalMoments
public import DiamondPinning.Proofs.BallotProof
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Strict transversality of the critical field response

The proof uses a walk with a harmonic barrier that dominates twice the logarithm.
The passage bound controls the expected cost of the drift before killing, and
the surviving payoff gives a uniform positive lower bound for the mixed spine
integral. For convergence, a linear combination of the mass and signed moment
has an antitone correction kernel. Its differentiated recurrence controls the
upward increments of the normalized response.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Asymptotics
open scoped BigOperators ENNReal

/-- A sequence bounded below on a tail converges if its upward increments
are bounded by a summable sequence of nonnegative errors. -/
private theorem response_tendsto_of_step {u e : ℕ → ℝ}
    (he : Summable e) (he0 : ∀ n, 0 ≤ e n) {b : ℝ}
    (hb : ∀ᶠ n in atTop, b ≤ u n)
    (hu : ∀ᶠ n in atTop, u (n + 1) ≤ u n + e n) :
    ∃ c : ℝ, b ≤ c ∧ Tendsto u atTop (𝓝 c) := by
  let s : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, e i
  let v : ℕ → ℝ := fun n => u n - s n
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hb.and hu)
  have hv : AntitoneOn v (Set.Ici N) := by
    rw [Set.Ici, ← antitone_add_nat_iff_antitoneOn_nat_Ici]
    apply antitone_nat_of_succ_le
    intro n
    have h := (hN (n + N) (by omega)).2
    change u (n + 1 + N) - s (n + 1 + N) ≤ u (n + N) - s (n + N)
    rw [show n + 1 + N = (n + N) + 1 by omega]
    dsimp [s]
    rw [Finset.sum_range_succ]
    linarith
  have hbd : BddBelow (v '' Set.Ici N) := by
    refine ⟨b - ∑' n, e n, ?_⟩
    rintro _ ⟨n, hn, rfl⟩
    dsimp [v, s]
    linarith [(hN n hn).1, he.sum_le_tsum (Finset.range n) (fun i _ => he0 i)]
  have ht := (Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici hv hbd).add
    he.hasSum.tendsto_sum_nat
  have hvu : (fun n => v n + s n) = u := by
    funext n
    simp [v]
  rw [hvu] at ht
  exact ⟨_, le_of_tendsto_of_tendsto tendsto_const_nhds ht hb, ht⟩

/-- A positive limit of the normalized response transfers the quadratic
order of the product to the unnormalized response. -/
private theorem response_quadratic {E P : ℕ → ℝ} {C κ : ℝ}
    (hC : 0 < C) (hκ : 0 < κ)
    (hP : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) ^ 2 / C ≤ P n ∧ P n ≤ C * ((n : ℝ) + 1) ^ 2)
    (hlim : Tendsto (fun n => E n / P n) atTop (𝓝 κ)) :
    E =Θ[atTop] fun n : ℕ => (n : ℝ) ^ 2 := by
  have hratio : (fun n => E n / P n) =Θ[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    (isTheta_of_div_tendsto_nhds_ne_zero (by simpa using hlim) hκ.ne').symm
  have hn : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have hP0 (n : ℕ) (hn : 1 ≤ n) : 0 < P n :=
    (div_pos (by positivity) hC).trans_le (hP n hn).1
  have hPθ : P =Θ[atTop] fun n : ℕ => (n : ℝ) ^ 2 := by
    constructor
    · refine IsBigO.of_bound (4 * C) ?_
      filter_upwards [hn] with n hn
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [Real.norm_eq_abs, abs_of_pos (hP0 n hn), Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc
        P n ≤ C * ((n : ℝ) + 1) ^ 2 := (hP n hn).2
        _ ≤ 4 * C * (n : ℝ) ^ 2 := by
          have h := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) + 1)
              (show (n : ℝ) + 1 ≤ 2 * n by linarith) 2) hC.le
          nlinarith only [h]
    · refine IsBigO.of_bound C ?_
      filter_upwards [hn] with n hn
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs, abs_of_pos (hP0 n hn)]
      have h := (div_le_iff₀ hC).1 (hP n hn).1
      nlinarith only [h, Nat.cast_nonneg (α := ℝ) n]
  have hmul := hratio.mul hPθ
  have heq : (fun n => E n / P n * P n) =ᶠ[atTop] E := by
    filter_upwards [hn] with n h
    exact div_mul_cancel₀ _ (hP0 n h).ne'
  exact ⟨by simpa only [one_mul] using hmul.1.congr' heq EventuallyEq.rfl,
    by simpa only [one_mul] using hmul.2.congr' EventuallyEq.rfl heq⟩

/-- Once the normalized mixed derivative has a positive lower bound, the
combined derivative recurrence and the linear first derivative give the
positive residue. -/
private theorem response_residue_of_recurrence {A H D E P : ℕ → ℝ}
    {C L M K c : ℝ}
    (hC : 0 < C) (hL : 0 ≤ L) (hM : 0 ≤ M) (hK : 0 ≤ K) (hc : 0 < c)
    (hP : ∀ n, 0 < P n) (hPs : ∀ n, P (n + 1) = A n * P n)
    (hPi : Summable (fun n => (P n)⁻¹))
    (hPquad : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) ^ 2 / C ≤ P n ∧ P n ≤ C * ((n : ℝ) + 1) ^ 2)
    (hD : ∀ n, 0 ≤ D n ∧ D n ≤ L * ((n : ℝ) + 1))
    (hH : ∀ᶠ n in atTop, |H n| ≤ K / ((n : ℝ) + 1))
    (hrec : ∀ᶠ n in atTop, E (n + 1) + M * D (n + 1) ≤
      A n * (E n + M * D n) + H n * D n)
    (hflux : ∀ᶠ n in atTop, c ≤ E n / P n) :
    ∃ κ : ℝ, 0 < κ ∧ Tendsto (fun n => E n / P n) atTop (𝓝 κ) ∧
      E =Θ[atTop] fun n : ℕ => (n : ℝ) ^ 2 := by
  have hPi' : Summable (fun n => (P (n + 1))⁻¹) := (summable_nat_add_iff 1).2 hPi
  let u : ℕ → ℝ := fun n => (E n + M * D n) / P n
  have hlow : ∀ᶠ n in atTop, c ≤ u n := by
    filter_upwards [hflux] with n hn
    dsimp [u]
    rw [add_div]
    exact hn.trans (le_add_of_nonneg_right (div_nonneg (mul_nonneg hM (hD n).1) (hP n).le))
  have hstep : ∀ᶠ n in atTop, u (n + 1) ≤ u n + K * L * (P (n + 1))⁻¹ := by
    filter_upwards [hrec, hH] with n hr hh
    have ha : A n ≠ 0 := by
      intro h
      have hp := hP (n + 1)
      simp [hPs, h] at hp
    have hhd : H n * D n ≤ K * L := calc
      H n * D n ≤ (K / ((n : ℝ) + 1)) * D n :=
        mul_le_mul_of_nonneg_right ((le_abs_self _).trans hh) (hD n).1
      _ ≤ (K / ((n : ℝ) + 1)) * (L * ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (hD n).2 (by positivity)
      _ = K * L := by field_simp
    calc
      u (n + 1) ≤ (A n * (E n + M * D n) + K * L) / P (n + 1) :=
        div_le_div_of_nonneg_right (hr.trans (add_le_add_right hhd _)) (hP _).le
      _ = _ := by
        dsimp [u]
        rw [add_div, div_eq_mul_inv (K * L), hPs]
        field_simp [ha, (hP n).ne']
  obtain ⟨κ, hk, hlim⟩ := response_tendsto_of_step (hPi'.mul_left (K * L))
    (fun n => mul_nonneg (mul_nonneg hK hL) (inv_pos.mpr (hP n.succ)).le) hlow hstep
  have hzero : Tendsto (fun n => M * D n / P n) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have htop : Tendsto (fun n : ℕ => M * L * C * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds (x := M * L * C)).mul ht
    apply squeeze_zero' (Eventually.of_forall fun n =>
      div_nonneg (mul_nonneg hM (hD n).1) (hP n).le) ?_ htop
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have ht : 0 < (n : ℝ) + 1 := by positivity
    calc
      M * D n / P n ≤ M * (L * ((n : ℝ) + 1)) / (((n : ℝ) + 1) ^ 2 / C) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (hD n).2 hM)
          (by positivity) (hPquad n hn).1
      _ = M * L * C * ((n : ℝ) + 1)⁻¹ := by field_simp
  have hE := hlim.sub hzero
  rw [sub_zero] at hE
  have hEq : (fun n => u n - M * D n / P n) = fun n => E n / P n := by
    funext n
    simp [u, add_div]
  rw [hEq] at hE
  exact ⟨κ, hc.trans_le hk, hE, response_quadratic hC (hc.trans_le hk) hPquad hE⟩

private theorem response_eval_floor {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ)
    (e : Env n) (he : Env.Pos n e) : floorSeq B n ≤ evalR B h n e := by
  induction n with
  | zero =>
    rw [floorSeq_zero]
    exact (evalR_pos_aux (by linarith) h 0 he).le
  | succ n ih =>
    obtain ⟨he₁, he₂⟩ := (show Env.Pos n e.1 ∧ Env.Pos n e.2 from he)
    rw [evalR_succ, floorSeq_succ]
    apply div_le_div_of_nonneg_right _ (by linarith)
    apply add_le_add_left
    rw [pow_two]
    exact mul_le_mul (ih e.1 he₁) (ih e.2 he₂) (floorSeq_nonneg hB n)
      (evalR_pos_aux (by linarith) h n he₁).le

private theorem response_pair_mono {B : ℝ} (hB : 2 < B) (n : ℕ)
    (e : Env n × Env n) (he : Env.Pos n e.1 ∧ Env.Pos n e.2) :
    Monotone (fun h => pairEval B 0 h n e) := by
  intro x y hxy
  change pairEval B 0 x n e ≤ pairEval B 0 y n e
  rw [← sum_pairContactPoly_coeff_exp B 0 x n e, ← sum_pairContactPoly_coeff_exp B 0 y n e]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg k.val)))
    (pairContactPoly_coeff_nonneg (by linarith) le_rfl n e he k.val)

private theorem response_pair_floor {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (e : Env n × Env n) (he : Env.Pos n e.1 ∧ Env.Pos n e.2) :
    floorSeq B 1 ^ 2 ≤ pairEval B 0 h n e := by
  simp only [pairEval, add_zero, pow_two]
  exact mul_le_mul ((floorSeq_one_le hB hn).trans (response_eval_floor hB h n e.1 he.1))
    ((floorSeq_one_le hB hn).trans (response_eval_floor hB h n e.2 he.2))
    (floorSeq_nonneg hB 1) (evalR_pos_aux (by linarith) h n he.1).le

private noncomputable def responseWeight (B M s : ℝ) : ℝ :=
  s ^ theta B * (Real.log s - 2 * Real.log B + M)

private theorem responseWeight_hasDerivAt {B M s : ℝ} (hs : 0 < s) :
    HasDerivAt (responseWeight B M)
      (s ^ (theta B - 1) * (1 + theta B * (Real.log s - 2 * Real.log B + M))) s := by
  have hl := (((Real.hasDerivAt_log hs.ne').sub_const (2 * Real.log B)).add_const M)
  have hp := Real.hasDerivAt_rpow_const (p := theta B) (Or.inl hs.ne')
  convert hp.mul hl using 1
  · rfl
  rw [Real.rpow_sub_one hs.ne']
  field_simp
  ring

/-- Adding a multiple of the mass to the first signed moment makes its
correction kernel antitone on the range of the pair product. -/
private theorem response_kernel_antitone {B : ℝ} (hB : 2 < B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ M' ≥ M,
      AntitoneOn (fun s => responseWeight B M' (s + (B - 1)) - responseWeight B M' s)
        (Set.Ici (floorSeq B 1 ^ 2)) := by
  let t := floorSeq B 1 ^ 2
  have ht : 0 < t := sq_pos_of_pos (floorSeq_one_pos hB)
  let p := 1 - theta B
  have hp : 0 < p := sub_pos.mpr (theta_lt_one hB)
  refine ⟨max 0 (2 * Real.log B - Real.log t + 1 / p), le_max_left _ _, ?_⟩
  intro M hM
  let f := responseWeight B M
  let g : ℝ → ℝ := fun s =>
    s ^ (theta B - 1) * (1 + theta B * (Real.log s - 2 * Real.log B + M))
  have hg (s : ℝ) (hs : 0 < s) :
      HasDerivAt g
        (s ^ (theta B - 2) * ((theta B - 1) *
          (1 + theta B * (Real.log s - 2 * Real.log B + M)) + theta B)) s := by
    have hl := (Real.hasDerivAt_log hs.ne').sub_const (2 * Real.log B) |>.add_const M
    have hl' := (hl.const_mul (theta B)).const_add 1
    have hd := (Real.hasDerivAt_rpow_const (p := theta B - 1) (Or.inl hs.ne')).mul hl'
    convert hd using 1
    rw [show theta B - 1 - 1 = theta B - 2 by ring,
      show theta B - 1 = theta B - 2 + 1 by ring,
      Real.rpow_add_one hs.ne']
    field_simp
  have hganti : AntitoneOn g (Set.Ici t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact fun s hs => (hg s (ht.trans_le hs)).continuousAt.continuousWithinAt
    · intro s hs
      exact (hg s (ht.trans_le (interior_subset hs))).differentiableAt.differentiableWithinAt
    · intro s hs
      have hts : t ≤ s := interior_subset hs
      have hs0 := ht.trans_le hts
      rw [(hg s hs0).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hs0.le _)
      have hl := Real.log_le_log ht hts
      have hM' := (le_max_right 0 (2 * Real.log B - Real.log t + 1 / p)).trans hM
      have hL : 1 / p ≤ Real.log s - 2 * Real.log B + M := by linarith
      have hθ := theta_pos hB
      have ht' := mul_le_mul_of_nonneg_left hL hθ.le
      have hp' := mul_le_mul_of_nonneg_left (add_le_add_left ht' 1) hp.le
      have hi : p * (theta B * (1 / p)) = theta B := by field_simp
      rw [show theta B - 1 = -p by dsimp [p]; ring]
      change -p * (1 + theta B * (Real.log s - 2 * Real.log B + M)) + theta B ≤ 0
      nlinarith only [hi, hp', hp.le]
  have hd (s : ℝ) (hs : t ≤ s) :
      HasDerivAt (fun s => f (s + (B - 1)) - f s) (g (s + (B - 1)) - g s) s := by
    have hs' : 0 < s + (B - 1) := by linarith [ht.trans_le hs]
    have hd₁ : HasDerivAt (fun x => f (x + (B - 1))) (g (s + (B - 1))) s := by
      simpa only [Function.comp_def, id_eq, mul_one, f, g] using
        ((responseWeight_hasDerivAt (M := M) hs').comp s ((hasDerivAt_id s).add_const (B - 1)))
    exact hd₁.sub (responseWeight_hasDerivAt (M := M) (ht.trans_le hs))
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
  · exact fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    have hs' : t ≤ s := interior_subset hs
    rw [(hd s hs').deriv]
    exact sub_nonpos.mpr (hganti hs' (by linarith : t ≤ s + (B - 1)) (by linarith))

private theorem response_B_pow {B : ℝ} (hB : 2 < B) : B ^ theta B = 2 := by
  have hlog := Real.log_pos (show 1 < B by linarith)
  rw [Real.rpow_def_of_pos (by linarith : 0 < B), theta, mul_comm (Real.log B), div_mul_cancel₀ _ hlog.ne', Real.exp_log (by norm_num : (0 : ℝ) < 2)]

private theorem response_mass_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : 0 < tiltedMass μ B h n := by
  letI := isProbabilityMeasure_lawR (μ := μ) B h n
  have hi : Integrable (fun x : ℝ => x ^ theta B) (lawR μ B h n) := by
    simpa only [Real.rpow_zero, mul_one] using
      integrable_absTiltedLogRpow_aux hpos hmean hB h n (s := 0) (le_refl 0)
  have ha : ∀ᵐ x ∂lawR μ B h n, 0 < x ^ theta B := by
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    exact Real.rpow_pos_of_pos hx _
  refine (integral_pos_iff_support_of_nonneg_ae (ha.mono fun _ hx => hx.le) hi).2 ?_
  exact pos_iff_ne_zero.2 (fun hz => by
    obtain ⟨x, hx, hzero⟩ := (ha.and (ae_iff.mp hz)).exists
    exact hx.ne' hzero)

private theorem response_env_moment_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n k : ℕ) :
    Integrable (fun e => evalR B h n e ^ theta B * (Real.log (evalR B h n e) - Real.log B) ^ k)
      (envMeasure μ n) := by
  have hi := integrable_absTiltedLogRpow_aux hpos hmean hB h n (s := (k : ℝ)) (by positivity)
  rw [← map_evalR_envMeasure_aux μ B h n] at hi
  have hc := (integrable_map_measure (f := evalR B h n) (g := fun x : ℝ =>
      x ^ theta B * |Real.log x - Real.log B| ^ (k : ℝ))
    (by fun_prop) (measurable_evalR B h n).aemeasurable).1 hi
  have ht := (theta_pos hB).le
  have hm := measurable_evalR B h n
  refine hc.mono (by fun_prop) ?_
  filter_upwards [ae_envPos_aux hpos n] with e he
  have hp := evalR_pos_aux (by linarith : 1 < B) h n he
  simp [Real.norm_eq_abs, Real.rpow_natCast, abs_of_nonneg (Real.rpow_nonneg hp.le (theta B))]

private theorem response_env_moment_integral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (B h : ℝ) (n k : ℕ) :
    (∫ e, evalR B h n e ^ theta B * (Real.log (evalR B h n e) - Real.log B) ^ k
      ∂envMeasure μ n) = tiltedLogMoment μ B h k n := by
  rw [tiltedLogMoment, ← map_evalR_envMeasure_aux μ B h n,
    integral_map (measurable_evalR B h n).aemeasurable (by fun_prop)]

private theorem response_combined_step {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B M : ℝ} (hB : 2 < B)
    (hM : AntitoneOn (fun s => responseWeight B M (s + (B - 1)) - responseWeight B M s)
      (Set.Ici (floorSeq B 1 ^ 2))) (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    deriv (fun h' => tiltedLogMoment μ B h' 1 (n + 1)) h +
      M * deriv (fun h' => tiltedMass μ B h' (n + 1)) h ≤
      tiltedMass μ B h n * (deriv (fun h' => tiltedLogMoment μ B h' 1 n) h +
        M * deriv (fun h' => tiltedMass μ B h' n) h) +
      tiltedLogMoment μ B h 1 n * deriv (fun h' => tiltedMass μ B h' n) h := by
  let A (n : ℕ) (x : ℝ) := tiltedMass μ B x n
  let H (n : ℕ) (x : ℝ) := tiltedLogMoment μ B x 1 n
  let ν := envMeasure μ n
  let K (x : ℝ) (e : Env n × Env n) :=
    responseWeight B M (pairEval B 0 x n e + (B - 1)) - responseWeight B M (pairEval B 0 x n e)
  have he : ∀ᵐ e : Env n × Env n ∂ν.prod ν, Env.Pos n e.1 ∧ Env.Pos n e.2 :=
    ae_envPos_aux hpos (n + 1)
  have hB0 : 0 < B := by linarith
  have hAt x m : Integrable (fun e => evalR B x m e ^ theta B) (envMeasure μ m) := by
    simpa only [pow_zero, mul_one] using response_env_moment_integrable hpos hmean hB x m 0
  have hHt x m : Integrable (fun e => evalR B x m e ^ theta B *
      (Real.log (evalR B x m e) - Real.log B)) (envMeasure μ m) := by
    simpa only [pow_one] using response_env_moment_integrable hpos hmean hB x m 1
  have hAi x m : (∫ e, evalR B x m e ^ theta B ∂envMeasure μ m) = A m x := by
    simpa only [A, tiltedLogMoment, tiltedMass, pow_zero, mul_one] using
      response_env_moment_integral (μ := μ) B x m 0
  have hHi x m : (∫ e, evalR B x m e ^ theta B *
      (Real.log (evalR B x m e) - Real.log B) ∂envMeasure μ m) = H m x := by
    simpa only [H, pow_one] using response_env_moment_integral (μ := μ) B x m 1
  let KInt (x : ℝ) := ∫ e, K x e ∂ν.prod ν
  have hr x : Integrable (K x) (ν.prod ν) ∧
      H (n + 1) x + M * A (n + 1) x =
        A n x * (H n x + M * A n x / 2) + KInt x / 2 := by
    let a (e : Env n) := evalR B x n e ^ theta B
    let b (e : Env n) := a e * (Real.log (evalR B x n e) - Real.log B)
    let a' (e : Env n × Env n) := evalR B x (n + 1) e ^ theta B
    let b' (e : Env n × Env n) := a' e * (Real.log (evalR B x (n + 1) e) - Real.log B)
    let f (e : Env n × Env n) := 2 * (b' e + M * a' e) -
      (b e.1 * a e.2 + a e.1 * b e.2 + M * (a e.1 * a e.2))
    have hi₁ : Integrable b ν := hHt x n
    have hi₂ : Integrable a ν := hAt x n
    have hi₃ : Integrable b' (ν.prod ν) := hHt x (n + 1)
    have hi₄ : Integrable a' (ν.prod ν) := hAt x (n + 1)
    have hf : Integrable f (ν.prod ν) :=
      ((hi₃.add (hi₄.const_mul M)).const_mul 2).sub
        (((hi₁.mul_prod hi₂).add (hi₂.mul_prod hi₁)).add ((hi₂.mul_prod hi₂).const_mul M))
    have hEq : f =ᵐ[ν.prod ν] K x := by
      filter_upwards [he] with e he
      have h1 := evalR_pos_aux (by linarith : 1 < B) x n he.1
      have h2 := evalR_pos_aux (by linarith : 1 < B) x n he.2
      have hs : 0 < evalR B x n e.1 * evalR B x n e.2 + (B - 1) := by
        have := mul_pos h1 h2
        linarith
      have hsuc : evalR B x (n + 1) e =
          (evalR B x n e.1 * evalR B x n e.2 + (B - 1)) / B := rfl
      simp only [f, a, b, a', b', K, responseWeight, pairEval, add_zero, hsuc,
        Real.div_rpow hs.le hB0.le, response_B_pow hB, Real.log_div hs.ne' hB0.ne',
        Real.mul_rpow h1.le h2.le, Real.log_mul h1.ne' h2.ne']
      ring
    refine ⟨hf.congr hEq, ?_⟩
    have hij := integral_congr_ae hEq
    change (∫ e, f e ∂ν.prod ν) = KInt x at hij
    dsimp only [f] at hij
    have hi₅ : Integrable (fun e : Env n × Env n => b' e + M * a' e) (ν.prod ν) :=
      hi₃.add (hi₄.const_mul M)
    have hi₆ : Integrable (fun e : Env n × Env n => b e.1 * a e.2 + a e.1 * b e.2) (ν.prod ν) :=
      (hi₁.mul_prod hi₂).add (hi₂.mul_prod hi₁)
    have hi₇ : Integrable (fun e : Env n × Env n => M * (a e.1 * a e.2)) (ν.prod ν) :=
      (hi₂.mul_prod hi₂).const_mul M
    have hi₈ : Integrable (fun e : Env n × Env n => 2 * (b' e + M * a' e)) (ν.prod ν) :=
      hi₅.const_mul 2
    have hi₉ : Integrable (fun e : Env n × Env n =>
        b e.1 * a e.2 + a e.1 * b e.2 + M * (a e.1 * a e.2)) (ν.prod ν) := hi₆.add hi₇
    rw [integral_sub hi₈ hi₉, integral_const_mul, integral_add hi₃ (hi₄.const_mul M),
      integral_const_mul, integral_add hi₆ hi₇, integral_add (hi₁.mul_prod hi₂) (hi₂.mul_prod hi₁),
      integral_const_mul, integral_prod_mul b a, integral_prod_mul a b, integral_prod_mul a a] at hij
    have hab : (∫ e, a e ∂ν) = A n x := hAi x n
    have hbb : (∫ e, b e ∂ν) = H n x := hHi x n
    rw [hab, hbb] at hij
    change 2 * ((∫ e : Env (n + 1), evalR B x (n + 1) e ^ theta B *
        (Real.log (evalR B x (n + 1) e) - Real.log B) ∂envMeasure μ (n + 1)) + M *
      (∫ e : Env (n + 1), evalR B x (n + 1) e ^ theta B ∂envMeasure μ (n + 1))) - _ = _ at hij
    rw [hHi x (n + 1), hAi x (n + 1)] at hij
    linarith only [hij]
  have hka : Antitone KInt := by
    intro x y hxy
    refine integral_mono_ae (hr y).1 (hr x).1 ?_
    filter_upwards [he] with e he
    exact hM (response_pair_floor hB x hn e he) (response_pair_floor hB y hn e he)
      (response_pair_mono hB n e he hxy)
  have hA m : HasDerivAt (A m) (deriv (A m) h) h :=
    (hasDerivAt_tiltedMass_aux hpos hmean hB h m).differentiableAt.hasDerivAt
  have hH m : HasDerivAt (H m) (deriv (H m) h) h :=
    (hasDerivAt_tiltedLogMoment_aux hpos hmean hB h 1 m).differentiableAt.hasDerivAt
  have hfun : KInt = fun x => 2 * (H (n + 1) x + M * A (n + 1) x -
      A n x * (H n x + M * A n x / 2)) := by
    funext x
    linarith only [(hr x).2]
  have hd := (((hH (n + 1)).add ((hA (n + 1)).const_mul M)).sub
    ((hA n).mul ((hH n).add (((hA n).const_mul M).div_const 2)))).const_mul 2
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at hd
  rw [← hfun] at hd
  have hh := hka.deriv_nonpos (x := h)
  rw [hd.deriv] at hh
  change deriv (H (n + 1)) h + M * deriv (A (n + 1)) h ≤
    A n h * (deriv (H n) h + M * deriv (A n) h) + H n h * deriv (A n) h
  linarith only [hh]

open ProbabilityTheory

private noncomputable def responseWalk {Ω : Type*} (Y : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ := ∑ j ∈ Finset.range n, Y j ω

private def responseSurvives {Ω : Type*} (Y : ℕ → Ω → ℝ) (z : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ k ≤ n, 0 ≤ z + responseWalk Y k ω}

private theorem responseWalk_measurable {Ω : Type*} [MeasurableSpace Ω] {Y : ℕ → Ω → ℝ}
    (hY : ∀ j, Measurable (Y j)) (n : ℕ) : Measurable (responseWalk Y n) :=
  Finset.measurable_sum _ fun j _ => hY j

private theorem responseSurvives_measurable {Ω : Type*} [MeasurableSpace Ω] {Y : ℕ → Ω → ℝ}
    (hY : ∀ j, Measurable (Y j)) (z : ℝ) (n : ℕ) :
    MeasurableSet (responseSurvives Y z n) := by
  have he : responseSurvives Y z n =
      ⋂ k : Fin (n + 1), {ω | 0 ≤ z + responseWalk Y k ω} := by
    ext ω
    simp only [responseSurvives, Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h k => h k (Nat.le_of_lt_succ k.isLt),
      fun h k hk => h ⟨k, Nat.lt_succ_of_le hk⟩⟩
  rw [he]
  exact MeasurableSet.iInter fun k =>
    measurableSet_le measurable_const ((responseWalk_measurable hY k).const_add z)

private theorem response_survival_indep {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : ℕ → Ω → ℝ} (hY : ∀ j, Measurable (Y j)) (hI : iIndepFun Y μ)
    (z : ℝ) (n : ℕ) :
    IndepFun ((responseSurvives Y z n).indicator (1 : Ω → ℝ)) (Y n) μ := by
  let P := {j // j ∈ Finset.range n}
  let W (u : P → ℝ) (k : ℕ) := ∑ j : P, if j.val < k then u j else 0
  let A : Set (P → ℝ) := ⋂ k : Fin (n + 1), {u | 0 ≤ z + W u k}
  have hA : MeasurableSet A := by
    apply MeasurableSet.iInter
    intro k
    apply measurableSet_le measurable_const
    apply Measurable.const_add
    exact Finset.measurable_sum _ fun j _ => by
      split_ifs
      · exact measurable_pi_apply j
      · exact measurable_const
  have hW (ω : Ω) (k : ℕ) (hk : k ≤ n) :
      W (fun j => Y j ω) k = responseWalk Y k ω := by
    dsimp [W, responseWalk]
    rw [Finset.sum_coe_sort (Finset.range n) (fun j => if j < k then Y j ω else 0)]
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun hj => ⟨hj.trans_le hk, hj⟩⟩
  let X (ω : Ω) (j : P) := Y j ω
  have hpre : X ⁻¹' A = responseSurvives Y z n := by
    ext ω
    simp only [A, responseSurvives, Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h k hk => (hW ω k hk) ▸ h ⟨k, Nat.lt_succ_of_le hk⟩,
      fun h k => (hW ω k (Nat.le_of_lt_succ k.isLt)).symm ▸ h k (Nat.le_of_lt_succ k.isLt)⟩
  have hblock := hI.indepFun_finset (Finset.range n) {n} (by simp) hY
  have hcomp := hblock.comp (φ := A.indicator (1 : (P → ℝ) → ℝ))
    (ψ := fun x : ({j // j ∈ ({n} : Finset ℕ)} → ℝ) =>
      x ⟨n, Finset.mem_singleton_self n⟩)
    (measurable_one.indicator hA) (show Measurable (fun x : ({j // j ∈ ({n} : Finset ℕ)} → ℝ) =>
      x ⟨n, Finset.mem_singleton_self n⟩) from measurable_pi_apply _)
  have hEq : A.indicator (1 : (P → ℝ) → ℝ) ∘ X =
      (responseSurvives Y z n).indicator (1 : Ω → ℝ) := by
    rw [← hpre]
    funext ω
    exact (Set.indicator_comp_right X).symm
  exact hEq ▸ hcomp

private theorem response_stopped_expectation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ j, Measurable (Y j)) (hYi : ∀ j, Integrable (Y j) μ)
    (hI : iIndepFun Y μ) {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    z + ∑ j ∈ Finset.range n, μ.real (responseSurvives Y z j) * (∫ ω, Y j ω ∂μ) ≤
      ∫ ω in responseSurvives Y z n, (z + responseWalk Y n ω) ∂μ := by
  let A := responseSurvives Y z
  let V (j : ℕ) (ω : Ω) := z + responseWalk Y j ω
  have hAm (j : ℕ) : MeasurableSet (A j) := responseSurvives_measurable hY z j
  have hVi (j : ℕ) : Integrable (V j) μ :=
    (integrable_const z).add (integrable_finsetSum _ fun i _ => hYi i)
  have hAs : A 0 = Set.univ := by
    ext ω
    simp [A, responseSurvives, responseWalk, hz]
  have hVs (ω : Ω) (j : ℕ) : V (j + 1) ω = V j ω + Y j ω := by
    simp [V, responseWalk, Finset.sum_range_succ, add_assoc]
  induction n with
  | zero =>
    simp [show responseSurvives Y z 0 = Set.univ from hAs, responseWalk, probReal_univ]
  | succ n ih =>
    have hpt : ∀ ω, (A n).indicator (fun ω => V n ω + Y n ω) ω ≤
        (A (n + 1)).indicator (V (n + 1)) ω := by
      intro ω
      have hanti : ω ∈ A (n + 1) → ω ∈ A n := fun ha k hk =>
        ha k (hk.trans (Nat.le_succ n))
      by_cases h₁ : ω ∈ A n
      · by_cases h₂ : ω ∈ A (n + 1)
        · simp [Set.indicator_of_mem h₁, Set.indicator_of_mem h₂, hVs]
        · have hneg : V (n + 1) ω < 0 := by
            by_contra! hn
            apply h₂
            intro k hk
            rcases (Nat.lt_or_eq_of_le hk) with hlt | rfl
            · exact h₁ k (Nat.le_of_lt_succ hlt)
            · exact hn
          simpa only [Set.indicator_of_mem h₁, Set.indicator_of_notMem h₂, ← hVs] using hneg.le
      · simp [Set.indicator_of_notMem h₁, Set.indicator_of_notMem (mt hanti h₁)]
    have hmono := integral_mono (((hVi n).add (hYi n)).indicator (hAm n))
      ((hVi (n + 1)).indicator (hAm (n + 1))) hpt
    rw [integral_indicator (hAm n), integral_indicator (hAm (n + 1))] at hmono
    simp only [Pi.add_apply] at hmono
    rw [integral_add (hVi n).integrableOn (hYi n).integrableOn] at hmono
    have hfactor := (response_survival_indep hY hI z n).integral_mul_eq_mul_integral
      (measurable_one.indicator (hAm n)).aestronglyMeasurable (hY n).aestronglyMeasurable
    have hfact : (∫ ω in A n, Y n ω ∂μ) = μ.real (A n) * (∫ ω, Y n ω ∂μ) := by
      rw [← integral_indicator (hAm n)]
      rw [← integral_indicator_one (hAm n)]
      convert hfactor using 2
      ext ω
      by_cases h : ω ∈ responseSurvives Y z n <;> simp [A, h]
    rw [hfact] at hmono
    rw [Finset.sum_range_succ, ← add_assoc]
    exact (add_le_add_left ih _).trans hmono

/-- The cost of the negative drift on surviving paths grows sublinearly in
the initial height. The finite head costs at most a fixed constant, and
the square-summable tail can be made to cost less than a quarter of the
height. -/
private theorem response_positive_stopped_flux {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ j, Measurable (Y j)) (hYi : ∀ j, Integrable (Y j) μ)
    (hI : iIndepFun Y μ) {M C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hm : ∀ j : ℕ, -(M / ((j : ℝ) + 1)) ≤ ∫ ω, Y j ω ∂μ)
    (hb : ∀ n : ℕ, ∀ z : ℝ, 0 ≤ z →
      μ.real (responseSurvives Y z n) ≤ C * (z + 1) / ((n : ℝ) + 1)) :
    ∃ z > 0, ∀ n : ℕ, z / 2 ≤
      ∫ ω in responseSurvives Y z n, (z + responseWalk Y n ω) ∂μ := by
  let s : ℕ → ℝ := fun j => M * C * (((j : ℝ) + 1) ^ 2)⁻¹
  have hs : Summable s := by
    simpa only [s, Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 (by decide : 1 < (2 : ℕ)))).mul_left (M * C)
  have hs0 (j : ℕ) : 0 ≤ s j := by positivity
  have ht : Tendsto (fun n : ℕ => ∑' j : ℕ, s (n + j)) atTop (𝓝 0) := by
    have hsum (n : ℕ) : (∑' j : ℕ, s (n + j)) = (∑' j, s j) - ∑ j ∈ Finset.range n, s j := by
      have h := hs.sum_add_tsum_nat_add n
      simp_rw [add_comm n] 
      linarith
    simpa only [hsum, sub_self] using
      (tendsto_const_nhds (x := ∑' j, s j)).sub hs.hasSum.tendsto_sum_nat
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 ht).2 (1 / 8)
    (by norm_num : (0 : ℝ) < 1 / 8))
  let z : ℝ := 4 * ((N : ℝ) * M + 1)
  have hz : 0 < z := by positivity
  refine ⟨z, hz, fun n => ?_⟩
  let d (j : ℕ) := μ.real (responseSurvives Y z j) * (M / ((j : ℝ) + 1))
  have hd (j : ℕ) : d j ≤ M := by
    calc
      d j ≤ 1 * (M / ((j : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right measureReal_le_one (by positivity)
      _ ≤ M := by
        rw [one_mul, div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hM]
  have hd' (j : ℕ) : d j ≤ (z + 1) * s j := by
    calc
      d j ≤ (C * (z + 1) / ((j : ℝ) + 1)) * (M / ((j : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (hb j z hz.le) (by positivity)
      _ = (z + 1) * s j := by dsimp [s]; field_simp
  have hhead (k : ℕ) :
      (∑ j ∈ Finset.range k, d j) ≤ (k : ℝ) * M := by
    simpa [nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.range k) (fun j _ => hd j)
  have hloss : (∑ j ∈ Finset.range n, d j) ≤ (N : ℝ) * M + (z + 1) / 8 := by
    by_cases h : n ≤ N
    · exact (hhead n).trans ((mul_le_mul_of_nonneg_right (by exact_mod_cast h) hM).trans
        (le_add_of_nonneg_right (by positivity)))
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show N ≤ n by omega)
      rw [Finset.sum_range_add]
      have ht' : (∑ j ∈ Finset.range k, s (N + j)) ≤ 1 / 8 := by
        have hs' : Summable (fun j : ℕ => s (N + j)) := by
          simpa only [add_comm N] using (summable_nat_add_iff N).2 hs
        exact (hs'.sum_le_tsum _ fun j _ => hs0 _).trans (hN N le_rfl).le
      apply add_le_add (hhead N)
      calc
        (∑ j ∈ Finset.range k, d (N + j)) ≤ ∑ j ∈ Finset.range k, (z + 1) * s (N + j) :=
          Finset.sum_le_sum fun j _ => hd' _
        _ = (z + 1) * (∑ j ∈ Finset.range k, s (N + j)) := (Finset.mul_sum ..).symm
        _ ≤ (z + 1) / 8 := by
          simpa only [div_eq_mul_inv, one_mul] using
            (mul_le_mul_of_nonneg_left ht' (by positivity : 0 ≤ z + 1))
  have hsum : -(∑ j ∈ Finset.range n, d j) ≤
      ∑ j ∈ Finset.range n, μ.real (responseSurvives Y z j) * (∫ ω, Y j ω ∂μ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun j _ => by
      rw [show -d j = μ.real (responseSurvives Y z j) * -(M / ((j : ℝ) + 1)) by
        dsimp [d]; ring]
      exact mul_le_mul_of_nonneg_left (hm j) measureReal_nonneg
  have hexp := response_stopped_expectation hY hYi hI hz.le n
  dsimp [z] at hz hloss hsum hexp ⊢
  linarith

private theorem response_integrable_pow {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (h : MemLp f 4 μ)
    {k : ℕ} (hk : k ≤ 4) : Integrable (fun ω => f ω ^ k) μ := by
  have h' : MemLp f (k : ℝ≥0∞) μ := h.mono_exponent (by exact_mod_cast hk)
  exact h'.integrable_norm_pow'.mono (h.aestronglyMeasurable.pow _)
    (Eventually.of_forall fun ω => by
      rw [norm_pow, Real.norm_of_nonneg (pow_nonneg (norm_nonneg (f ω)) k)])

private theorem response_add_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf4 : MemLp f 4 μ) (hg4 : MemLp g 4 μ)
    (hi : IndepFun f g μ) (hf0 : (∫ ω, f ω ∂μ) = 0) (hg0 : (∫ ω, g ω ∂μ) = 0) :
    (∫ ω, (f ω + g ω) ^ 2 ∂μ) = (∫ ω, f ω ^ 2 ∂μ) + (∫ ω, g ω ^ 2 ∂μ) ∧
    (∫ ω, (f ω + g ω) ^ 4 ∂μ) = (∫ ω, f ω ^ 4 ∂μ) + (∫ ω, g ω ^ 4 ∂μ) +
      6 * (∫ ω, f ω ^ 2 ∂μ) * (∫ ω, g ω ^ 2 ∂μ) := by
  have hpi (k l : ℕ) (hk : k ≤ 4) (hl : l ≤ 4) :
      Integrable (fun ω => f ω ^ k * g ω ^ l) μ :=
    (hi.comp (φ := fun x : ℝ => x ^ k) (ψ := fun x : ℝ => x ^ l) (by fun_prop) (by fun_prop))
      |>.integrable_mul (response_integrable_pow hf4 hk) (response_integrable_pow hg4 hl)
  have hpf (k l : ℕ) : (∫ ω, f ω ^ k * g ω ^ l ∂μ) =
      (∫ ω, f ω ^ k ∂μ) * (∫ ω, g ω ^ l ∂μ) :=
    (hi.comp (φ := fun x : ℝ => x ^ k) (ψ := fun x : ℝ => x ^ l) (by fun_prop) (by fun_prop))
      |>.integral_fun_mul_eq_mul_integral ((hf.pow_const k).aestronglyMeasurable)
        ((hg.pow_const l).aestronglyMeasurable)
  have hf₂ := response_integrable_pow hf4 (k := 2) (by decide)
  have hg₂ := response_integrable_pow hg4 (k := 2) (by decide)
  have hf₄ := response_integrable_pow hf4 (k := 4) le_rfl
  have hg₄ := response_integrable_pow hg4 (k := 4) le_rfl
  have h11 := hpi 1 1 (by decide) (by decide)
  have h31 := hpi 3 1 (by decide) (by decide)
  have h13 := hpi 1 3 (by decide) (by decide)
  have h22 := hpi 2 2 (by decide) (by decide)
  constructor
  · simp_rw [show ∀ ω, (f ω + g ω) ^ 2 =
      f ω ^ 2 + g ω ^ 2 + 2 * (f ω ^ 1 * g ω ^ 1) from fun ω => by ring]
    have hA : Integrable (fun ω => f ω ^ 2 + g ω ^ 2) μ := hf₂.add hg₂
    rw [integral_add hA (h11.const_mul 2), integral_add hf₂ hg₂,
      integral_const_mul, hpf]
    simp [hf0, hg0]
  · simp_rw [show ∀ ω, (f ω + g ω) ^ 4 =
      ((f ω ^ 4 + g ω ^ 4) + 4 * (f ω ^ 3 * g ω ^ 1)) +
      4 * (f ω ^ 1 * g ω ^ 3) + 6 * (f ω ^ 2 * g ω ^ 2) from fun ω => by ring]
    have hA : Integrable (fun ω => f ω ^ 4 + g ω ^ 4) μ := hf₄.add hg₄
    have hB : Integrable (fun ω => f ω ^ 4 + g ω ^ 4 + 4 * (f ω ^ 3 * g ω ^ 1)) μ :=
      hA.add (h31.const_mul 4)
    have hC : Integrable (fun ω => f ω ^ 4 + g ω ^ 4 + 4 * (f ω ^ 3 * g ω ^ 1) +
        4 * (f ω ^ 1 * g ω ^ 3)) μ := hB.add (h13.const_mul 4)
    rw [integral_add hC (h22.const_mul 6), integral_add hB (h13.const_mul 4),
      integral_add hA (h31.const_mul 4),
      integral_add hf₄ hg₄, integral_const_mul, integral_const_mul, integral_const_mul,
      hpf, hpf, hpf]
    simp [hf0, hg0, mul_assoc]

private theorem response_walk_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : ℕ → Ω → ℝ} (hY : ∀ j, MemLp (Y j) 4 μ) (n : ℕ) :
    MemLp (responseWalk Y n) 4 μ := by
  unfold responseWalk
  exact memLp_finsetSum (Finset.range n) (fun j _ => hY j)

private theorem response_centered_walk_bounds {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : ℕ → Ω → ℝ}
    (hm : ∀ j, Measurable (Z j)) (hZ : ∀ j, MemLp (Z j) 4 μ)
    (hi : iIndepFun Z μ) (hc : ∀ j, (∫ ω, Z j ω ∂μ) = 0)
    {a b d : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hv : ∀ᶠ j : ℕ in atTop, a * ((j : ℝ) + 1) ≤ ∫ ω, Z j ω ^ 2 ∂μ)
    (hv' : ∀ j : ℕ, (∫ ω, Z j ω ^ 2 ∂μ) ≤ b * ((j : ℝ) + 1))
    (hq : ∀ j : ℕ, (∫ ω, Z j ω ^ 4 ∂μ) ≤ d * ((j : ℝ) + 1) ^ 3) :
    (∀ n, (∫ ω, responseWalk Z n ω ∂μ) = 0) ∧
    ∀ᶠ n : ℕ in atTop,
      (a / 8) * (n : ℝ) ^ 2 ≤ (∫ ω, responseWalk Z n ω ^ 2 ∂μ) ∧
      (∫ ω, responseWalk Z n ω ^ 4 ∂μ) ≤ (d + 6 * b ^ 2) * (n : ℝ) ^ 4 := by
  let S := responseWalk Z
  let v (n : ℕ) := ∫ ω, S n ω ^ 2 ∂μ
  let q (n : ℕ) := ∫ ω, S n ω ^ 4 ∂μ
  have hS n : (∫ ω, S n ω ∂μ) = 0 := by
    dsimp [S, responseWalk]
    rw [integral_finsetSum _ (fun i _ =>
      (hZ i).integrable (by norm_num))]
    simp only [hc, Finset.sum_const_zero]
  refine ⟨hS, ?_⟩
  have hstep n : v (n + 1) = v n + (∫ ω, Z n ω ^ 2 ∂μ) ∧
      q (n + 1) = q n + (∫ ω, Z n ω ^ 4 ∂μ) + 6 * v n * (∫ ω, Z n ω ^ 2 ∂μ) := by
    have hInd : IndepFun (S n) (Z n) μ := by
      have heq : S n = ∑ j ∈ Finset.range n, Z j := by
        funext ω
        simp [S, responseWalk, Finset.sum_apply]
      rw [heq]
      exact hi.indepFun_finsetSum_of_notMem hm (s := Finset.range n) (i := n) (by simp)
    have hSum : ∀ ω, S (n + 1) ω = S n ω + Z n ω := fun ω =>
      Finset.sum_range_succ (fun j => Z j ω) n
    simpa only [v, q, hSum] using
      response_add_moments (responseWalk_measurable hm n) (hm n)
        (response_walk_memLp hZ n) (hZ n) hInd (hS n) (hc n)
  have hv0 n : 0 ≤ v n := integral_nonneg fun _ => sq_nonneg _
  have hvu (n : ℕ) : v n ≤ b * (n : ℝ) ^ 2 := by
    induction n with
    | zero => simp [v, S, responseWalk]
    | succ n ih =>
      rw [(hstep n).1, Nat.cast_succ]
      have ht : b * (n : ℝ) ^ 2 + b * (↑n + 1) ≤ b * (↑n + 1) ^ 2 := by
        nlinarith only [mul_nonneg hb (Nat.cast_nonneg (α := ℝ) n)]
      exact (add_le_add ih (hv' n)).trans ht
  have hqu (n : ℕ) : q n ≤ (d + 6 * b ^ 2) * (n : ℝ) ^ 4 := by
    induction n with
    | zero => simp [q, S, responseWalk]
    | succ n ih =>
      rw [(hstep n).2, Nat.cast_succ]
      have hz : 0 ≤ ∫ ω, Z n ω ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
      have hmul := mul_le_mul (hvu n) (hv' n) hz (by positivity)
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      have hpow₁ : (n : ℝ) ^ 4 + (↑n + 1) ^ 3 ≤ (↑n + 1) ^ 4 := by
        nlinarith only [hn, sq_nonneg (n : ℝ), pow_nonneg hn 3]
      have hpow₂ : (n : ℝ) ^ 4 + (n : ℝ) ^ 2 * (↑n + 1) ≤ (↑n + 1) ^ 4 := by
        nlinarith only [hn, sq_nonneg (n : ℝ), pow_nonneg hn 3]
      nlinarith only [ih, hq n, hmul, mul_le_mul_of_nonneg_left hpow₁ hd,
        mul_le_mul_of_nonneg_left hpow₂ (show 0 ≤ 6 * b ^ 2 by positivity)]
  obtain ⟨N, hN⟩ := eventually_atTop.1 hv
  have hvl (m : ℕ) : (a / 2) * (m : ℝ) ^ 2 ≤ v (N + m) := by
    induction m with
    | zero => simpa using hv0 N
    | succ m ih =>
      change (a / 2) * ((m + 1 : ℕ) : ℝ) ^ 2 ≤ v (N + m + 1)
      rw [(hstep (N + m)).1, Nat.cast_succ]
      have hh := hN (N + m) (Nat.le_add_right _ _)
      push_cast at hh
      nlinarith only [ih, hh, mul_nonneg ha.le (Nat.cast_nonneg (α := ℝ) N), ha.le]
  filter_upwards [eventually_ge_atTop (2 * N)] with n hn
  refine ⟨?_, hqu n⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show N ≤ n by omega)
  have hNm : (N : ℝ) ≤ m := by exact_mod_cast (show N ≤ m by omega)
  have hp : ((N : ℝ) + m) ^ 2 ≤ (2 * (m : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  push_cast
  nlinarith only [hvl m, mul_le_mul_of_nonneg_left hp (show 0 ≤ a / 8 by positivity)]

/-- Uniform second and fourth moments of centered variables give a
uniform positive upper tail. Two scalar truncations suffice. -/
private theorem response_upper_tail {a d : ℝ} (ha : 0 < a) (_hd : 0 ≤ d) :
    ∃ t > 0, ∃ δ > 0, ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] {X : Ω → ℝ}, Measurable X → MemLp X 4 μ →
      (∫ ω, X ω ∂μ) = 0 → a ≤ (∫ ω, X ω ^ 2 ∂μ) →
      (∫ ω, X ω ^ 4 ∂μ) ≤ d → δ ≤ μ.real {ω | t ≤ X ω} := by
  let L := max (1 : ℝ) (2 * d / a)
  have hL : 0 < L := zero_lt_one.trans_le (le_max_left ..)
  have hL₁ : 1 ≤ L := le_max_left .. 
  have hLd : d / L ^ 2 ≤ a / 2 := by
    have h₁ := (div_le_iff₀ ha).1 (le_max_right 1 (2 * d / a))
    have h₂ : L ≤ L ^ 2 := by nlinarith only [mul_nonneg hL.le (sub_nonneg.mpr hL₁)]
    rw [div_le_iff₀ (sq_pos_of_pos hL)]
    linarith only [h₁, mul_le_mul_of_nonneg_left h₂ ha.le]
  let t := a / (16 * L)
  have ht : 0 < t := by positivity
  let M := max 1 (d / t)
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left ..)
  have hM₁ : 1 ≤ M := le_max_left ..
  have hMd : d / M ^ 3 ≤ t := by
    have h₁ := (div_le_iff₀ ht).1 (le_max_right 1 (d / t))
    have h₂ : M ≤ M ^ 3 := by
      nlinarith only [mul_nonneg hM.le (mul_nonneg (by linarith : 0 ≤ M - 1)
        (by positivity : 0 ≤ M + 1))]
    rw [div_le_iff₀ (pow_pos hM 3)]
    exact h₁.trans (by nlinarith only [mul_le_mul_of_nonneg_left h₂ ht.le])
  refine ⟨t, ht, t / M, div_pos ht hM, ?_⟩
  intro Ω _ μ _ X hXm hX h0 h2 h4
  have hXi : Integrable X μ := hX.integrable (by norm_num)
  have hXa := hXi.norm
  have hX2 := response_integrable_pow hX (k := 2) (by decide)
  have hX4 := response_integrable_pow hX (k := 4) le_rfl
  have htrunc (x : ℝ) : x ^ 2 ≤ L * |x| + x ^ 4 / L ^ 2 := by
    by_cases h : |x| ≤ L
    · have hc := mul_le_mul_of_nonneg_right h (abs_nonneg x)
      rw [← pow_two, sq_abs] at hc
      exact hc.trans (le_add_of_nonneg_right (by positivity))
    · have hlt := lt_of_not_ge h
      have hc := pow_le_pow_left₀ hL.le hlt.le 2
      rw [sq_abs] at hc
      have hle : x ^ 2 ≤ x ^ 4 / L ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos hL)]
        nlinarith only [mul_le_mul_of_nonneg_left hc (sq_nonneg x)]
      exact hle.trans (le_add_of_nonneg_left (by positivity))
  have htrI : Integrable (fun ω => L * ‖X ω‖ + X ω ^ 4 / L ^ 2) μ :=
    (hXa.const_mul L).add (hX4.div_const (L ^ 2))
  have htr := integral_mono hX2 htrI
    (fun ω => by simpa only [Real.norm_eq_abs] using htrunc (X ω))
  rw [integral_add (hXa.const_mul L) (hX4.div_const (L ^ 2)), integral_const_mul, integral_div] at htr
  have habs : a / 2 ≤ L * (∫ ω, |X ω| ∂μ) := by
    simp only [Real.norm_eq_abs] at htr
    linarith only [htr, h2, (div_le_div_of_nonneg_right h4 (sq_nonneg L)).trans hLd]
  let Xp (ω : Ω) := max (X ω) 0
  have hXpi : Integrable Xp μ := hXi.sup (integrable_const 0)
  have hXp : 4 * t ≤ ∫ ω, Xp ω ∂μ := by
    have heq : (fun ω => 2 * Xp ω) = fun ω => |X ω| + X ω := by
      funext ω
      dsimp [Xp]
      rcases le_or_gt 0 (X ω) with h | h
      · rw [max_eq_left h, abs_of_nonneg h]
        ring
      · rw [max_eq_right h.le, abs_of_neg h]
        ring
    have hi := congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) heq
    have hXa' : Integrable (fun ω => |X ω|) μ := by simpa [Real.norm_eq_abs] using hXa
    rw [integral_const_mul, integral_add hXa' hXi, h0, add_zero] at hi
    have hval : 8 * t * L = a / 2 := by dsimp [t]; field_simp; ring
    apply le_of_mul_le_mul_left _ hL
    nlinarith only [congrArg (L * ·) hi, habs, hval]
  let T : Set Ω := {ω | t ≤ X ω}
  have hTm : MeasurableSet T := measurableSet_le measurable_const hXm
  have hti : Integrable (T.indicator (1 : Ω → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hTm
  have hcap (ω : Ω) : Xp ω ≤ t + M * T.indicator 1 ω + X ω ^ 4 / M ^ 3 := by
    by_cases hω : ω ∈ T
    · have hx : t ≤ X ω := hω
      rw [Set.indicator_of_mem hω]
      simp only [Pi.one_apply, mul_one, Xp, max_eq_left (ht.le.trans hx)]
      by_cases h : X ω ≤ M
      · linarith only [h, ht, show 0 ≤ X ω ^ 4 / M ^ 3 by positivity]
      · have hpow : M ^ 3 ≤ X ω ^ 3 := pow_le_pow_left₀ hM.le (lt_of_not_ge h).le 3
        have hh : X ω ≤ X ω ^ 4 / M ^ 3 := by
          rw [le_div_iff₀ (pow_pos hM 3)]
          nlinarith only [mul_le_mul_of_nonneg_left hpow (ht.le.trans hx)]
        linarith only [hh, ht, hM]
    · have hx : X ω < t := lt_of_not_ge hω
      rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      exact (max_le hx.le ht.le).trans (le_add_of_nonneg_right (by positivity))
  have hcap₁ : Integrable (fun ω => t + M * T.indicator 1 ω) μ :=
    (integrable_const t).add (hti.const_mul M)
  have hcap₂ : Integrable (fun ω => t + M * T.indicator 1 ω + X ω ^ 4 / M ^ 3) μ :=
    hcap₁.add (hX4.div_const (M ^ 3))
  have hcap' := integral_mono hXpi hcap₂ hcap
  rw [integral_add hcap₁ (hX4.div_const (M ^ 3)),
    integral_add (integrable_const t) (hti.const_mul M), integral_const,
    probReal_univ, one_smul, integral_const_mul, integral_indicator_one hTm, integral_div] at hcap'
  rw [div_le_iff₀ hM]
  linarith only [hcap', hXp, ht, (div_le_div_of_nonneg_right h4 (pow_nonneg hM.le 3)).trans hMd]

private theorem response_prob_tiltedLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : IsProbabilityMeasure (tiltedLaw μ B h n) := by
  have hA := response_mass_pos hpos hmean hB h n
  have hi : Integrable (fun x : ℝ => x ^ theta B) (lawR μ B h n) := by
    simpa only [Real.rpow_zero, mul_one] using
      integrable_absTiltedLogRpow_aux hpos hmean hB h n (s := 0) (le_refl 0)
  have hnon : 0 ≤ᵐ[lawR μ B h n] (fun x : ℝ => x ^ theta B / tiltedMass μ B h n) := by
    filter_upwards [ae_pos_lawR hpos hB h n] with x hx
    exact div_nonneg (Real.rpow_nonneg hx.le _) hA.le
  rw [isProbabilityMeasure_iff, tiltedLaw, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.div_const _) hnon, integral_div]
  change ENNReal.ofReal (tiltedMass μ B h n / tiltedMass μ B h n) = 1
  rw [div_self hA.ne', ENNReal.ofReal_one]

private theorem response_tiltedLaw_ae {μ : Measure ℝ} {B h : ℝ} (n : ℕ)
    {P : ℝ → Prop} (hp : ∀ᵐ x ∂lawR μ B h n, P x) :
    ∀ᵐ x ∂tiltedLaw μ B h n, P x :=
  (withDensity_absolutelyContinuous _ _).ae_le hp

private theorem response_tiltedLaw_moment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n k : ℕ) :
    Integrable (fun r : ℝ => (Real.log r - Real.log B) ^ k) (tiltedLaw μ B h n) ∧
    (∫ r : ℝ, (Real.log r - Real.log B) ^ k ∂tiltedLaw μ B h n) =
      tiltedLogMoment μ B h k n / tiltedMass μ B h n := by
  have hA := response_mass_pos hpos hmean hB h n
  have hM : Measurable (fun r : ℝ => ENNReal.ofReal (r ^ theta B / tiltedMass μ B h n)) :=
    ((Real.continuous_rpow_const (theta_pos hB).le).measurable.div_const _).ennreal_ofReal
  have hp := ae_pos_lawR hpos hB h n
  have hf : ∀ᵐ x ∂lawR μ B h n,
      (ENNReal.ofReal (x ^ theta B / tiltedMass μ B h n)).toReal =
        x ^ theta B / tiltedMass μ B h n := by
    filter_upwards [hp] with x hx
    exact ENNReal.toReal_ofReal (div_nonneg (Real.rpow_nonneg hx.le _) hA.le)
  constructor
  · rw [tiltedLaw, integrable_withDensity_iff hM (by simp)]
    have hi := (integrable_absTiltedLogRpow_aux hpos hmean hB h n (s := (k : ℝ)) (by positivity))
      |>.div_const (tiltedMass μ B h n)
    have hm : Measurable (fun x : ℝ => (Real.log x - Real.log B) ^ k *
        (ENNReal.ofReal (x ^ theta B / tiltedMass μ B h n)).toReal) :=
      ((Real.measurable_log.sub_const _).pow_const _).mul hM.ennreal_toReal
    refine hi.mono hm.aestronglyMeasurable ?_
    filter_upwards [hf, hp] with x hx hx0
    simp only [hx, Real.norm_eq_abs, abs_mul, abs_pow, abs_div, abs_abs,
      Real.rpow_natCast, abs_of_nonneg (Real.rpow_nonneg hx0.le _), abs_of_pos hA]
    exact le_of_eq (by ring)
  · rw [tiltedLaw, integral_withDensity_eq_integral_toReal_smul hM (by simp)]
    calc
      (∫ x : ℝ, (ENNReal.ofReal (x ^ theta B / tiltedMass μ B h n)).toReal •
          (Real.log x - Real.log B) ^ k ∂lawR μ B h n) =
        ∫ x : ℝ, (x ^ theta B * (Real.log x - Real.log B) ^ k) / tiltedMass μ B h n
          ∂lawR μ B h n := by
            apply integral_congr_ae
            filter_upwards [hf] with x hx
            rw [hx, smul_eq_mul, div_mul_eq_mul_div]
      _ = _ := integral_div _ _

private theorem response_mass_bounds {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (hF : freeEnergy μ B h = 0) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ n, m ≤ tiltedMass μ B h n ∧ tiltedMass μ B h n ≤ M := by
  let m := min (tiltedMass μ B h 0) (floorSeq B 1 ^ theta B)
  let M := max (tiltedMass μ B h 0) ((B - 1) ^ theta B)
  have hA := response_mass_pos hpos hmean hB h 0
  refine ⟨m, M, lt_min hA (Real.rpow_pos_of_pos (floorSeq_one_pos hB) _),
    hA.trans_le (le_max_left ..), fun n => ?_⟩
  cases n with
  | zero => exact ⟨min_le_left .., le_max_left ..⟩
  | succ n =>
    obtain ⟨C, hC⟩ := criticalMoments_aux hB
    refine ⟨(min_le_right ..).trans ?_, ((hC μ hpos hmean h hF).1 _ (Nat.succ_pos n)).1.trans (le_max_right ..)⟩
    letI := isProbabilityMeasure_lawR (μ := μ) B h (n + 1)
    have hi : Integrable (fun x : ℝ => x ^ theta B) (lawR μ B h (n + 1)) := by
      simpa only [Real.rpow_zero, mul_one] using
        integrable_absTiltedLogRpow_aux hpos hmean hB h (n + 1) (s := 0) (le_refl 0)
    have hcomp : ∀ᵐ x ∂lawR μ B h (n + 1), floorSeq B 1 ^ theta B ≤ x ^ theta B := by
      filter_upwards [ae_floorSeq_le_lawR hpos hB h (n + 1)] with x hx
      exact Real.rpow_le_rpow (floorSeq_nonneg hB 1)
        ((floorSeq_one_le hB (Nat.succ_pos n)).trans hx) (theta_pos hB).le
    simpa only [tiltedMass, integral_const, probReal_univ, one_smul] using integral_mono_ae (integrable_const _) hi hcomp

private theorem response_global_poly_bound {f : ℕ → ℝ} (k : ℕ) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ᶠ j : ℕ in atTop, |f j| ≤ C * ((j : ℝ) + 1) ^ k) :
    ∃ D > 0, ∀ j : ℕ, |f j| ≤ D * ((j : ℝ) + 1) ^ k := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  let D := C + (∑ j ∈ Finset.range N, |f j|) + 1
  have hD : 0 < D := by positivity
  refine ⟨D, hD, fun j => ?_⟩
  by_cases hj : N ≤ j
  · exact (hN j hj).trans (mul_le_mul_of_nonneg_right
      (by dsimp [D]; linarith [Finset.sum_nonneg (s := Finset.range N) (fun i _ => abs_nonneg (f i))])
      (by positivity))
  · have h₁ : |f j| ≤ ∑ i ∈ Finset.range N, |f i| := Finset.single_le_sum (f := fun i => |f i|)
      (fun i _ => abs_nonneg _) (Finset.mem_range.2 (lt_of_not_ge hj))
    calc
      |f j| ≤ D := by dsimp [D]; linarith
      _ ≤ D * ((j : ℝ) + 1) ^ k := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg (α := ℝ) j) : 1 ≤ (j : ℝ) + 1)) hD.le

private theorem response_global_decay_bound {f : ℕ → ℝ}
    (h : f =O[atTop] fun n : ℕ => (n : ℝ)⁻¹) :
    ∃ K > 0, ∀ n : ℕ, |f n| ≤ K / ((n : ℝ) + 1) := by
  obtain ⟨C, hC, h⟩ := h.exists_pos
  have he : ∀ᶠ n : ℕ in atTop, |f n * ((n : ℝ) + 1)| ≤ (2 * C) * ((n : ℝ) + 1)^0 := by
    filter_upwards [h.bound, eventually_ge_atTop (1 : ℕ)] with n hn hn₁
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn₁
    have hn0 : 0 < (n : ℝ) := by linarith
    simp only [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn0.le)] at hn
    rw [abs_mul, abs_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity), pow_zero, mul_one]
    apply (mul_le_mul_of_nonneg_right hn (by positivity)).trans
    rw [← div_eq_mul_inv, div_mul_eq_mul_div, div_le_iff₀ hn0]
    nlinarith only [mul_le_mul_of_nonneg_left hn' hC.le]
  obtain ⟨K, hK, hh⟩ := response_global_poly_bound 0 (by positivity) he
  refine ⟨K, hK, fun n => ?_⟩
  rw [le_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)]
  simpa only [abs_mul, abs_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity), pow_zero, mul_one]
    using hh n

private theorem response_center_moments {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {X : Ω → ℝ}
    (hf : MemLp X 4 ν) {m : ℝ} (hm : (∫ ω, X ω ∂ν) = m) :
    let Z := fun ω => X ω - m
    MemLp Z 4 ν ∧ (∫ ω, Z ω ∂ν) = 0 ∧
      (∫ ω, Z ω ^ 2 ∂ν) = (∫ ω, X ω ^ 2 ∂ν) - m ^ 2 ∧
      (∫ ω, Z ω ^ 4 ∂ν) ≤ 8 * ((∫ ω, X ω ^ 4 ∂ν) + m ^ 4) := by
  intro Z
  have hi : Integrable X ν := hf.integrable (by norm_num)
  have hZ : MemLp Z 4 ν := hf.sub (memLp_const m)
  refine ⟨hZ, ?_, ?_, ?_⟩
  · dsimp [Z]
    rw [integral_sub hi (integrable_const m), hm, integral_const, probReal_univ, one_smul, sub_self]
  · dsimp [Z]
    have h₂ := response_integrable_pow hf (k := 2) (by decide)
    have he (ω : Ω) : (X ω - m) ^ 2 = X ω ^ 2 - (2 * m) * X ω + m ^ 2 := by ring
    have ha : Integrable (fun ω => X ω ^ 2 - (2 * m) * X ω) ν := h₂.sub (hi.const_mul _)
    simp_rw [he]
    rw [integral_add ha (integrable_const _), integral_sub h₂ (hi.const_mul _),
      integral_const_mul, hm, integral_const, probReal_univ, one_smul]
    ring
  · have h₄ := response_integrable_pow hf (k := 4) le_rfl
    have ha : Integrable (fun ω => X ω ^ 4 + m ^ 4) ν := h₄.add (integrable_const _)
    have hm₄ : (∫ ω, (X ω ^ 4 + m ^ 4) ∂ν) = (∫ ω, X ω ^ 4 ∂ν) + m ^ 4 := by
      rw [integral_add h₄ (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [← hm₄, ← integral_const_mul]
    refine integral_mono (response_integrable_pow hZ (k := 4) le_rfl) (ha.const_mul 8) fun ω => ?_
    have h₁ : (X ω - m)^2 ≤ 2 * (X ω ^ 2 + m ^ 2) := by
      nlinarith only [sq_nonneg (X ω + m)]
    have h₂ := pow_le_pow_left₀ (sq_nonneg _) h₁ 2
    dsimp [Z]
    nlinarith only [h₂, sq_nonneg (X ω ^ 2 - m ^ 2)]

private theorem response_walk_tail {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {Y Z : ℕ → Ω → ℝ} {m : ℕ → ℝ}
    (hYZ : ∀ j ω, Y j ω = Z j ω + m j)
    (hZm : ∀ j, Measurable (Z j)) (hZlp : ∀ j, MemLp (Z j) 4 ν)
    (hmean : Tendsto m atTop (𝓝 0))
    (hZ0 : ∀ n, (∫ ω, responseWalk Z n ω ∂ν) = 0)
    {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d)
    (hZmoms : ∀ᶠ n : ℕ in atTop, a * (n : ℝ)^2 ≤ (∫ ω, responseWalk Z n ω ^ 2 ∂ν) ∧
      (∫ ω, responseWalk Z n ω ^ 4 ∂ν) ≤ d * (n : ℝ)^4) :
    ∃ η > 0, ∃ δ > 0, ∀ᶠ n : ℕ in atTop,
      δ ≤ ν.real {ω | η * (n : ℝ) ≤ responseWalk Y n ω} := by
  obtain ⟨t, ht, δ, hδ, htail⟩ := response_upper_tail ha hd
  refine ⟨t / 2, by positivity, δ, hδ, ?_⟩
  have hsum (n : ℕ) (ω : Ω) :
      responseWalk Y n ω = responseWalk Z n ω + ∑ j ∈ Finset.range n, m j := by
    simp only [responseWalk, hYZ, Finset.sum_add_distrib]
  have hmean' := (tendsto_order.1 hmean.cesaro).1 (-(t / 2)) (by linarith)
  filter_upwards [hmean', hZmoms, eventually_ge_atTop (1 : ℕ)] with n hmn hmoms hn
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.2 (by omega)
  let X : Ω → ℝ := fun ω => ((n : ℝ)⁻¹) * responseWalk Z n ω
  have hXm : Measurable X := (responseWalk_measurable hZm n).const_mul _
  have hXlp : MemLp X 4 ν := (response_walk_memLp hZlp n).const_mul _
  have hX0 : (∫ ω, X ω ∂ν) = 0 := by
    simp only [X, integral_const_mul, hZ0, mul_zero]
  have hX (k : ℕ) : (∫ ω, X ω ^ k ∂ν) =
      ((n : ℝ) ^ k)⁻¹ * (∫ ω, responseWalk Z n ω ^ k ∂ν) := by
    simp only [X, mul_pow, inv_pow, integral_const_mul]
  have hXl : a ≤ (∫ ω, X ω ^ 2 ∂ν) := by
    rw [hX, ← div_eq_inv_mul, le_div_iff₀ (pow_pos hn0 2)]
    exact hmoms.1
  have hXu : (∫ ω, X ω ^ 4 ∂ν) ≤ d := by
    rw [hX, ← div_eq_inv_mul, div_le_iff₀ (pow_pos hn0 4)]
    exact hmoms.2
  refine (htail ν hXm hXlp hX0 hXl hXu).trans (measureReal_mono fun ω hω => ?_)
  have hω' : t * (n : ℝ) ≤ responseWalk Z n ω := by
    apply (le_div_iff₀ hn0).1
    simpa only [div_eq_inv_mul] using (show t ≤ X ω from hω)
  have hmn' : -(t / 2) * (n : ℝ) < ∑ i ∈ Finset.range n, m i := by
    apply (lt_div_iff₀ hn0).1
    simpa only [div_eq_inv_mul] using hmn
  change t / 2 * (n : ℝ) ≤ responseWalk Y n ω
  rw [hsum]
  linarith only [hω', hmn']

private theorem response_log_le_sum (n : ℕ) :
    2 * Real.log ((n : ℝ) + 1) ≤ ∑ j ∈ Finset.range n, 2 / ((j : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let x := (n : ℝ) + 1
    have hx : 0 < x := by positivity
    have hp : 0 < (x + 1) / x := by positivity
    have hl := Real.log_le_sub_one_of_pos hp
    rw [Real.log_div (by positivity) hx.ne'] at hl
    have he : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    rw [he] at hl
    rw [Finset.sum_range_succ, Nat.cast_succ]
    change 2 * Real.log (x + 1) ≤ (∑ j ∈ Finset.range n, 2 / ((j : ℝ) + 1)) + 2 / x
    have ih' : 2 * Real.log x ≤ ∑ j ∈ Finset.range n, 2 / ((j : ℝ) + 1) := ih
    have htwo : 2 / x = 2 * (1 / x) := by ring
    rw [htwo]
    linarith only [hl, ih']

private noncomputable def responseSpineIncrement (B : ℝ) (j : ℕ) (u : ℕ → ℝ) : ℝ :=
  Real.log (u j) - Real.log B - 2 / ((j : ℝ) + 1)

private theorem response_measurable_increment (B : ℝ) (j : ℕ) :
    Measurable (responseSpineIncrement B j) :=
  ((Real.measurable_log.comp (measurable_pi_apply j)).sub_const _).sub_const _

private theorem response_spine_flux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (hF : freeEnergy μ B h = 0) {C : ℝ} (hC : 0 < C)
    (hH : (fun n : ℕ => tiltedLogMoment μ B h 1 n) =O[atTop] fun n : ℕ => (n : ℝ)⁻¹)
    (hK : (fun n : ℕ => tiltedLogMoment μ B h 2 n) =Θ[atTop] fun n : ℕ => (n : ℝ))
    (hL : ∀ n : ℕ, 1 ≤ n → tiltedLogMoment μ B h 4 n ≤ C * ((n : ℝ) + 1) ^ 3) :
    let ν := Measure.infinitePi (tiltedLaw μ B h)
    ∃ z > 0, ∀ n : ℕ, z / 2 ≤
      ∫ u in responseSurvives (responseSpineIncrement B) z n,
        (z + responseWalk (responseSpineIncrement B) n u) ∂ν := by
  intro ν
  letI (j : ℕ) : IsProbabilityMeasure (tiltedLaw μ B h j) :=
    response_prob_tiltedLaw hpos hmean hB h j
  letI : IsProbabilityMeasure ν := inferInstanceAs
    (IsProbabilityMeasure (Measure.infinitePi (tiltedLaw μ B h)))
  let X (j : ℕ) (u : ℕ → ℝ) := Real.log (u j) - Real.log B
  let Y := responseSpineIncrement B
  let A := tiltedMass μ B h
  let H (j : ℕ) := tiltedLogMoment μ B h 1 j
  let K (j : ℕ) := tiltedLogMoment μ B h 2 j
  let L (j : ℕ) := tiltedLogMoment μ B h 4 j
  let m (j : ℕ) := H j / A j
  let Z (j : ℕ) (u : ℕ → ℝ) := X j u - m j
  let mY (j : ℕ) := m j - 2 / ((j : ℝ) + 1)
  have hX (j : ℕ) : Measurable (X j) :=
    (Real.measurable_log.comp (measurable_pi_apply j)).sub_const _
  have hXm (j k : ℕ) : Integrable (fun u => X j u ^ k) ν ∧
      (∫ u, X j u ^ k ∂ν) = tiltedLogMoment μ B h k j / A j := by
    have hmp := measurePreserving_eval_infinitePi (tiltedLaw μ B h) j
    obtain ⟨hi, he⟩ := response_tiltedLaw_moment hpos hmean hB h j k
    refine ⟨hmp.integrable_comp_of_integrable hi, ?_⟩
    change (∫ u, (Real.log (u j) - Real.log B) ^ k ∂ν) = _
    rw [← he, ← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by fun_prop)]
  have hXlp (j : ℕ) : MemLp (X j) 4 ν := by
    apply (integrable_norm_rpow_iff (hX j).aestronglyMeasurable (by norm_num) (by norm_num)).1
    have he (u : ℕ → ℝ) : ‖X j u‖ ^ (4 : ℝ) = X j u ^ (4 : ℕ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs,
        (show Even (4 : ℕ) by decide).pow_abs]
    simpa only [ENNReal.toReal_ofNat, he] using (hXm j 4).1
  have hZmeas (j : ℕ) : Measurable (Z j) := (hX j).sub_const _
  have hZm (j : ℕ) := response_center_moments (hXlp j)
    (m := m j) (by simpa only [pow_one] using (hXm j 1).2)
  have hZi : iIndepFun Z ν :=
    iIndepFun_infinitePi (P := tiltedLaw μ B h)
      (X := fun (j : ℕ) (x : ℝ) => Real.log x - Real.log B - m j)
      (fun _ => (Real.measurable_log.sub_const _).sub_const _)
  have hYi : iIndepFun Y ν :=
    iIndepFun_infinitePi (P := tiltedLaw μ B h)
      (X := fun (j : ℕ) (x : ℝ) => Real.log x - Real.log B - 2 / ((j : ℝ) + 1))
      (fun _ => (Real.measurable_log.sub_const _).sub_const _)
  have hYint (j : ℕ) : Integrable (Y j) ν :=
    ((hXlp j).integrable (by norm_num)).sub (integrable_const _)
  have hYm (j : ℕ) : (∫ u, Y j u ∂ν) = mY j := by
    have hi : Integrable (X j) ν := (hXlp j).integrable (by norm_num)
    change (∫ u, X j u - 2 / ((j : ℝ) + 1) ∂ν) = _
    rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul]
    have he : (∫ u, X j u ∂ν) = m j := by simpa only [pow_one] using (hXm j 1).2
    rw [he]
  obtain ⟨a, b, ha, hb, hmass⟩ := response_mass_bounds hpos hmean hB h hF
  obtain ⟨D, hD, hD'⟩ := response_global_decay_bound hH
  have hm (j : ℕ) : |m j| ≤ (D / a) / ((j : ℝ) + 1) := by
    dsimp [m]
    rw [abs_div, abs_of_pos (ha.trans_le (hmass j).1)]
    convert div_le_div₀ (by positivity) (hD' j) ha (hmass j).1 using 1
    ring
  have hma (j : ℕ) : |m j| ≤ D / a := (hm j).trans
    (div_le_self (by positivity) (le_add_of_nonneg_left (Nat.cast_nonneg (α := ℝ) j) : 1 ≤ (j : ℝ) + 1))
  have hdecay (c : ℝ) : Tendsto (fun j : ℕ => c / ((j : ℝ) + 1)) atTop (𝓝 0) := by
    have hi : Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [div_eq_mul_inv, mul_zero] using (tendsto_const_nhds (x := c)).mul hi
  have hm0 : Tendsto m atTop (𝓝 0) :=
    squeeze_zero_norm (fun j => by simpa only [Real.norm_eq_abs] using hm j) (hdecay (D / a))
  have hmy0 : Tendsto mY atTop (𝓝 0) := by
    simpa only [sub_zero] using hm0.sub (hdecay 2)
  have hK0 j : 0 ≤ K j := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_pos_lawR hpos hB h j] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le _) (sq_nonneg _)
  have hL0 j : 0 ≤ L j := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_pos_lawR hpos hB h j] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le _) (by positivity)
  obtain ⟨Ck, hCk, hK'⟩ := hK.1.exists_pos
  obtain ⟨Kmax, hKmax, hKu⟩ := response_global_poly_bound (f := K) 1 hCk.le (by
    filter_upwards [hK'.bound] with j hj
    simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)] at hj
    simpa only [pow_one] using hj.trans (by linarith))
  obtain ⟨Lmax, hLmax, hLu⟩ := response_global_poly_bound (f := L) 3 hC.le (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
    simpa only [abs_of_nonneg (hL0 j)] using hL j hj)
  obtain ⟨Kmin, hKmin, hKl⟩ := hK.2.exists_pos
  let v (j : ℕ) := ∫ u, Z j u ^ 2 ∂ν
  have hvar (j : ℕ) : v j = K j / A j - m j ^ 2 := by
    change (∫ u, (X j u - m j) ^ 2 ∂ν) = _
    have he : (∫ u, (X j u - m j) ^ 2 ∂ν) = (∫ u, X j u ^ 2 ∂ν) - m j ^ 2 :=
      (hZm j).2.2.1
    rw [he, (hXm j 2).2]
  have hvu (j : ℕ) : v j ≤ (Kmax / a) * ((j : ℝ) + 1) := by
    rw [hvar]
    have hbound : K j ≤ Kmax * ((j : ℝ) + 1) := by
      simpa only [pow_one] using (le_abs_self (K j)).trans (hKu j)
    have he : K j / A j ≤ Kmax * ((j : ℝ) + 1) / a :=
      div_le_div₀ (by positivity) hbound ha (hmass j).1
    have he' : Kmax * ((j : ℝ) + 1) / a = Kmax / a * ((j : ℝ) + 1) := by ring
    linarith only [he, he', sq_nonneg (m j)]
  let γ : ℝ := 1 / (4 * Kmin * b)
  have hγ : 0 < γ := by positivity
  have hlarge : ∀ᶠ j : ℕ in atTop, (D / a)^2 ≤ γ * ((j : ℝ) + 1) := by
    have ht := tendsto_natCast_atTop_atTop (R := ℝ)
    filter_upwards [ht.eventually_ge_atTop ((D / a)^2 / γ)] with j hj
    have hj' := (div_le_iff₀ hγ).1 hj
    linarith only [hj', hγ.le]
  have hvl : ∀ᶠ j : ℕ in atTop, γ * ((j : ℝ) + 1) ≤ v j := by
    filter_upwards [hKl.bound, hlarge, eventually_ge_atTop (1 : ℕ)] with j hj hbig hj'
    have hj₁ : (1 : ℝ) ≤ j := by exact_mod_cast hj'
    change ‖(j : ℝ)‖ ≤ Kmin * ‖K j‖ at hj
    simp only [Real.norm_eq_abs, abs_of_nonneg (hK0 j), abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)] at hj
    have h1 : ((j : ℝ) + 1) / (2 * Kmin) ≤ K j := by
      rw [div_le_iff₀ (by positivity)]
      linarith only [hj, hj₁]
    have h2 : ((j : ℝ) + 1) / (2 * Kmin) / b ≤ K j / A j :=
      div_le_div₀ (hK0 j) h1 (ha.trans_le (hmass j).1) (hmass j).2
    have hsq := pow_le_pow_left₀ (abs_nonneg (m j)) (hma j) 2
    rw [sq_abs] at hsq
    rw [hvar]
    have he : ((j : ℝ) + 1) / (2 * Kmin) / b = 2 * (γ * ((j : ℝ) + 1)) := by
      dsimp [γ]
      field_simp
      norm_num
    linarith only [h2, hbig, hsq, he]
  let Q := 8 * (Lmax / a + (D / a)^4)
  have hQ : 0 ≤ Q := by positivity
  have hqu (j : ℕ) : (∫ u, Z j u ^ 4 ∂ν) ≤ Q * ((j : ℝ) + 1)^3 := by
    have h1 : (∫ u, Z j u ^ 4 ∂ν) ≤ 8 * ((∫ u, X j u ^ 4 ∂ν) + (m j)^4) :=
      (hZm j).2.2.2
    rw [(hXm j 4).2] at h1
    change _ ≤ 8 * (L j / A j + (m j)^4) at h1
    have h2 : L j / A j ≤ Lmax / a * ((j : ℝ) + 1)^3 := by
      calc
        _ ≤ Lmax * ((j : ℝ) + 1)^3 / a :=
          div_le_div₀ (by positivity) ((le_abs_self (L j)).trans (hLu j)) ha (hmass j).1
        _ = _ := by ring
    have h3 := pow_le_pow_left₀ (abs_nonneg (m j)) (hma j) 4
    rw [(show Even (4 : ℕ) by decide).pow_abs] at h3
    have h4 : (D / a)^4 ≤ (D / a)^4 * ((j : ℝ) + 1)^3 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg (α := ℝ) j) : 1 ≤ (j : ℝ) + 1))
          (show 0 ≤ (D / a)^4 by positivity)
    dsimp [Q]
    nlinarith only [h1, h2, h3, h4]
  obtain ⟨hz0, hzv⟩ := response_centered_walk_bounds hZmeas (fun j => (hZm j).1)
    hZi (fun j => (hZm j).2.1) hγ (by positivity : 0 ≤ Kmax / a) hQ hvl hvu hqu
  obtain ⟨η, hη, δ, hδ, htail⟩ := response_walk_tail (Y := Y) (m := mY)
    (fun j u => by dsimp [Y, Z, mY, X, responseSpineIncrement]; ring)
    hZmeas (fun j => (hZm j).1) hmy0 hz0 (by positivity) (by positivity) hzv
  let b0 := max 0 (Real.log B - Real.log (floorSeq B 1) + 2)
  have hlower (j : ℕ) (hj : 1 ≤ j) : ∀ᵐ u ∂ν, -b0 ≤ Y j u := by
    have hfloor := response_tiltedLaw_ae j (ae_floorSeq_le_lawR hpos hB h j)
    filter_upwards [(measurePreserving_eval_infinitePi (tiltedLaw μ B h) j).quasiMeasurePreserving.ae hfloor]
      with u hu
    have hl := Real.log_le_log (floorSeq_one_pos hB) ((floorSeq_one_le hB hj).trans hu)
    have h2 : (2 : ℝ) / ((j : ℝ) + 1) ≤ 2 := div_le_self (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg (α := ℝ) j))
    dsimp [Y, responseSpineIncrement]
    linarith only [hl, h2, le_max_right 0 (Real.log B - Real.log (floorSeq B 1) + 2)]
  obtain ⟨G, hG⟩ := criticalMoments_aux hB
  have hρ : 0 ≤ 2 / B := by positivity
  have hρ' : 2 / B < 1 := (div_lt_one (by linarith)).2 hB
  have hs : Summable (fun j => (∫ u, Y j u ∂ν)⁺) := by
    apply (summable_nat_add_iff 1).1
    refine Summable.of_nonneg_of_le (fun _ => posPart_nonneg _) (fun j => ?_)
      ((summable_nat_add_iff 1).2 ((summable_geometric_of_lt_one hρ hρ').mul_left (max G 0 / a)))
    have hHp := ((hG μ hpos hmean h hF).1 (j + 1) (Nat.succ_pos _)).2
    rw [hYm]
    rw [posPart_def]
    apply max_le _ (by positivity)
    have hle : H (j + 1) ≤ max G 0 * (2 / B) ^ (j + 1) :=
      hHp.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hρ _))
    have hle' := div_le_div₀ (show 0 ≤ max G 0 * (2 / B) ^ (j + 1) by positivity)
      (le_refl _) ha (hmass (j + 1)).1
    change H (j + 1) / tiltedMass μ B h (j + 1) - 2 / (((j + 1 : ℕ) : ℝ) + 1)
      ≤ (max G 0 / a) * (2 / B) ^ (j + 1)
    have he := div_le_div_of_nonneg_right hle (ha.trans_le (hmass (j + 1)).1).le
    rw [← mul_div_right_comm]
    exact (sub_le_self _ (by positivity)).trans (he.trans hle')
  have hnneg : Integrable (fun u => (Y 0 u)⁻) ν := by
    refine (hYint 0).mono (by
      exact ((response_measurable_increment B 0).neg.max measurable_const).aestronglyMeasurable)
      (Eventually.of_forall fun u => ?_)
    rw [negPart_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  obtain ⟨M, hM⟩ := response_ballot_aux ν Y hYi hYint (le_max_left ..) hη hδ
    hlower hnneg hs htail
  have hedge (j : ℕ) : -((D / a + 2) / ((j : ℝ) + 1)) ≤ ∫ u, Y j u ∂ν := by
    rw [hYm]
    dsimp [mY]
    rw [add_div]
    linarith only [hm j, neg_abs_le (m j)]
  refine response_positive_stopped_flux (response_measurable_increment B) hYint hYi
    (by positivity) (le_max_right M 0) hedge (fun n z hz => ?_)
  have heq : responseSurvives Y z n = {u | ∀ k ≤ n, -z ≤ ∑ j ∈ Finset.range k, Y j u} := by
    ext u
    simp only [responseSurvives, responseWalk, Set.mem_ofPred_eq, neg_le_iff_add_nonneg']
  rw [heq]
  exact (hM n z hz).trans (by
    gcongr
    exact le_max_left _ _)

private noncomputable def responseSpineWalk (B : ℝ) (n : ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (Real.log (u j) - Real.log B)

private theorem response_spineWalk_restrict (B : ℝ) {n k : ℕ} (hk : k ≤ n)
    (u : ℕ → ℝ) :
    spineWalk B (fun j : Fin n => u j) k = responseSpineWalk B k u := by
  unfold spineWalk responseSpineWalk
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < k then Real.log (u j) - Real.log B else 0),
    ← Finset.sum_filter]
  have he : (Finset.range n).filter (fun j => j < k) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun hj => ⟨hj.trans_le hk, hj⟩⟩
  rw [he]

private theorem response_spine_walk_sub (B : ℝ) (n : ℕ) (u : ℕ → ℝ) :
    responseWalk (responseSpineIncrement B) n u =
      responseSpineWalk B n u - ∑ j ∈ Finset.range n, 2 / ((j : ℝ) + 1) := by
  simp only [responseWalk, responseSpineWalk, responseSpineIncrement, Finset.sum_sub_distrib]

private noncomputable def responseSpineMass (B : ℝ) (n : ℕ) (r : ℝ) (u : ℕ → ℝ) : ℝ :=
  Real.exp (responseSpineWalk B n u) *
    (r + (B - 1) / B * ∑ k ∈ Finset.Icc 1 n, Real.exp (-responseSpineWalk B k u))

private theorem response_spine_base_pos {B r : ℝ} (hB : 2 < B) (hr : 0 < r)
    (n : ℕ) (u : Fin n → ℝ) :
    0 < 1 + (B - 1) / (B * r) * ∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B u k) := by
  have hB' : 0 < B := by linarith
  have hc : 0 < B - 1 := by linarith
  positivity

private theorem response_spineW_pos {B r : ℝ} (hB : 2 < B) (hr : 0 < r)
    (n : ℕ) (u : Fin n → ℝ) : 0 < spineW B n r u := by
  unfold spineW
  exact Real.rpow_pos_of_pos (response_spine_base_pos hB hr n u) _

private theorem response_spineT_restrict {B r : ℝ} (hB : 2 < B) (hr : 0 < r)
    (n : ℕ) (u : ℕ → ℝ) :
    spineT B n r (fun j : Fin n => u j) = responseSpineMass B n r u := by
  have hp : 0 < 1 - theta B := sub_pos.mpr (theta_lt_one hB)
  have hbase := response_spine_base_pos hB hr n (fun j : Fin n => u j)
  have he : -(1 - theta B) * -(1 / (1 - theta B)) = 1 := by
    field_simp [hp.ne']
  simp only [spineT, spineW, ← Real.rpow_mul hbase.le, he, Real.rpow_one]
  rw [response_spineWalk_restrict B le_rfl, responseSpineMass]
  have hsum : (∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B (fun j : Fin n => u j) k)) =
      ∑ k ∈ Finset.Icc 1 n, Real.exp (-responseSpineWalk B k u) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [response_spineWalk_restrict B (Finset.mem_Icc.1 hk).2]
  rw [hsum]
  field_simp [hr.ne', show B ≠ 0 by linarith]

private theorem response_spineMass_pos {B r : ℝ} (hB : 2 < B) (hr : 0 < r)
    (n : ℕ) (u : ℕ → ℝ) : 0 < responseSpineMass B n r u := by
  unfold responseSpineMass
  have hB' : 0 < B := by linarith
  have hc : 0 < B - 1 := by linarith
  positivity

private theorem response_spineMass_step {B r : ℝ} (hB : 2 < B)
    (n : ℕ) (u : ℕ → ℝ) (hu : 0 < u n) :
    responseSpineMass B (n + 1) r u = (responseSpineMass B n r u * u n + (B - 1)) / B := by
  have hB' : 0 < B := by linarith
  have hS : responseSpineWalk B (n + 1) u =
      responseSpineWalk B n u + (Real.log (u n) - Real.log B) := Finset.sum_range_succ _ _
  have hf : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  let S := responseSpineWalk B (n + 1) u
  have hcancel : Real.exp S * Real.exp (-S) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have he : Real.exp S = Real.exp (responseSpineWalk B n u) * (u n / B) := by
    dsimp [S]
    rw [hS, Real.exp_add, Real.exp_sub, Real.exp_log hu, Real.exp_log hB']
  let g := ∑ k ∈ Finset.Icc 1 n, Real.exp (-responseSpineWalk B k u)
  unfold responseSpineMass
  rw [hf, Finset.sum_insert (by simp)]
  change Real.exp S * (r + (B - 1) / B * (Real.exp (-S) + g)) = _
  calc
    _ = Real.exp S * (r + (B - 1) / B * g) +
        (B - 1) / B * (Real.exp S * Real.exp (-S)) := by ring
    _ = _ := by rw [hcancel, he]; dsimp [g]; field_simp

private theorem response_spineMass_floor {B r : ℝ} (hB : 2 < B) (hr : 0 < r)
    (u : ℕ → ℝ) (hu : ∀ j, 0 < u j) (hf : ∀ j, floorSeq B j ≤ u j) (n : ℕ) :
    floorSeq B n ≤ responseSpineMass B n r u := by
  induction n with
  | zero =>
    simpa [responseSpineMass, responseSpineWalk] using hr.le
  | succ n hn =>
    rw [response_spineMass_step hB n u (hu n), floorSeq_succ]
    apply div_le_div_of_nonneg_right _ (by linarith)
    rw [pow_two]
    exact add_le_add_left
      (mul_le_mul hn (hf n) (floorSeq_nonneg hB n) (response_spineMass_pos hB hr n u).le) _

private theorem response_spineMass_log_lower {B r : ℝ} (hB : 2 < B) (hr : 0 < r)
    (n : ℕ) (u : ℕ → ℝ) :
    Real.log r + responseSpineWalk B n u ≤ Real.log (responseSpineMass B n r u) := by
  have hB' : 0 < B := by linarith
  have hc : 0 < B - 1 := by linarith
  have he : 0 < r * Real.exp (responseSpineWalk B n u) := by positivity
  rw [← Real.log_exp (responseSpineWalk B n u), ← Real.log_mul hr.ne' (Real.exp_ne_zero _)]
  apply Real.log_le_log he
  rw [responseSpineMass, mul_comm r]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (Real.exp_pos _).le

private theorem response_spine_restrict_measure (ν : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)]
    (n : ℕ) :
    MeasurePreserving (fun u : ℕ → ℝ => fun j : Fin n => u j)
      (Measure.infinitePi ν) (Measure.pi fun j : Fin n => ν j) := by
  let s := Finset.range n
  let e : s ≃ Fin n :=
    { toFun j := ⟨j.val, Finset.mem_range.1 j.property⟩
      invFun j := ⟨j.val, Finset.mem_range.2 j.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : MeasurePreserving s.restrict (Measure.infinitePi ν) (Measure.pi fun j : s => ν j) :=
    ⟨measurable_pi_iff.2 (fun j => measurable_pi_apply j.val), Measure.infinitePi_map_restrict ν⟩
  have he : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e)
      (Measure.pi fun j : s => ν j) (Measure.pi fun j : Fin n => ν j) :=
    measurePreserving_piCongrLeft (fun j : Fin n => ν j) e
  have hcomp : (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e) ∘ s.restrict =
      fun u : ℕ → ℝ => fun j : Fin n => u j := by
    funext u j
    change MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e (s.restrict u) (e (e.symm j)) = _
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    rfl
  rw [← hcomp]
  exact he.comp hs

private theorem response_positive_root {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hp : ∀ᵐ r ∂ν, 0 < r) :
    ∃ r₀ > 0, 0 < ν.real (Set.Ici r₀) := by
  by_contra! h
  have hu : Set.Ioi (0 : ℝ) = ⋃ j : ℕ, Set.Ici (1 / ((j : ℝ) + 1)) := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ici]
    refine ⟨fun hx => ?_, fun ⟨j, hj⟩ => (div_pos one_pos (by positivity)).trans_le hj⟩
    obtain ⟨j, hj⟩ := exists_nat_gt (1 / x)
    refine ⟨j, ?_⟩
    apply (div_le_iff₀ (by positivity : 0 < (j : ℝ) + 1)).2
    have ht := (div_lt_iff₀ hx).1 hj
    nlinarith only [ht, hx]
  have hzero (j : ℕ) : ν (Set.Ici (1 / ((j : ℝ) + 1))) = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top ν _)).1
      (le_antisymm (h _ (by positivity)) measureReal_nonneg)
  have hnull : ν (Set.Ioi (0 : ℝ)) = 0 := hu ▸ measure_iUnion_null hzero
  have hnull' : ν {r | 0 < r} = 0 := hnull
  have hae : ∀ᵐ r ∂ν, ¬ 0 < r := ae_iff.2 (by simpa only [not_not] using hnull')
  obtain ⟨r, hr, hn⟩ := (hp.and hae).exists
  exact hn hr

private theorem response_spine_weight_on_survival {B z r₀ r : ℝ} (hB : 2 < B)
    (hr₀ : 0 < r₀) (hr : r₀ ≤ r) {n : ℕ} {u : ℕ → ℝ}
    (hu : u ∈ responseSurvives (responseSpineIncrement B) z n) :
    (1 + (B - 1) / (B * r₀) * (Real.exp z *
      ∑' k : ℕ, (((k : ℝ) + 1)^2)⁻¹)) ^ (-(1 - theta B)) ≤
      spineW B n r (fun j : Fin n => u j) := by
  have hB0 : 0 < B := by linarith
  have hc : 0 ≤ B - 1 := by linarith
  have hS : (∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B (fun j : Fin n => u j) k)) ≤
      Real.exp z * (∑' k : ℕ, (((k : ℝ) + 1)^2)⁻¹) := by
    have hsum : Summable (fun k : ℕ => (((k : ℝ) + 1)^2)⁻¹) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 (by decide : 1 < (2 : ℕ)))
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 n, Real.exp z * (((k : ℝ) + 1)^2)⁻¹ := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := (Finset.mem_Icc.1 hk).2
        have hs := hu k hk'
        rw [response_spine_walk_sub] at hs
        rw [response_spineWalk_restrict B hk']
        have he : Real.exp z * (((k : ℝ) + 1)^2)⁻¹ =
            Real.exp (z - 2 * Real.log ((k : ℝ) + 1)) := by
          have hl : Real.log (((k : ℝ) + 1) ^ 2) = 2 * Real.log ((k : ℝ) + 1) := by
            simpa only [Nat.cast_ofNat] using Real.log_pow ((k : ℝ) + 1) 2
          rw [Real.exp_sub, ← hl, Real.exp_log (by positivity), div_eq_mul_inv]
        rw [he]
        apply Real.exp_le_exp.2
        linarith only [response_log_le_sum k, hs]
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun _ _ => by positivity) (Real.exp_pos _).le
  unfold spineW
  apply Real.rpow_le_rpow_of_nonpos (response_spine_base_pos hB (hr₀.trans_le hr) n _)
    _ (neg_nonpos.2 (sub_nonneg.2 (theta_lt_one hB).le))
  apply add_le_add_right
  exact mul_le_mul
    (div_le_div_of_nonneg_left hc (mul_pos hB0 hr₀) (mul_le_mul_of_nonneg_left hr hB0.le))
    hS (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) (div_nonneg hc (mul_pos hB0 hr₀).le)

private theorem response_spine_mean_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (hF : freeEnergy μ B h = 0) {C : ℝ} (hC : 0 < C)
    (hd : 0 < 1 / theta B - Real.log B)
    (hH : (fun n : ℕ => tiltedLogMoment μ B h 1 n) =O[atTop] fun n : ℕ => (n : ℝ)⁻¹)
    (hK : (fun n : ℕ => tiltedLogMoment μ B h 2 n) =Θ[atTop] fun n : ℕ => (n : ℝ))
    (hL : ∀ n : ℕ, 1 ≤ n → tiltedLogMoment μ B h 4 n ≤ C * ((n : ℝ) + 1) ^ 3) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, c ≤ spineMeanWLog μ B h n := by
  letI (j : ℕ) : IsProbabilityMeasure (tiltedLaw μ B h j) :=
    response_prob_tiltedLaw hpos hmean hB h j
  let ν := Measure.infinitePi (tiltedLaw μ B h)
  let τ := tiltedLaw μ B h 0
  let d := 1 / theta B - Real.log B
  have hτ : ∀ᵐ r ∂τ, 0 < r := response_tiltedLaw_ae 0 (ae_pos_lawR hpos hB h 0)
  obtain ⟨r₀, hr₀, hroot⟩ := response_positive_root hτ
  obtain ⟨z, hz, hflux⟩ := response_spine_flux hpos hmean hB h hF hC hH hK hL
  let W₀ : ℝ := (1 + (B - 1) / (B * r₀) * (Real.exp z *
    ∑' k : ℕ, (((k : ℝ) + 1)^2)⁻¹)) ^ (-(1 - theta B))
  have hW₀ : 0 < W₀ := by
    have hb : 0 < B := by linarith
    have hc : 0 < B - 1 := by linarith
    have hs : 0 ≤ ∑' k : ℕ, (((k : ℝ) + 1)^2)⁻¹ := tsum_nonneg fun _ => by positivity
    dsimp [W₀]
    exact Real.rpow_pos_of_pos (by positivity) _
  refine ⟨W₀ * τ.real (Set.Ici r₀) * (z / 2), by positivity, ?_⟩
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  have hlarge : ∀ᶠ n : ℕ in atTop, z ≤ Real.log r₀ + 2 * Real.log ((n : ℝ) + 1) + d := by
    filter_upwards [hlog.eventually_ge_atTop ((z - Real.log r₀ - d) / 2)] with n hn
    linarith
  have hfloor : ∀ᶠ n in atTop, Real.exp (-d) ≤ floorSeq B n :=
    ((tendsto_order.1 (tendsto_floorSeq hB)).1 _ (by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.2 (neg_neg_of_pos hd))).mono fun _ hn => hn.le
  have hall : ∀ᵐ u : ℕ → ℝ ∂ν, ∀ j, 0 < u j ∧ floorSeq B j ≤ u j := by
    apply ae_all_iff.2
    intro j
    exact (measurePreserving_eval_infinitePi (tiltedLaw μ B h) j).quasiMeasurePreserving.ae
      (response_tiltedLaw_ae j ((ae_pos_lawR hpos hB h j).and (ae_floorSeq_le_lawR hpos hB h j)))
  have hae : ∀ᵐ x : ℝ × (ℕ → ℝ) ∂τ.prod ν, 0 < x.1 ∧ ∀ j, 0 < x.2 j ∧ floorSeq B j ≤ x.2 j :=
    ((measurePreserving_fst (μ := τ) (ν := ν)).quasiMeasurePreserving.ae hτ).and
      ((measurePreserving_snd (μ := τ) (ν := ν)).quasiMeasurePreserving.ae hall)
  filter_upwards [hlarge, hfloor] with n hn hfn
  let I := responseSurvives (responseSpineIncrement B) z n
  let V (u : ℕ → ℝ) := z + responseWalk (responseSpineIncrement B) n u
  let p (r : ℝ) := (Set.Ici r₀).indicator (fun _ : ℝ => W₀) r
  let q := I.indicator V
  let f (x : ℝ × (Fin n → ℝ)) :=
    spineW B n x.1 x.2 * (Real.log (spineT B n x.1 x.2) + d)
  let emb (x : ℝ × (ℕ → ℝ)) : ℝ × (Fin n → ℝ) := (x.1, fun j => x.2 j)
  have hmp : MeasurePreserving emb (τ.prod ν) (spineMeasure μ B h n) :=
    (MeasurePreserving.id τ).prod (response_spine_restrict_measure (tiltedLaw μ B h) n)
  have hpi : Integrable p τ := (integrable_const W₀).indicator measurableSet_Ici
  have hqi : Integrable q ν := by
    have hYi (j : ℕ) : Integrable (responseSpineIncrement B j) ν := by
      have hE := measurePreserving_eval_infinitePi (tiltedLaw μ B h) j
      have hi := hE.integrable_comp_of_integrable (response_tiltedLaw_moment hpos hmean hB h j 1).1
      have hi' : Integrable (fun u : ℕ → ℝ => Real.log (u j) - Real.log B) ν := by
        simpa only [Function.comp_def, pow_one] using hi
      exact hi'.sub (integrable_const _)
    have hVi : Integrable V ν := (integrable_const z).add (integrable_finsetSum _ fun j _ => hYi j)
    exact hVi.indicator (responseSurvives_measurable (response_measurable_increment B) z n)
  have hfi : Integrable f (spineMeasure μ B h n) := (integrable_spine_aux hpos hmean hB h n).2
  have hpt : ∀ᵐ x : ℝ × (ℕ → ℝ) ∂τ.prod ν, p x.1 * q x.2 ≤ f (emb x) := by
    filter_upwards [hae] with x hx
    have ht := response_spineT_restrict hB hx.1 n x.2
    have hTfloor := response_spineMass_floor hB hx.1 x.2 (fun j => (hx.2 j).1)
      (fun j => (hx.2 j).2) n
    have hf0 : 0 ≤ f (emb x) := by
      dsimp [f, emb]
      apply mul_nonneg (response_spineW_pos hB hx.1 n _).le
      rw [ht]
      have hl := Real.log_le_log (Real.exp_pos (-d)) (hfn.trans hTfloor)
      rw [Real.log_exp] at hl
      linarith only [hl]
    by_cases hr : x.1 ∈ Set.Ici r₀
    · by_cases hu : x.2 ∈ I
      · have hw := response_spine_weight_on_survival hB hr₀ hr hu
        have hV0 : 0 ≤ V x.2 := hu n le_rfl
        have hlogT := response_spineMass_log_lower hB hx.1 n x.2
        have hlogr := Real.log_le_log hr₀ hr
        have hlogV : V x.2 ≤ Real.log (responseSpineMass B n x.1 x.2) + d := by
          dsimp [V]
          rw [response_spine_walk_sub]
          linarith only [hlogT, hlogr, hn, response_log_le_sum n]
        simp only [p, q, Set.indicator_of_mem hr, Set.indicator_of_mem hu, f, emb, ht]
        exact mul_le_mul hw hlogV hV0 (response_spineW_pos hB hx.1 n _).le
      · simpa only [q, Set.indicator_of_notMem hu, mul_zero] using hf0
    · simpa only [p, Set.indicator_of_notMem hr, zero_mul] using hf0
  have hle := integral_mono_ae (hpi.mul_prod hqi) (hmp.integrable_comp_of_integrable hfi) hpt
  change (∫ x : ℝ × (ℕ → ℝ), p x.1 * q x.2 ∂τ.prod ν) ≤ ∫ x, f (emb x) ∂τ.prod ν at hle
  have hfm : AEStronglyMeasurable f ((τ.prod ν).map emb) := by
    rw [hmp.map_eq]
    exact hfi.aestronglyMeasurable
  rw [integral_prod_mul p q, ← integral_map hmp.measurable.aemeasurable hfm,
    hmp.map_eq] at hle
  have hpI : (∫ r, p r ∂τ) = W₀ * τ.real (Set.Ici r₀) := by
    change (∫ r, (Set.Ici r₀).indicator (fun _ : ℝ => W₀) r ∂τ) = _
    rw [integral_indicator measurableSet_Ici, setIntegral_const, smul_eq_mul, mul_comm]
  have hqI : z / 2 ≤ ∫ u, q u ∂ν := by
    change z / 2 ≤ ∫ u, I.indicator V u ∂ν
    have hI : MeasurableSet I :=
      responseSurvives_measurable (response_measurable_increment B) z n
    rw [integral_indicator hI]
    exact hflux n
  rw [hpI] at hle
  exact (mul_le_mul_of_nonneg_left hqI (mul_nonneg hW₀.le measureReal_nonneg)).trans hle

/-- Strict transversality from the critical product, spine identities and
linear first response. The strict-shift premise is carried by the three
critical inputs. -/
theorem response_transversality_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
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
    (hSpine : ∀ n : ℕ, 0 < 1 / theta B - Real.log B ∧
      deriv (fun h' => tiltedMass μ B h' n) (criticalPoint μ B) / tiltedProduct μ B (criticalPoint μ B) n =
        theta B * tiltedMass μ B (criticalPoint μ B) 0 * spineMeanW μ B (criticalPoint μ B) n ∧
      deriv (fun h' => tiltedLogMoment μ B h' 1 n) (criticalPoint μ B) / tiltedProduct μ B (criticalPoint μ B) n =
        theta B * tiltedMass μ B (criticalPoint μ B) 0 * spineMeanWLog μ B (criticalPoint μ B) n)
    (hLinear : ∃ C : ℝ, ∀ n : ℕ,
      deriv (fun h => tiltedMass μ B h n) (criticalPoint μ B) ≤ C * ((n : ℝ) + 1)) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
        tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ) ∧
      (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B)) =Θ[atTop]
        fun n : ℕ => (n : ℝ) ^ 2 := by
  rcases hProd with ⟨C, hC, hp, hPi, _, _, _, hK, hH, _⟩
  obtain ⟨L, hL⟩ := hLinear
  let h := criticalPoint μ B
  let A := tiltedMass μ B h
  let H (n : ℕ) := tiltedLogMoment μ B h 1 n
  let P := tiltedProduct μ B h
  let D (n : ℕ) := deriv (fun x => tiltedMass μ B x n) h
  let E (n : ℕ) := deriv (fun x => tiltedLogMoment μ B x 1 n) h
  have hzero : freeEnergy μ B h = 0 := (criticalPoint_isGreatest_aux hpos hmean hB).1
  have hA n : 0 < A n := response_mass_pos hpos hmean hB h n
  have hP n : 0 < P n := Finset.prod_pos fun j _ => hA j
  have hPs n : P (n + 1) = A n * P n := by
    simp only [P, tiltedProduct, Finset.prod_range_succ, A, mul_comm]
  have hD n : 0 ≤ D n ∧ D n ≤ max L 0 * ((n : ℝ) + 1) := by
    refine ⟨?_, (hL n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩
    dsimp [D]
    rw [(hasDerivAt_tiltedMass_aux hpos hmean hB h n).deriv]
    apply mul_nonneg (theta_pos hB).le
    unfold contactMoment
    apply integral_nonneg_of_ae
    filter_upwards [ae_envPos_aux hpos n, gibbsWeight_isProb_aux hpos hB h n] with e he hw
    apply mul_nonneg (Real.rpow_nonneg (evalR_pos_aux (by linarith) h n he).le _)
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (hw.1 j) (pow_nonneg (Nat.cast_nonneg (α := ℝ) j) _)
  obtain ⟨M, hM, hkernel⟩ := response_kernel_antitone hB
  obtain ⟨K, hK0, hHd⟩ := response_global_decay_bound hH
  obtain ⟨b, hb, hsp⟩ := response_spine_mean_pos hpos hmean hB h hzero hC
    (hSpine 0).1 hH hK (fun n hn => (hp n hn).2.2.2)
  have hf : ∀ᶠ n in atTop, theta B * A 0 * b ≤ E n / P n := by
    filter_upwards [hsp] with n hn
    change theta B * A 0 * b ≤ deriv (fun h' => tiltedLogMoment μ B h' 1 n) h / tiltedProduct μ B h n
    rw [(hSpine n).2.2]
    exact mul_le_mul_of_nonneg_left hn (mul_nonneg (theta_pos hB).le (hA 0).le)
  have hr : ∀ᶠ n in atTop, E (n + 1) + M * D (n + 1) ≤
      A n * (E n + M * D n) + H n * D n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact response_combined_step hpos hmean hB (hkernel M le_rfl) h hn
  exact response_residue_of_recurrence hC (le_max_right L 0) hM hK0.le
    (mul_pos (mul_pos (theta_pos hB) (hA 0)) hb) hP hPs hPi
    (fun n hn => ⟨(hp n hn).1, (hp n hn).2.1⟩) hD
    (Eventually.of_forall hHd) hr hf

end DiamondPinning
