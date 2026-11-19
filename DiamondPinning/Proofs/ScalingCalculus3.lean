module

public import DiamondPinning.Proofs.ScalingCalculus2
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
Bounded-generation consequences of the Mellin recurrence: one-sided transform
increments, summability of the defect, bounded variation, and a uniform
one-sided Lipschitz estimate.  This covers `source/scaling.tex`, lines
148--161 and 179--188.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Set

private theorem exp_le_three {s N : ℝ} (hs : 0 ≤ s) (hN : 0 < N) (hsN : s ≤ N) :
    Real.exp (s / N) ≤ 3 := by
  have hx0 : 0 ≤ s / N := div_nonneg hs hN.le
  have hx1 : s / N ≤ 1 := (div_le_one hN).2 hsN
  have hexp := abs_exp_sub_one_sub_id_le (show |s / N| ≤ 1 by rw [abs_of_nonneg hx0]; exact hx1)
  have hh := le_abs_self (Real.exp (s / N) - 1 - s / N)
  have hxx : (s / N) ^ 2 ≤ s / N := by nlinarith
  rw [abs_of_nonneg hx0] at hexp
  nlinarith [hexp]

private theorem one_div_sq_le_one_div {N : ℝ} (hN : 1 ≤ N) : 1 / N ^ 2 ≤ 1 / N := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  apply (div_le_div_iff₀ (sq_pos_of_pos hN0) hN0).2
  nlinarith

private theorem eventually_weightExponent_mem {B : ℝ} (hB : 2 < B) (s : ℝ) :
    ∀ᶠ N : ℝ in atTop, weightExponent B N s ∈
      Set.Icc (theta B / 2) ((1 + theta B) / 2) := by
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hden : Tendsto (fun N : ℝ => Real.log B * N) atTop atTop :=
    tendsto_id.const_mul_atTop hlogB
  have hdiv : Tendsto (fun N : ℝ => s / (Real.log B * N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hlim : Tendsto (fun N : ℝ => weightExponent B N s) atTop (𝓝 (theta B)) := by
    simpa [weightExponent] using (tendsto_const_nhds.sub hdiv :
      Tendsto (fun N : ℝ => theta B - s / (Real.log B * N)) atTop
        (𝓝 (theta B - 0)))
  exact hlim.eventually (Icc_mem_nhds
    (by linarith [theta_pos hB]) (by linarith [theta_lt_one hB]))

private theorem eventually_weightExponent_range {B : ℝ} (hB : 2 < B)
    {s₀ s₁ : ℝ} :
    ∀ᶠ N : ℝ in atTop, ∀ s ∈ Set.Icc s₀ s₁, weightExponent B N s ∈
      Set.Icc (theta B / 2) ((1 + theta B) / 2) := by
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  filter_upwards [eventually_weightExponent_mem hB s₀,
    eventually_weightExponent_mem hB s₁, eventually_ge_atTop (0 : ℝ)] with N h0 h1 hN
  intro s hsI
  have hden : 0 ≤ Real.log B * N := mul_nonneg hlogB.le hN
  have hq1 : weightExponent B N s₁ ≤ weightExponent B N s := by
    unfold weightExponent
    have hd : s / (Real.log B * N) ≤ s₁ / (Real.log B * N) :=
      div_le_div_of_nonneg_right hsI.2 hden
    linarith
  have hq0 : weightExponent B N s ≤ weightExponent B N s₀ := by
    unfold weightExponent
    have hd : s₀ / (Real.log B * N) ≤ s / (Real.log B * N) :=
      div_le_div_of_nonneg_right hsI.1 hden
    linarith
  exact ⟨h1.1.trans hq1, hq0.trans h0.2⟩

private theorem eventually_geometric_floor {B r : ℝ} (hB : 2 < B) (hr : 0 < r) :
    ∀ᶠ N : ℝ in atTop, N ^ 2 * (2 / B) ^ ⌊N * r⌋₊ ≤ 1 / N := by
  let ρ := 2 / B
  have hρ0 : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by dsimp [ρ]; exact (div_lt_one (by linarith)).2 (by linarith)
  have hlogρ : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  let c := -r * Real.log ρ
  have hc : 0 < c := by
    dsimp [c]
    nlinarith [mul_pos hr (neg_pos.mpr hlogρ)]
  have hlim : Tendsto (fun N : ℝ => N ^ (3 : ℝ) * Real.exp (-c * N)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 c hc
  have hsmall : ∀ᶠ N : ℝ in atTop, N ^ (3 : ℝ) * Real.exp (-c * N) ≤ ρ := by
    filter_upwards [hlim.eventually (Iio_mem_nhds hρ0)] with N hN
    exact hN.le
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with N hg hN1
  have hN : 0 < N := zero_lt_one.trans_le hN1
  have hrN : N * r < ⌊N * r⌋₊ + 1 := Nat.lt_floor_add_one _
  have hpow : ρ ^ ⌊N * r⌋₊ ≤ ρ⁻¹ * Real.exp (-c * N) := by
    rw [← Real.rpow_natCast]
    calc
      ρ ^ (⌊N * r⌋₊ : ℝ) ≤ ρ ^ (r * N - 1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1.le
        exact_mod_cast (show r * N - 1 ≤ (⌊N * r⌋₊ : ℝ) by
          nlinarith)
      _ = ρ⁻¹ * Real.exp (-c * N) := by
        rw [Real.rpow_sub hρ0, Real.rpow_one, Real.rpow_def_of_pos hρ0]
        dsimp [c]
        rw [show Real.log ρ * (r * N) = -(-r * Real.log ρ) * N by ring]
        field_simp
  have hN3 : N ^ (3 : ℝ) = N ^ 3 := by norm_num [Real.rpow_natCast]
  have hg' : N ^ 3 * Real.exp (-c * N) ≤ ρ := by simpa [hN3] using hg
  change N ^ 2 * ρ ^ ⌊N * r⌋₊ ≤ 1 / N
  calc
    N ^ 2 * ρ ^ ⌊N * r⌋₊ ≤ N ^ 2 * (ρ⁻¹ * Real.exp (-c * N)) := by
      exact mul_le_mul_of_nonneg_left hpow (sq_nonneg N)
    _ = (ρ⁻¹ * (N ^ 3 * Real.exp (-c * N))) / N := by field_simp
    _ ≤ ρ⁻¹ * ρ / N := by gcongr
    _ = 1 / N := by rw [inv_mul_cancel₀ hρ0.ne']

private theorem transformAt_bounded_on_generations {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {B : ℝ} {r δ s₀ M : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    {N : ℝ} (hN : 0 < N) (h : ℝ) (n : ℕ)
    (hbound : ∀ t ∈ Set.Icc r (r + δ), |transformAt μ B h N ⌊N * t⌋₊ s₀| ≤ M)
    (hn0 : ⌊N * r⌋₊ ≤ n) (hnb : n < ⌈(r + δ) * N⌉₊) :
    |transformAt μ B h N n s₀| ≤ M := by
  by_cases hn : n = ⌊N * r⌋₊
  · subst n
    simpa using hbound r ⟨le_rfl, by linarith⟩
  · have hlt : ⌊N * r⌋₊ < n := lt_of_le_of_ne hn0 (Ne.symm hn)
    have hNr : N * r < (n : ℝ) := (Nat.floor_lt (mul_nonneg hN.le hr.le)).mp hlt
    have hnN : (n : ℝ) < (r + δ) * N := Nat.lt_ceil.mp hnb
    have ht : (n : ℝ) / N ∈ Set.Icc r (r + δ) := by
      constructor
      · exact (le_div_iff₀ hN).2 (by nlinarith)
      · exact (div_le_iff₀ hN).2 hnN.le
    have hb := hbound ((n : ℝ) / N) ht
    have hfloor : ⌊N * ((n : ℝ) / N)⌋₊ = n := by
      rw [show N * ((n : ℝ) / N) = (n : ℝ) by field_simp, Nat.floor_natCast]
    rwa [hfloor] at hb

-- The variation, defect-sum, and one-sided Lipschitz estimates share one
-- elaboration budget.
set_option maxHeartbeats 400000 in
/-- On a bounded generation interval the transform has uniform one-sided increments, summable
Mellin defects, bounded variation, and an asymptotically uniform one-sided Lipschitz bound.
This proves `DiamondPinning.transform_bounded` (in
`DiamondPinning.Statements.Scaling`). -/
theorem transform_bounded_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    ∃ C : ℝ, ∀ r δ s₀ M : ℝ, 0 < r → 0 < δ → 0 ≤ s₀ →
      ∃ N₁ CM : ℝ, ∃ ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ N : ℝ, N₁ ≤ N → ∀ h : ℝ,
          (∀ t ∈ Set.Icc r (r + δ), |transformAt μ B h N ⌊N * t⌋₊ s₀| ≤ M) →
          (∀ t ∈ Set.Icc r (r + δ),
              transformAt μ B h N (⌊N * t⌋₊ + 1) s₀ - transformAt μ B h N ⌊N * t⌋₊ s₀ ≤
                psiS s₀ (transformAt μ B h N ⌊N * t⌋₊ s₀) / N + CM / N ^ 2 +
                  C * N * (2 / B) ^ ⌊N * t⌋₊) ∧
          ∑ n ∈ Finset.Ico ⌈r * N⌉₊ ⌈(r + δ) * N⌉₊,
              |defectMean μ B h n (weightExponent B N s₀)| ≤ CM / N ∧
          eVariationOn (fun t => transformAt μ B h N ⌊N * t⌋₊ s₀) (Set.Icc r (r + δ)) ≤
              ENNReal.ofReal CM ∧
          ∀ t₁ t₂ : ℝ, r ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ r + δ →
            transformAt μ B h N ⌊N * t₂⌋₊ s₀ - transformAt μ B h N ⌊N * t₁⌋₊ s₀ ≤
              CM * (t₂ - t₁) + ε N := by
  obtain ⟨Cf, hCf⟩ := transform_floor_aux hpos hmean hB
  obtain ⟨CL, hCL⟩ := defectMean_lower_aux hpos hmean hB
    (theta B / 2) ((1 + theta B) / 2) (by linarith [theta_pos hB])
      (by linarith [theta_lt_one hB])
  let Cd := |CL|
  let F := |Cf|
  have hCd : 0 ≤ Cd := abs_nonneg _
  have hF : 0 ≤ F := abs_nonneg _
  refine ⟨2 * Cd, fun r δ s₀ M hr hδ hs₀ => ?_⟩
  have hev : ∀ᶠ N : ℝ in atTop, 1 ≤ N ∧ s₀ ≤ N ∧ 2 / r ≤ N ∧
      N ^ 2 * (2 / B) ^ ⌊N * r⌋₊ ≤ 1 / N ∧
      (∀ s ∈ Set.Icc s₀ s₀, weightExponent B N s ∈
        Set.Icc (theta B / 2) ((1 + theta B) / 2)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop s₀,
      eventually_ge_atTop (2 / r), eventually_geometric_floor hB hr,
      eventually_weightExponent_range hB] with N h1 hs h2 hg hq
    exact ⟨h1, hs, h2, hg, hq⟩
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  let A₀ := s₀ ^ 2 * M + (s₀ + 1) * M ^ 2
  let A₁ := 4 * s₀ * M + M ^ 2
  let A₂ := 2 * s₀ * M + 3 * M ^ 2 / 2
  let Kd := A₁ * (δ + 2) + 2 * M + 2 * F + 2 * Cd * (δ + 2)
  let Kv := A₂ * (δ + 2) + (3 / 2) * Kd
  let Kp := s₀ * M + M ^ 2 / 2
  let Ke := Kp + A₀ + A₀ * δ + 2 * Cd * (δ + 1)
  let CM := A₀ + Kd + Kv + Kp + 1
  have hε : Tendsto (fun N : ℝ => Ke / N) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero :
        Tendsto (fun N : ℝ => N⁻¹) atTop (𝓝 0)) :
        Tendsto (fun N : ℝ => Ke * N⁻¹) atTop (𝓝 (Ke * 0)))
  refine ⟨N₁, CM, fun N => Ke / N, hε, ?_⟩
  intro N hNN h hbound
  obtain ⟨hN1, hsN, hNr, hgeo, hqN⟩ := hN₁ N hNN
  have hN0 : 0 < N := zero_lt_one.trans_le hN1
  have hM : 0 ≤ M := by
    exact (abs_nonneg (transformAt μ B h N ⌊N * r⌋₊ s₀)).trans
      (hbound r ⟨le_rfl, by linarith⟩)
  have hA₀0 : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hA₁0 : 0 ≤ A₁ := by dsimp [A₁]; positivity
  have hA₂0 : 0 ≤ A₂ := by dsimp [A₂]; positivity
  have hKd0 : 0 ≤ Kd := by dsimp [Kd]; positivity
  have hKv0 : 0 ≤ Kv := by dsimp [Kv]; positivity
  have hKp0 : 0 ≤ Kp := by dsimp [Kp]; positivity
  let a₀ := ⌊N * r⌋₊
  let a := ⌈r * N⌉₊
  let b := ⌈(r + δ) * N⌉₊
  let L := fun n => transformAt μ B h N n s₀
  let D := fun n => defectMean μ B h n (weightExponent B N s₀)
  let ρ := 2 / B
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := by
    dsimp [ρ]
    exact (div_le_one (by linarith)).2 (by linarith)
  have ha₀1 : 1 ≤ a₀ := by
    apply Nat.le_floor
    have hh := mul_le_mul_of_nonneg_right hNr hr.le
    have heq : 2 / r * r = 2 := by field_simp
    rw [heq] at hh
    norm_num
    linarith
  have hab : a₀ ≤ b := by
    dsimp [a₀, b]
    have hh : N * r ≤ N * (r + δ) := by nlinarith
    exact (Nat.floor_mono hh).trans (by simpa [mul_comm] using Nat.floor_le_ceil (N * (r + δ)))
  have ha₀a : a₀ ≤ a := by
    dsimp [a₀, a]
    simpa [mul_comm] using Nat.floor_le_ceil (N * r)
  have hLext : ∀ n ∈ Finset.Ico a₀ b, |L n| ≤ M := by
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    exact transformAt_bounded_on_generations hr hδ hN0 h n
      (by simpa [L, a₀, b, mul_comm] using hbound) hn'.1 hn'.2
  have hLa₀ : |L a₀| ≤ M := by
    dsimp [L, a₀]
    exact hbound r ⟨le_rfl, by linarith⟩
  have hq0 : weightExponent B N s₀ ∈ Set.Icc (theta B / 2) ((1 + theta B) / 2) :=
    hqN s₀ ⟨le_rfl, le_rfl⟩
  have hq0nonneg : 0 ≤ weightExponent B N s₀ := by
    linarith [theta_pos hB, hq0.1]
  have hDlower : ∀ n : ℕ, 1 ≤ n → -(Cd * ρ ^ n) ≤ D n := by
    intro n hn
    have hh := hCL h n hn _ hq0
    have hc := mul_le_mul_of_nonneg_right (le_abs_self CL) (pow_nonneg hρ0 n)
    dsimp [Cd, D, ρ]
    nlinarith
  have hcard : ((b - a₀ : ℕ) : ℝ) ≤ δ * N + 2 := by
    have hf := Nat.lt_floor_add_one (N * r)
    have hc := Nat.ceil_lt_add_one (mul_nonneg (by linarith) hN0.le :
      0 ≤ (r + δ) * N)
    rw [Nat.cast_sub hab]
    dsimp [a₀, b]
    nlinarith
  have hNρ : N * ρ ^ a₀ ≤ 1 / N := by
    have hh : N * ρ ^ a₀ ≤ N ^ 2 * ρ ^ a₀ := by
      have hm := mul_nonneg (sub_nonneg.mpr hN1) (pow_nonneg hρ0 a₀)
      nlinarith
    exact hh.trans (by simpa [a₀, ρ, mul_comm] using hgeo)
  have hρle : ρ ^ a₀ ≤ 1 / N := by
    exact (by
      have hh : ρ ^ a₀ ≤ N * ρ ^ a₀ := by
        have hm := mul_nonneg (sub_nonneg.mpr hN1) (pow_nonneg hρ0 a₀)
        nlinarith
      exact hh.trans hNρ)
  have hcardρ : (δ * N + 2) * ρ ^ a₀ ≤ (δ + 2) / N := by
    calc
      (δ * N + 2) * ρ ^ a₀ = δ * (N * ρ ^ a₀) + 2 * ρ ^ a₀ := by ring
      _ ≤ δ * (1 / N) + 2 * (1 / N) :=
        add_le_add (mul_le_mul_of_nonneg_left hNρ hδ.le)
          (mul_le_mul_of_nonneg_left hρle (by norm_num))
      _ = (δ + 2) / N := by ring
  have hconst : ((b - a₀ : ℕ) : ℝ) * A₁ / N ^ 2 ≤ A₁ * (δ + 2) / N := by
    have hA₁ : 0 ≤ A₁ := by dsimp [A₁]; positivity
    have hdiv : 1 / N ^ 2 ≤ 1 / N := one_div_sq_le_one_div hN1
    calc
      ((b - a₀ : ℕ) : ℝ) * A₁ / N ^ 2 ≤ (δ * N + 2) * A₁ / N ^ 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcard hA₁) (sq_nonneg N)
      _ = A₁ * δ / N + 2 * A₁ * (1 / N ^ 2) := by field_simp
      _ ≤ A₁ * δ / N + 2 * A₁ * (1 / N) := by gcongr
      _ = A₁ * (δ + 2) / N := by ring
  have hdefect_ext : ∑ n ∈ Finset.Ico a₀ b, |D n| ≤ Kd / N := by
    let E := Real.exp (s₀ / N)
    let k := 2 / (N * E)
    have hE0 : 0 < E := Real.exp_pos _
    have hE1 : 1 ≤ E := Real.one_le_exp (div_nonneg hs₀ hN0.le)
    have hk0 : 0 ≤ k := by dsimp [k]; positivity
    have hkN : k ≤ 2 / N := by
      dsimp [k]
      apply div_le_div_of_nonneg_left (by norm_num) hN0
      nlinarith
    have hpoint : ∀ n ∈ Finset.Ico a₀ b, |D n| ≤
        A₁ / N ^ 2 - k * (L (n + 1) - L n) + 2 * Cd * ρ ^ n := by
      intro n hn
      have hn1 := ha₀1.trans (Finset.mem_Ico.mp hn).1
      have hh := defect_step_upper hpos hmean hB h hN1 hs₀ hsN hM hCd
        hn1 (hLext n hn) (by simpa [D, ρ] using hDlower n hn1)
      simpa [D, L, ρ, A₁, E, k] using hh
    have hsum : ∑ n ∈ Finset.Ico a₀ b, |D n| ≤
        ∑ n ∈ Finset.Ico a₀ b, (A₁ / N ^ 2 - k * (L (n + 1) - L n) + 2 * Cd * ρ ^ n) :=
      Finset.sum_le_sum hpoint
    have hsumEq : ∑ n ∈ Finset.Ico a₀ b,
        (A₁ / N ^ 2 - k * (L (n + 1) - L n) + 2 * Cd * ρ ^ n) =
        ((b - a₀ : ℕ) : ℝ) * A₁ / N ^ 2 - k * (L b - L a₀) +
          2 * Cd * ∑ n ∈ Finset.Ico a₀ b, ρ ^ n := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_Ico_sub _ hab, Nat.card_Ico]
      ring
    have hρb : ρ ^ b ≤ ρ ^ a₀ := pow_le_pow_of_le_one hρ0 hρ1 hab
    have hend : -(k * (L b - L a₀)) ≤ 2 * M / N + 2 * F * ρ ^ a₀ := by
      have hLa : L a₀ ≤ M := (abs_le.mp hLa₀).2
      have hLb0 := (hCf h N b s₀ s₀ hN0 hs₀ le_rfl hq0nonneg).1
      have hcf : Cf * N * (2 / B) ^ b ≤ F * N * (2 / B) ^ b := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self Cf) hN0.le) (by positivity)
      have hLb : -(F * N * ρ ^ b) ≤ L b := by
        dsimp [L, ρ]
        nlinarith
      have hdiff : -(M + F * N * ρ ^ b) ≤ L b - L a₀ := by nlinarith
      have hnon : 0 ≤ M + F * N * ρ ^ b := by positivity
      calc
        -(k * (L b - L a₀)) = k * (-(L b - L a₀)) := by ring
        _ ≤ k * (M + F * N * ρ ^ b) :=
          mul_le_mul_of_nonneg_left (by simpa using neg_le_neg hdiff) hk0
        _ ≤ (2 / N) * (M + F * N * ρ ^ b) := mul_le_mul_of_nonneg_right hkN hnon
        _ = 2 * M / N + 2 * F * ρ ^ b := by field_simp
        _ ≤ 2 * M / N + 2 * F * ρ ^ a₀ := by gcongr
    have hgeom : 2 * Cd * ∑ n ∈ Finset.Ico a₀ b, ρ ^ n ≤ 2 * Cd * (δ + 2) / N := by
      have hs : ∑ n ∈ Finset.Ico a₀ b, ρ ^ n ≤ ((b - a₀ : ℕ) : ℝ) * ρ ^ a₀ := by
        calc
          ∑ n ∈ Finset.Ico a₀ b, ρ ^ n ≤ ∑ _n ∈ Finset.Ico a₀ b, ρ ^ a₀ := by
            apply Finset.sum_le_sum
            intro n hn
            exact pow_le_pow_of_le_one hρ0 hρ1 (Finset.mem_Ico.mp hn).1
          _ = ((b - a₀ : ℕ) : ℝ) * ρ ^ a₀ := by simp [Nat.card_Ico]
      have hs' : ∑ n ∈ Finset.Ico a₀ b, ρ ^ n ≤ (δ * N + 2) * ρ ^ a₀ :=
        hs.trans (mul_le_mul_of_nonneg_right hcard (pow_nonneg hρ0 a₀))
      have hs'' := mul_le_mul_of_nonneg_left (hs'.trans hcardρ) (show 0 ≤ 2 * Cd by positivity)
      calc
        2 * Cd * ∑ n ∈ Finset.Ico a₀ b, ρ ^ n ≤
            2 * Cd * ((δ + 2) / N) := hs''
        _ = 2 * Cd * (δ + 2) / N := by ring
    calc
      ∑ n ∈ Finset.Ico a₀ b, |D n| ≤
          ∑ n ∈ Finset.Ico a₀ b,
            (A₁ / N ^ 2 - k * (L (n + 1) - L n) + 2 * Cd * ρ ^ n) := hsum
      _ = ((b - a₀ : ℕ) : ℝ) * A₁ / N ^ 2 - k * (L b - L a₀) +
          2 * Cd * ∑ n ∈ Finset.Ico a₀ b, ρ ^ n := hsumEq
      _ ≤ A₁ * (δ + 2) / N + (2 * M / N + 2 * F * ρ ^ a₀) + 2 * Cd * (δ + 2) / N := by
        exact add_le_add (add_le_add hconst hend) hgeom
      _ ≤ A₁ * (δ + 2) / N + (2 * M / N + 2 * F * (1 / N)) + 2 * Cd * (δ + 2) / N := by
        gcongr
      _ = Kd / N := by dsimp [Kd]; field_simp; ring
  have hdefect : ∑ n ∈ Finset.Ico a b, |D n| ≤ CM / N := by
    have hsub : Finset.Ico a b ⊆ Finset.Ico a₀ b := Finset.Ico_subset_Ico ha₀a le_rfl
    have hs : ∑ n ∈ Finset.Ico a b, |D n| ≤ ∑ n ∈ Finset.Ico a₀ b, |D n| :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi hi' => abs_nonneg _)
    have hKdCM : Kd ≤ CM := by dsimp [CM]; linarith
    exact hs.trans (hdefect_ext.trans (div_le_div_of_nonneg_right hKdCM hN0.le))
  have hE3 : Real.exp (s₀ / N) ≤ 3 := exp_le_three hs₀ hN0 hsN
  have hstep_ext : ∑ n ∈ Finset.Ico a₀ b, |L (n + 1) - L n| ≤ Kv := by
    have hpoint : ∀ n ∈ Finset.Ico a₀ b, |L (n + 1) - L n| ≤
        A₂ / N + (3 * N / 2) * |D n| := by
      intro n hn
      have hh := transform_step_abs hpos hmean hB h hN1 hs₀ hsN hM
        (ha₀1.trans (Finset.mem_Ico.mp hn).1) (hLext n hn)
      have he : N * Real.exp (s₀ / N) / 2 * |D n| ≤ (3 * N / 2) * |D n| := by
        calc
          N * Real.exp (s₀ / N) / 2 * |D n| =
              (N / 2 * Real.exp (s₀ / N)) * |D n| := by ring
          _ ≤ (N / 2 * 3) * |D n| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hE3 (by positivity)) (abs_nonneg _)
          _ = (3 * N / 2) * |D n| := by ring
      exact hh.trans (add_le_add le_rfl (by simpa [D, L, A₂] using he))
    have hsum := Finset.sum_le_sum hpoint
    have hsumEq : ∑ n ∈ Finset.Ico a₀ b, (A₂ / N + (3 * N / 2) * |D n|) =
        ((b - a₀ : ℕ) : ℝ) * A₂ / N + (3 * N / 2) * ∑ n ∈ Finset.Ico a₀ b, |D n| := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum, Nat.card_Ico]
      ring
    have hA₂ : 0 ≤ A₂ := by dsimp [A₂]; positivity
    have hfirst : ((b - a₀ : ℕ) : ℝ) * A₂ / N ≤ A₂ * (δ + 2) := by
      calc
        ((b - a₀ : ℕ) : ℝ) * A₂ / N ≤ (δ * N + 2) * A₂ / N := by
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hA₂) hN0.le
        _ = A₂ * (δ + 2 / N) := by field_simp
        _ ≤ A₂ * (δ + 2) := by
          have hh : 2 / N ≤ 2 := (div_le_iff₀ hN0).2 (by nlinarith only [hN1])
          exact mul_le_mul_of_nonneg_left (by linarith only [hh]) hA₂
    calc
      ∑ n ∈ Finset.Ico a₀ b, |L (n + 1) - L n| ≤
          ∑ n ∈ Finset.Ico a₀ b, (A₂ / N + (3 * N / 2) * |D n|) := hsum
      _ = ((b - a₀ : ℕ) : ℝ) * A₂ / N +
        (3 * N / 2) * ∑ n ∈ Finset.Ico a₀ b, |D n| := hsumEq
      _ ≤ A₂ * (δ + 2) + (3 * N / 2) * (Kd / N) := by gcongr
      _ = Kv := by dsimp [Kv]; field_simp
  have hstep : ∀ t ∈ Set.Icc r (r + δ),
      L (⌊N * t⌋₊ + 1) - L ⌊N * t⌋₊ ≤
        psiS s₀ (L ⌊N * t⌋₊) / N + CM / N ^ 2 + 2 * Cd * N * ρ ^ ⌊N * t⌋₊ := by
    intro t ht
    have hn0 : a₀ ≤ ⌊N * t⌋₊ := by
      dsimp [a₀]
      exact Nat.floor_mono (mul_le_mul_of_nonneg_left ht.1 hN0.le)
    have hh := transform_step_upper hpos hmean hB h hN1 hs₀ hsN hM hCd
      (ha₀1.trans hn0) (hbound t ht) (by
        simpa [D, ρ] using hDlower _ (ha₀1.trans hn0))
    have hA₀CM : A₀ ≤ CM := by dsimp [CM]; linarith
    exact hh.trans (add_le_add (add_le_add le_rfl
      (div_le_div_of_nonneg_right hA₀CM (sq_nonneg N))) le_rfl)
  have hKp : ∀ n ∈ Finset.Ico a₀ b, psiS s₀ (L n) ≤ Kp := by
    intro n hn
    have hLn := hLext n hn
    have hLu : L n ≤ M := (abs_le.mp hLn).2
    have hL2 : L n ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg (L n)) hM).2 hLn
    dsimp [Kp, psiS]
    exact add_le_add (mul_le_mul_of_nonneg_left hLu hs₀)
      (div_le_div_of_nonneg_right hL2 (by norm_num))
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [L, ρ] using hstep
  · simpa [D, a, b] using hdefect
  · rw [eVariationOn]
    apply iSup_le
    rintro ⟨p, u, hu, hus⟩
    let v := fun i => ⌊N * u i⌋₊
    have hv : Monotone v := by
      intro i j hij
      exact Nat.floor_mono (mul_le_mul_of_nonneg_left (hu hij) hN0.le)
    have hv0 : a₀ ≤ v 0 := by
      dsimp [a₀, v]
      exact Nat.floor_mono (mul_le_mul_of_nonneg_left (hus 0).1 hN0.le)
    have hvp : v p ≤ b := by
      dsimp [v, b]
      exact (Nat.floor_le_ceil (N * u p)).trans
        (Nat.ceil_mono (by simpa [mul_comm] using
          mul_le_mul_of_nonneg_left (hus p).2 hN0.le))
    have hvar : ∑ i ∈ Finset.range p, |L (v (i + 1)) - L (v i)| ≤ Kv := by
      calc
        ∑ i ∈ Finset.range p, |L (v (i + 1)) - L (v i)| ≤
            ∑ n ∈ Finset.Ico (v 0) (v p), |L (n + 1) - L n| :=
          monotone_sum_steps_le L v hv p
        _ ≤ ∑ n ∈ Finset.Ico a₀ b, |L (n + 1) - L n| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico hv0 hvp)
          intro i hi hi'
          exact abs_nonneg _
        _ ≤ Kv := hstep_ext
    have hKvCM : Kv ≤ CM := by dsimp [CM]; linarith
    simp_rw [edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => abs_nonneg _)]
    exact (ENNReal.ofReal_le_ofReal hvar).trans (ENNReal.ofReal_le_ofReal hKvCM)
  · intro t₁ t₂ ht₁ htt ht₂
    let m := ⌊N * t₁⌋₊
    let k₂ := ⌊N * t₂⌋₊
    have hmk : m ≤ k₂ := by
      dsimp [m, k₂]
      exact Nat.floor_mono (mul_le_mul_of_nonneg_left htt hN0.le)
    have hm0 : a₀ ≤ m := by
      dsimp [a₀, m]
      exact Nat.floor_mono (mul_le_mul_of_nonneg_left ht₁ hN0.le)
    have hkb : k₂ ≤ b := by
      dsimp [k₂, b]
      exact (Nat.floor_le_ceil (N * t₂)).trans
        (Nat.ceil_mono (by simpa [mul_comm] using
          mul_le_mul_of_nonneg_left ht₂ hN0.le))
    have hsub : Finset.Ico m k₂ ⊆ Finset.Ico a₀ b := Finset.Ico_subset_Ico hm0 hkb
    have hcardmk : ((k₂ - m : ℕ) : ℝ) ≤ N * (t₂ - t₁) + 1 := by
      have hf := Nat.lt_floor_add_one (N * t₁)
      have hk := Nat.floor_le (mul_nonneg hN0.le (by linarith : 0 ≤ t₂))
      rw [Nat.cast_sub hmk]
      dsimp [m, k₂]
      nlinarith only [hf, hk]
    have hΔ : L k₂ - L m = ∑ n ∈ Finset.Ico m k₂, (L (n + 1) - L n) := by
      rw [Finset.sum_Ico_sub L hmk]
    have hpoint : ∀ n ∈ Finset.Ico m k₂, L (n + 1) - L n ≤
        Kp / N + A₀ / N ^ 2 + 2 * Cd * N * ρ ^ n := by
      intro n hn
      have hn' : n ∈ Finset.Ico a₀ b := hsub hn
      have hn1 := ha₀1.trans (Finset.mem_Ico.mp hn').1
      have hh := transform_step_upper hpos hmean hB h hN1 hs₀ hsN hM hCd
        hn1 (hLext n hn') (by simpa [D, ρ] using hDlower n hn1)
      exact hh.trans (by gcongr; exact hKp n hn')
    have hsum := Finset.sum_le_sum hpoint
    have hsumEq : ∑ n ∈ Finset.Ico m k₂, (Kp / N + A₀ / N ^ 2 + 2 * Cd * N * ρ ^ n) =
        ((k₂ - m : ℕ) : ℝ) * Kp / N + ((k₂ - m : ℕ) : ℝ) * A₀ / N ^ 2 +
          2 * Cd * N * ∑ n ∈ Finset.Ico m k₂, ρ ^ n := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum, Nat.card_Ico]
      ring
    have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
    have hKp0 : 0 ≤ Kp := by dsimp [Kp]; positivity
    have hfirst : ((k₂ - m : ℕ) : ℝ) * Kp / N ≤ Kp * (t₂ - t₁) + Kp / N := by
      calc
        ((k₂ - m : ℕ) : ℝ) * Kp / N ≤ (N * (t₂ - t₁) + 1) * Kp / N := by
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcardmk hKp0) hN0.le
        _ = Kp * (t₂ - t₁) + Kp / N := by field_simp
    have hsecond : ((k₂ - m : ℕ) : ℝ) * A₀ / N ^ 2 ≤ A₀ * δ / N + A₀ / N := by
      have hdiv : 1 / N ^ 2 ≤ 1 / N := one_div_sq_le_one_div hN1
      have hdt : t₂ - t₁ ≤ δ := by linarith
      calc
        ((k₂ - m : ℕ) : ℝ) * A₀ / N ^ 2 ≤ (N * (t₂ - t₁) + 1) * A₀ / N ^ 2 := by
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcardmk hA₀) (sq_nonneg N)
        _ = A₀ * (t₂ - t₁) / N + A₀ * (1 / N ^ 2) := by field_simp
        _ ≤ A₀ * δ / N + A₀ * (1 / N) := by
          have hd : A₀ * (t₂ - t₁) / N ≤ A₀ * δ / N := by gcongr
          exact add_le_add hd (by gcongr)
        _ = A₀ * δ / N + A₀ / N := by ring
    have hgeom : 2 * Cd * N * ∑ n ∈ Finset.Ico m k₂, ρ ^ n ≤ 2 * Cd * (δ + 1) / N := by
      have hs : ∑ n ∈ Finset.Ico m k₂, ρ ^ n ≤ ((k₂ - m : ℕ) : ℝ) * ρ ^ a₀ := by
        calc
          ∑ n ∈ Finset.Ico m k₂, ρ ^ n ≤ ∑ _n ∈ Finset.Ico m k₂, ρ ^ a₀ := by
            apply Finset.sum_le_sum
            intro n hn
            exact pow_le_pow_of_le_one hρ0 hρ1 (hm0.trans (Finset.mem_Ico.mp hn).1)
          _ = ((k₂ - m : ℕ) : ℝ) * ρ ^ a₀ := by simp [Nat.card_Ico]
      have hs' : ∑ n ∈ Finset.Ico m k₂, ρ ^ n ≤ (N * (t₂ - t₁) + 1) * ρ ^ a₀ :=
        hs.trans (mul_le_mul_of_nonneg_right hcardmk (pow_nonneg hρ0 a₀))
      have hdt : t₂ - t₁ ≤ δ := by linarith
      have hmain : N * ((N * (t₂ - t₁) + 1) * ρ ^ a₀) ≤ (δ + 1) / N := by
        calc
          N * ((N * (t₂ - t₁) + 1) * ρ ^ a₀) =
              (t₂ - t₁) * (N ^ 2 * ρ ^ a₀) + N * ρ ^ a₀ := by ring
          _ ≤ (t₂ - t₁) * (1 / N) + 1 / N := by
            have hgeo' : N ^ 2 * ρ ^ a₀ ≤ 1 / N := by simpa [a₀, ρ, mul_comm] using hgeo
            exact add_le_add (mul_le_mul_of_nonneg_left hgeo' (by linarith)) hNρ
          _ ≤ δ * (1 / N) + 1 / N := by gcongr
          _ = (δ + 1) / N := by ring
      calc
        2 * Cd * N * ∑ n ∈ Finset.Ico m k₂, ρ ^ n =
            2 * Cd * (N * ∑ n ∈ Finset.Ico m k₂, ρ ^ n) := by ring
        _ ≤ 2 * Cd * (N * ((N * (t₂ - t₁) + 1) * ρ ^ a₀)) := by
          gcongr
        _ ≤ 2 * Cd * ((δ + 1) / N) :=
          mul_le_mul_of_nonneg_left hmain (show 0 ≤ 2 * Cd by positivity)
        _ = 2 * Cd * (δ + 1) / N := by ring
    have hKpCM : Kp ≤ CM := by
      dsimp only [CM]
      linarith only [hA₀0, hKd0, hKv0, hKp0]
    calc
      L k₂ - L m = ∑ n ∈ Finset.Ico m k₂, (L (n + 1) - L n) := hΔ
      _ ≤ ∑ n ∈ Finset.Ico m k₂, (Kp / N + A₀ / N ^ 2 + 2 * Cd * N * ρ ^ n) := hsum
      _ = ((k₂ - m : ℕ) : ℝ) * Kp / N + ((k₂ - m : ℕ) : ℝ) * A₀ / N ^ 2 +
          2 * Cd * N * ∑ n ∈ Finset.Ico m k₂, ρ ^ n := hsumEq
      _ ≤ (Kp * (t₂ - t₁) + Kp / N) + (A₀ * δ / N + A₀ / N) + 2 * Cd * (δ + 1) / N := by
        exact add_le_add (add_le_add hfirst hsecond) hgeom
      _ = Kp * (t₂ - t₁) + Ke / N := by dsimp only [Ke]; ring
      _ ≤ CM * (t₂ - t₁) + Ke / N :=
        add_le_add (mul_le_mul_of_nonneg_right hKpCM (sub_nonneg.mpr htt)) le_rfl

end DiamondPinning
