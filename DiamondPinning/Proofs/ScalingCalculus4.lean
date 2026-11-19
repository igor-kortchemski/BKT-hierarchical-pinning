module

public import DiamondPinning.Proofs.ScalingCalculus3
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
The summed estimate for the difference of two transform recurrences at weights
`s` and `s₀`, proving `scaling:transform-difference`.  This covers
`source/scaling.tex`, lines 162--167 and 189--192.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Set

private theorem recurrence_remainder_abs {N u L K : ℝ} (hN : 1 ≤ N)
    (hu : 0 ≤ u) (huN : u ≤ N) (hL : |L| ≤ K) :
    |(Real.exp (u / N) - 1 - u / N) * L +
        (Real.exp (u / N) - 1) / (2 * N) * L ^ 2| ≤
      (u ^ 2 * K + u * K ^ 2) / N ^ 2 := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hK : 0 ≤ K := (abs_nonneg L).trans hL
  let E := Real.exp (u / N)
  have hx0 : 0 ≤ u / N := div_nonneg hu hN0.le
  have hx1 : u / N ≤ 1 := (div_le_one hN0).2 huN
  have hexp : |E - 1 - u / N| ≤ |u / N| ^ 2 :=
    abs_exp_sub_one_sub_id_le (by rw [abs_of_nonneg hx0]; exact hx1)
  have hE0 : 0 ≤ E - 1 := by dsimp [E]; linarith [Real.one_le_exp hx0]
  have hEsmall : E - 1 ≤ 2 * (u / N) := by
    have hh := le_abs_self (E - 1 - u / N)
    rw [abs_of_nonneg hx0] at hexp
    nlinarith [sq_nonneg (u / N - 1)]
  have hL2 : L ^ 2 ≤ K ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg L) hK).2 hL
  have h1 : |(E - 1 - u / N) * L| ≤ u ^ 2 * K / N ^ 2 := by
    calc
      |(E - 1 - u / N) * L| = |E - 1 - u / N| * |L| := abs_mul _ _
      _ ≤ |u / N| ^ 2 * K := mul_le_mul hexp hL (abs_nonneg _) (sq_nonneg _)
      _ = u ^ 2 * K / N ^ 2 := by rw [abs_of_nonneg hx0, div_pow]; field_simp
  have h2 : |(E - 1) / (2 * N) * L ^ 2| ≤ u * K ^ 2 / N ^ 2 := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hE0 (by positivity)), abs_of_nonneg (sq_nonneg _)]
    calc
      (E - 1) / (2 * N) * L ^ 2 ≤ (2 * (u / N)) / (2 * N) * K ^ 2 := by gcongr
      _ = u * K ^ 2 / N ^ 2 := by field_simp
  calc
    |(E - 1 - u / N) * L + (E - 1) / (2 * N) * L ^ 2| ≤
        |(E - 1 - u / N) * L| + |(E - 1) / (2 * N) * L ^ 2| := abs_add_le _ _
    _ ≤ u ^ 2 * K / N ^ 2 + u * K ^ 2 / N ^ 2 := add_le_add h1 h2
    _ = (u ^ 2 * K + u * K ^ 2) / N ^ 2 := by ring

private theorem transformError_abs {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {B : ℝ} (h : ℝ) {N s₀ s s₁ K : ℝ} (hN : 1 ≤ N) (hs₀ : 0 ≤ s₀)
    (hss : s₀ ≤ s) (hs₁ : s ≤ s₁) (hsN : s₁ ≤ N) {n : ℕ}
    (hrec : transformAt μ B h N (n + 1) s =
      Real.exp (s / N) * transformAt μ B h N n s +
        Real.exp (s / N) / (2 * N) * transformAt μ B h N n s ^ 2 -
        N / 2 * Real.exp (s / N) * defectMean μ B h n (weightExponent B N s))
    (hrec₀ : transformAt μ B h N (n + 1) s₀ =
      Real.exp (s₀ / N) * transformAt μ B h N n s₀ +
        Real.exp (s₀ / N) / (2 * N) * transformAt μ B h N n s₀ ^ 2 -
        N / 2 * Real.exp (s₀ / N) * defectMean μ B h n (weightExponent B N s₀))
    (hLs : |transformAt μ B h N n s| ≤ K)
    (hL₀ : |transformAt μ B h N n s₀| ≤ K) :
    |transformError μ B h N n s s₀| ≤
      2 * (s₁ ^ 2 * K + s₁ * K ^ 2) / N ^ 2 +
        3 * N / 2 * |defectMean μ B h n (weightExponent B N s) -
          defectMean μ B h n (weightExponent B N s₀)| +
        2 * s₁ * |defectMean μ B h n (weightExponent B N s₀)| := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hs : 0 ≤ s := hs₀.trans hss
  have hsN' : s ≤ N := hs₁.trans hsN
  have hs₀₁ : s₀ ≤ s₁ := hss.trans hs₁
  have hK : 0 ≤ K := (abs_nonneg (transformAt μ B h N n s)).trans hLs
  have hs₀N : s₀ ≤ N := hss.trans hsN'
  let E := Real.exp (s / N)
  let E₀ := Real.exp (s₀ / N)
  let L := transformAt μ B h N n s
  let L₀ := transformAt μ B h N n s₀
  let D := defectMean μ B h n (weightExponent B N s)
  let D₀ := defectMean μ B h n (weightExponent B N s₀)
  let R := (E - 1 - s / N) * L + (E - 1) / (2 * N) * L ^ 2
  let R₀ := (E₀ - 1 - s₀ / N) * L₀ + (E₀ - 1) / (2 * N) * L₀ ^ 2
  have hid : transformError μ B h N n s s₀ =
      R - R₀ - N / 2 * E * (D - D₀) - N / 2 * (E - E₀) * D₀ := by
    unfold transformError
    rw [hrec, hrec₀]
    dsimp only [R, R₀, E, E₀, L, L₀, D, D₀]
    unfold psiS
    ring
  have hexp_small : ∀ u : ℝ, 0 ≤ u → u ≤ N →
      0 ≤ Real.exp (u / N) - 1 ∧ Real.exp (u / N) - 1 ≤ 2 * (u / N) := by
    intro u hu huN
    have hx0 : 0 ≤ u / N := div_nonneg hu hN0.le
    have hx1 : u / N ≤ 1 := (div_le_one hN0).2 huN
    have hexp := abs_exp_sub_one_sub_id_le
      (show |u / N| ≤ 1 by rw [abs_of_nonneg hx0]; exact hx1)
    have hh := le_abs_self (Real.exp (u / N) - 1 - u / N)
    rw [abs_of_nonneg hx0] at hexp
    constructor
    · linarith [Real.one_le_exp hx0]
    · nlinarith [sq_nonneg (u / N - 1)]
  have hE3 : E ≤ 3 := by
    have hx0 : 0 ≤ s / N := div_nonneg hs hN0.le
    have hx1 : s / N ≤ 1 := (div_le_one hN0).2 hsN'
    have hexp := abs_exp_sub_one_sub_id_le
      (show |s / N| ≤ 1 by rw [abs_of_nonneg hx0]; exact hx1)
    have hh := le_abs_self (E - 1 - s / N)
    have hxx : (s / N) ^ 2 ≤ s / N := by nlinarith
    rw [abs_of_nonneg hx0] at hexp
    dsimp only [E]
    nlinarith [hexp]
  have hR : |R| ≤ (s₁ ^ 2 * K + s₁ * K ^ 2) / N ^ 2 := by
    have hh := recurrence_remainder_abs hN hs hsN' hLs
    change |(Real.exp (s / N) - 1 - s / N) * L +
      (Real.exp (s / N) - 1) / (2 * N) * L ^ 2| ≤ _ at hh
    apply hh.trans
    gcongr
  have hR₀ : |R₀| ≤ (s₁ ^ 2 * K + s₁ * K ^ 2) / N ^ 2 := by
    have hh := recurrence_remainder_abs hN hs₀ hs₀N hL₀
    change |(Real.exp (s₀ / N) - 1 - s₀ / N) * L₀ +
      (Real.exp (s₀ / N) - 1) / (2 * N) * L₀ ^ 2| ≤ _ at hh
    apply hh.trans
    gcongr
  have hEdiff : |E - E₀| ≤ 4 * s₁ / N := by
    obtain ⟨hE0, hEs⟩ := hexp_small s hs hsN'
    obtain ⟨hE₀0, hE₀s⟩ := hexp_small s₀ hs₀ hs₀N
    calc
      |E - E₀| = |(E - 1) - (E₀ - 1)| := by congr 1; ring
      _ ≤ |E - 1| + |E₀ - 1| := abs_sub _ _
      _ = (E - 1) + (E₀ - 1) := by rw [abs_of_nonneg hE0, abs_of_nonneg hE₀0]
      _ ≤ 2 * (s / N) + 2 * (s₀ / N) := add_le_add hEs hE₀s
      _ = 2 * (s + s₀) / N := by ring
      _ ≤ 4 * s₁ / N := div_le_div_of_nonneg_right (by nlinarith) hN0.le
  have hT1 : |N / 2 * E * (D - D₀)| ≤ 3 * N / 2 * |D - D₀| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ N / 2),
      abs_of_pos (Real.exp_pos _)]
    change N / 2 * E * |D - D₀| ≤ _
    calc
      N / 2 * E * |D - D₀| ≤ N / 2 * 3 * |D - D₀| := by gcongr
      _ = 3 * N / 2 * |D - D₀| := by ring
  have hT2 : |N / 2 * (E - E₀) * D₀| ≤ 2 * s₁ * |D₀| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ N / 2)]
    calc
      N / 2 * |E - E₀| * |D₀| ≤ N / 2 * (4 * s₁ / N) * |D₀| := by gcongr
      _ = 2 * s₁ * |D₀| := by field_simp; ring
  rw [hid]
  calc
    |R - R₀ - N / 2 * E * (D - D₀) - N / 2 * (E - E₀) * D₀| ≤
        |R - R₀ - N / 2 * E * (D - D₀)| + |N / 2 * (E - E₀) * D₀| := abs_sub _ _
    _ ≤ (|R - R₀| + |N / 2 * E * (D - D₀)|) +
        |N / 2 * (E - E₀) * D₀| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ ((|R| + |R₀|) + |N / 2 * E * (D - D₀)|) +
        |N / 2 * (E - E₀) * D₀| := by gcongr; exact abs_sub _ _
    _ ≤ ((s₁ ^ 2 * K + s₁ * K ^ 2) / N ^ 2 +
          (s₁ ^ 2 * K + s₁ * K ^ 2) / N ^ 2) +
        3 * N / 2 * |D - D₀| + 2 * s₁ * |D₀| := by gcongr
    _ = 2 * (s₁ ^ 2 * K + s₁ * K ^ 2) / N ^ 2 +
        3 * N / 2 * |D - D₀| + 2 * s₁ * |D₀| := by ring

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

-- The uniform recurrence comparison and its finite-sum estimates share one
-- elaboration budget.
set_option maxHeartbeats 400000 in
/-- Uniformly for weights in a compact interval, the summed recurrence-difference errors on a
bounded generation interval are `O(N⁻¹)`.
This proves `DiamondPinning.transform_difference` (in
`DiamondPinning.Statements.Scaling`). -/
theorem transform_difference_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    ∀ r δ s₀ s₁ M : ℝ, 0 < r → 0 < δ → 0 ≤ s₀ → s₀ ≤ s₁ →
      ∃ N₁ C : ℝ, ∀ N : ℝ, N₁ ≤ N → ∀ h : ℝ,
        (∀ t ∈ Set.Icc r (r + δ), |transformAt μ B h N ⌊N * t⌋₊ s₀| ≤ M) →
        ∀ s ∈ Set.Icc s₀ s₁,
          ∑ n ∈ Finset.Ico ⌈r * N⌉₊ ⌈(r + δ) * N⌉₊, |transformError μ B h N n s s₀| ≤
            C / N := by
  obtain ⟨Cf, hCf⟩ := transform_floor_aux hpos hmean hB
  obtain ⟨Cs, hCs⟩ := defectMean_sub_aux hpos hmean hB
    (theta B / 2) ((1 + theta B) / 2) (by linarith [theta_pos hB])
      (by linarith [theta_lt_one hB])
  obtain ⟨Cb, hCb⟩ := transform_bounded_aux hpos hmean hB
  intro r δ s₀ s₁ M hr hδ hs₀ hs₀₁
  obtain ⟨Nb, CM, ε, hε, hb⟩ := hCb r δ s₀ M hr hδ hs₀
  have hev : ∀ᶠ N : ℝ in atTop, Nb ≤ N ∧ 1 ≤ N ∧ s₁ ≤ N ∧ 2 / r ≤ N ∧
      N ^ 2 * (2 / B) ^ ⌊N * r⌋₊ ≤ 1 / N ∧
      (∀ s ∈ Set.Icc s₀ s₁, weightExponent B N s ∈
        Set.Icc (theta B / 2) ((1 + theta B) / 2)) := by
    filter_upwards [eventually_ge_atTop Nb, eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop s₁, eventually_ge_atTop (2 / r),
      eventually_geometric_floor hB hr,
      eventually_weightExponent_range hB] with N hNb h1 hs h2 hg hq
    exact ⟨hNb, h1, hs, h2, hg, hq⟩
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  let F := |Cf|
  let S := |Cs|
  let K := M + F
  let Q := S * (s₁ - s₀) / Real.log B
  let A := 2 * (s₁ ^ 2 * K + s₁ * K ^ 2)
  let P := 3 / 2 * Q + 2 * s₁
  let G := 3 / 2 * Q * S
  let C := A * (δ + 2) + P * |CM| + G * (δ + 2)
  refine ⟨N₁, C, fun N hNN h hbound => ?_⟩
  intro s hsI
  obtain ⟨hNb, hN1, hsN, hNr, hgeo, hqN⟩ := hN₁ N hNN
  have hN0 : 0 < N := zero_lt_one.trans_le hN1
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hden : 0 < Real.log B * N := mul_pos hlogB hN0
  have hM : 0 ≤ M :=
    (abs_nonneg (transformAt μ B h N ⌊N * r⌋₊ s₀)).trans
      (hbound r ⟨le_rfl, by linarith⟩)
  have hF : 0 ≤ F := abs_nonneg _
  have hS : 0 ≤ S := abs_nonneg _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs₁ : 0 ≤ s₁ := hs₀.trans hs₀₁
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  let a₀ := ⌊N * r⌋₊
  let a := ⌈r * N⌉₊
  let b := ⌈(r + δ) * N⌉₊
  let L₀ := fun n => transformAt μ B h N n s₀
  let L := fun n => transformAt μ B h N n s
  let D₀ := fun n => defectMean μ B h n (weightExponent B N s₀)
  let D := fun n => defectMean μ B h n (weightExponent B N s)
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
  have ha₀a : a₀ ≤ a := by
    dsimp [a₀, a]
    simpa [mul_comm] using Nat.floor_le_ceil (N * r)
  have hab : a ≤ b := by
    dsimp [a, b]
    apply Nat.ceil_mono
    nlinarith [mul_nonneg hN0.le hδ.le]
  have ha₀b : a₀ ≤ b := ha₀a.trans hab
  have hs : 0 ≤ s := hs₀.trans hsI.1
  have hq0 : weightExponent B N s₀ ∈ Set.Icc (theta B / 2) ((1 + theta B) / 2) :=
    hqN s₀ ⟨le_rfl, hs₀₁⟩
  have hqs : weightExponent B N s ∈ Set.Icc (theta B / 2) ((1 + theta B) / 2) :=
    hqN s hsI
  have hq0nonneg : 0 ≤ weightExponent B N s₀ := by
    linarith [theta_pos hB, hq0.1]
  have hqsnonneg : 0 ≤ weightExponent B N s := by
    linarith [theta_pos hB, hqs.1]
  have hsub : Finset.Ico a b ⊆ Finset.Ico a₀ b := Finset.Ico_subset_Ico ha₀a le_rfl
  have hLext₀ : ∀ n ∈ Finset.Ico a₀ b, |L₀ n| ≤ M := by
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    exact transformAt_bounded_on_generations hr hδ hN0 h n
      (by simpa [L₀, a₀, b, mul_comm] using hbound) hn'.1 hn'.2
  have hLext : ∀ n ∈ Finset.Ico a b, |L₀ n| ≤ M := by
    intro n hn
    exact hLext₀ n (hsub hn)
  have hNρ₀ : N * ρ ^ a₀ ≤ 1 / N := by
    have hh : N * ρ ^ a₀ ≤ N ^ 2 * ρ ^ a₀ := by
      have hm := mul_nonneg (sub_nonneg.mpr hN1) (pow_nonneg hρ0 a₀)
      nlinarith
    exact hh.trans (by simpa [a₀, ρ, mul_comm] using hgeo)
  have hρle₀ : ρ ^ a₀ ≤ 1 / N := by
    have hh : ρ ^ a₀ ≤ N * ρ ^ a₀ := by
      have hm := mul_nonneg (sub_nonneg.mpr hN1) (pow_nonneg hρ0 a₀)
      nlinarith
    exact hh.trans hNρ₀
  have hNρ : ∀ n : ℕ, a₀ ≤ n → N * ρ ^ n ≤ 1 / N := by
    intro n hn
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0 hρ1 hn) hN0.le).trans hNρ₀
  have hpoint : ∀ n ∈ Finset.Ico a b, |transformError μ B h N n s s₀| ≤
      A / N ^ 2 + P * |D₀ n| + G * ρ ^ n := by
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    have hn0 : a₀ ≤ n := ha₀a.trans hn'.1
    have hn1 : 1 ≤ n := ha₀1.trans hn0
    have hL0M : |L₀ n| ≤ M := hLext n hn
    have hL0K : |L₀ n| ≤ K := hL0M.trans (by dsimp [K]; linarith)
    have hfloor := hCf h N n s₀ s hN0 hs₀ hsI.1 hqsnonneg
    have hNρn := hNρ n hn0
    have hNρone : N * ρ ^ n ≤ 1 := by
      exact hNρn.trans ((div_le_one hN0).2 (by simpa using hN1))
    have hFN : F * N * ρ ^ n ≤ F := by
      have hh := mul_le_mul_of_nonneg_left hNρone hF
      calc
        F * N * ρ ^ n = F * (N * ρ ^ n) := by ring
        _ ≤ F * 1 := hh
        _ = F := mul_one F
    have hCfρ : Cf * N * ρ ^ n ≤ F := by
      have hh : Cf * N * ρ ^ n ≤ F * N * ρ ^ n := by
        dsimp [F]
        gcongr
        exact le_abs_self Cf
      exact hh.trans hFN
    have hLs : |L n| ≤ K := by
      rw [abs_le]
      constructor
      · have hL0upper : L₀ n ≤ M := (abs_le.mp hL0M).2
        dsimp [L, L₀, K] at *
        nlinarith [hfloor.1]
      · have hL0upper : L₀ n ≤ M := (abs_le.mp hL0M).2
        dsimp [L, L₀, K] at *
        nlinarith [hfloor.2]
    have hrec := transform_recurrence_aux hpos hmean hB h hN0 hn1 hs
    have hrec₀ := transform_recurrence_aux hpos hmean hB h hN0 hn1 hs₀
    have herr := transformError_abs h hN1 hs₀ hsI.1 hsI.2 hsN hrec hrec₀
      (by simpa [L] using hLs) (by simpa [L₀] using hL0K)
    have hdq : |weightExponent B N s - weightExponent B N s₀| =
        (s - s₀) / (Real.log B * N) := by
      have heq : weightExponent B N s - weightExponent B N s₀ =
          -((s - s₀) / (Real.log B * N)) := by
        unfold weightExponent
        ring
      rw [heq, abs_neg, abs_div, abs_of_nonneg (sub_nonneg.mpr hsI.1), abs_of_pos hden]
    have hraw := hCs h n hn1 _ hqs _ hq0
    have hnon : 0 ≤ Cs * |weightExponent B N s - weightExponent B N s₀| *
        (defectMean μ B h n (weightExponent B N s₀) + Cs * (2 / B) ^ n) :=
      (abs_nonneg _).trans hraw
    have hbase : 0 ≤ |D₀ n| + S * ρ ^ n := by positivity
    have hbaseC : |defectMean μ B h n (weightExponent B N s₀) + Cs * (2 / B) ^ n| ≤
        |D₀ n| + S * ρ ^ n := by
      calc
        |defectMean μ B h n (weightExponent B N s₀) + Cs * (2 / B) ^ n| ≤
            |defectMean μ B h n (weightExponent B N s₀)| + |Cs * (2 / B) ^ n| :=
          abs_add_le _ _
        _ = |D₀ n| + S * ρ ^ n := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hρ0 n)]
    have hdiff₀ : |D n - D₀ n| ≤
        S * ((s - s₀) / (Real.log B * N)) * (|D₀ n| + S * ρ ^ n) := by
      calc
        |D n - D₀ n| ≤ Cs * |weightExponent B N s - weightExponent B N s₀| *
            (defectMean μ B h n (weightExponent B N s₀) + Cs * (2 / B) ^ n) := hraw
        _ = |Cs * |weightExponent B N s - weightExponent B N s₀| *
            (defectMean μ B h n (weightExponent B N s₀) + Cs * (2 / B) ^ n)| :=
          (abs_of_nonneg hnon).symm
        _ = S * |weightExponent B N s - weightExponent B N s₀| *
            |defectMean μ B h n (weightExponent B N s₀) + Cs * (2 / B) ^ n| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (abs_nonneg _)]
        _ ≤ S * |weightExponent B N s - weightExponent B N s₀| *
            (|D₀ n| + S * ρ ^ n) := by gcongr
        _ = S * ((s - s₀) / (Real.log B * N)) * (|D₀ n| + S * ρ ^ n) := by rw [hdq]
    have hfactor : (s - s₀) / (Real.log B * N) ≤
        (s₁ - s₀) / (Real.log B * N) :=
      div_le_div_of_nonneg_right (by linarith [hsI.2]) hden.le
    have hdiff₁ : |D n - D₀ n| ≤
        S * ((s₁ - s₀) / (Real.log B * N)) * (|D₀ n| + S * ρ ^ n) := by
      apply hdiff₀.trans
      gcongr
    have hdiff : N * |D n - D₀ n| ≤ Q * (|D₀ n| + S * ρ ^ n) := by
      have hh := mul_le_mul_of_nonneg_left hdiff₁ hN0.le
      calc
        N * |D n - D₀ n| ≤
            N * (S * ((s₁ - s₀) / (Real.log B * N)) * (|D₀ n| + S * ρ ^ n)) := hh
        _ = Q * (|D₀ n| + S * ρ ^ n) := by
          dsimp [Q]
          field_simp [hlogB.ne', hN0.ne']
    have hDterm : 3 * N / 2 * |D n - D₀ n| ≤
        (3 / 2) * Q * (|D₀ n| + S * ρ ^ n) := by
      calc
        3 * N / 2 * |D n - D₀ n| = (3 / 2) * (N * |D n - D₀ n|) := by ring
        _ ≤ (3 / 2) * (Q * (|D₀ n| + S * ρ ^ n)) :=
          mul_le_mul_of_nonneg_left hdiff (by norm_num)
        _ = (3 / 2) * Q * (|D₀ n| + S * ρ ^ n) := by ring
    calc
      |transformError μ B h N n s s₀| ≤
          2 * (s₁ ^ 2 * K + s₁ * K ^ 2) / N ^ 2 +
            3 * N / 2 * |D n - D₀ n| + 2 * s₁ * |D₀ n| := herr
      _ ≤ 2 * (s₁ ^ 2 * K + s₁ * K ^ 2) / N ^ 2 +
            (3 / 2) * Q * (|D₀ n| + S * ρ ^ n) + 2 * s₁ * |D₀ n| := by gcongr
      _ = A / N ^ 2 + P * |D₀ n| + G * ρ ^ n := by
        dsimp [A, P, G]
        ring
  have hsum := Finset.sum_le_sum hpoint
  have hcard : ((b - a : ℕ) : ℝ) ≤ δ * N + 2 := by
    have hca : r * N ≤ (⌈r * N⌉₊ : ℝ) := Nat.le_ceil _
    have hcb := Nat.ceil_lt_add_one (mul_nonneg (by linarith) hN0.le :
      0 ≤ (r + δ) * N)
    rw [Nat.cast_sub hab]
    dsimp [a, b]
    nlinarith
  have hconst : ((b - a : ℕ) : ℝ) * A / N ^ 2 ≤ A * (δ + 2) / N := by
    have hdiv : 1 / N ^ 2 ≤ 1 / N := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hN0) hN0).2
      nlinarith
    calc
      ((b - a : ℕ) : ℝ) * A / N ^ 2 ≤ (δ * N + 2) * A / N ^ 2 := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hA) (sq_nonneg N)
      _ = A * δ / N + 2 * A * (1 / N ^ 2) := by field_simp
      _ ≤ A * δ / N + 2 * A * (1 / N) := by gcongr
      _ = A * (δ + 2) / N := by ring
  have hdefect : ∑ n ∈ Finset.Ico a b, |D₀ n| ≤ |CM| / N := by
    have hh := (hb N hNb h hbound).2.1
    have hh' : ∑ n ∈ Finset.Ico a b, |D₀ n| ≤ CM / N := by
      simpa [D₀, a, b] using hh
    exact hh'.trans (div_le_div_of_nonneg_right (le_abs_self CM) hN0.le)
  have hgeom : ∑ n ∈ Finset.Ico a b, ρ ^ n ≤ (δ + 2) / N := by
    have hs : ∑ n ∈ Finset.Ico a b, ρ ^ n ≤ ((b - a : ℕ) : ℝ) * ρ ^ a₀ := by
      calc
        ∑ n ∈ Finset.Ico a b, ρ ^ n ≤ ∑ _n ∈ Finset.Ico a b, ρ ^ a₀ := by
          apply Finset.sum_le_sum
          intro n hn
          exact pow_le_pow_of_le_one hρ0 hρ1 (ha₀a.trans (Finset.mem_Ico.mp hn).1)
        _ = ((b - a : ℕ) : ℝ) * ρ ^ a₀ := by simp [Nat.card_Ico]
    have hs' : ∑ n ∈ Finset.Ico a b, ρ ^ n ≤ (δ * N + 2) * ρ ^ a₀ :=
      hs.trans (mul_le_mul_of_nonneg_right hcard (pow_nonneg hρ0 a₀))
    have hcardρ : (δ * N + 2) * ρ ^ a₀ ≤ (δ + 2) / N := by
      calc
        (δ * N + 2) * ρ ^ a₀ = δ * (N * ρ ^ a₀) + 2 * ρ ^ a₀ := by ring
        _ ≤ δ * (1 / N) + 2 * (1 / N) :=
          add_le_add (mul_le_mul_of_nonneg_left hNρ₀ hδ.le)
            (mul_le_mul_of_nonneg_left hρle₀ (by norm_num))
        _ = (δ + 2) / N := by ring
    exact hs'.trans hcardρ
  have hsumEq : ∑ n ∈ Finset.Ico a b, (A / N ^ 2 + P * |D₀ n| + G * ρ ^ n) =
      ((b - a : ℕ) : ℝ) * A / N ^ 2 + P * (∑ n ∈ Finset.Ico a b, |D₀ n|) +
        G * (∑ n ∈ Finset.Ico a b, ρ ^ n) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, Nat.card_Ico]
    ring
  calc
    ∑ n ∈ Finset.Ico a b, |transformError μ B h N n s s₀| ≤
        ∑ n ∈ Finset.Ico a b, (A / N ^ 2 + P * |D₀ n| + G * ρ ^ n) := hsum
    _ = ((b - a : ℕ) : ℝ) * A / N ^ 2 + P * (∑ n ∈ Finset.Ico a b, |D₀ n|) +
        G * (∑ n ∈ Finset.Ico a b, ρ ^ n) := hsumEq
    _ ≤ A * (δ + 2) / N + P * (|CM| / N) + G * ((δ + 2) / N) := by gcongr
    _ = C / N := by dsimp [C]; ring

end DiamondPinning
