module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Model.Basic
public import DiamondPinning.Model.Moments
public import DiamondPinning.Model.Scaling
public import DiamondPinning.Model.Window
public import DiamondPinning.Proofs.ScalingCalculus4
public import DiamondPinning.Proofs.IntegrabilityProof
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Proof of `scaling:compactness`, part 1: extraction machinery and analytic lemmas

General lemmas used by the proof of `scaling_compactness_of`
(`DiamondPinning.Proofs.CompactnessProof2`):

* diagonal extraction for countable families of eventually bounded sequences;
* uniform Cauchy property from convergence on a dense set and asymptotic
  equicontinuity (the Arzelà–Ascoli step);
* the selection lemma for almost monotone sequences (`S_N` satisfies a one-sided
  Lipschitz bound up to errors tending to zero);
* existence of weak limits of finite measures on `[0, ∞)` whose Laplace transforms
  converge (Prokhorov's theorem and Weierstrass approximation in `e^{-x}`);
* measurability of a measure-valued map from the measurability of its integrals;
* the analytic extension of the compensated Laplace transform;
* the third-order Taylor bound of `e^{-z}` with remainder `O(|z|^{7/2})`, and the
  extraction of polynomial coefficients from such an expansion;
* the integral of a step function `τ ↦ F ⌊N τ⌋`.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Set
open scoped BoundedContinuousFunction

/-! ### Diagonal extraction -/

/-- Diagonal extraction: a countable family of eventually bounded real sequences has a common
subsequence along which all of them converge. -/
theorem exists_subseq_tendsto_of_countable {ι : Type*} [Countable ι] (x : ℕ → ι → ℝ)
    (hx : ∀ i, ∃ M : ℝ, ∀ᶠ j in atTop, |x j i| ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∃ L : ℝ, Tendsto (fun j => x (φ j) i) atTop (𝓝 L) := by
  choose M hM using hx
  let y : ℕ → ι → ℝ := fun j i => max (-|M i|) (min |M i| (x j i))
  have hmem : ∀ j, y j ∈ Set.pi Set.univ (fun i => Set.Icc (-|M i|) |M i|) := by
    intro j i _
    refine ⟨le_max_left _ _, max_le ?_ (min_le_left _ _)⟩
    linarith [abs_nonneg (M i)]
  have hK : IsCompact (Set.pi Set.univ (fun i => Set.Icc (-|M i|) |M i|)) :=
    isCompact_univ_pi fun i => isCompact_Icc
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  refine ⟨φ, hφ, fun i => ⟨a i, ?_⟩⟩
  have h1 : Tendsto (fun j => y (φ j) i) atTop (𝓝 (a i)) := tendsto_pi_nhds.1 hlim i
  have h2 : ∀ᶠ j in atTop, y (φ j) i = x (φ j) i := by
    filter_upwards [hφ.tendsto_atTop.eventually (hM i)] with j hj
    have hj' := abs_le.1 (hj.trans (le_abs_self _))
    change max (-|M i|) (min |M i| (x (φ j) i)) = x (φ j) i
    rw [min_eq_right hj'.2, max_eq_right hj'.1]
  exact h1.congr' h2

/-! ### Uniform convergence from a dense set -/

/-- Convergence on a dense set and asymptotic equicontinuity give a uniformly Cauchy
sequence on a compact set. -/
theorem uniformCauchySeqOn_of_dense {α : Type*} [PseudoMetricSpace α] (f : ℕ → α → ℝ)
    {K D : Set α} (hK : IsCompact K) (hD : ∀ x ∈ K, ∀ δ > 0, ∃ d ∈ D, dist x d < δ)
    (hconv : ∀ d ∈ D, ∃ L, Tendsto (fun j => f j d) atTop (𝓝 L))
    (heq : ∀ ε > 0, ∃ δ > 0, ∀ᶠ j in atTop, ∀ x ∈ K, ∀ d ∈ D, dist x d < δ →
      |f j x - f j d| < ε) :
    UniformCauchySeqOn f atTop K := by
  choose! L hL using hconv
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hev⟩ := heq (ε / 3) (by linarith)
  have hcover : K ⊆ ⋃ d ∈ D, Metric.ball d δ := by
    intro x hx
    obtain ⟨d, hd, hxd⟩ := hD x hx δ hδ
    exact Set.mem_biUnion hd (Metric.mem_ball.2 hxd)
  obtain ⟨t, htD, htfin, hKt⟩ :=
    hK.elim_finite_subcover_image (fun d _ => Metric.isOpen_ball) hcover
  have hfin : ∀ᶠ j in atTop, ∀ d ∈ t, |f j d - L d| < ε / 6 := by
    refine (Filter.eventually_all_finite htfin).2 fun d hd => ?_
    exact (Metric.tendsto_nhds.1 (hL d (htD hd)) (ε / 6) (by linarith)).mono fun j hj => by
      simpa [Real.dist_eq] using hj
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and hfin)
  refine ⟨N, fun m hm n hn x hx => ?_⟩
  obtain ⟨d, hdt, hxd⟩ := Set.mem_iUnion₂.1 (hKt hx)
  have hxd' : dist x d < δ := Metric.mem_ball.1 hxd
  have h1 := abs_lt.1 ((hN m hm).1 x hx d (htD hdt) hxd')
  have h2 := abs_lt.1 ((hN n hn).1 x hx d (htD hdt) hxd')
  have h3 := abs_lt.1 ((hN m hm).2 d hdt)
  have h4 := abs_lt.1 ((hN n hn).2 d hdt)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

/-- A uniformly Cauchy sequence converges uniformly to its pointwise limit `limUnder`. -/
theorem tendstoUniformlyOn_limUnder {α : Type*} {f : ℕ → α → ℝ} {K : Set α}
    (h : UniformCauchySeqOn f atTop K) :
    TendstoUniformlyOn f (fun x => limUnder atTop fun j => f j x) atTop K :=
  h.tendstoUniformlyOn_of_tendsto fun _ hx => (h.cauchySeq hx).tendsto_limUnder

/-! ### Selection for almost monotone sequences -/

/-- If `f j` is bounded on `[a, b]`, satisfies the one-sided bound
`f j t₂ - f j t₁ ≤ C (t₂ - t₁) + ε j` with `ε j → 0`, and converges on a dense set `D`,
then it converges at every point of `(a, b)` outside a countable set. -/
theorem countable_not_tendsto_of_almostMono (f : ℕ → ℝ → ℝ) {a b C M : ℝ} (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hM : ∀ᶠ j in atTop, ∀ t ∈ Set.Icc a b, |f j t| ≤ M)
    (hmono : ∀ᶠ j in atTop, ∀ t₁ t₂ : ℝ, a ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ b →
      f j t₂ - f j t₁ ≤ C * (t₂ - t₁) + ε j)
    {D : Set ℝ} (hD : ∀ x y : ℝ, a ≤ x → x < y → y ≤ b → ∃ q ∈ D, x < q ∧ q < y)
    (hDconv : ∀ q ∈ D, q ∈ Set.Icc a b → ∃ L, Tendsto (fun j => f j q) atTop (𝓝 L)) :
    Set.Countable {t | t ∈ Set.Ioo a b ∧ ¬ ∃ L, Tendsto (fun j => f j t) atTop (𝓝 L)} := by
  classical
  by_cases hab : a < b
  swap
  · refine Set.Countable.mono ?_ Set.countable_empty
    rintro t ⟨ht, -⟩
    exact absurd (ht.1.trans ht.2) hab
  let g : ℝ → ℝ := fun q => limUnder atTop fun j => f j q
  have hg : ∀ q ∈ D, q ∈ Set.Icc a b → Tendsto (fun j => f j q) atTop (𝓝 (g q)) :=
    fun q hq hqI => tendsto_nhds_limUnder (hDconv q hq hqI)
  have hgM : ∀ q ∈ D, q ∈ Set.Icc a b → |g q| ≤ M := fun q hq hqI =>
    le_of_tendsto (hg q hq hqI).abs (hM.mono fun j hj => hj q hqI)
  let m : ℝ → ℝ := fun q => g q - C * q
  let B₀ : ℝ := M + |C| * (|a| + |b|)
  have hmB : ∀ q ∈ D, q ∈ Set.Icc a b → m q ≤ B₀ := by
    intro q hq hqI
    have h1 := hgM q hq hqI
    have h2 : |q| ≤ |a| + |b| := by
      rw [abs_le]; constructor <;>
        cases abs_cases a <;> cases abs_cases b <;> linarith [hqI.1, hqI.2]
    have h3 : -(C * q) ≤ |C| * (|a| + |b|) := by
      have := abs_mul C q
      have h4 : |C * q| ≤ |C| * (|a| + |b|) := by
        rw [this]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
      linarith [neg_abs_le (C * q), abs_le.1 h4]
    have := le_abs_self (g q)
    simp only [m, B₀]
    linarith
  let V : ℝ → ℝ := fun t => sSup (m '' (D ∩ Set.Ioo t b))
  have hbdd : ∀ t, a ≤ t → BddAbove (m '' (D ∩ Set.Ioo t b)) := by
    intro t ht
    refine ⟨B₀, ?_⟩
    rintro _ ⟨q, ⟨hqD, hq⟩, rfl⟩
    exact hmB q hqD ⟨by linarith [hq.1], hq.2.le⟩
  have hne : ∀ t, a ≤ t → t < b → (m '' (D ∩ Set.Ioo t b)).Nonempty := by
    intro t ht htb
    obtain ⟨q, hqD, h1, h2⟩ := hD t b ht htb le_rfl
    exact ⟨m q, q, ⟨hqD, h1, h2⟩, rfl⟩
  have hle_V : ∀ t q, a ≤ t → q ∈ D → t < q → q < b → m q ≤ V t :=
    fun t q ht hqD h1 h2 => le_csSup (hbdd t ht) ⟨q, ⟨hqD, h1, h2⟩, rfl⟩
  have hV_anti : ∀ t₁ t₂, a ≤ t₁ → t₁ ≤ t₂ → t₂ < b → V t₂ ≤ V t₁ := by
    intro t₁ t₂ h1 h12 h2
    refine csSup_le_csSup (hbdd t₁ h1) (hne t₂ (h1.trans h12) h2) ?_
    exact Set.image_mono fun q hq => ⟨hq.1, lt_of_le_of_lt h12 hq.2.1, hq.2.2⟩
  have hconv_pt : ∀ t, a < t → t < b → (∀ e > 0, ∃ s, a < s ∧ s < t ∧ V s < V t + e) →
      Tendsto (fun j => f j t) atTop (𝓝 (V t + C * t)) := by
    intro t hat htb hleft
    rw [tendsto_order]
    constructor
    · intro y hy
      have he0 : 0 < V t + C * t - y := by linarith
      obtain ⟨_, ⟨q', ⟨hq'D, hq'1, hq'2⟩, rfl⟩, hq'⟩ := exists_lt_of_lt_csSup
        (hne t hat.le htb) (show V t - (V t + C * t - y) / 3 < V t by linarith)
      have hq'I : q' ∈ Set.Icc a b := ⟨by linarith, hq'2.le⟩
      filter_upwards [(tendsto_order.1 (hg q' hq'D hq'I)).1 (g q' - (V t + C * t - y) / 3)
          (by linarith), (tendsto_order.1 hε).2 ((V t + C * t - y) / 3) (by linarith), hmono]
        with j hj1 hj2 hj3
      have := hj3 t q' hat.le hq'1.le hq'2.le
      simp only [m] at hq'
      linarith
    · intro y hy
      obtain ⟨s, hs1, hs2, hs3⟩ := hleft ((y - (V t + C * t)) / 3) (by linarith)
      obtain ⟨q, hqD, hq1, hq2⟩ := hD s t hs1.le hs2 htb.le
      have hqI : q ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
      have hmq : m q ≤ V s := hle_V s q hs1.le hqD hq1 (hq2.trans htb)
      filter_upwards [(tendsto_order.1 (hg q hqD hqI)).2 (g q + (y - (V t + C * t)) / 3)
          (by linarith), (tendsto_order.1 hε).2 ((y - (V t + C * t)) / 3) (by linarith), hmono]
        with j hj1 hj2 hj3
      have := hj3 q t hqI.1 hq2.le htb.le
      simp only [m] at hmq
      linarith
  let bk : ℕ → ℝ := fun k => b - (b - a) / ((k : ℝ) + 2)
  have hbk : ∀ k, a < bk k ∧ bk k < b := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have h1 : (b - a) / ((k : ℝ) + 2) < b - a := by
      rw [div_lt_iff₀ hk]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h2 : 0 < (b - a) / ((k : ℝ) + 2) := div_pos (by linarith) hk
    constructor <;> simp only [bk] <;> linarith
  let W : ℕ → ℝ → ℝ := fun k t => V (max a (min t (bk k)))
  have hW_anti : ∀ k, Antitone (W k) := by
    intro k t₁ t₂ h12
    refine hV_anti _ _ (le_max_left _ _) (max_le_max le_rfl (min_le_min_right _ h12)) ?_
    exact lt_of_le_of_lt (max_le (hbk k).1.le (min_le_right _ _)) (hbk k).2
  have hsub : {t | t ∈ Set.Ioo a b ∧ ¬ ∃ L, Tendsto (fun j => f j t) atTop (𝓝 L)} ⊆
      ⋃ k, {t | ¬ ContinuousAt (W k) t} := by
    rintro t ⟨⟨hat, htb⟩, hnot⟩
    obtain ⟨k, hk⟩ : ∃ k : ℕ, t < bk k := by
      obtain ⟨k, hk⟩ := exists_nat_gt ((b - a) / (b - t))
      refine ⟨k, ?_⟩
      have hbt : 0 < b - t := by linarith
      have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      have h1 : b - a < (k : ℝ) * (b - t) := (div_lt_iff₀ hbt).1 hk
      have h2 : (b - a) / ((k : ℝ) + 2) < b - t := by
        rw [div_lt_iff₀ hk2]; nlinarith
      simp only [bk]; linarith
    refine Set.mem_iUnion.2 ⟨k, fun hcont => hnot ⟨_, hconv_pt t hat htb ?_⟩⟩
    intro e he
    obtain ⟨δ, hδ, hδW⟩ := Metric.continuousAt_iff.1 hcont e he
    have hWeq : ∀ s, a ≤ s → s ≤ bk k → W k s = V s := by
      intro s hs1 hs2
      simp only [W, min_eq_left hs2, max_eq_right hs1]
    refine ⟨max ((a + t) / 2) (t - δ / 2), ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    · exact max_lt (by linarith) (by linarith)
    · set s := max ((a + t) / 2) (t - δ / 2) with hs
      have hs1 : a ≤ s := le_trans (by linarith) (le_max_left _ _)
      have hs2 : s ≤ bk k := (max_le (by linarith) (by linarith)).trans hk.le
      have hst : dist s t < δ := by
        rw [Real.dist_eq, abs_lt]
        constructor
        · linarith [le_max_right ((a + t) / 2) (t - δ / 2)]
        · linarith [max_lt (show (a + t) / 2 < t by linarith) (show t - δ / 2 < t by linarith)]
      have := hδW hst
      rw [hWeq s hs1 hs2, hWeq t hat.le hk.le, Real.dist_eq] at this
      linarith [(abs_lt.1 this).2]
  exact (Set.countable_iUnion fun k => (hW_anti k).countable_not_continuousAt).mono hsub

/-! ### Taylor bound for the exponential and coefficient extraction -/

/-- Third-order Taylor bound for `e^{-z}` with a `|z|^{7/2}` remainder, for `|z| ≤ 1` or
`Re z ≥ 0`. -/
theorem norm_cexp_neg_sub_taylor_le (z : ℂ) (hz : ‖z‖ ≤ 1 ∨ 0 ≤ z.re) :
    ‖Complex.exp (-z) - (1 - z + z ^ 2 / 2 - z ^ 3 / 6)‖ ≤
      4 * ‖z‖ ^ 3 * Real.sqrt ‖z‖ := by
  have hn0 : 0 ≤ ‖z‖ := norm_nonneg z
  rcases le_or_gt ‖z‖ 1 with h1 | h1
  · have hb := Complex.exp_bound (x := -z) (by simpa using h1) (n := 4) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 4, (-z) ^ m / (m.factorial : ℂ) =
        1 - z + z ^ 2 / 2 - z ^ 3 / 6 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      ring
    rw [hsum, norm_neg] at hb
    have hsq : ‖z‖ ≤ Real.sqrt ‖z‖ := by
      rw [Real.le_sqrt hn0 hn0]
      nlinarith
    have hcube : 0 ≤ ‖z‖ ^ 3 := pow_nonneg hn0 3
    calc ‖Complex.exp (-z) - (1 - z + z ^ 2 / 2 - z ^ 3 / 6)‖
        ≤ ‖z‖ ^ 4 * (((Nat.succ 4 : ℕ) : ℝ) * ((Nat.factorial 4 : ℕ) * (4 : ℕ) : ℝ)⁻¹) := hb
      _ = ‖z‖ ^ 3 * ‖z‖ * (5 / 96) := by norm_num [Nat.factorial]; ring
      _ ≤ ‖z‖ ^ 3 * Real.sqrt ‖z‖ * 4 := by
          have := mul_le_mul_of_nonneg_left hsq hcube
          nlinarith [Real.sqrt_nonneg ‖z‖]
      _ = 4 * ‖z‖ ^ 3 * Real.sqrt ‖z‖ := by ring
  · have hre : 0 ≤ z.re := hz.resolve_left (not_le.2 h1)
    have hexp : ‖Complex.exp (-z)‖ ≤ 1 := by
      rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff]
      linarith
    have hs1 : 1 ≤ Real.sqrt ‖z‖ := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt h1.le
    have hz2 : ‖z‖ ≤ ‖z‖ ^ 2 := by nlinarith
    have hz3 : ‖z‖ ^ 2 ≤ ‖z‖ ^ 3 := by nlinarith
    have hz1 : 1 ≤ ‖z‖ ^ 3 := by nlinarith
    calc ‖Complex.exp (-z) - (1 - z + z ^ 2 / 2 - z ^ 3 / 6)‖
        ≤ ‖Complex.exp (-z)‖ + 1 + ‖z‖ + ‖z‖ ^ 2 / 2 + ‖z‖ ^ 3 / 6 := by
          have e1 : ‖Complex.exp (-z) - (1 - z + z ^ 2 / 2 - z ^ 3 / 6)‖ ≤
              ‖Complex.exp (-z)‖ + ‖(1 : ℂ) - z + z ^ 2 / 2 - z ^ 3 / 6‖ := norm_sub_le _ _
          have e2 : ‖(1 : ℂ) - z + z ^ 2 / 2 - z ^ 3 / 6‖ ≤
              ‖(1 : ℂ)‖ + ‖z‖ + ‖z ^ 2 / 2‖ + ‖z ^ 3 / 6‖ := by
            have f1 := norm_sub_le ((1 : ℂ) - z + z ^ 2 / 2) (z ^ 3 / 6)
            have f2 := norm_add_le ((1 : ℂ) - z) (z ^ 2 / 2)
            have f3 := norm_sub_le (1 : ℂ) z
            linarith
          have e3 : ‖z ^ 2 / 2‖ = ‖z‖ ^ 2 / 2 := by simp [norm_pow]
          have e4 : ‖z ^ 3 / 6‖ = ‖z‖ ^ 3 / 6 := by
            rw [norm_div, norm_pow]; norm_num
          rw [e3, e4, norm_one] at e2
          linarith
      _ ≤ 4 * ‖z‖ ^ 3 * 1 := by nlinarith
      _ ≤ 4 * ‖z‖ ^ 3 * Real.sqrt ‖z‖ := by
          apply mul_le_mul_of_nonneg_left hs1; positivity

/-- The real version: for `y ≥ -1`,
`|e^{-y} - (1 - y + y²/2 - y³/6)| ≤ 4 |y|³ √|y|`. -/
theorem abs_exp_neg_sub_taylor_le {y : ℝ} (hy : -1 ≤ y) :
    |Real.exp (-y) - (1 - y + y ^ 2 / 2 - y ^ 3 / 6)| ≤ 4 * |y| ^ 3 * Real.sqrt |y| := by
  have hcond : ‖(y : ℂ)‖ ≤ 1 ∨ 0 ≤ (y : ℂ).re := by
    rcases le_or_gt 0 y with h | h
    · right; simpa using h
    · left
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg h]
      linarith
  have h := norm_cexp_neg_sub_taylor_le (y : ℂ) hcond
  have heq : Complex.exp (-(y : ℂ)) - (1 - (y : ℂ) + (y : ℂ) ^ 2 / 2 - (y : ℂ) ^ 3 / 6) =
      ((Real.exp (-y) - (1 - y + y ^ 2 / 2 - y ^ 3 / 6) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- If `|a| ≤ K √s` for every `s ∈ (0, 1]`, then `a = 0`. -/
theorem eq_zero_of_abs_le_mul_sqrt {a K : ℝ}
    (h : ∀ s : ℝ, 0 < s → s ≤ 1 → |a| ≤ K * Real.sqrt s) : a = 0 := by
  by_contra ha
  have ha' : 0 < |a| := abs_pos.2 ha
  have hK : 0 < K := by
    have := h 1 one_pos le_rfl
    rw [Real.sqrt_one, mul_one] at this
    linarith
  set s := min 1 ((|a| / (2 * K)) ^ 2) with hs
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsq : Real.sqrt s ≤ |a| / (2 * K) := by
    rw [Real.sqrt_le_left (by positivity)]
    exact min_le_right _ _
  have := h s hs0 hs1
  have h2 : K * Real.sqrt s ≤ K * (|a| / (2 * K)) := mul_le_mul_of_nonneg_left hsq hK.le
  have h3 : K * (|a| / (2 * K)) = |a| / 2 := by field_simp
  linarith

/-- Coefficient extraction: if `|a₁ s + a₂ s² + a₃ s³| ≤ C s³ √s` for every `s ∈ (0, 1]`,
then `a₁ = a₂ = a₃ = 0`. -/
theorem coeff_eq_zero_of_taylor {a₁ a₂ a₃ C : ℝ}
    (h : ∀ s : ℝ, 0 < s → s ≤ 1 →
      |a₁ * s + a₂ * s ^ 2 + a₃ * s ^ 3| ≤ C * s ^ 3 * Real.sqrt s) :
    a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 := by
  have hC : 0 ≤ C := by
    have := h 1 one_pos le_rfl
    rw [Real.sqrt_one] at this
    linarith [abs_nonneg (a₁ * 1 + a₂ * 1 ^ 2 + a₃ * 1 ^ 3)]
  have hsq : ∀ s : ℝ, 0 < s → s ≤ 1 → s ≤ Real.sqrt s ∧ Real.sqrt s ≤ 1 := by
    intro s hs0 hs1
    refine ⟨?_, ?_⟩
    · rw [Real.le_sqrt hs0.le hs0.le]; nlinarith
    · rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hs1
  have h1 : a₁ = 0 := by
    apply eq_zero_of_abs_le_mul_sqrt (K := C + |a₂| + |a₃|)
    intro s hs0 hs1
    obtain ⟨hs2, hs3⟩ := hsq s hs0 hs1
    have hb := h s hs0 hs1
    have e1 : |a₁ * s| ≤ |a₁ * s + a₂ * s ^ 2 + a₃ * s ^ 3| + |a₂| * s ^ 2 + |a₃| * s ^ 3 := by
      have h4 : |a₂ * s ^ 2 + a₃ * s ^ 3| ≤ |a₂| * s ^ 2 + |a₃| * s ^ 3 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 3)]
      calc |a₁ * s| = |(a₁ * s + a₂ * s ^ 2 + a₃ * s ^ 3) - (a₂ * s ^ 2 + a₃ * s ^ 3)| := by
            congr 1; ring
        _ ≤ |a₁ * s + a₂ * s ^ 2 + a₃ * s ^ 3| + |a₂ * s ^ 2 + a₃ * s ^ 3| := abs_sub _ _
        _ ≤ _ := by linarith [h4]
    rw [abs_mul, abs_of_pos hs0] at e1
    have hs32 : s ^ 3 ≤ s ^ 2 := by nlinarith
    have hs21 : s ^ 2 ≤ s * Real.sqrt s := by nlinarith
    have hss : s ^ 3 * Real.sqrt s ≤ s ^ 2 := by nlinarith [Real.sqrt_nonneg s]
    have : |a₁| * s ≤ (C + |a₂| + |a₃|) * (s * Real.sqrt s) := by
      nlinarith [abs_nonneg a₂, abs_nonneg a₃]
    have := (mul_le_mul_iff_of_pos_right hs0).1
      (show |a₁| * s ≤ ((C + |a₂| + |a₃|) * Real.sqrt s) * s by linarith)
    exact this
  subst h1
  have h2 : a₂ = 0 := by
    apply eq_zero_of_abs_le_mul_sqrt (K := C + |a₃|)
    intro s hs0 hs1
    obtain ⟨hs2, hs3⟩ := hsq s hs0 hs1
    have hb := h s hs0 hs1
    simp only [zero_mul, zero_add] at hb
    have e1 : |a₂ * s ^ 2| ≤ |a₂ * s ^ 2 + a₃ * s ^ 3| + |a₃| * s ^ 3 := by
      calc |a₂ * s ^ 2| = |(a₂ * s ^ 2 + a₃ * s ^ 3) - a₃ * s ^ 3| := by congr 1; ring
        _ ≤ |a₂ * s ^ 2 + a₃ * s ^ 3| + |a₃ * s ^ 3| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 3)]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2)] at e1
    have hs0' : 0 < s ^ 2 := by positivity
    have : |a₂| * s ^ 2 ≤ ((C + |a₃|) * Real.sqrt s) * s ^ 2 := by
      have hs32 : s ^ 3 ≤ s ^ 2 := by nlinarith
      have hss : s ^ 3 ≤ s ^ 2 * Real.sqrt s := by nlinarith
      have hss' : s ^ 3 * Real.sqrt s ≤ s ^ 2 * Real.sqrt s :=
        mul_le_mul_of_nonneg_right hs32 (Real.sqrt_nonneg s)
      have k1 : C * (s ^ 3 * Real.sqrt s) ≤ C * (s ^ 2 * Real.sqrt s) :=
        mul_le_mul_of_nonneg_left hss' hC
      have k2 : |a₃| * s ^ 3 ≤ |a₃| * (s ^ 2 * Real.sqrt s) :=
        mul_le_mul_of_nonneg_left hss (abs_nonneg _)
      have k3 : C * s ^ 3 * Real.sqrt s = C * (s ^ 3 * Real.sqrt s) := by ring
      have k4 : (C + |a₃|) * Real.sqrt s * s ^ 2 =
          C * (s ^ 2 * Real.sqrt s) + |a₃| * (s ^ 2 * Real.sqrt s) := by ring
      linarith
    exact (mul_le_mul_iff_of_pos_right hs0').1 this
  subst h2
  refine ⟨rfl, rfl, ?_⟩
  apply eq_zero_of_abs_le_mul_sqrt (K := C)
  intro s hs0 hs1
  have hb := h s hs0 hs1
  simp only [zero_mul, zero_add] at hb
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 3)] at hb
  have hs0' : 0 < s ^ 3 := by positivity
  exact (mul_le_mul_iff_of_pos_right hs0').1 (by linarith)

/-! ### Step functions -/

theorem floor_mul_eq_of_mem {N τ : ℝ} (hN : 0 < N) {k : ℕ} (h1 : (k : ℝ) / N ≤ τ)
    (h2 : τ < ((k : ℝ) + 1) / N) : ⌊N * τ⌋₊ = k := by
  rw [Nat.floor_eq_iff (by have := (div_le_iff₀ hN).1 h1; nlinarith [Nat.cast_nonneg (α := ℝ) k])]
  constructor
  · have := (div_le_iff₀ hN).1 h1; linarith
  · have := (lt_div_iff₀ hN).1 h2; linarith

theorem measurable_floor_comp (F : ℕ → ℝ) (N : ℝ) :
    Measurable fun τ : ℝ => F ⌊N * τ⌋₊ :=
  measurable_from_nat.comp (Nat.measurable_floor.comp (measurable_const_mul N))

/-- The step function `τ ↦ F ⌊N τ⌋` is interval integrable on bounded intervals. -/
theorem intervalIntegrable_floor_comp (F : ℕ → ℝ) {N : ℝ} (hN : 0 < N) (a b : ℝ) :
    IntervalIntegrable (fun τ => F ⌊N * τ⌋₊) volume a b := by
  let m : ℕ := ⌊N * max |a| |b|⌋₊
  let K : ℝ := ∑ n ∈ Finset.range (m + 1), |F n|
  refine (intervalIntegrable_const (c := K)).mono_fun
    (measurable_floor_comp F N).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun τ hτ => ?_)
  show ‖F ⌊N * τ⌋₊‖ ≤ |K|
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ K from Finset.sum_nonneg fun n _ => abs_nonneg _)]
  have hτ' : τ ≤ max |a| |b| := by
    have h : τ ≤ max a b := (Set.uIoc_subset_uIcc hτ).2
    have : max a b ≤ max |a| |b| := max_le_max (le_abs_self a) (le_abs_self b)
    linarith
  have hle : ⌊N * τ⌋₊ ≤ m := Nat.floor_le_floor (mul_le_mul_of_nonneg_left hτ' hN.le)
  exact Finset.single_le_sum (f := fun n => |F n|) (fun n _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hle))

/-- The integral of the step function `τ ↦ F ⌊N τ⌋` between grid points. -/
theorem integral_floor_comp (F : ℕ → ℝ) {N : ℝ} (hN : 0 < N) (m k : ℕ) (hmk : m ≤ k) :
    ∫ τ in (m : ℝ) / N..(k : ℝ) / N, F ⌊N * τ⌋₊ = (∑ n ∈ Finset.Ico m k, F n) / N := by
  induction k, hmk using Nat.le_induction with
  | base => simp
  | succ k hmk ih =>
    have hpiece : ∫ τ in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N, F ⌊N * τ⌋₊ = F k / N := by
      have hle : (k : ℝ) / N ≤ ((k + 1 : ℕ) : ℝ) / N := by
        apply div_le_div_of_nonneg_right _ hN.le; push_cast; linarith
      rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]
      have hcongr : ∫ τ in Set.Ioo ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N), F ⌊N * τ⌋₊ =
          ∫ τ in Set.Ioo ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N), F k :=
        setIntegral_congr_fun measurableSet_Ioo fun τ hτ => by
          have h2 := hτ.2
          push_cast at h2
          rw [floor_mul_eq_of_mem hN hτ.1.le h2]
      rw [hcongr, setIntegral_const, Real.volume_real_Ioo_of_le hle, smul_eq_mul]
      push_cast
      field_simp
      ring
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_floor_comp F hN _ _) (intervalIntegrable_floor_comp F hN _ _),
      ih, hpiece, Finset.sum_Ico_succ_top hmk, add_div]

/-! ### Bounded continuous test functions -/

theorem dist_le_one_of_mem_Icc {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : dist x y ≤ 1 := by
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem exp_neg_mul_max_mem_Icc (k : ℕ) (x : ℝ) :
    Real.exp (-((k : ℝ) * max x 0)) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2
    (neg_nonpos.2 (mul_nonneg (Nat.cast_nonneg k) (le_max_right x 0)))⟩

/-- `x ↦ e^{-k max(x, 0)}` as a bounded continuous function. -/
noncomputable def laplaceBCF (k : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => Real.exp (-((k : ℝ) * max x 0)),
      Real.continuous_exp.comp ((continuous_const.mul (continuous_id.max continuous_const)).neg)⟩
    1 fun x y => dist_le_one_of_mem_Icc (exp_neg_mul_max_mem_Icc k x) (exp_neg_mul_max_mem_Icc k y)

theorem laplaceBCF_apply (k : ℕ) (x : ℝ) :
    laplaceBCF k x = Real.exp (-((k : ℝ) * max x 0)) := rfl

theorem ramp_mem_Icc (q c x : ℝ) : min 1 (max 0 (1 - c * (x - q))) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

/-- The ramp `x ↦ min 1 (max 0 (1 - (k + 1)(x - q)))`: `1` on `(-∞, q]`, `0` on
`[q + 1/(k+1), ∞)`. -/
noncomputable def rampBCF (q : ℝ) (k : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min 1 (max 0 (1 - ((k : ℝ) + 1) * (x - q))),
      continuous_const.min (continuous_const.max
        (continuous_const.sub (continuous_const.mul (continuous_id.sub continuous_const))))⟩
    1 fun x y => dist_le_one_of_mem_Icc (ramp_mem_Icc q _ x) (ramp_mem_Icc q _ y)

theorem rampBCF_apply (q : ℝ) (k : ℕ) (x : ℝ) :
    rampBCF q k x = min 1 (max 0 (1 - ((k : ℝ) + 1) * (x - q))) := rfl

theorem rampBCF_eq_one {q x : ℝ} (hx : x ≤ q) (k : ℕ) : rampBCF q k x = 1 := by
  rw [rampBCF_apply]
  have : 0 ≤ ((k : ℝ) + 1) * (q - x) := mul_nonneg (by positivity) (by linarith)
  rw [min_eq_left]
  exact le_max_of_le_right (by nlinarith)

theorem tendsto_rampBCF (q x : ℝ) :
    Tendsto (fun k => rampBCF q k x) atTop
      (𝓝 ((Set.Iic q).indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : x ≤ q
  · rw [Set.indicator_of_mem (show x ∈ Set.Iic q from hx)]
    exact tendsto_const_nhds.congr fun k => (rampBCF_eq_one hx k).symm
  · rw [Set.indicator_of_notMem (show x ∉ Set.Iic q from hx)]
    push_neg at hx
    obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 / (x - q))
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨k₀, fun k hk => ?_⟩)
    show 0 = rampBCF q k x
    rw [rampBCF_apply]
    have h1 : 1 ≤ ((k : ℝ) + 1) * (x - q) := by
      have hk' : (k₀ : ℝ) ≤ k := Nat.cast_le.2 hk
      have : (1 : ℝ) / (x - q) < k + 1 := by linarith
      rw [div_lt_iff₀ (by linarith)] at this
      linarith
    rw [max_eq_left (by linarith), min_eq_right zero_le_one]

/-! ### Weak limits of measures with converging Laplace transforms -/

theorem coe_finiteMeasure_apply (μ : FiniteMeasure ℝ) (s : Set ℝ) :
    ((μ s : NNReal) : ℝ) = (μ : Measure ℝ).real s := by
  rw [measureReal_def]
  rfl

/-- Existence of a weak limit: finite measures on `[0, ∞)` with uniformly bounded mass, a
uniform tail bound `ν (n + 1, ∞) ≤ C/(n + 1)`, and converging Laplace transforms
`∫ e^{-k x} dν` (`k ∈ ℕ`), converge weakly to a finite measure on `[0, ∞)`. -/
theorem exists_weakLimit_of_laplace (ν : ℕ → Measure ℝ) [hfin : ∀ j, IsFiniteMeasure (ν j)]
    (hsupp : ∀ j, ν j (Set.Iio 0) = 0) {C : ℝ}
    (hmass : ∀ j, (ν j).real Set.univ ≤ C)
    (htail : ∀ j (n : ℕ), (ν j).real (Set.Ioi ((n : ℝ) + 1)) ≤ C / ((n : ℝ) + 1))
    (hlap : ∀ k : ℕ, ∃ L, Tendsto (fun j => ∫ x, laplaceBCF k x ∂(ν j)) atTop (𝓝 L)) :
    ∃ ν' : FiniteMeasure ℝ, (ν' : Measure ℝ) (Set.Iio 0) = 0 ∧
      ∀ f : ℝ →ᵇ ℝ, Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop
        (𝓝 (∫ x, f x ∂(ν' : Measure ℝ))) := by
  classical
  have hC0 : 0 ≤ C := le_trans measureReal_nonneg (hmass 0)
  let μs : ℕ → FiniteMeasure ℝ := fun j => ⟨ν j, hfin j⟩
  let K : ℕ → Set ℝ := fun n => Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)
  let u : ℕ → NNReal := fun n => ⟨C / ((n : ℝ) + 1), by positivity⟩
  have hu : Tendsto u atTop (𝓝 0) := by
    rw [← NNReal.tendsto_coe]
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    show C * (1 / ((n : ℝ) + 1)) = C / ((n : ℝ) + 1)
    ring
  have hKmono : Monotone K := by
    intro m n hmn
    have : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    exact Set.Icc_subset_Icc (by linarith) (by linarith)
  have hKc : IsCompact {μ : FiniteMeasure ℝ | μ.mass ≤ C.toNNReal ∧ ∀ n, μ (K n)ᶜ ≤ u n} :=
    isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le C.toNNReal hu
      (fun n => isCompact_Icc) (Or.inr hKmono)
  have hcompl : ∀ (μ : Measure ℝ), μ (Set.Iio 0) = 0 → ∀ n : ℕ,
      μ (K n)ᶜ ≤ μ (Set.Ioi ((n : ℝ) + 1)) := by
    intro μ h0 n
    have hsub : (K n)ᶜ ⊆ Set.Iio 0 ∪ Set.Ioi ((n : ℝ) + 1) := by
      intro x hx
      simp only [K, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · left
        show x < 0
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      · right; exact hx
    calc μ (K n)ᶜ ≤ μ (Set.Iio 0 ∪ Set.Ioi ((n : ℝ) + 1)) := measure_mono hsub
      _ ≤ μ (Set.Iio 0) + μ (Set.Ioi ((n : ℝ) + 1)) := measure_union_le _ _
      _ = μ (Set.Ioi ((n : ℝ) + 1)) := by rw [h0, zero_add]
  have hmem : ∀ j, μs j ∈ {μ : FiniteMeasure ℝ | μ.mass ≤ C.toNNReal ∧ ∀ n, μ (K n)ᶜ ≤ u n} := by
    intro j
    refine ⟨?_, fun n => ?_⟩
    · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hC0, FiniteMeasure.mass,
        coe_finiteMeasure_apply]
      exact hmass j
    · rw [← NNReal.coe_le_coe, coe_finiteMeasure_apply]
      show (ν j).real (K n)ᶜ ≤ C / ((n : ℝ) + 1)
      refine le_trans ?_ (htail j n)
      rw [measureReal_def, measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (hcompl _ (hsupp j) n)
  obtain ⟨νl, hνlK, hclust⟩ := hKc (f := Filter.map μs atTop)
    (tendsto_principal.2 (Eventually.of_forall hmem))
  have hcl : ∀ (f : ℝ →ᵇ ℝ) (L : ℝ), Tendsto (fun j => ∫ x, f x ∂(ν j)) atTop (𝓝 L) →
      ∫ x, f x ∂(νl : Measure ℝ) = L := by
    intro f L hL
    have h1 : MapClusterPt (∫ x, f x ∂(νl : Measure ℝ)) atTop (fun j => ∫ x, f x ∂(ν j)) :=
      MapClusterPt.tendsto_comp (u := μs)
        ((FiniteMeasure.continuous_integral_boundedContinuousFunction f).tendsto νl) hclust
    exact eq_of_nhds_neBot (ClusterPt.mono h1 hL).neBot
  -- the limit is supported on `[0, ∞)`
  have hsuppl : (νl : Measure ℝ) (Set.Iio 0) = 0 := by
    have hI : Set.Iio (0 : ℝ) ⊆ ⋃ m : ℕ, Set.Iic (-(1 / ((m : ℝ) + 1))) := by
      intro x hx
      have hx' : 0 < -x := neg_pos.2 hx
      obtain ⟨m, hm⟩ := exists_nat_gt (1 / (-x))
      refine Set.mem_iUnion.2 ⟨m, ?_⟩
      show x ≤ -(1 / ((m : ℝ) + 1))
      have h1 : 1 < (m : ℝ) * (-x) := (div_lt_iff₀ hx').1 hm
      have : 1 / ((m : ℝ) + 1) < -x := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    refine measure_mono_null hI (measure_iUnion_null fun m => ?_)
    set q : ℝ := -(1 / ((m : ℝ) + 1)) with hq
    have hψ0 : ∀ j, ∫ x, rampBCF q m x ∂(ν j) = 0 := by
      intro j
      refine integral_eq_zero_of_ae ?_
      have hae : ∀ᵐ x ∂(ν j), 0 ≤ x := by
        rw [ae_iff]
        simp only [not_le]
        exact hsupp j
      filter_upwards [hae] with x hx
      rw [rampBCF_apply, Pi.zero_apply]
      have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have : 1 - ((m : ℝ) + 1) * (x - q) = -(((m : ℝ) + 1) * x) := by
        rw [hq]; field_simp; ring
      rw [this, max_eq_left (by nlinarith), min_eq_right zero_le_one]
    have hint := hcl (rampBCF q m) 0 (by simp only [hψ0]; exact tendsto_const_nhds)
    have hnn : 0 ≤ ⇑(rampBCF q m) := fun x => (ramp_mem_Icc q _ x).1
    have hae := (integral_eq_zero_iff_of_nonneg hnn ((rampBCF q m).integrable _)).1 hint
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hae)
    show ¬ (rampBCF q m x = (0 : ℝ → ℝ) x)
    rw [rampBCF_eq_one hx m, Pi.zero_apply]
    exact one_ne_zero
  have hνlmass : (νl : Measure ℝ).real Set.univ ≤ C := by
    have h1 := hνlK.1
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hC0, FiniteMeasure.mass,
      coe_finiteMeasure_apply] at h1
    exact h1
  have hνltail : ∀ n : ℕ, (νl : Measure ℝ).real (Set.Ioi ((n : ℝ) + 1)) ≤ C / ((n : ℝ) + 1) := by
    intro n
    have h1 := hνlK.2 n
    rw [← NNReal.coe_le_coe, coe_finiteMeasure_apply] at h1
    have hsub : Set.Ioi ((n : ℝ) + 1) ⊆ (K n)ᶜ := fun x hx hxK => absurd hxK.2 (not_le.2 hx)
    exact (measureReal_mono hsub).trans h1
  have hlapl : ∀ k, Tendsto (fun j => ∫ x, laplaceBCF k x ∂(ν j)) atTop
      (𝓝 (∫ x, laplaceBCF k x ∂(νl : Measure ℝ))) := by
    intro k
    obtain ⟨L, hL⟩ := hlap k
    rwa [hcl _ L hL]
  -- approximation by exponential polynomials
  have happrox : ∀ (f : ℝ →ᵇ ℝ) (ε : ℝ), 0 < ε → ∃ P : ℝ →ᵇ ℝ,
      Tendsto (fun j => ∫ x, P x ∂(ν j)) atTop (𝓝 (∫ x, P x ∂(νl : Measure ℝ))) ∧
      ∀ μ : Measure ℝ, IsFiniteMeasure μ → μ (Set.Iio 0) = 0 → μ.real Set.univ ≤ C →
        (∀ n : ℕ, μ.real (Set.Ioi ((n : ℝ) + 1)) ≤ C / ((n : ℝ) + 1)) →
        |∫ x, f x ∂μ - ∫ x, P x ∂μ| ≤ ε := by
    intro f ε hε
    set A := ‖f‖ with hA
    have hA0 : 0 ≤ A := norm_nonneg f
    obtain ⟨n, hn⟩ := exists_nat_gt ((2 * A + 1) * C / (ε / 2))
    have hn1 : (2 * A + 1) * C / ((n : ℝ) + 1) ≤ ε / 2 := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hn
      nlinarith
    set ε' := min 1 (ε / (2 * (C + 1))) with hε'
    have hε'0 : 0 < ε' := lt_min one_pos (by positivity)
    have hε'1 : ε' ≤ 1 := min_le_left _ _
    have hε'C : ε' * C ≤ ε / 2 := by
      have h1 : ε' ≤ ε / (2 * (C + 1)) := min_le_right _ _
      have h2 : ε / (2 * (C + 1)) * C ≤ ε / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      exact (mul_le_mul_of_nonneg_right h1 hC0).trans h2
    set c := Real.exp (-((n : ℝ) + 1)) with hc
    let g : ℝ → ℝ := fun y => f (-Real.log (max y c))
    have hg : ContinuousOn g (Set.Icc 0 1) := by
      apply Continuous.continuousOn
      exact f.continuous.comp ((continuous_id.max continuous_const).log
        (fun y => (lt_max_of_lt_right (Real.exp_pos _)).ne')).neg
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 g hg ε' hε'0
    let P : ℝ →ᵇ ℝ := ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • laplaceBCF i
    have hPx : ∀ x, P x = p.eval (Real.exp (-(max x 0))) := by
      intro x
      rw [Polynomial.eval_eq_sum_range]
      simp only [P, BoundedContinuousFunction.coe_sum, Finset.sum_apply,
        BoundedContinuousFunction.coe_smul, smul_eq_mul, laplaceBCF_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Real.exp_nat_mul, mul_neg]
    have hPint : ∀ μ : Measure ℝ, IsFiniteMeasure μ → ∫ x, P x ∂μ =
        ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * ∫ x, laplaceBCF i x ∂μ := by
      intro μ _
      simp only [P, BoundedContinuousFunction.coe_sum, Finset.sum_apply,
        BoundedContinuousFunction.coe_smul, smul_eq_mul]
      rw [integral_finsetSum _ (fun i _ => ((laplaceBCF i).integrable μ).const_mul _)]
      simp_rw [integral_const_mul]
    refine ⟨P, ?_, ?_⟩
    · have e1 : (fun j => ∫ x, P x ∂(ν j)) = fun j => ∑ i ∈ Finset.range (p.natDegree + 1),
          p.coeff i * ∫ x, laplaceBCF i x ∂(ν j) := funext fun j => hPint (ν j) (hfin j)
      rw [e1, hPint _ inferInstance]
      exact tendsto_finsetSum _ fun i _ => (hlapl i).const_mul _
    · intro μ hμ h0 hmassμ htailμ
      have hpos : ∀ᵐ x ∂μ, 0 ≤ x := by
        rw [ae_iff]
        simp only [not_le]
        exact h0
      have hpt : ∀ᵐ x ∂μ, ‖f x - P x‖ ≤
          ε' + (Set.Ioi ((n : ℝ) + 1)).indicator (fun _ => 2 * A + ε') x := by
        filter_upwards [hpos] with x hx
        rw [hPx x, max_eq_left hx, Real.norm_eq_abs]
        have hyI : Real.exp (-x) ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by linarith)⟩
        have hpy := hp _ hyI
        by_cases hxn : x ≤ (n : ℝ) + 1
        · rw [Set.indicator_of_notMem (show x ∉ Set.Ioi ((n : ℝ) + 1) from not_lt.2 hxn),
            add_zero]
          have hmax : max (Real.exp (-x)) c = Real.exp (-x) :=
            max_eq_left (Real.exp_le_exp.2 (by linarith))
          have hgx : g (Real.exp (-x)) = f x := by
            simp only [g, hmax, Real.log_exp, neg_neg]
          rw [hgx] at hpy
          rw [abs_sub_comm]
          exact hpy.le
        · rw [Set.indicator_of_mem (show x ∈ Set.Ioi ((n : ℝ) + 1) from lt_of_not_ge hxn)]
          have h1 : |g (Real.exp (-x))| ≤ A := by
            rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _
          have h2 : |f x| ≤ A := by
            rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x
          have t1 := abs_sub_le (f x) (g (Real.exp (-x))) (p.eval (Real.exp (-x)))
          have t2 := abs_sub (f x) (g (Real.exp (-x)))
          have t3 := abs_sub_comm (g (Real.exp (-x))) (p.eval (Real.exp (-x)))
          linarith [hpy.le]
      have hbint : Integrable (fun x =>
          ε' + (Set.Ioi ((n : ℝ) + 1)).indicator (fun _ => 2 * A + ε') x) μ :=
        (integrable_const _).add ((integrable_const _).indicator measurableSet_Ioi)
      have hmassμ0 : 0 ≤ μ.real (Set.Ioi ((n : ℝ) + 1)) := measureReal_nonneg
      calc |∫ x, f x ∂μ - ∫ x, P x ∂μ| = ‖∫ x, (f x - P x) ∂μ‖ := by
            rw [integral_sub (f.integrable μ) (P.integrable μ), Real.norm_eq_abs]
        _ ≤ ∫ x, (ε' + (Set.Ioi ((n : ℝ) + 1)).indicator (fun _ => 2 * A + ε') x) ∂μ :=
            norm_integral_le_of_norm_le hbint hpt
        _ = ε' * μ.real Set.univ + μ.real (Set.Ioi ((n : ℝ) + 1)) * (2 * A + ε') := by
            rw [integral_add (integrable_const _)
              ((integrable_const _).indicator measurableSet_Ioi), integral_const,
              integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, smul_eq_mul]
            ring
        _ ≤ ε' * C + C / ((n : ℝ) + 1) * (2 * A + 1) := by
            have k1 := mul_le_mul_of_nonneg_left hmassμ hε'0.le
            have k2 : μ.real (Set.Ioi ((n : ℝ) + 1)) * (2 * A + ε') ≤
                C / ((n : ℝ) + 1) * (2 * A + 1) :=
              mul_le_mul (htailμ n) (by linarith) (by positivity) (by positivity)
            linarith
        _ ≤ ε := by
            have : C / ((n : ℝ) + 1) * (2 * A + 1) = (2 * A + 1) * C / ((n : ℝ) + 1) := by ring
            linarith
  refine ⟨νl, hsuppl, fun f => ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨P, hPconv, hPbound⟩ := happrox f (ε / 3) (by linarith)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hPconv (ε / 3) (by linarith)
  refine ⟨N, fun j hj => ?_⟩
  have h1 := abs_le.1 (hPbound (ν j) (hfin j) (hsupp j) (hmass j) (htail j))
  have h2 := abs_le.1 (hPbound (νl : Measure ℝ) inferInstance hsuppl hνlmass hνltail)
  have h3 := hN j hj
  rw [Real.dist_eq] at h3 ⊢
  have h3' := abs_lt.1 h3
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3'.1, h3'.2]

/-! ### Measurability of a measure-valued map -/

/-- A map `t ↦ ν t` into finite measures on `ℝ` is measurable as soon as the integrals of
bounded continuous functions are measurable in `t`. -/
theorem measurable_toMeasure_of_integral {ν : ℝ → FiniteMeasure ℝ}
    (h : ∀ f : ℝ →ᵇ ℝ, Measurable fun t => ∫ x, f x ∂(ν t : Measure ℝ)) :
    Measurable fun t => (ν t : Measure ℝ) := by
  have hreal : ∀ q : ℝ, Measurable fun t => (ν t : Measure ℝ).real (Set.Iic q) := by
    intro q
    refine measurable_of_tendsto_metrizable
      (f := fun k t => ∫ x, rampBCF q k x ∂(ν t : Measure ℝ)) (fun k => h _) ?_
    rw [tendsto_pi_nhds]
    intro t
    have := tendsto_integral_of_dominated_convergence (μ := (ν t : Measure ℝ))
      (F := fun k x => rampBCF q k x) (f := fun x => (Set.Iic q).indicator (fun _ => (1 : ℝ)) x)
      (fun _ => (1 : ℝ)) (fun k => (rampBCF q k).continuous.aestronglyMeasurable)
      (integrable_const 1)
      (fun k => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, rampBCF_apply, abs_of_nonneg (ramp_mem_Icc q _ x).1]
        exact (ramp_mem_Icc q _ x).2)
      (Eventually.of_forall fun x => tendsto_rampBCF q x)
    rwa [integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_one] at this
  refine Measurable.measure_of_isPiSystem (S := Set.range (Set.Iic : ℝ → Set ℝ)) ?_
    isPiSystem_Iic ?_ ?_
  · exact (BorelSpace.measurable_eq).trans (borel_eq_generateFrom_Iic ℝ)
  · rintro _ ⟨q, rfl⟩
    have : (fun t => (ν t : Measure ℝ) (Set.Iic q)) =
        fun t => ENNReal.ofReal ((ν t : Measure ℝ).real (Set.Iic q)) := by
      funext t
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [this]
    exact ENNReal.measurable_ofReal.comp (hreal q)
  · have h1 := h (BoundedContinuousFunction.const ℝ 1)
    have : (fun t => (ν t : Measure ℝ) Set.univ) = fun t =>
        ENNReal.ofReal (∫ x, (BoundedContinuousFunction.const ℝ (1 : ℝ)) x ∂(ν t : Measure ℝ)) := by
      funext t
      rw [BoundedContinuousFunction.const_apply, integral_const, smul_eq_mul, mul_one,
        measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [this]
    exact ENNReal.measurable_ofReal.comp h1

/-! ### The analytic extension of the compensated Laplace transform -/

theorem norm_cexp_neg_mul_ofReal (z : ℂ) (x : ℝ) :
    ‖Complex.exp (-(z * x))‖ = Real.exp (-(z.re * x)) := by
  rw [Complex.norm_exp, Complex.neg_re, Complex.re_mul_ofReal]

/-- For a finite measure on `[0, ∞)`, `s ↦ ∫ (e^{-sx} - 1) dν` is holomorphic on `{Re s > 0}`
and continuous on `{Re s ≥ 0}`. -/
theorem complexCompensatedLaplace_extension {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hsupp : ν (Set.Iio 0) = 0) :
    DifferentiableOn ℂ (complexCompensatedLaplace ν) {z : ℂ | 0 < z.re} ∧
      ContinuousOn (complexCompensatedLaplace ν) {z : ℂ | 0 ≤ z.re} := by
  have hpos : ∀ᵐ x ∂ν, 0 ≤ x := by
    rw [ae_iff]
    simp only [not_le]
    exact hsupp
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun x : ℝ => Complex.exp (-(z * x)) - 1) ν :=
    fun z => (Continuous.aestronglyMeasurable (by fun_prop))
  have hbound2 : ∀ z : ℂ, 0 ≤ z.re → ∀ x : ℝ, 0 ≤ x → ‖Complex.exp (-(z * x)) - 1‖ ≤ 2 := by
    intro z hz x hx
    refine (norm_sub_le _ _).trans ?_
    rw [norm_cexp_neg_mul_ofReal, norm_one]
    have : Real.exp (-(z.re * x)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hz hx))
    linarith
  constructor
  · intro z₀ hz₀
    have hz₀' : 0 < z₀.re := hz₀
    have hδ : 0 < z₀.re / 2 := by positivity
    have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
      (F := fun (z : ℂ) (x : ℝ) => Complex.exp (-(z * x)) - 1)
      (F' := fun (z : ℂ) (x : ℝ) => -(x : ℂ) * Complex.exp (-(z * x)))
      (bound := fun _ => 2 / z₀.re) (x₀ := z₀) (s := Metric.ball z₀ (z₀.re / 2))
      (Metric.ball_mem_nhds z₀ hδ) (Eventually.of_forall hmeas)
      ((integrable_const (2 : ℝ)).mono' (hmeas z₀) (by
        filter_upwards [hpos] with x hx
        exact hbound2 z₀ hz₀'.le x hx))
      (Continuous.aestronglyMeasurable (by fun_prop))
      (by
        filter_upwards [hpos] with x hx z hz
        have hre : z₀.re / 2 < z.re := by
          have h1 : |z.re - z₀.re| < z₀.re / 2 := by
            calc |z.re - z₀.re| = |(z - z₀).re| := by rw [Complex.sub_re]
              _ ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
              _ < z₀.re / 2 := by rw [← dist_eq_norm]; exact Metric.mem_ball.1 hz
          linarith [(abs_lt.1 h1).1]
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx,
          norm_cexp_neg_mul_ofReal]
        have h1 : Real.exp (-(z.re * x)) ≤ Real.exp (-(z₀.re / 2 * x)) :=
          Real.exp_le_exp.2 (by nlinarith)
        have h2 : z₀.re / 2 * x + 1 ≤ Real.exp (z₀.re / 2 * x) := Real.add_one_le_exp _
        have h3 : Real.exp (-(z₀.re / 2 * x)) * Real.exp (z₀.re / 2 * x) = 1 := by
          rw [← Real.exp_add]; simp
        have h4 : x * Real.exp (-(z₀.re / 2 * x)) ≤ 2 / z₀.re := by
          rw [le_div_iff₀ hz₀']
          have hpos' := Real.exp_pos (-(z₀.re / 2 * x))
          nlinarith
        calc x * Real.exp (-(z.re * x)) ≤ x * Real.exp (-(z₀.re / 2 * x)) :=
              mul_le_mul_of_nonneg_left h1 hx
          _ ≤ 2 / z₀.re := h4)
      (integrable_const _)
      (Eventually.of_forall fun x z _ => by
        have h0 := (hasDerivAt_id z).mul_const (-(x : ℂ))
        have h1 : HasDerivAt (fun w : ℂ => -(w * (x : ℂ))) (-(x : ℂ)) z := by
          refine (h0.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)).congr_deriv ?_
          · simp only [id]; ring
          · ring
        have := h1.cexp.sub_const 1
        convert this using 1
        ring)
    exact hderiv.2.differentiableAt.differentiableWithinAt
  · refine continuousOn_of_dominated (bound := fun _ => (2 : ℝ)) (fun z _ => hmeas z) ?_
      (integrable_const _) (Eventually.of_forall fun x =>
        (by fun_prop : Continuous fun z : ℂ => Complex.exp (-(z * x)) - 1).continuousOn)
    intro z hz
    filter_upwards [hpos] with x hx
    exact hbound2 z hz x hx

/-! ### Real powers with half-integer exponents -/

theorem rpow_seven_halves_mul_sqrt {x : ℝ} (hx : 0 ≤ x) : x ^ ((7 : ℝ) / 2) = x ^ 3 * Real.sqrt x := by
  rw [show (7 : ℝ) / 2 = (3 : ℕ) + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num),
    Real.rpow_natCast, Real.sqrt_eq_rpow]

theorem rpow_five_halves {x : ℝ} (hx : 0 ≤ x) : x ^ ((5 : ℝ) / 2) = x ^ 2 * Real.sqrt x := by
  rw [show (5 : ℝ) / 2 = (2 : ℕ) + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num),
    Real.rpow_natCast, Real.sqrt_eq_rpow]

/-! ## Model-level estimates -/

/-- The cubic Taylor remainder `r(z) = e^{-z} - (1 - z + z²/2 - z³/6)`. -/
noncomputable def taylorRem (z : ℝ) : ℝ :=
  Real.exp (-z) - (1 - z + z ^ 2 / 2 - z ^ 3 / 6)

theorem continuous_taylorRem : Continuous taylorRem := by
  unfold taylorRem; fun_prop

theorem abs_taylorRem_le {z : ℝ} (hz : -1 ≤ z) : |taylorRem z| ≤ 4 * |z| ^ 3 * Real.sqrt |z| :=
  abs_exp_neg_sub_taylor_le hz

/-- The remainder moment `∫ x^θ r(c (log x - a)) d(law of R_n(h))`. -/
noncomputable def taylorRemMoment (μ : Measure ℝ) (B h : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  ∫ x, x ^ theta B * taylorRem (c * (Real.log x - Real.log B)) ∂(lawR μ B h n)

theorem log_pos_of_two_lt {B : ℝ} (hB : 2 < B) : 0 < Real.log B := Real.log_pos (by linarith)

section ModelEstimates

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem integrable_tiltedLogPow (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ}
    (hB : 2 < B) (h : ℝ) (n k : ℕ) :
    Integrable (fun x : ℝ => x ^ theta B * (Real.log x - Real.log B) ^ k) (lawR μ B h n) := by
  have hi := integrable_absTiltedLogRpow_aux hpos hmean hB h n (s := (k : ℝ)) (Nat.cast_nonneg k)
  refine hi.mono' ((Real.continuous_rpow_const (theta_pos hB).le).measurable.mul
    ((Real.measurable_log.sub_const _).pow_const k)).aestronglyMeasurable ?_
  filter_upwards [ae_pos_lawR hpos hB h n] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx _), abs_pow, Real.rpow_natCast]

theorem integrable_tiltedPow (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ}
    (hB : 2 < B) (h : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ theta B) (lawR μ B h n) := by
  simpa using integrable_tiltedLogPow hpos hmean hB h n 0

theorem ae_floor_one_le (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ}
    (hn : 1 ≤ n) : ∀ᵐ x ∂(lawR μ B h n), floorSeq B 1 ≤ x := by
  filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx
  exact (floorSeq_one_le hB hn).trans hx

/-- `x^{q_N(s)} = e^{-s/N} x^θ e^{-c (log x - a)}`, `c = s/(aN)`. -/
theorem rpow_weightExponent_eq {B N s x : ℝ} (hB : 2 < B) (hN : 0 < N) (hx : 0 < x) :
    x ^ weightExponent B N s = Real.exp (-(s / N)) *
      (x ^ theta B * Real.exp (-(s / (Real.log B * N) * (Real.log x - Real.log B)))) := by
  have ha := log_pos_of_two_lt hB
  rw [weightExponent, Real.rpow_sub hx, Real.rpow_def_of_pos hx (s / (Real.log B * N)),
    div_eq_mul_inv, ← Real.exp_neg]
  have : -(Real.log x * (s / (Real.log B * N))) =
      -(s / N) + -(s / (Real.log B * N) * (Real.log x - Real.log B)) := by
    field_simp
    ring
  rw [this, Real.exp_add]
  ring

theorem transformAt_zero (μ : Measure ℝ) (B h N : ℝ) (n : ℕ) :
    transformAt μ B h N n 0 = N * (tiltedMass μ B h n - 1) := by
  simp [transformAt, weightExponent, realMoment, tiltedMass]

/-- The exact Taylor decomposition of `L_{n,N}(s) - L_{n,N}(0)` and the bound on its
remainder by the `7/2` tilted moment. -/
theorem transform_sub_eq (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ}
    (hB : 2 < B) (h N s : ℝ) {n : ℕ} (hN : 0 < N) (hn : 1 ≤ n) (hs : 0 ≤ s)
    (hsmall : s / (Real.log B * N) * (Real.log B - Real.log (floorSeq B 1)) ≤ 1) :
    transformAt μ B h N n s - transformAt μ B h N n 0 =
      N * (Real.exp (-(s / N)) * (tiltedMass μ B h n -
        s / (Real.log B * N) * tiltedLogMoment μ B h 1 n +
        (s / (Real.log B * N)) ^ 2 / 2 * tiltedLogMoment μ B h 2 n -
        (s / (Real.log B * N)) ^ 3 / 6 * tiltedLogMoment μ B h 3 n +
        taylorRemMoment μ B h n (s / (Real.log B * N))) - tiltedMass μ B h n) ∧
    |taylorRemMoment μ B h n (s / (Real.log B * N))| ≤
      4 * ((s / (Real.log B * N)) ^ 3 * Real.sqrt (s / (Real.log B * N))) *
        absTiltedLogRpowMoment μ B h (7 / 2) n := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have ha := log_pos_of_two_lt hB
  set a := Real.log B with ha_def
  set c := s / (a * N) with hc_def
  have hc0 : 0 ≤ c := div_nonneg hs (mul_pos ha hN).le
  set L := lawR μ B h n with hL
  have hb1 : 0 < floorSeq B 1 := floorSeq_one_pos hB
  -- the remainder is controlled
  have hz : ∀ᵐ x ∂L, -1 ≤ c * (Real.log x - a) := by
    filter_upwards [ae_floor_one_le hpos hB h hn] with x hx
    have hlog : Real.log (floorSeq B 1) ≤ Real.log x := Real.log_le_log hb1 hx
    nlinarith
  have hpt : ∀ᵐ x ∂L, ‖x ^ theta B * taylorRem (c * (Real.log x - a))‖ ≤
      4 * (c ^ 3 * Real.sqrt c) * (x ^ theta B * |Real.log x - a| ^ ((7 : ℝ) / 2)) := by
    filter_upwards [hz, ae_pos_lawR hpos hB h n] with x hzx hx
    have hθx : 0 < x ^ theta B := Real.rpow_pos_of_pos hx _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hθx, rpow_seven_halves_mul_sqrt (abs_nonneg _)]
    have h1 := abs_taylorRem_le hzx
    rw [abs_mul, abs_of_nonneg hc0, Real.sqrt_mul hc0, mul_pow] at h1
    have h2 : x ^ theta B * |taylorRem (c * (Real.log x - a))| ≤
        x ^ theta B * (4 * (c ^ 3 * |Real.log x - a| ^ 3) *
          (Real.sqrt c * Real.sqrt |Real.log x - a|)) := mul_le_mul_of_nonneg_left h1 hθx.le
    calc x ^ theta B * |taylorRem (c * (Real.log x - a))|
        ≤ x ^ theta B * (4 * (c ^ 3 * |Real.log x - a| ^ 3) *
          (Real.sqrt c * Real.sqrt |Real.log x - a|)) := h2
      _ = 4 * (c ^ 3 * Real.sqrt c) * (x ^ theta B *
          (|Real.log x - a| ^ 3 * Real.sqrt |Real.log x - a|)) := by ring
  have hmeasR : AEStronglyMeasurable (fun x => x ^ theta B * taylorRem (c * (Real.log x - a))) L :=
    ((Real.continuous_rpow_const (theta_pos hB).le).measurable.mul
      (continuous_taylorRem.measurable.comp
        ((Real.measurable_log.sub_const _).const_mul c))).aestronglyMeasurable
  have h72 := integrable_absTiltedLogRpow_aux hpos hmean hB h n (s := (7 : ℝ) / 2) (by norm_num)
  have hintR : Integrable (fun x => x ^ theta B * taylorRem (c * (Real.log x - a))) L :=
    (h72.const_mul (4 * (c ^ 3 * Real.sqrt c))).mono' hmeasR hpt
  refine ⟨?_, ?_⟩
  · -- the identity
    have hq : realMoment μ B h n (weightExponent B N s) =
        Real.exp (-(s / N)) * ∫ x, x ^ theta B * Real.exp (-(c * (Real.log x - a))) ∂L := by
      rw [realMoment, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [ae_pos_lawR hpos hB h n] with x hx
      exact rpow_weightExponent_eq hB hN hx
    have hexp : ∫ x, x ^ theta B * Real.exp (-(c * (Real.log x - a))) ∂L =
        tiltedMass μ B h n - c * tiltedLogMoment μ B h 1 n + c ^ 2 / 2 * tiltedLogMoment μ B h 2 n -
          c ^ 3 / 6 * tiltedLogMoment μ B h 3 n + taylorRemMoment μ B h n c := by
      have i0 := integrable_tiltedPow hpos hmean hB h n
      have i1 := integrable_tiltedLogPow hpos hmean hB h n 1
      have i2 := integrable_tiltedLogPow hpos hmean hB h n 2
      have i3 := integrable_tiltedLogPow hpos hmean hB h n 3
      have hfun : (fun x => x ^ theta B * Real.exp (-(c * (Real.log x - a)))) = fun x =>
          x ^ theta B - c * (x ^ theta B * (Real.log x - a) ^ 1) +
            c ^ 2 / 2 * (x ^ theta B * (Real.log x - a) ^ 2) -
            c ^ 3 / 6 * (x ^ theta B * (Real.log x - a) ^ 3) +
            x ^ theta B * taylorRem (c * (Real.log x - a)) := by
        funext x
        simp only [taylorRem]
        ring
      rw [hfun, integral_add _ hintR, integral_sub _ (i3.const_mul _), integral_add _ (i2.const_mul _),
        integral_sub i0 (i1.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul]
      · rfl
      · exact i0.sub (i1.const_mul _)
      · exact (i0.sub (i1.const_mul _)).add (i2.const_mul _)
      · exact ((i0.sub (i1.const_mul _)).add (i2.const_mul _)).sub (i3.const_mul _)
    rw [transformAt_zero, transformAt, hq, hexp]
    ring
  · -- the remainder bound
    unfold taylorRemMoment
    calc |∫ x, x ^ theta B * taylorRem (c * (Real.log x - a)) ∂L|
        = ‖∫ x, x ^ theta B * taylorRem (c * (Real.log x - a)) ∂L‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x, 4 * (c ^ 3 * Real.sqrt c) * (x ^ theta B * |Real.log x - a| ^ ((7 : ℝ) / 2)) ∂L :=
          norm_integral_le_of_norm_le (h72.const_mul _) hpt
      _ = 4 * (c ^ 3 * Real.sqrt c) * absTiltedLogRpowMoment μ B h (7 / 2) n := by
          rw [integral_const_mul]; rfl

/-- The algebraic form of the Taylor bound for `ℋ_N`. -/
theorem taylor_algebra {a N s A H K J R : ℝ} (ha : 0 < a) (hN : 0 < N) (hs : 0 ≤ s)
    (hsN : s ≤ N) :
    |(s + N * (Real.exp (-(s / N)) * (A - s / (a * N) * H + (s / (a * N)) ^ 2 / 2 * K -
        (s / (a * N)) ^ 3 / 6 * J + R) - A)) -
      (-(s * (H / a)) + s ^ 2 * (K / (a ^ 2 * N)) / 2 - s ^ 3 * (J / (a ^ 3 * N ^ 2)) / 6)| ≤
      s ^ 2 / N + s / N * |N * (A - 1)| +
        s / N * |-(s * (H / a)) + s ^ 2 * (K / (a ^ 2 * N)) / 2 - s ^ 3 * (J / (a ^ 3 * N ^ 2)) / 6| +
        N * |R| := by
  set E := Real.exp (-(s / N)) with hE
  set p := -(s * (H / a)) + s ^ 2 * (K / (a ^ 2 * N)) / 2 - s ^ 3 * (J / (a ^ 3 * N ^ 2)) / 6
    with hp
  have hsN0 : 0 ≤ s / N := div_nonneg hs hN.le
  have hsN1 : s / N ≤ 1 := (div_le_one hN).2 hsN
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hE0 : 0 < E := Real.exp_pos _
  have hE2 : 1 - s / N ≤ E := by have := Real.add_one_le_exp (-(s / N)); linarith
  have hE3 : |E - 1 + s / N| ≤ (s / N) ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := -(s / N)) (by rw [abs_neg, abs_of_nonneg hsN0]; exact hsN1)
    rw [neg_sq] at this
    have e : E - 1 + s / N = Real.exp (-(s / N)) - 1 - -(s / N) := by rw [hE]; ring
    rwa [e]
  have hid : (s + N * (E * (A - s / (a * N) * H + (s / (a * N)) ^ 2 / 2 * K -
        (s / (a * N)) ^ 3 / 6 * J + R) - A)) - p =
      N * (E - 1 + s / N) + (E - 1) * (N * (A - 1)) + (E - 1) * p + E * (N * R) := by
    rw [hp]
    field_simp
    ring
  rw [hid]
  have hE4 : |E - 1| ≤ s / N := by rw [abs_le]; constructor <;> linarith
  have t1 : |N * (E - 1 + s / N)| ≤ s ^ 2 / N := by
    rw [abs_mul, abs_of_pos hN]
    calc N * |E - 1 + s / N| ≤ N * (s / N) ^ 2 := mul_le_mul_of_nonneg_left hE3 hN.le
      _ = s ^ 2 / N := by field_simp
  have t2 : |(E - 1) * (N * (A - 1))| ≤ s / N * |N * (A - 1)| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hE4 (abs_nonneg _)
  have t3 : |(E - 1) * p| ≤ s / N * |p| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hE4 (abs_nonneg _)
  have t4 : |E * (N * R)| ≤ N * |R| := by
    rw [abs_mul, abs_mul, abs_of_pos hE0, abs_of_pos hN]
    calc E * (N * |R|) ≤ 1 * (N * |R|) := mul_le_mul_of_nonneg_right hE1 (by positivity)
      _ = N * |R| := one_mul _
  calc |N * (E - 1 + s / N) + (E - 1) * (N * (A - 1)) + (E - 1) * p + E * (N * R)|
      ≤ |N * (E - 1 + s / N)| + |(E - 1) * (N * (A - 1))| + |(E - 1) * p| + |E * (N * R)| := by
        have := abs_add_le (N * (E - 1 + s / N) + (E - 1) * (N * (A - 1)) + (E - 1) * p) (E * (N * R))
        have := abs_add_le (N * (E - 1 + s / N) + (E - 1) * (N * (A - 1))) ((E - 1) * p)
        have := abs_add_le (N * (E - 1 + s / N)) ((E - 1) * (N * (A - 1)))
        linarith
    _ ≤ _ := by linarith

/-- `|e^α - e^β| ≤ e^{max α β} |α - β|`. -/
theorem abs_exp_sub_exp_le (α β : ℝ) :
    |Real.exp α - Real.exp β| ≤ Real.exp (max α β) * |α - β| := by
  rcases le_total α β with h | h
  · rw [max_eq_right h, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 h)),
      abs_of_nonpos (sub_nonpos.2 h)]
    have h1 := Real.add_one_le_exp (α - β)
    have h2 : Real.exp α = Real.exp β * Real.exp (α - β) := by rw [← Real.exp_add]; ring_nf
    rw [h2]
    nlinarith [Real.exp_pos β]
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 h)),
      abs_of_nonneg (sub_nonneg.2 h)]
    have h1 := Real.add_one_le_exp (β - α)
    have h2 : Real.exp β = Real.exp α * Real.exp (β - α) := by rw [← Real.exp_add]; ring_nf
    rw [h2]
    nlinarith [Real.exp_pos α]

/-- For `n ≥ 1` and `q ≤ 1`, `x ↦ x^q` is integrable for the law of `R_n(h)` (the law is
supported on `[b_1, ∞)`). -/
theorem integrable_rpow_lawR (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ}
    (hB : 2 < B) (h : ℝ) {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq : q ≤ 1) :
    Integrable (fun x : ℝ => x ^ q) (lawR μ B h n) := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have hb1 : 0 < floorSeq B 1 := floorSeq_one_pos hB
  have hi := integrable_lawR_of hpos hmean hB h n
  refine ((integrable_const (floorSeq B 1 ^ q + 1)).add hi).mono'
    (measurable_id.pow_const q).aestronglyMeasurable ?_
  filter_upwards [ae_pos_lawR hpos hB h n, ae_floor_one_le hpos hB h hn] with x hx hxb
  show ‖x ^ q‖ ≤ floorSeq B 1 ^ q + 1 + x
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le q)]
  have hb0 : 0 ≤ floorSeq B 1 ^ q := Real.rpow_nonneg hb1.le q
  rcases le_total q 0 with hq0 | hq0
  · have := Real.rpow_le_rpow_of_nonpos hb1 hxb hq0
    linarith
  · rcases le_total x 1 with hx1 | hx1
    · have := Real.rpow_le_one hx.le hx1 hq0
      linarith
    · have : x ^ q ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hq
      rw [Real.rpow_one] at this
      linarith

/-- Lipschitz bound of `s ↦ L_{n,N}(s)` on a bounded range of weights. -/
theorem transform_lipschitz (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ}
    (hB : 2 < B) (h N s s' : ℝ) {n : ℕ} (hN : 0 < N) (hn : 1 ≤ n) (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (hsmall : max s s' / (Real.log B * N) * (-Real.log (floorSeq B 1)) ≤ Real.log 2) :
    |transformAt μ B h N n s - transformAt μ B h N n s'| ≤
      |s - s'| * (2 / Real.log B) * (tiltedLogMoment μ B h 1 n +
        (Real.log B + 2 * (-Real.log (floorSeq B 1))) * tiltedMass μ B h n) := by
  letI : IsProbabilityMeasure (lawR μ B h n) := isProbabilityMeasure_lawR B h n
  have ha := log_pos_of_two_lt hB
  set a := Real.log B with ha_def
  set β := -Real.log (floorSeq B 1) with hβ
  have hb1 : 0 < floorSeq B 1 := floorSeq_one_pos hB
  have hβ0 : 0 ≤ β := by
    rw [hβ, neg_nonneg]; exact Real.log_nonpos hb1.le (floorSeq_le_one hB 1)
  set L := lawR μ B h n with hL
  have i0 := integrable_tiltedPow hpos hmean hB h n
  have i1 := integrable_tiltedLogPow hpos hmean hB h n 1
  -- pointwise bound
  have hpt : ∀ᵐ x ∂L, ‖x ^ weightExponent B N s - x ^ weightExponent B N s'‖ ≤
      2 * (|s - s'| / (a * N)) * (x ^ theta B * (Real.log x - a) + (a + 2 * β) * x ^ theta B) := by
    filter_upwards [ae_pos_lawR hpos hB h n, ae_floor_one_le hpos hB h hn] with x hx hxb
    have hlog : -β ≤ Real.log x := by rw [hβ, neg_neg]; exact Real.log_le_log hb1 hxb
    have hθx : 0 < x ^ theta B := Real.rpow_pos_of_pos hx _
    have hform : ∀ v : ℝ, x ^ weightExponent B N v =
        x ^ theta B * Real.exp (-(Real.log x * (v / (a * N)))) := by
      intro v
      rw [weightExponent, Real.rpow_sub hx, Real.rpow_def_of_pos hx (v / (a * N)),
        Real.exp_neg, div_eq_mul_inv]
    rw [hform s, hform s', ← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_pos hθx]
    have hmax : max (-(Real.log x * (s / (a * N)))) (-(Real.log x * (s' / (a * N)))) ≤
        Real.log 2 := by
      have haN : 0 < a * N := mul_pos ha hN
      apply max_le
      · have : -(Real.log x * (s / (a * N))) ≤ max s s' / (a * N) * β := by
          have h1 : s / (a * N) ≤ max s s' / (a * N) :=
            div_le_div_of_nonneg_right (le_max_left _ _) haN.le
          have h2 : 0 ≤ s / (a * N) := div_nonneg hs haN.le
          nlinarith
        linarith
      · have : -(Real.log x * (s' / (a * N))) ≤ max s s' / (a * N) * β := by
          have h1 : s' / (a * N) ≤ max s s' / (a * N) :=
            div_le_div_of_nonneg_right (le_max_right _ _) haN.le
          have h2 : 0 ≤ s' / (a * N) := div_nonneg hs' haN.le
          nlinarith
        linarith
    have hexp := abs_exp_sub_exp_le (-(Real.log x * (s / (a * N)))) (-(Real.log x * (s' / (a * N))))
    have h2 : Real.exp (max (-(Real.log x * (s / (a * N)))) (-(Real.log x * (s' / (a * N))))) ≤ 2 := by
      calc _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 hmax
        _ = 2 := Real.exp_log (by norm_num)
    have h3 : |-(Real.log x * (s / (a * N))) - -(Real.log x * (s' / (a * N)))| =
        |s - s'| / (a * N) * |Real.log x| := by
      rw [show -(Real.log x * (s / (a * N))) - -(Real.log x * (s' / (a * N))) =
        (s - s') / (a * N) * (-Real.log x) by ring, abs_mul, abs_div,
        abs_of_pos (mul_pos ha hN), abs_neg]
    have h4 : |Real.log x| ≤ (Real.log x - a) + (a + 2 * β) := by
      rcases le_total 0 (Real.log x) with hl | hl
      · rw [abs_of_nonneg hl]; linarith
      · rw [abs_of_nonpos hl]; linarith
    have h5 : |Real.exp (-(Real.log x * (s / (a * N)))) - Real.exp (-(Real.log x * (s' / (a * N))))| ≤
        2 * (|s - s'| / (a * N)) * ((Real.log x - a) + (a + 2 * β)) := by
      calc _ ≤ Real.exp (max (-(Real.log x * (s / (a * N)))) (-(Real.log x * (s' / (a * N))))) *
            |-(Real.log x * (s / (a * N))) - -(Real.log x * (s' / (a * N)))| := hexp
        _ ≤ 2 * (|s - s'| / (a * N) * |Real.log x|) := by
            rw [h3]; exact mul_le_mul_of_nonneg_right h2 (by positivity)
        _ ≤ 2 * (|s - s'| / (a * N) * ((Real.log x - a) + (a + 2 * β))) := by
            gcongr
        _ = _ := by ring
    calc x ^ theta B * |Real.exp (-(Real.log x * (s / (a * N)))) -
          Real.exp (-(Real.log x * (s' / (a * N))))|
        ≤ x ^ theta B * (2 * (|s - s'| / (a * N)) * ((Real.log x - a) + (a + 2 * β))) :=
          mul_le_mul_of_nonneg_left h5 hθx.le
      _ = _ := by ring
  have hdom : Integrable (fun x : ℝ => 2 * (|s - s'| / (a * N)) *
      (x ^ theta B * (Real.log x - a) + (a + 2 * β) * x ^ theta B)) L := by
    refine Integrable.const_mul ?_ _
    exact (by simpa using i1 : Integrable (fun x : ℝ => x ^ theta B * (Real.log x - a)) L).add
      (i0.const_mul _)
  have hI : ∀ v : ℝ, 0 ≤ v → Integrable (fun x : ℝ => x ^ weightExponent B N v) L := by
    intro v hv
    refine integrable_rpow_lawR hpos hmean hB h hn ?_
    rw [weightExponent]
    have := div_nonneg hv (mul_pos ha hN).le
    linarith [theta_lt_one hB]
  have e : transformAt μ B h N n s - transformAt μ B h N n s' =
      N * ∫ x, (x ^ weightExponent B N s - x ^ weightExponent B N s') ∂L := by
    rw [integral_sub (hI s hs) (hI s' hs'), transformAt, transformAt, realMoment, realMoment]
    ring
  rw [e, abs_mul, abs_of_pos hN]
  calc N * |∫ x, (x ^ weightExponent B N s - x ^ weightExponent B N s') ∂L|
      ≤ N * ∫ x, 2 * (|s - s'| / (a * N)) *
          (x ^ theta B * (Real.log x - a) + (a + 2 * β) * x ^ theta B) ∂L :=
        mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hdom hpt) hN.le
    _ = |s - s'| * (2 / a) * (tiltedLogMoment μ B h 1 n + (a + 2 * β) * tiltedMass μ B h n) := by
        rw [integral_const_mul, integral_add (by simpa using i1) (i0.const_mul _),
          integral_const_mul]
        have e1 : ∫ x, x ^ theta B * (Real.log x - a) ∂L = tiltedLogMoment μ B h 1 n := by
          simp [tiltedLogMoment, hL, ha_def]
        rw [e1]
        simp only [tiltedMass, hL]
        field_simp

/-! ### The Riccati difference equation -/

/-- The compensated transform `s + L_{n,N}(s) - L_{n,N}(0)` at generation `n` and field `h`. -/
noncomputable def compGen (μ : Measure ℝ) (B h N : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  s + transformAt μ B h N n s - transformAt μ B h N n 0

/-- The Riccati right-hand side `S ℋ + ℋ²/2 - s²/2` at generation level. -/
noncomputable def riccatiGen (μ : Measure ℝ) (B h N : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  transformAt μ B h N n 0 * compGen μ B h N n s + compGen μ B h N n s ^ 2 / 2 - s ^ 2 / 2

theorem compGen_succ_sub (μ : Measure ℝ) (B h N : ℝ) (n : ℕ) (s : ℝ) (hN : N ≠ 0) :
    compGen μ B h N (n + 1) s - compGen μ B h N n s =
      riccatiGen μ B h N n s / N + transformError μ B h N n s 0 := by
  simp only [riccatiGen, compGen, transformError, psiS]
  field_simp
  ring

theorem compGen_telescope (μ : Measure ℝ) (B h N s : ℝ) (hN : N ≠ 0) (m k : ℕ) (hmk : m ≤ k) :
    compGen μ B h N k s - compGen μ B h N m s =
      (∑ n ∈ Finset.Ico m k, riccatiGen μ B h N n s) / N +
        ∑ n ∈ Finset.Ico m k, transformError μ B h N n s 0 := by
  induction k, hmk using Nat.le_induction with
  | base => simp
  | succ k hmk ih =>
    rw [Finset.sum_Ico_succ_top hmk, Finset.sum_Ico_succ_top hmk, add_div]
    have := compGen_succ_sub μ B h N k s hN
    linarith

/-! ### Window bounds from the hypotheses -/

theorem tiltedLogMoment_two_nonneg (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ)
    (n : ℕ) : 0 ≤ tiltedLogMoment μ B h 2 n := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_pos_lawR hpos hB h n] with x hx
  exact mul_nonneg (Real.rpow_nonneg hx.le _) (sq_nonneg _)

theorem tiltedMass_nonneg (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    0 ≤ tiltedMass μ B h n := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_pos_lawR hpos hB h n] with x hx
  exact Real.rpow_nonneg hx.le _

set_option maxHeartbeats 400000 in
-- the window lemma collects many bounds in one elaboration
/-- Generation-level bounds at the field `h_c + u` in the window `u (n+1)² ≤ η`, from
`th:product`, `prop:window-moments` and the residue limits; and the matching estimate. -/
theorem gen_window (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) {ℓ₃ κ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
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
    (hWindow : ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ u : ℝ, 0 ≤ u →
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
            tiltedProduct μ B (criticalPoint μ B) n - 1| ≤ C * u * ((n : ℝ) + 1) ^ 2) :
    0 < ℓ₃ ∧ ∃ (n₀ : ℕ) (η C c : ℝ), 1 ≤ n₀ ∧ 0 < η ∧ 0 < C ∧ 0 < c ∧
      (∀ n : ℕ, n₀ ≤ n → ∀ u : ℝ, 0 ≤ u → u * ((n : ℝ) + 1) ^ 2 ≤ η →
        c / n - C * u * ((n : ℝ) + 1) ≤ tiltedMass μ B (criticalPoint μ B + u) n - 1 ∧
        tiltedMass μ B (criticalPoint μ B + u) n - 1 ≤ C / n + C * u * ((n : ℝ) + 1) ∧
        |tiltedLogMoment μ B (criticalPoint μ B + u) 1 n| ≤
          C / n + C * u * ((n : ℝ) + 1) ^ 2 + C * u ^ 2 * ((n : ℝ) + 1) ^ 4 ∧
        c * n - C * u * ((n : ℝ) + 1) ^ 3 ≤ tiltedLogMoment μ B (criticalPoint μ B + u) 2 n ∧
        tiltedLogMoment μ B (criticalPoint μ B + u) 2 n ≤ C * n + C * u * ((n : ℝ) + 1) ^ 3 ∧
        c * ((n : ℝ) + 1) ^ 2 - C * u * ((n : ℝ) + 1) ^ 4 ≤
          tiltedLogMoment μ B (criticalPoint μ B + u) 3 n ∧
        tiltedLogMoment μ B (criticalPoint μ B + u) 3 n ≤
          C * ((n : ℝ) + 1) ^ 2 + C * u * ((n : ℝ) + 1) ^ 4 ∧
        absTiltedLogRpowMoment μ B (criticalPoint μ B + u) (7 / 2) n ≤
          C * ((n : ℝ) + 1) ^ ((5 : ℝ) / 2)) ∧
      (∀ ε > 0, ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∀ u : ℝ, 0 ≤ u → u * ((n : ℝ) + 1) ^ 2 ≤ η →
        |tiltedLogMoment μ B (criticalPoint μ B + u) 1 n -
            u * (κ / ℓ₃) * tiltedLogMoment μ B (criticalPoint μ B + u) 3 n| ≤
          C / n + ε * u * ((n : ℝ) + 1) ^ 2 + C * u ^ 2 * ((n : ℝ) + 1) ^ 4) := by
  set hc := criticalPoint μ B with hc_def
  obtain ⟨C₁, hC₁, hbnd, -, ⟨ℓ₃', hℓ₃'pos, hℓ₃'lim⟩, hA1, hAθ, hKθ, hHO, -⟩ := hProd
  have hℓ : ℓ₃ = ℓ₃' := tendsto_nhds_unique hℓ₃ hℓ₃'lim
  have hℓpos : 0 < ℓ₃ := hℓ ▸ hℓ₃'pos
  obtain ⟨η, CW, hη, hCW, hW⟩ := hWindow
  -- asymptotic bounds at `h_c`
  obtain ⟨cA, hcA, hcAb⟩ := hAθ.isBigO.exists_pos
  obtain ⟨cA', hcA', hcA'b⟩ := hAθ.isBigO_symm.exists_pos
  obtain ⟨cK, hcK, hcKb⟩ := hKθ.isBigO.exists_pos
  obtain ⟨cK', hcK', hcK'b⟩ := hKθ.isBigO_symm.exists_pos
  obtain ⟨cH, hcH, hcHb⟩ := hHO.exists_pos
  have hκb : ∀ᶠ n : ℕ in atTop, |deriv (fun h => tiltedLogMoment μ B h 1 n) hc /
      tiltedProduct μ B hc n - κ| < 1 := by
    have := (Metric.tendsto_nhds.1 hκ) 1 one_pos
    simpa [Real.dist_eq] using this
  have hJb : ∀ᶠ n : ℕ in atTop, |tiltedLogMoment μ B hc 3 n / tiltedProduct μ B hc n - ℓ₃| <
      ℓ₃ / 2 := by
    have := (Metric.tendsto_nhds.1 hℓ₃) (ℓ₃ / 2) (by linarith)
    simpa [Real.dist_eq] using this
  obtain ⟨n₀', hn₀'⟩ := eventually_atTop.1 (hA1.and (hcAb.bound.and (hcA'b.bound.and
    (hcKb.bound.and (hcK'b.bound.and (hcHb.bound.and (hκb.and hJb)))))))
  set n₀ := max n₀' 1 with hn₀
  have hpieces : ∀ n : ℕ, n₀ ≤ n →
      1 ≤ n ∧ 1 / (cA' * n) ≤ tiltedMass μ B hc n - 1 ∧ tiltedMass μ B hc n - 1 ≤ cA / n ∧
      tiltedLogMoment μ B hc 2 n ≤ cK * n ∧ n / cK' ≤ tiltedLogMoment μ B hc 2 n ∧
      |tiltedLogMoment μ B hc 1 n| ≤ cH / n ∧
      |deriv (fun h => tiltedLogMoment μ B h 1 n) hc| ≤ (|κ| + 1) * (C₁ * ((n : ℝ) + 1) ^ 2) ∧
      ℓ₃ / (2 * C₁) * ((n : ℝ) + 1) ^ 2 ≤ tiltedLogMoment μ B hc 3 n ∧
      tiltedLogMoment μ B hc 3 n ≤ 2 * ℓ₃ * C₁ * ((n : ℝ) + 1) ^ 2 := by
    intro n hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨hA1n, hcAn, hcA'n, hcKn, hcK'n, hcHn, hκn, hJn⟩ := hn₀' n (le_trans (le_max_left _ _) hn)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hK0 := tiltedLogMoment_two_nonneg hpos hB hc n
    obtain ⟨hPi1, hPi2, -, -⟩ := hbnd n hn1
    have hPipos : 0 < tiltedProduct μ B hc n := lt_of_lt_of_le (by positivity) hPi1
    simp only [Real.norm_eq_abs, abs_inv, Nat.abs_cast] at hcAn hcA'n hcKn hcK'n hcHn
    rw [abs_of_pos (by linarith : (0 : ℝ) < tiltedMass μ B hc n - 1)] at hcAn hcA'n
    rw [abs_of_nonneg hK0] at hcKn hcK'n
    refine ⟨hn1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hcA'n hnpos.le
      rw [mul_inv_cancel₀ hnpos.ne'] at this
      calc (1 : ℝ) ≤ n * (cA' * (tiltedMass μ B hc n - 1)) := this
        _ = (tiltedMass μ B hc n - 1) * (cA' * n) := by ring
    · rwa [div_eq_mul_inv]
    · exact hcKn
    · rw [div_le_iff₀ hcK', mul_comm]; exact hcK'n
    · rwa [div_eq_mul_inv]
    · have h1 : |deriv (fun h => tiltedLogMoment μ B h 1 n) hc / tiltedProduct μ B hc n| ≤
          |κ| + 1 := by
        have := abs_sub_abs_le_abs_sub (deriv (fun h => tiltedLogMoment μ B h 1 n) hc /
          tiltedProduct μ B hc n) κ
        linarith only [this, hκn]
      rw [abs_div, abs_of_pos hPipos, div_le_iff₀ hPipos] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hPi2 (by positivity))
    · have h1 := (abs_lt.1 hJn).1
      have h2 : ℓ₃ / 2 ≤ tiltedLogMoment μ B hc 3 n / tiltedProduct μ B hc n := by
        linarith only [h1]
      rw [le_div_iff₀ hPipos] at h2
      calc ℓ₃ / (2 * C₁) * ((n : ℝ) + 1) ^ 2 = ℓ₃ / 2 * (((n : ℝ) + 1) ^ 2 / C₁) := by ring
        _ ≤ ℓ₃ / 2 * tiltedProduct μ B hc n :=
            mul_le_mul_of_nonneg_left hPi1 (by positivity)
        _ ≤ _ := h2
    · have h1 := (abs_lt.1 hJn).2
      have h2 : tiltedLogMoment μ B hc 3 n / tiltedProduct μ B hc n ≤ 2 * ℓ₃ := by
        linarith only [h1, hℓpos]
      rw [div_le_iff₀ hPipos] at h2
      calc tiltedLogMoment μ B hc 3 n ≤ 2 * ℓ₃ * tiltedProduct μ B hc n := h2
        _ ≤ 2 * ℓ₃ * (C₁ * ((n : ℝ) + 1) ^ 2) :=
            mul_le_mul_of_nonneg_left hPi2 (by positivity)
        _ = _ := by ring
  set C := cA + cK + cH + CW + (|κ| + 1) * C₁ + 2 * ℓ₃ * C₁ + CW * (|κ| / ℓ₃) + 1 with hC
  have hC0 : 0 < C := by positivity
  have hterms : 0 ≤ (|κ| + 1) * C₁ ∧ 0 ≤ 2 * ℓ₃ * C₁ ∧ 0 ≤ CW * (|κ| / ℓ₃) :=
    ⟨by positivity, by positivity, by positivity⟩
  set c := min (1 / cA') (min (1 / cK') (ℓ₃ / (2 * C₁))) with hc'
  have hc0 : 0 < c := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨hℓpos, n₀, η, C, c, le_max_right _ _, hη, hC0, hc0, ?_, ?_⟩
  · intro n hn u hu hun
    obtain ⟨hn1, hA_lo, hA_hi, hK_hi, hK_lo, hH, hE, hJ_lo, hJ_hi⟩ := hpieces n hn
    obtain ⟨wA, wH, wK, wJ, w72, -⟩ := hW n hn1 u hu hun
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hn1' : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hcA_le : cA ≤ C := by
      rw [hC]; linarith only [hterms.1, hterms.2.1, hterms.2.2, hcA, hcK, hcH, hCW]
    have hcK_le : cK ≤ C := by
      rw [hC]; linarith only [hterms.1, hterms.2.1, hterms.2.2, hcA, hcK, hcH, hCW]
    have hcH_le : cH ≤ C := by
      rw [hC]; linarith only [hterms.1, hterms.2.1, hterms.2.2, hcA, hcK, hcH, hCW]
    have hCW_le : CW ≤ C := by
      rw [hC]; linarith only [hterms.1, hterms.2.1, hterms.2.2, hcA, hcK, hcH, hCW]
    have hκ_le : (|κ| + 1) * C₁ ≤ C := by
      rw [hC]; linarith only [hterms.1, hterms.2.1, hterms.2.2, hcA, hcK, hcH, hCW]
    have hJ_le : 2 * ℓ₃ * C₁ ≤ C := by
      rw [hC]; linarith only [hterms.1, hterms.2.1, hterms.2.2, hcA, hcK, hcH, hCW]
    have hc_A : c ≤ 1 / cA' := min_le_left _ _
    have hc_K : c ≤ 1 / cK' := (min_le_right _ _).trans (min_le_left _ _)
    have hc_J : c ≤ ℓ₃ / (2 * C₁) := (min_le_right _ _).trans (min_le_right _ _)
    have p1 : 0 ≤ u * ((n : ℝ) + 1) := by positivity
    have p2 : 0 ≤ u * ((n : ℝ) + 1) ^ 2 := by positivity
    have p3 : 0 ≤ u * ((n : ℝ) + 1) ^ 3 := by positivity
    have p4 : 0 ≤ u * ((n : ℝ) + 1) ^ 4 := by positivity
    have p5 : 0 ≤ u ^ 2 * ((n : ℝ) + 1) ^ 4 := by positivity
    have wA' := abs_le.1 wA
    have wH' := abs_le.1 wH
    have wK' := abs_le.1 wK
    have wJ' := abs_le.1 wJ
    have m1 : CW * u * ((n : ℝ) + 1) ≤ C * u * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCW_le hu) hn1'
    have m3 : CW * u * ((n : ℝ) + 1) ^ 3 ≤ C * u * ((n : ℝ) + 1) ^ 3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCW_le hu) (by positivity)
    have m4 : CW * u * ((n : ℝ) + 1) ^ 4 ≤ C * u * ((n : ℝ) + 1) ^ 4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCW_le hu) (by positivity)
    have m5 : CW * u ^ 2 * ((n : ℝ) + 1) ^ 4 ≤ C * u ^ 2 * ((n : ℝ) + 1) ^ 4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCW_le (sq_nonneg u))
        (by positivity)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have e1 : c / n ≤ 1 / (cA' * n) := by
        rw [← div_div]; exact div_le_div_of_nonneg_right hc_A hnpos.le
      linarith only [e1, m1, hA_lo, wA'.1]
    · have e1 : cA / n ≤ C / n := div_le_div_of_nonneg_right hcA_le hnpos.le
      linarith only [e1, m1, hA_hi, wA'.2]
    · have e1 : cH / n ≤ C / n := div_le_div_of_nonneg_right hcH_le hnpos.le
      have e2 : |u * deriv (fun h => tiltedLogMoment μ B h 1 n) hc| ≤ C * u * ((n : ℝ) + 1) ^ 2 := by
        rw [abs_mul, abs_of_nonneg hu]
        calc u * |deriv (fun h => tiltedLogMoment μ B h 1 n) hc|
            ≤ u * ((|κ| + 1) * (C₁ * ((n : ℝ) + 1) ^ 2)) := mul_le_mul_of_nonneg_left hE hu
          _ = (|κ| + 1) * C₁ * (u * ((n : ℝ) + 1) ^ 2) := by ring
          _ ≤ C * (u * ((n : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_right hκ_le p2
          _ = _ := by ring
      have e4 := abs_le.1 e2
      have e5 := abs_le.1 hH
      rw [abs_le]
      constructor
      · linarith only [e1, e4.1, e5.1, wH'.1, m5]
      · linarith only [e1, e4.2, e5.2, wH'.2, m5]
    · have e1 : c * n ≤ n / cK' := by
        calc c * n ≤ 1 / cK' * n := mul_le_mul_of_nonneg_right hc_K hnpos.le
          _ = n / cK' := by ring
      linarith only [e1, m3, hK_lo, wK'.1]
    · have e1 : cK * n ≤ C * n := mul_le_mul_of_nonneg_right hcK_le hnpos.le
      linarith only [e1, m3, hK_hi, wK'.2]
    · have e1 : c * ((n : ℝ) + 1) ^ 2 ≤ ℓ₃ / (2 * C₁) * ((n : ℝ) + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hc_J (by positivity)
      linarith only [e1, m4, hJ_lo, wJ'.1]
    · have e1 : 2 * ℓ₃ * C₁ * ((n : ℝ) + 1) ^ 2 ≤ C * ((n : ℝ) + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hJ_le (by positivity)
      linarith only [e1, m4, hJ_hi, wJ'.2]
    · exact w72.trans (mul_le_mul_of_nonneg_right hCW_le (Real.rpow_nonneg hn1' _))
  · -- matching
    intro ε hε
    set ε' := ε / (C₁ * (1 + |κ| / ℓ₃)) with hε'
    have hε'0 : 0 < ε' := by positivity
    have hκ' := (Metric.tendsto_nhds.1 hκ) ε' hε'0
    have hJ' := (Metric.tendsto_nhds.1 hℓ₃) ε' hε'0
    obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (hκ'.and hJ')
    refine ⟨max n₁ n₀, fun n hn u hu hun => ?_⟩
    have hn0 : n₀ ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨hn1, -, -, -, -, hH, -, -, -⟩ := hpieces n hn0
    obtain ⟨hκn, hJn⟩ := hn₁ n (le_trans (le_max_left _ _) hn)
    rw [Real.dist_eq] at hκn hJn
    obtain ⟨-, wH, -, wJ, -, -⟩ := hW n hn1 u hu hun
    obtain ⟨hPi1, hPi2, -, -⟩ := hbnd n hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hPipos : 0 < tiltedProduct μ B hc n := lt_of_lt_of_le (by positivity) hPi1
    set E := deriv (fun h => tiltedLogMoment μ B h 1 n) hc with hE_def
    set J := tiltedLogMoment μ B hc 3 n
    set PiN := tiltedProduct μ B hc n
    -- |E - (κ/ℓ₃) J| ≤ ε (n+1)²
    have hEJ : |E - κ / ℓ₃ * J| ≤ ε * ((n : ℝ) + 1) ^ 2 := by
      have h1 : E - κ / ℓ₃ * J = PiN * ((E / PiN - κ) - κ / ℓ₃ * (J / PiN - ℓ₃)) := by
        field_simp
        ring
      rw [h1, abs_mul, abs_of_pos hPipos]
      have h2 : |(E / PiN - κ) - κ / ℓ₃ * (J / PiN - ℓ₃)| ≤ ε' + |κ| / ℓ₃ * ε' := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_div, abs_of_pos hℓpos]
        exact add_le_add hκn.le (mul_le_mul_of_nonneg_left hJn.le (by positivity))
      have h3 : ε' + |κ| / ℓ₃ * ε' = ε / C₁ := by
        rw [hε']; field_simp
      calc PiN * |(E / PiN - κ) - κ / ℓ₃ * (J / PiN - ℓ₃)| ≤ PiN * (ε / C₁) :=
            mul_le_mul_of_nonneg_left (h3 ▸ h2) hPipos.le
        _ ≤ (C₁ * ((n : ℝ) + 1) ^ 2) * (ε / C₁) :=
            mul_le_mul_of_nonneg_right hPi2 (by positivity)
        _ = _ := by field_simp
    have hC_le1 : cH ≤ C := by
      rw [hC]; linarith only [hterms.1, hterms.2.1, hterms.2.2, hcA, hcK, hcH, hCW]
    have hC_le2 : CW + CW * (|κ| / ℓ₃) ≤ C := by
      rw [hC]; linarith only [hterms.1, hterms.2.1, hterms.2.2, hcA, hcK, hcH, hCW]
    -- decomposition
    have hdec : tiltedLogMoment μ B (hc + u) 1 n - u * (κ / ℓ₃) * tiltedLogMoment μ B (hc + u) 3 n =
        tiltedLogMoment μ B hc 1 n + u * (E - κ / ℓ₃ * J) +
          (tiltedLogMoment μ B (hc + u) 1 n - tiltedLogMoment μ B hc 1 n - u * E) -
          u * (κ / ℓ₃) * (tiltedLogMoment μ B (hc + u) 3 n - J) := by ring
    rw [hdec]
    have t1 : |tiltedLogMoment μ B hc 1 n| ≤ C / n :=
      hH.trans (div_le_div_of_nonneg_right hC_le1 hnpos.le)
    have t2 : |u * (E - κ / ℓ₃ * J)| ≤ ε * u * ((n : ℝ) + 1) ^ 2 := by
      rw [abs_mul, abs_of_nonneg hu]
      calc u * |E - κ / ℓ₃ * J| ≤ u * (ε * ((n : ℝ) + 1) ^ 2) :=
            mul_le_mul_of_nonneg_left hEJ hu
        _ = _ := by ring
    have t4 : |u * (κ / ℓ₃) * (tiltedLogMoment μ B (hc + u) 3 n - J)| ≤
        |κ| / ℓ₃ * (CW * u ^ 2 * ((n : ℝ) + 1) ^ 4) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_div, abs_of_pos hℓpos]
      calc u * (|κ| / ℓ₃) * |tiltedLogMoment μ B (hc + u) 3 n - J|
          ≤ u * (|κ| / ℓ₃) * (CW * u * ((n : ℝ) + 1) ^ 4) :=
            mul_le_mul_of_nonneg_left wJ (by positivity)
        _ = _ := by ring
    have p5 : 0 ≤ u ^ 2 * ((n : ℝ) + 1) ^ 4 := by positivity
    have t5 : CW * u ^ 2 * ((n : ℝ) + 1) ^ 4 + |κ| / ℓ₃ * (CW * u ^ 2 * ((n : ℝ) + 1) ^ 4) ≤
        C * u ^ 2 * ((n : ℝ) + 1) ^ 4 := by
      calc CW * u ^ 2 * ((n : ℝ) + 1) ^ 4 + |κ| / ℓ₃ * (CW * u ^ 2 * ((n : ℝ) + 1) ^ 4)
          = (CW + CW * (|κ| / ℓ₃)) * (u ^ 2 * ((n : ℝ) + 1) ^ 4) := by ring
        _ ≤ C * (u ^ 2 * ((n : ℝ) + 1) ^ 4) := mul_le_mul_of_nonneg_right hC_le2 p5
        _ = _ := by ring
    have a1 := abs_le.1 t1
    have a2 := abs_le.1 t2
    have a3 := abs_le.1 wH
    have a4 := abs_le.1 t4
    rw [abs_le]
    constructor
    · linarith only [a1.1, a2.1, a3.1, a4.2, t5]
    · linarith only [a1.2, a2.2, a3.2, a4.1, t5]

end ModelEstimates

end DiamondPinning
