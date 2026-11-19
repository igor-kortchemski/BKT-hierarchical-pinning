module

public import DiamondPinning.Model.Basic
public import DiamondPinning.Model.Scaling
public import DiamondPinning.Model.Profile
public import DiamondPinning.Proofs.Scaling
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Key statements, batch 2c (part 1): the near-critical scaling limit

Section 5 of the paper (`source/scaling.tex`): the scaling objects
(lines 9–41, definitions in `DiamondPinning.Model.Scaling` and
`DiamondPinning.Model.Profile`), `cont:continuation` (lines 45–54, proved in
Section 7, `source/continuation.tex`), `scaling:compactness` (lines 56–118)
and `scaling:mellin-calculus` (lines 124–193). `lem:one-sided` is in
`DiamondPinning.Statements.OneSided`.

Standing assumptions: `μ` is the law of `W` (a probability measure with
`W > 0` a.s. and `E W = 1`), `B > 2`, `c = B - 1`, `a = log B`,
`θ = log 2 / log B`, `ρ = 2 / B`, `b_n = floorSeq B n`. The scale `N > 0` is
real and generations are natural numbers (lines 10–11). The Mellin lemma holds
at every field `h`, with constants independent of `h` (it is applied at the
fields `h_N`, which vary with `N`). `scaling:compactness` and
`cont:continuation` are results about the model under `h_c > h_a`; following
blueprint E5, the residues `ℓ₃ = lim J_n/Π_n` and `κ = lim ∂_h H_n(h_c)/Π_n`
enter as real parameters with their defining limits as hypotheses, and
`γ = 3 a² κ/(2 ℓ₃)` (`eq:gamma`), `v = γ λ`.

The Mellin lemma uses the domains of author decision 2 (audit F3–F4):
measurable kernels, generations `n ≥ 1`, weights in a compact `[s₀, s₁]` with
`q_N(s) ≥ 0` (here: `N` large). The proofs are holes pending approval.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology

/-! ### The rescaled measure (lines 12–17) -/

/-- `scaling:measure` (`scaling.tex` lines 14–17): for `N > 0`, at every field
and generation, the rescaled tilted measure
`N E[(R_n^θ - 1) 1{R_n ≥ 1} δ_{log R_n/(aN)}(dx)]` is a finite positive measure
on `[0, ∞)`. -/
theorem rescaledMeasure_finite {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {N : ℝ} (hN : 0 < N) (n : ℕ) :
    IsFiniteMeasure (rescaledMeasure μ B h N n) ∧
      rescaledMeasure μ B h N n (Set.Iio 0) = 0 := by
  exact rescaledMeasure_finite_aux hpos hmean hB h hN n

/-! ### Mellin defect estimates (lines 124–193) -/

/-- `scaling:mellin-calculus`, first claim (`scaling.tex` lines 130–131): for a
fixed compact subinterval `[q₁, q₂]` of `(0, 1)` there is `C` such that
`D_n(q) ≥ -C ρ^n` for all `q ∈ [q₁, q₂]`, every field `h` and every `n ≥ 1`. -/
theorem defectMean_lower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    ∀ q₁ q₂ : ℝ, 0 < q₁ → q₂ < 1 → ∃ C : ℝ, ∀ (h : ℝ) (n : ℕ), 1 ≤ n →
      ∀ q ∈ Set.Icc q₁ q₂, -(C * (2 / B) ^ n) ≤ defectMean μ B h n q := by
  exact defectMean_lower_aux hpos hmean hB

/-- `scaling:mellin-calculus`, `scaling:kernel` (`scaling.tex` lines 131–136),
with the domains of author decision 2 (measurable `F`, `n ≥ 1`): for a fixed
compact subinterval `[q₁, q₂]` of `(0, 1)` there is `C` such that for every
measurable `F` bounded on `[b_1², ∞)` and differentiable near `1` there is
`C_F` with `|E F(r_n) - F(1)| ≤ C_F (D_n(q₀) + C ρ^n)` for all
`q₀ ∈ [q₁, q₂]`, every field `h` and every `n ≥ 1`. -/
theorem kernel_comparison {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    ∀ q₁ q₂ : ℝ, 0 < q₁ → q₂ < 1 → ∃ C : ℝ, ∀ F : ℝ → ℝ, Measurable F →
      (∃ K : ℝ, ∀ r : ℝ, floorSeq B 1 ^ 2 ≤ r → |F r| ≤ K) →
      (∀ᶠ r in 𝓝 (1 : ℝ), DifferentiableAt ℝ F r) →
      ∃ CF : ℝ, ∀ (h : ℝ) (n : ℕ), 1 ≤ n → ∀ q₀ ∈ Set.Icc q₁ q₂,
        |kernelExpectation μ B h n F - F 1| ≤
          CF * (defectMean μ B h n q₀ + C * (2 / B) ^ n) := by
  exact kernel_comparison_aux hpos hmean hB

/-- `scaling:mellin-calculus`, `cont:defectdifference` (`scaling.tex`
lines 137–141): for a fixed compact subinterval `[q₁, q₂]` of `(0, 1)` there is
`C` with `|D_n(q) - D_n(q₀)| ≤ C |q - q₀| (D_n(q₀) + C ρ^n)` for all
`q, q₀ ∈ [q₁, q₂]`, every field `h` and every `n ≥ 1`. -/
theorem defectMean_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    ∀ q₁ q₂ : ℝ, 0 < q₁ → q₂ < 1 → ∃ C : ℝ, ∀ (h : ℝ) (n : ℕ), 1 ≤ n →
      ∀ q ∈ Set.Icc q₁ q₂, ∀ q₀ ∈ Set.Icc q₁ q₂,
        |defectMean μ B h n q - defectMean μ B h n q₀| ≤
          C * |q - q₀| * (defectMean μ B h n q₀ + C * (2 / B) ^ n) := by
  exact defectMean_sub_aux hpos hmean hB

/-- `scaling:mellin-calculus`, `cont:recurrence` (`scaling.tex` lines 142–147):
the exact transform recurrence
`L_{n+1,N}(s) = e^{s/N} L_{n,N}(s) + e^{s/N}/(2N) L_{n,N}(s)² - (N/2) e^{s/N} D_n(q_N(s))`,
at every field `h`, for real `N > 0`, `n ≥ 1` (decision 2) and `s ≥ 0`
(`scaling.tex` line 19). -/
theorem transform_recurrence {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {N : ℝ} (hN : 0 < N) {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    transformAt μ B h N (n + 1) s =
      Real.exp (s / N) * transformAt μ B h N n s +
        Real.exp (s / N) / (2 * N) * transformAt μ B h N n s ^ 2 -
        N / 2 * Real.exp (s / N) * defectMean μ B h n (weightExponent B N s) := by
  exact transform_recurrence_aux hpos hmean hB h hN hn hs

/-- Proof of `scaling:mellin-calculus`, the floor and monotonicity display
(`scaling.tex` lines 184–188), on the range where it holds (audit F3,
decision 2: `0 ≤ s₀ ≤ s` and `q_N(s) ≥ 0`): there is `C` with
`-C N ρ^n ≤ L_{n,N}(s) ≤ L_{n,N}(s₀) + C N ρ^n` at every field `h`, for every
real `N > 0` and every `n`. -/
theorem transform_floor {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    ∃ C : ℝ, ∀ (h N : ℝ) (n : ℕ) (s₀ s : ℝ), 0 < N → 0 ≤ s₀ → s₀ ≤ s →
      0 ≤ weightExponent B N s →
      -(C * N * (2 / B) ^ n) ≤ transformAt μ B h N n s ∧
        transformAt μ B h N n s ≤ transformAt μ B h N n s₀ + C * N * (2 / B) ^ n := by
  exact transform_floor_aux hpos hmean hB

/-- `scaling:mellin-calculus`, consequences of a bounded transform
(`scaling.tex` lines 148–161): there is `C` such that for a time interval
`[r, r + δ] ⊂ (0, ∞)`, a weight `s₀ ≥ 0` and a bound `M`, there are `N₁`,
`C_M` and errors `ε_N → 0` such that for every real `N ≥ N₁` and every field
`h`, if `|L_N(t, s₀)| = |L_{⌊Nt⌋,N}(s₀)| ≤ M` for `t ∈ [r, r + δ]`, then on
this interval

* `Δ L_{n,N}(s₀) ≤ N⁻¹ Ψ_{s₀}(L_{n,N}(s₀)) + C_M N⁻² + C N ρ^n` for
  `n = ⌊N t⌋` (`cont:onesided`);
* `∑_{rN ≤ n < (r+δ)N} |D_n(q_N(s₀))| ≤ C_M / N` (`scaling:defectsum`);
* `L_N(·, s₀)` has variation at most `C_M` on `[r, r + δ]` (bounded in `BV`);
* `L_N(t₂, s₀) - L_N(t₁, s₀) ≤ C_M (t₂ - t₁) + ε_N` for `t₁ ≤ t₂` (the uniform
  one-sided Lipschitz bound up to an error tending to zero).

`Δ x_n = x_{n+1} - x_n`. -/
theorem transform_bounded {μ : Measure ℝ} [IsProbabilityMeasure μ]
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
  exact transform_bounded_aux hpos hmean hB

/-- `scaling:mellin-calculus`, `scaling:transform-difference` (`scaling.tex`
lines 161–167), with weights in a compact `[s₀, s₁]` (decision 2; `N` large,
so that `q_N(s) ≥ 0`): for a time interval `[r, r + δ] ⊂ (0, ∞)`,
`0 ≤ s₀ ≤ s₁` and a bound `M`, there are `N₁` and `C` such that for every real
`N ≥ N₁` and every field `h`, if `|L_N(t, s₀)| ≤ M` for `t ∈ [r, r + δ]`, then
for every `s ∈ [s₀, s₁]` the errors
`e_{n,N}(s) = Δ(L_{n,N}(s) - L_{n,N}(s₀)) - (Ψ_s(L_{n,N}(s)) - Ψ_{s₀}(L_{n,N}(s₀)))/N`
satisfy `∑_{rN ≤ n < (r+δ)N} |e_{n,N}(s)| ≤ C / N`. The constant is uniform
over the compact weight range. -/
theorem transform_difference {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    ∀ r δ s₀ s₁ M : ℝ, 0 < r → 0 < δ → 0 ≤ s₀ → s₀ ≤ s₁ →
      ∃ N₁ C : ℝ, ∀ N : ℝ, N₁ ≤ N → ∀ h : ℝ,
        (∀ t ∈ Set.Icc r (r + δ), |transformAt μ B h N ⌊N * t⌋₊ s₀| ≤ M) →
        ∀ s ∈ Set.Icc s₀ s₁,
          ∑ n ∈ Finset.Ico ⌈r * N⌉₊ ⌈(r + δ) * N⌉₊, |transformError μ B h N n s s₀| ≤
            C / N := by
  exact transform_difference_aux hpos hmean hB

/-! ### Compactness and entrance data (lines 56–118) -/

/-- `scaling:compactness` (`scaling.tex` lines 56–118). At `h_c > h_a`, with
the residues `ℓ₃, κ`: there is `η₀ > 0` such that for `λ ≥ 0` and `T > 0` with
`λ T² ≤ η₀` (the source's "`λ T²` sufficiently small", line 59) there is
an entrance constant `C > 0`, chosen before the sequence, such that every real
sequence `N_j → ∞` has a subsequence `N_{φ(j)}` along which, with entrance
data `E` (`EntranceData T λ (λ κ a²/ℓ₃) C`: equations `scaling:odes` to
`scaling:matching`):

* `S_N → S` in `L¹([r, T])` for every `0 < r < T` (`L¹_loc((0, T])`);
* `d_N, 𝒦_N, 𝒫_N → d, K, P` uniformly on `[r, T]` for every `r > 0`;
* `ℋ_N → ℋ` uniformly on `[r, T] × [0, M]` for all `r > 0`, `M` (compact
  subsets of `(0, T] × [0, ∞)`);
* for almost every `t ∈ (0, T]`, `ν_N(t, ·) → ν_t` weakly (the measures of
  `scaling:laplace` are the limits of the rescaled measures, lines 248–259).

All moments are at `h_N = h_c + λ/N²` and `n = ⌊N t⌋`. -/
theorem scaling_compactness {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ lam T : ℝ, 0 ≤ lam → 0 < T → lam * T ^ 2 ≤ η₀ →
      ∃ C : ℝ, 0 < C ∧ ∀ Nseq : ℕ → ℝ, Tendsto Nseq atTop atTop →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ E : EntranceData T lam (lam * κ * Real.log B ^ 2 / ℓ₃) C,
            (∀ r : ℝ, 0 < r → r < T →
              Tendsto (fun j => timeIntegral
                (fun t => |scaledMass μ B lam (Nseq (φ j)) t - E.S t|) r T) atTop (𝓝 0)) ∧
            (∀ r : ℝ, 0 < r →
              TendstoUniformlyOn (fun j t => scaledDrift μ B lam (Nseq (φ j)) t) E.d atTop
                (Set.Icc r T)) ∧
            (∀ r : ℝ, 0 < r →
              TendstoUniformlyOn (fun j t => scaledSecond μ B lam (Nseq (φ j)) t) E.K atTop
                (Set.Icc r T)) ∧
            (∀ r : ℝ, 0 < r →
              TendstoUniformlyOn (fun j t => scaledThird μ B lam (Nseq (φ j)) t) E.P atTop
                (Set.Icc r T)) ∧
            (∀ r M : ℝ, 0 < r →
              TendstoUniformlyOn
                (fun j (p : ℝ × ℝ) => scaledCompensated μ B lam (Nseq (φ j)) p.1 p.2)
                (fun p => E.H p.1 p.2) atTop (Set.Icc r T ×ˢ Set.Icc 0 M)) ∧
            (∀ᵐ t, t ∈ Set.Ioc 0 T →
              WeakConvergence (fun j => scalingMeasure μ B lam (Nseq (φ j)) t) atTop (E.ν t)) := by
  exact scaling_compactness_aux hpos hmean hB hshift hℓ₃ hκ

/-! ### Weighted convergence before the pole (lines 45–54) -/

/-- `cont:continuation` (`scaling.tex` lines 45–54; proof in
`continuation.tex`). At `h_c > h_a`, with the residues `ℓ₃, κ` and
`γ = 3 a² κ/(2 ℓ₃)`: let `λ > 0`, `v = γ λ`, let `I ⊂ (0, T_v)` be compact and
let `s > 0` with `s + inf_{t ∈ I} b_v(t) > 0`. Then, as the real scale
`N → ∞`, `L_N(t, s) → F_v(t, s)` uniformly for `t ∈ I`
(`cont:transformconvergence`), and at each `t ∈ I`, `e^{-sx} ν_N(t, dx)`
converges weakly to `e^{-sx} f_v(t, x) dx`. -/
theorem continuation {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ γ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hγ : γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃)) {lam : ℝ} (hlam : 0 < lam)
    {I : Set ℝ} (hI : IsCompact I) (hIpole : ∀ t ∈ I, IsPrePoleTime (γ * lam) t)
    {s : ℝ} (hs : 0 < s) (hadm : 0 < s + sInf (profileB (γ * lam) '' I)) :
    TendstoUniformlyOn (fun N t => scaledTransform μ B lam N t s)
        (fun t => profileTransform (γ * lam) t s) atTop I ∧
      ∀ t ∈ I, WeakConvergence (fun N => weightedMeasure (scalingMeasure μ B lam N t) s) atTop
        (weightedMeasure (profileMeasure (γ * lam) t) s) := by
  exact continuation_aux hpos hmean hB hshift hℓ₃ hκ hγ hlam hI hIpole hs hadm

end DiamondPinning
