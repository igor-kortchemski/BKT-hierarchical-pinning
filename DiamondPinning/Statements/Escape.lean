module

public import DiamondPinning.Model.Basic
public import DiamondPinning.Model.Hard
public import DiamondPinning.Proofs.Escape
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Free-energy asymptotics

Section 8 of the paper (`source/escape.tex`): `cont:freeenergyupper`
(lines 11–36), the hard recursion and `F_d` (lines 45–50), `escape:pairs`
(lines 52–94), `escape:band-exit` (lines 96–154), `escape:comparison`
(lines 156–189) and `escape:constant` (lines 199–239).

The hard free energy takes values in `[0, ∞]`:
`F_d(ν) = inf_j 2^{-j} E Y_j` for every law `ν` on `ℕ`, which is the source's
limit (`hardFreeEnergy_tendsto`), with a real specialization when
`E Y_0 < ∞` (`hardFreeEnergy_real`). The hard statements hold for every
initial law on `ℕ` and need no model assumption.

`cont:freeenergyupper` and `escape:constant` are results about the model
under `h_c > h_a`. Their constant `γ = 3 a² κ / (2 ℓ₃)` (`eq:gamma`) is that
of `th:bkt`; the residues `ℓ₃ = lim J_n / Π_n` and
`κ = lim ∂_h H_n(h_c) / Π_n` enter as real parameters with their defining
limits as hypotheses (the limits exist by `th:product` and `th:response`, and
are unique). For `λ > 0`, `v = γ λ` and `T_v = π / √v`. The `limsup` and
`liminf` of the source are stated in eventual form.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology
open scoped ENNReal

/-! ### The hard free energy (lines 45–50, 145–151) -/

/-- Definition of `F_d` (`escape.tex` lines 45–50, and lines 145–146): for
every probability law `ν` on `ℕ`, the sequence `2^{-j} E Y_j ∈ [0, ∞]` is
nonincreasing and converges to `F_d(ν) = inf_j 2^{-j} E Y_j`. -/
theorem hardFreeEnergy_tendsto (ν : Measure ℕ) [IsProbabilityMeasure ν] :
    Antitone (fun j : ℕ => ((2 : ℝ≥0∞) ^ j)⁻¹ * hardMean ν j) ∧
      Tendsto (fun j : ℕ => ((2 : ℝ≥0∞) ^ j)⁻¹ * hardMean ν j) atTop
        (𝓝 (hardFreeEnergy ν)) := by
  exact hardFreeEnergy_tendsto_aux ν

/-- `escape:finite-hard` (`escape.tex` lines 146–151): for every probability law
`ν` on `ℕ` and every `j`, `F_d ≥ 2^{-j} (E Y_j - 1)` (truncated subtraction in
`[0, ∞]`). -/
theorem hardFreeEnergy_ge (ν : Measure ℕ) [IsProbabilityMeasure ν] (j : ℕ) :
    ((2 : ℝ≥0∞) ^ j)⁻¹ * (hardMean ν j - 1) ≤ hardFreeEnergy ν := by
  exact hardFreeEnergy_ge_aux ν j

/-- Real specialization of `F_d` (`escape.tex` line 48):
if `E Y_0 < ∞`, then every `E Y_j` and `F_d` are finite and
`2^{-j} E Y_j → F_d` in `ℝ`. -/
theorem hardFreeEnergy_real (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (hfin : hardMean ν 0 ≠ ∞) :
    (∀ j, hardMean ν j ≠ ∞) ∧ hardFreeEnergy ν ≠ ∞ ∧
      Tendsto (fun j : ℕ => ((2 : ℝ) ^ j)⁻¹ * (hardMean ν j).toReal) atTop
        (𝓝 (hardFreeEnergy ν).toReal) := by
  exact hardFreeEnergy_real_aux ν hfin

/-! ### Pair counting and the band criterion (lines 52–154) -/

/-- `escape:pairs` (`escape.tex` lines 52–61, `escape:pair-tail`): for every
initial law `ν` on `ℕ`, every integer `L ≥ 2`, every `I ⊆ {⌈3L/4⌉, …, L}` and
`M_I = E[2^{Y_0} 1{Y_0 ∈ I}]`,
`P(Y_L ≥ k) ≥ 2^{-k} · 2 (M_I / (M_I + 2))²` for `1 ≤ k ≤ ⌊L/2⌋`. -/
theorem escape_pairs (ν : Measure ℕ) [IsProbabilityMeasure ν] {L : ℕ} (hL : 2 ≤ L)
    {I : Finset ℕ} (hI : I ⊆ upperBand L) {k : ℕ} (hk : 1 ≤ k) (hkL : k ≤ L / 2) :
    ((2 : ℝ) ^ k)⁻¹ * 2 * (bandMoment ν I / (bandMoment ν I + 2)) ^ 2 ≤
      (hardLaw ν L).real {y | k ≤ y} := by
  exact escape_pairs_aux ν hL hI hk hkL

/-- `escape:band-exit` (`escape.tex` lines 96–107), with the constants
`D_* = L_* = 10^4` that the source allows (which give the existence of the
absolute constants): for every initial law `ν` on `ℕ`, if `L ≥ L_*` and
`L E[2^{Y_0} 1{⌈3L/4⌉ ≤ Y_0 ≤ L}] ≥ D_*` (`escape:band-condition`), then
`E Y_T ≥ 3/2` for some integer `T ≤ 2L`, and `F_d ≥ ½ 2^{-2L}`
(`escape:hard-energy`). -/
theorem escape_bandExit (ν : Measure ℕ) [IsProbabilityMeasure ν] {L : ℕ}
    (hL : 10 ^ 4 ≤ L) (hband : (10 : ℝ) ^ 4 ≤ L * bandMoment ν (upperBand L)) :
    (∃ T : ℕ, T ≤ 2 * L ∧ (3 / 2 : ℝ≥0∞) ≤ hardMean ν T) ∧
      2⁻¹ * ((2 : ℝ≥0∞) ^ (2 * L))⁻¹ ≤ hardFreeEnergy ν := by
  exact escape_bandExit_of_pairs (fun ν _ _ hL _ hI _ hk hkL => escape_pairs ν hL hI hk hkL) ν hL hband

/-! ### Exact coupling at the deterministic floor (lines 156–189) -/

/-- `escape:comparison` (`escape.tex` lines 158–175): fix a field `h` and
`n ≥ 1`, and let `μ_*` be the law of `Y_0 = ⌊log(R_n/b_n)/a_n⌋`,
`a_n = log(B/b_n)` (`escape:normalization`). Then `μ_*` has finite mean and
`F(h) ≥ 2^{-n} a_n F_d(μ_*)` (`escape:energy-transfer`). If `μ_*`, or any law
`ν` on `ℕ` stochastically smaller than `μ_*`, satisfies
`escape:band-condition` (with `D_* = L_* = 10^4`), then
`F(h) ≥ (a_n/2) 2^{-n-2L}` (`escape:diamond-exit`). -/
theorem escape_comparison {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {n : ℕ} (hn : 1 ≤ n) :
    hardMean (floorHardLaw μ B h n) 0 ≠ ∞ ∧
      ((2 : ℝ) ^ n)⁻¹ * Real.log (B / floorSeq B n) *
          (hardFreeEnergy (floorHardLaw μ B h n)).toReal ≤ freeEnergy μ B h ∧
      ∀ (ν : Measure ℕ) [IsProbabilityMeasure ν],
        (∀ k : ℕ, ν {y | k ≤ y} ≤ floorHardLaw μ B h n {y | k ≤ y}) →
        ∀ L : ℕ, 10 ^ 4 ≤ L → (10 : ℝ) ^ 4 ≤ L * bandMoment ν (upperBand L) →
          Real.log (B / floorSeq B n) / 2 * ((2 : ℝ) ^ (n + 2 * L))⁻¹ ≤ freeEnergy μ B h := by
  exact escape_comparison_of_bandExit (fun ν _ _ hL hband => (escape_bandExit ν hL hband).2) hpos hmean hB h hn

/-! ### The two free-energy bounds (lines 11–36, 199–239) -/

/-- `cont:freeenergyupper` (`escape.tex` lines 11–17, `cont:upperconstant`): at
`h_c > h_a`, with `γ = 3 a² κ / (2 ℓ₃)`,
`limsup_{u ↓ 0} √u log F(h_c + u) ≤ -π log 2 / √γ`, in eventual form: for every
`ε > 0`, eventually as `u ↓ 0`, `√u log F(h_c + u) ≤ -π log 2 / √γ + ε`.
Since Lean's `Real.log 0 = 0`, this eventual form also forces `F(h_c + u) > 0`
for small `u > 0`; that holds by `lem:basic-bounds` (`F > 0` above `h_c`). The
hypotheses on `ℓ₃, κ, γ` are the defining limits of `eq:constants` and
`eq:gamma`, proved by `th:product` and `th:response`, so `γ > 0`. -/
theorem freeEnergy_upper {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ γ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hγ : γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃)) :
    ∀ ε > 0, ∀ᶠ u in 𝓝[>] (0 : ℝ),
      Real.sqrt u * Real.log (freeEnergy μ B (criticalPoint μ B + u)) ≤
        -(Real.pi * Real.log 2) / Real.sqrt γ + ε := by
  exact freeEnergy_upper_aux hpos hmean hB hshift hℓ₃ hκ hγ

/-- `escape:constant` (`escape.tex` lines 199–205, `escape:liminf`): at
`h_c > h_a`, with `γ = 3 a² κ / (2 ℓ₃)`, for every fixed `λ > 0`, `v = γ λ` and
`T_v = π / √v`, `liminf_{N → ∞} N⁻¹ log F(h_c + λ/N²) ≥ -T_v log 2` along real
`N`, in eventual form: for every `ε > 0`, for all large real `N`,
`F(h_c + λ/N²) > 0` (so that the logarithm is the source's) and
`N⁻¹ log F(h_c + λ/N²) ≥ -T_v log 2 - ε`. -/
theorem escape_constant {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ γ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hγ : γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃)) {lam : ℝ} (hlam : 0 < lam) :
    ∀ ε > 0, ∀ᶠ N : ℝ in atTop,
      0 < freeEnergy μ B (criticalPoint μ B + lam / N ^ 2) ∧
        -(Real.pi / Real.sqrt (γ * lam)) * Real.log 2 - ε ≤
          N⁻¹ * Real.log (freeEnergy μ B (criticalPoint μ B + lam / N ^ 2)) := by
  exact escape_constant_aux hpos hmean hB hshift hℓ₃ hκ hγ hlam

end DiamondPinning
