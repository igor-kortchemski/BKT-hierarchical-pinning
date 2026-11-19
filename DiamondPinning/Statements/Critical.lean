module

public import DiamondPinning.Model.Moments
public import DiamondPinning.Model.Basic
public import DiamondPinning.Proofs.Critical
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Critical moments and the critical product

Sections 2 and 3 of the paper: `lem:mellin-correction`, the Jensen step
`eq:jensen` (proof of `prop:criticalmoments`, used again in `th:return`),
`prop:criticalmoments`, `lem:barrier`, `th:return` and `th:product`. The
remaining parts of `lem:basic-bounds` (the floor, the finite-volume bounds,
the field comparison) are proved in `DiamondPinning.Model.Basic` and
`DiamondPinning.Model.FreeEnergy`.

Standing assumptions: `μ` is the law of `W` (a probability measure with
`W > 0` a.s. and `E W = 1`), `B > 2`, `c = B - 1`, `a = log B`,
`θ = log 2 / log B`, `ρ = 2 / B`, `b_n = floorSeq B n`. Statements at `h_c`
assume `h_c > h_a = log c`.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Asymptotics

/-- `lem:mellin-correction`, equation `eq:C`: for `n ≥ 1` and `Re z < 1`,
`C_n(z) = z ∫_0^c E (S_n + t)^{z-1} dt`. -/
theorem correction_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z.re < 1) :
    correction μ B h n z = z * shiftedMomentIntegral μ B h n (z - 1) := by
  exact correction_eq_aux hpos hmean hB h hn hz

/-- `lem:mellin-correction`: for `n ≥ 1`, `C_n` is holomorphic on
`{Re z < 1}`. -/
theorem differentiableOn_correction {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {n : ℕ} (hn : 1 ≤ n) :
    DifferentiableOn ℂ (correction μ B h n) {z : ℂ | z.re < 1} := by
  exact differentiableOn_correction_aux hpos hmean hB h hn

/-- `lem:mellin-correction`: the functions `C_n`, `n ≥ 1`, are uniformly bounded
on every compact subset of `{Re z < 1}`. -/
theorem correction_bounded {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ {z : ℂ | z.re < 1}) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ z ∈ K, ‖correction μ B h n z‖ ≤ C := by
  exact correction_bounded_aux hpos hmean hB h hK hKsub

/-- Equation `eq:jensen` (proof of `prop:criticalmoments`), at every field: for
`0 < q < 1` and `s_n = G_n(q)^{1/q}`, `s_{n+1} ≥ (s_n² + c)/B`. -/
theorem jensen_step {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    ((realMoment μ B h n q ^ (1 / q)) ^ 2 + (B - 1)) / B ≤
      realMoment μ B h (n + 1) q ^ (1 / q) := by
  exact jensen_step_aux hpos hmean hB h hq0 hq1 n

/-- `prop:criticalmoments`. There is a constant `C_B`, depending only on `B`,
such that for every disorder and every field `h` with `F(h) = 0`, for all
`n ≥ 1`: `G_n(θ) ≤ c^θ` and `H_n(h) ≤ C_B ρ^n`; moreover
`sup_n E[R_n^θ |log R_n - a|] < ∞`. -/
theorem criticalMoments {B : ℝ} (hB : 2 < B) :
    ∃ C : ℝ, ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], (∀ᵐ w ∂μ, 0 < w) →
      ∫ w, w ∂μ = 1 → ∀ h : ℝ, freeEnergy μ B h = 0 →
        (∀ n : ℕ, 1 ≤ n →
          tiltedMass μ B h n ≤ (B - 1) ^ theta B ∧
          tiltedLogMoment μ B h 1 n ≤ C * (2 / B) ^ n) ∧
        ∃ M : ℝ, ∀ n : ℕ, absTiltedLogMoment μ B h 1 n ≤ M := by
  exact criticalMoments_aux hB

/-- `lem:barrier`: if `h_c > h_a`, then `G_n(q) ≥ b_n^q + B^q - 2` at `h_c`
for `θ < q < 1` and `n ≥ 1`. -/
theorem barrier {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {q : ℝ} (hq : theta B < q)
    (hq1 : q < 1) {n : ℕ} (hn : 1 ≤ n) :
    floorSeq B n ^ q + B ^ q - 2 ≤ realMoment μ B (criticalPoint μ B) n q := by
  exact barrier_aux hpos hmean hB hshift hq hq1 hn

/-- `th:return`: if `h_c > h_a`, then `liminf_n G_n(θ) = 1` at `h_c`, stated as:
`A_n < 1 + ε` for infinitely many `n`, and `A_n > 1 - ε` for all large `n`, for
every `ε > 0` (the sequence `A_n` is bounded, by `prop:criticalmoments`). -/
theorem returns_to_one {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) :
    (∀ ε > 0, ∃ᶠ n in atTop, tiltedMass μ B (criticalPoint μ B) n < 1 + ε) ∧
    (∀ ε > 0, ∀ᶠ n in atTop, 1 - ε < tiltedMass μ B (criticalPoint μ B) n) := by
  exact returns_to_one_aux hpos hmean hB hshift

/-- `th:product`, `eq:Hsmall`: there is `C_B`, depending only on `B`, with
`|H_n| ≤ C_B ((A_n - 1)^+ + ρ^n)` at `h_c` for all `n ≥ 1`, for every disorder
with `h_c > h_a`. -/
theorem criticalProduct_Hsmall {B : ℝ} (hB : 2 < B) :
    ∃ C : ℝ, ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], (∀ᵐ w ∂μ, 0 < w) →
      ∫ w, w ∂μ = 1 → Real.log (B - 1) < criticalPoint μ B → ∀ n : ℕ, 1 ≤ n →
        |tiltedLogMoment μ B (criticalPoint μ B) 1 n| ≤
          C * (max (tiltedMass μ B (criticalPoint μ B) n - 1) 0 + (2 / B) ^ n) := by
  exact criticalProduct_Hsmall_aux hB

/-- `th:product` (other parts), at `h_c > h_a`, with constants independent of
`n`: `C⁻¹ (n+1)² ≤ Π_n ≤ C (n+1)²`, `K_n² ≤ C Π_n` and `L_n ≤ C (n+1)³` for
`n ≥ 1` (`eq:product`, `eq:critical-fourth`); `Σ Π_n⁻¹ < ∞`;
`ℓ₃ = lim J_n / Π_n` exists in `(0, ∞)` (`eq:thirdresidue`); and
`eq:criticalrates`: `A_n - 1 ≍ n⁻¹`, `K_n ≍ n`, `H_n = O(n⁻¹)`, and `R_n → 1` in
probability. The sign is part of the rate: `A_n > 1` for all large `n`, so
`c/n ≤ A_n - 1 ≤ C/n` eventually. Here `K_n, J_n, L_n` are the tilted log
moments of orders 2, 3, 4. -/
theorem criticalProduct {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) :
    ∃ C : ℝ, 0 < C ∧
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
        atTop (𝓝 0) := by
  exact criticalProduct_aux hpos hmean hB hshift

end DiamondPinning
