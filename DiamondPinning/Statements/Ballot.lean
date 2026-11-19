module

public import DiamondPinning.Proofs.Ballot
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Independence.Basic

/-!
# Passage estimate

Statement of the passage estimate `response:ballot` from
*BKT asymptotics for disordered pinning on the diamond hierarchical lattice*.
-/

@[expose] public section

namespace DiamondPinning

universe u

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Lemma `response:ballot` (`source/response.tex`, lines 28–39; proof at
lines 40–60). Let `Y j` be independent integrable real random variables and
put `S k = ∑ j < k, Y j`. For `b ≥ 0` and `η, δ > 0`, suppose that
`Y j ≥ -b` almost surely for `j ≥ 1`, `Y 0` has integrable negative part,
the positive parts of the expectations are summable, and
`P (S n ≥ η n) ≥ δ` eventually. Then there is a constant `C`, chosen after
all these hypotheses, such that for every `n` and every `z ≥ 0`,
`P (∀ k ≤ n, -z ≤ S k) ≤ C (z + 1) / (n + 1)`.

The separate integrability of the negative part of `Y 0` is implied by
integrability of `Y 0`; it is retained because the source states it explicitly.
The sums are written out rather than introducing a new definition of `S`. -/
theorem response_ballot {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hYindep : iIndepFun Y μ)
    (hYint : ∀ j, Integrable (Y j) μ) {b η δ : ℝ} (hb : 0 ≤ b) (hη : 0 < η)
    (hδ : 0 < δ) (hYlower : ∀ j, 1 ≤ j → ∀ᵐ ω ∂μ, -b ≤ Y j ω)
    (hY0neg : Integrable (fun ω => (Y 0 ω)⁻) μ)
    (hmean : Summable (fun j => (∫ ω, Y j ω ∂μ)⁺))
    (htail : ∀ᶠ n : ℕ in atTop,
      δ ≤ μ.real {ω | η * n ≤ ∑ j ∈ Finset.range n, Y j ω}) :
    ∃ C : ℝ, ∀ (n : ℕ) (z : ℝ), 0 ≤ z →
      μ.real {ω | ∀ k ≤ n, -z ≤ ∑ j ∈ Finset.range k, Y j ω} ≤
        C * (z + 1) / (n + 1) := by
  exact response_ballot_aux μ Y hYindep hYint hb hη hδ hYlower hY0neg hmean htail

/-- Lemma `response:ballot`, with the constant made explicit in its data (as
in the source's proof, `response.tex` lines 40–60): `C` depends only on `b`,
`η`, `δ`, a threshold `N₀` from which the tail bound holds, a bound `mNeg` on
`E Y_0^-` and a bound `mPos` on `Σ_j (E Y_j)^+`, and works for every probability
space and every sequence of independent integrable increments satisfying the
hypotheses with these data. -/
theorem response_ballot_uniform {b η δ mNeg mPos : ℝ} (N₀ : ℕ) (hb : 0 ≤ b) (hη : 0 < η)
    (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Y : ℕ → Ω → ℝ), iIndepFun Y μ → (∀ j, Integrable (Y j) μ) →
      (∀ j, 1 ≤ j → ∀ᵐ ω ∂μ, -b ≤ Y j ω) →
      ∫ ω, (Y 0 ω)⁻ ∂μ ≤ mNeg →
      Summable (fun j => (∫ ω, Y j ω ∂μ)⁺) →
      ∑' j, (∫ ω, Y j ω ∂μ)⁺ ≤ mPos →
      (∀ n : ℕ, N₀ ≤ n → δ ≤ μ.real {ω | η * n ≤ ∑ j ∈ Finset.range n, Y j ω}) →
      ∀ (n : ℕ) (z : ℝ), 0 ≤ z →
        μ.real {ω | ∀ k ≤ n, -z ≤ ∑ j ∈ Finset.range k, Y j ω} ≤
          C * (z + 1) / (n + 1) := by
  exact response_ballot_uniform_aux N₀ hb hη hδ

end DiamondPinning
