module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# BKT asymptotics for disordered pinning on the diamond hierarchical lattice

Statement of the main theorem (`th:bkt`) and of parts of the basic bounds
(`lem:basic-bounds`) of the paper, with the definitions they use.

Throughout, `μ` is the law of the disorder `W` (a probability measure on `ℝ`
with `W > 0` almost surely and `E W = 1`, as in the theorems), and `B > 2`.
`lawR μ B h n` is the law of `R_n(h)` in the recursion `eq:model`,
`R_0(h) = e^h W` and `R_{n+1}(h) = (R_n^{(1)}(h) R_n^{(2)}(h) + c) / B` with
independent copies and `c = B - 1`. The proofs are `sorry` in this file.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter

/-- The law of `R_n(h)` (equation `eq:model`, with `c = B - 1`) for the
disorder law `μ` and the parameter `B`: `R_0(h) = e^h W` with `W ∼ μ`, and
`R_{n+1}(h)` has the law of `(X Y + c) / B` where `X, Y` are independent with
the law of `R_n(h)`. -/
noncomputable def lawR (μ : Measure ℝ) (B h : ℝ) (n : ℕ) : Measure ℝ :=
  Nat.rec (μ.map fun w => Real.exp h * w)
    (fun _ L => (L.prod L).map fun p => (p.1 * p.2 + (B - 1)) / B) n

/-- The quenched free energy `F(h) = lim_{n → ∞} 2^{-n} E log R_n(h)`. The
limit exists for every `h` (`freeEnergy_tendsto`); `limUnder` would return an
unspecified value where no limit exists. -/
noncomputable def freeEnergy (μ : Measure ℝ) (B h : ℝ) : ℝ :=
  limUnder atTop fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * ∫ x, Real.log x ∂(lawR μ B h n)

/-- The critical point `h_c = sup {h | F(h) = 0}`. The set of zeros is
nonempty and bounded above and contains its supremum
(`criticalPoint_isGreatest`), so `sSup` is the true supremum. -/
noncomputable def criticalPoint (μ : Measure ℝ) (B : ℝ) : ℝ :=
  sSup {h : ℝ | freeEnergy μ B h = 0}

/-- The exponent `θ = log 2 / log B`. -/
noncomputable def theta (B : ℝ) : ℝ :=
  Real.log 2 / Real.log B

/-- The tilted mass `A_n(h) = E R_n(h)^θ`. -/
noncomputable def tiltedMass (μ : Measure ℝ) (B h : ℝ) (n : ℕ) : ℝ :=
  ∫ x, x ^ theta B ∂(lawR μ B h n)

/-- The product `Π_n(h) = ∏_{j < n} A_j(h)`; it includes `A_0` and `Π_0 = 1`. -/
noncomputable def tiltedProduct (μ : Measure ℝ) (B h : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, tiltedMass μ B h j

/-- The signed tilted logarithmic moment `E[R_n(h)^θ (log R_n(h) - a)^k]`,
with `a = log B`. The paper's `H_n(h)` is the case `k = 1` (at any field `h`);
its `J_n` is the case `k = 3` at `h = h_c`. -/
noncomputable def tiltedLogMoment (μ : Measure ℝ) (B h : ℝ) (k n : ℕ) : ℝ :=
  ∫ x, x ^ theta B * (Real.log x - Real.log B) ^ k ∂(lawR μ B h n)

end DiamondPinning

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Asymptotics

/-- `lem:basic-bounds`: `E R_n(h) < ∞` for every field `h` and every
`n ≥ 0`. -/
theorem integrable_lawR {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x) (lawR μ B h n) := by
  sorry

/-- `lem:basic-bounds`: `E[R_n(h)^θ |log R_n(h)|^q] < ∞` for every field `h`,
every `n ≥ 0` (including `n = 0`) and every real `q ≥ 0`. The case `q = 0`
makes `tiltedMass` a genuine expectation, and the cases `q = 0, …, k` do the
same for `tiltedLogMoment` with exponent `k`. -/
theorem integrable_tiltedLogPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) (n : ℕ)
    {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun x : ℝ => x ^ theta B * |Real.log x| ^ q) (lawR μ B h n) := by
  sorry

/-- `lem:basic-bounds` (implicit in `eq:finitesize` and its proof): for
`n ≥ 1`, `log R_n(h)` is integrable, so the terms
`2^{-n} E log R_n(h)` defining `F(h)` are genuine expectations from `n = 1` on
(at `n = 0` no logarithmic moment of `W` is assumed). -/
theorem integrable_log_lawR {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) {n : ℕ}
    (hn : 1 ≤ n) :
    Integrable Real.log (lawR μ B h n) := by
  sorry

/-- `lem:basic-bounds` (existence of the free energy): for every field `h`,
`2^{-n} E log R_n(h)` converges, so `freeEnergy μ B h` is this limit. -/
theorem freeEnergy_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) :
    Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * ∫ x, Real.log x ∂(lawR μ B h n)) atTop
      (𝓝 (freeEnergy μ B h)) := by
  sorry

/-- `lem:basic-bounds` (the critical point): `F` vanishes at `h_c`, and every
zero of `F` is at most `h_c`; in particular the set of zeros is nonempty and
bounded above, so `h_c` is a genuine supremum. (The lemma also gives
`h_a ≤ h_c`, which is not stated here.) -/
theorem criticalPoint_isGreatest {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    IsGreatest {h : ℝ | freeEnergy μ B h = 0} (criticalPoint μ B) := by
  sorry

/-- Theorem `th:bkt`. Let `B > 2` and let `μ` be the law of the disorder
`W > 0` with `E W = 1`. Suppose `h_c > h_a = log (B - 1)`. Write `a = log B`,
`Π_n = ∏_{j<n} E R_j(h_c)^θ`, `H_n(h) = E[R_n(h)^θ (log R_n(h) - a)]` and
`J_n = E[R_n(h_c)^θ (log R_n(h_c) - a)^3]`. Then:

* `ℓ₃ = lim J_n / Π_n` exists and is positive;
* each `H_n` is differentiable at `h_c`, and `κ = lim ∂_h H_n(h_c) / Π_n` exists
  and is positive;
* `Π_n ∼ 3 a³ n² / (2 ℓ₃)`;
* `γ = 3 a² κ / (2 ℓ₃) = lim ∂_h H_n(h_c) / (a n²)`;
* `F(h_c + u) > 0` for `u > 0`, and
  `lim_{u ↓ 0} √u log F(h_c + u) = -π log 2 / √γ`, so the BKT constant is
  `K = π log 2 / √γ`.

The differentiability of each `H_n` at `h_c` and the positivity of
`F(h_c + u)` are implicit in the paper's statement (it differentiates `H_n`
and takes `log F`) and are made explicit here. -/
theorem bkt {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) :
    ∃ ℓ₃ κ γ : ℝ, 0 < ℓ₃ ∧ 0 < κ ∧ γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃) ∧
      Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
        tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃) ∧
      (∀ n : ℕ, DifferentiableAt ℝ (fun h => tiltedLogMoment μ B h 1 n)
        (criticalPoint μ B)) ∧
      Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
        tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ) ∧
      (fun n : ℕ => tiltedProduct μ B (criticalPoint μ B) n) ~[atTop]
        (fun n : ℕ => 3 * Real.log B ^ 3 * (n : ℝ) ^ 2 / (2 * ℓ₃)) ∧
      Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
        (Real.log B * (n : ℝ) ^ 2)) atTop (𝓝 γ) ∧
      (∀ u : ℝ, 0 < u → 0 < freeEnergy μ B (criticalPoint μ B + u)) ∧
      Tendsto (fun u : ℝ => Real.sqrt u * Real.log (freeEnergy μ B (criticalPoint μ B + u)))
        (𝓝[>] 0) (𝓝 (-(Real.pi * Real.log 2) / Real.sqrt γ)) := by
  sorry

end DiamondPinning
