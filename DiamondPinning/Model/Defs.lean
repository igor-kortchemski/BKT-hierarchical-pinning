module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Basic

/-!
# The diamond pinning model: definitions

Definitions of *BKT asymptotics for disordered pinning on the diamond
hierarchical lattice* (research draft of 18 November 2026), Section 1.1,
at the level of laws.

* `lawR μ B h n` is the law of `R_n(h)`: `R_0(h) = e^h W` with `W ∼ μ`, and
  `R_{n+1}(h)` has the law of `(X Y + (B - 1)) / B` for independent `X, Y`
  with the law of `R_n(h)` (equation `eq:model`).
* `freeEnergy μ B h` is `F(h) = lim_{n → ∞} 2^{-n} E log R_n(h)`.
* `criticalPoint μ B` is `h_c = sup {h | F(h) = 0}`.
* `theta B` is `θ = log 2 / log B`.
* `tiltedMass μ B h n` is `A_n(h) = E R_n(h)^θ`, `tiltedProduct μ B h n` is
  `Π_n(h) = ∏_{j < n} A_j(h)` (so `Π_0 = 1`), and
  `tiltedLogMoment μ B h k n` is `E[R_n(h)^θ (log R_n(h) - log B)^k]`; the
  paper's `H_n(h)` is the case `k = 1`, and its `J_n` the case `k = 3` at
  `h = h_c`.

Every quantity is a function of the law of `R_n(h)` at one fixed field `h`,
so the coupling of different fields in one environment, which the proofs use,
does not enter the statements. The limit, the supremum, the integrals and the
real powers are Mathlib's total operations; the theorems that give them their
intended meaning (existence of the limit, the zero set of `F`, integrability)
are proved separately.

This module contains only definitions, and is reached by the main
statement.
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
