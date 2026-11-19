module

public import DiamondPinning.Model.Defs

/-!
# The logarithmic mean `E log R_n(h)`

The quantity of the finite-size bounds `eq:finitesize` (`source/critical.tex`
lines 15–26), defined here so that the statements using it do not elaborate
an integral themselves.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory

/-- The logarithmic mean `m_n(h) = E log R_n(h)`. -/
noncomputable def logMean (μ : Measure ℝ) (B h : ℝ) (n : ℕ) : ℝ :=
  ∫ x, Real.log x ∂(lawR μ B h n)

end DiamondPinning
