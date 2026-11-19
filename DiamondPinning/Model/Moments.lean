module

public import DiamondPinning.Model.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Mellin moments and the correction term (Section 2)

Definitions used by the statements of Sections 2 and 3 of the paper, at the
level of laws, at an arbitrary field `h`:

* `realMoment μ B h n q = G_n(q) = E R_n(h)^q` for real `q` (so
  `tiltedMass μ B h n = realMoment μ B h n (theta B)`);
* `absTiltedLogMoment μ B h k n = E[R_n(h)^θ |log R_n(h) - a|^k]`, `a = log B`;
* `productLaw μ B h n`, the law of `S_n = R_n^{(1)}(h) R_n^{(2)}(h)` for two
  independent copies;
* `correction μ B h n z = C_n(z) = E[(S_n + c)^z - S_n^z]` with `c = B - 1`;
* `shiftedMoment μ B h n t z = E (S_n + t)^z`, so that `eq:C` reads
  `C_n(z) = z ∫_0^c shiftedMoment μ B h n t (z - 1) dt`.

All integrals of this file are taken here, so that the statements using these
definitions do not elaborate an integral themselves.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory

/-- The real Mellin moment `G_n(q) = E R_n(h)^q`. -/
noncomputable def realMoment (μ : Measure ℝ) (B h : ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  ∫ x, x ^ q ∂(lawR μ B h n)

/-- The absolute tilted logarithmic moment `E[R_n(h)^θ |log R_n(h) - a|^k]`,
`a = log B`. -/
noncomputable def absTiltedLogMoment (μ : Measure ℝ) (B h : ℝ) (k n : ℕ) : ℝ :=
  ∫ x, x ^ theta B * |Real.log x - Real.log B| ^ k ∂(lawR μ B h n)

/-- The law of `S_n = R_n^{(1)}(h) R_n^{(2)}(h)`, the product of two independent
copies of `R_n(h)`. -/
noncomputable def productLaw (μ : Measure ℝ) (B h : ℝ) (n : ℕ) : Measure ℝ :=
  ((lawR μ B h n).prod (lawR μ B h n)).map fun p => p.1 * p.2

/-- The correction term `C_n(z) = E[(S_n + c)^z - S_n^z]`, `c = B - 1`, which
records the additive constant of the recursion. -/
noncomputable def correction (μ : Measure ℝ) (B h : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ s, (((s + (B - 1) : ℝ) : ℂ) ^ z - (s : ℂ) ^ z) ∂(productLaw μ B h n)

/-- The shifted moment `E (S_n + t)^z`. -/
noncomputable def shiftedMoment (μ : Measure ℝ) (B h : ℝ) (n : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  ∫ s, (((s + t : ℝ) : ℂ) ^ z) ∂(productLaw μ B h n)

/-- The integral `∫_0^c E (S_n + t)^z dt` of `eq:C`, with `c = B - 1`. -/
noncomputable def shiftedMomentIntegral (μ : Measure ℝ) (B h : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..(B - 1), shiftedMoment μ B h n t z

end DiamondPinning
