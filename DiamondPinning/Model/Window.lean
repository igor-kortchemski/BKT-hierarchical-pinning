module

public import DiamondPinning.Model.Moments

/-!
# Auxiliary moments of the field response (Section 4)

* `absTiltedLogRpowMoment μ B h s n = E[R_n(h)^θ |log R_n(h) - a|^s]` for a
  real exponent `s ≥ 0` (the case `s = 7/2` is `response:windowSevenHalves`,
  `source/response.tex` line 281);
* `kernelPsi B s = ψ(s) = (s + c)^θ log((s + c)/B²) - s^θ log(s/B²)`, `c = B - 1`
  (`response.tex` line 185), and `kernelMean μ B h n = E ψ(S_n)` with
  `S_n = R_n^{(1)}(h) R_n^{(2)}(h)`, the kernel term of
  `H_{n+1} = A_n H_n + ½ E ψ(S_n)` (`response.tex` line 193).
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory

/-- The absolute tilted logarithmic moment with a real exponent,
`E[R_n(h)^θ |log R_n(h) - a|^s]`, `a = log B`. -/
noncomputable def absTiltedLogRpowMoment (μ : Measure ℝ) (B h s : ℝ) (n : ℕ) : ℝ :=
  ∫ x, x ^ theta B * |Real.log x - Real.log B| ^ s ∂(lawR μ B h n)

/-- The kernel `ψ(s) = (s + c)^θ log((s + c)/B²) - s^θ log(s/B²)`, `c = B - 1`. -/
noncomputable def kernelPsi (B s : ℝ) : ℝ :=
  (s + (B - 1)) ^ theta B * Real.log ((s + (B - 1)) / B ^ 2) -
    s ^ theta B * Real.log (s / B ^ 2)

/-- The kernel term `E ψ(S_n)`, `S_n = R_n^{(1)}(h) R_n^{(2)}(h)` for two
independent copies of `R_n(h)`. -/
noncomputable def kernelMean (μ : Measure ℝ) (B h : ℝ) (n : ℕ) : ℝ :=
  ∫ s, kernelPsi B s ∂(productLaw μ B h n)

/-- The average `h ↦ ∫ f e h dν(e)` of a family of functions of the field `h`
used by the differentiation envelope. -/
noncomputable def fieldMean {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (f : Ω → ℝ → ℝ)
    (h : ℝ) : ℝ :=
  ∫ e, f e h ∂ν

end DiamondPinning
