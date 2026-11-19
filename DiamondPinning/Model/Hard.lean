module

public import DiamondPinning.Model.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The hard recursion (Section 8)

Definitions for Section 8 of the paper (`source/escape.tex`, lines 45–55 and
156–162), with the hard free energy in `[0, ∞]` (author decision 1, blueprint
E4):

* `hardLaw ν j`, the law of `Y_j` for the hard recursion
  `Y_{j+1} = (Y_j^{(1)} + Y_j^{(2)} - 1)^+` with independent copies and initial
  law `ν` on `ℕ` (truncated subtraction on `ℕ` is the positive part);
* `hardMean ν j = E Y_j ∈ [0, ∞]` (lower Lebesgue integral);
* `hardFreeEnergy ν = F_d = inf_j 2^{-j} E Y_j ∈ [0, ∞]`; the sequence
  `2^{-j} E Y_j` is nonincreasing, so this is the source's limit
  (`hardFreeEnergy_tendsto`);
* `bandMoment ν I = M_I = E[2^{Y_0} 1{Y_0 ∈ I}] = ∑_{r ∈ I} 2^r P(Y_0 = r)` for
  a finite set `I` (`escape:pairs`);
* `floorHardLaw μ B h n`, the law on `ℕ` of
  `Y_0 = ⌊log(R_n(h)/b_n) / a_n⌋`, `a_n = log(B/b_n)`, `b_n` the deterministic
  floor (`escape:normalization`); `Nat.floor` returns `0` on negative
  arguments, which `R_n ≥ b_n` excludes almost surely.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory
open scoped ENNReal

/-- The law of `Y_j` for the hard recursion `Y_{j+1} = (Y_j^{(1)} + Y_j^{(2)} - 1)^+`
with independent copies, started from the law `ν` on `ℕ`. -/
noncomputable def hardLaw (ν : Measure ℕ) (j : ℕ) : Measure ℕ :=
  Nat.rec ν (fun _ L => (L.prod L).map fun p : ℕ × ℕ => p.1 + p.2 - 1) j

/-- The extended mean `E Y_j ∈ [0, ∞]` of the hard recursion. -/
noncomputable def hardMean (ν : Measure ℕ) (j : ℕ) : ℝ≥0∞ :=
  ∫⁻ y, (y : ℝ≥0∞) ∂(hardLaw ν j)

/-- The hard free energy `F_d = inf_j 2^{-j} E Y_j ∈ [0, ∞]` (author
decision 1); it equals `lim_j 2^{-j} E Y_j`, the source's definition. -/
noncomputable def hardFreeEnergy (ν : Measure ℕ) : ℝ≥0∞ :=
  ⨅ j : ℕ, ((2 : ℝ≥0∞) ^ j)⁻¹ * hardMean ν j

/-- The band moment `M_I = E[2^{Y_0} 1{Y_0 ∈ I}] = ∑_{r ∈ I} 2^r P(Y_0 = r)` of
the law `ν` on a finite set `I ⊂ ℕ`. -/
noncomputable def bandMoment (ν : Measure ℕ) (I : Finset ℕ) : ℝ :=
  ∑ r ∈ I, (2 : ℝ) ^ r * ν.real {r}

/-- The upper-quarter band `{⌈3L/4⌉, …, L}` of `escape:pairs` and
`escape:band-condition`. -/
noncomputable def upperBand (L : ℕ) : Finset ℕ :=
  Finset.Icc ⌈(3 * L : ℝ) / 4⌉₊ L

/-- The law on `ℕ` of `Y_0 = ⌊log(R_n(h)/b_n) / a_n⌋`, `a_n = log(B/b_n)`,
`b_n = floorSeq B n` (`escape:normalization`). -/
noncomputable def floorHardLaw (μ : Measure ℝ) (B h : ℝ) (n : ℕ) : Measure ℕ :=
  (lawR μ B h n).map fun r =>
    ⌊Real.log (r / floorSeq B n) / Real.log (B / floorSeq B n)⌋₊

end DiamondPinning
