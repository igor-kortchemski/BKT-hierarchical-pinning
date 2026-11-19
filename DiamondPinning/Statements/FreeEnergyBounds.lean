module

public import DiamondPinning.Model.Defs
public import DiamondPinning.Model.LogMean
public import DiamondPinning.Model.Basic
public import DiamondPinning.Proofs.FreeEnergyBounds

/-!
# Key statements: the basic bounds of `lem:basic-bounds`

The parts of `lem:basic-bounds` (`source/critical.tex` lines 15–26) that the
other modules do not already state: the deterministic floor, the
finite-size bounds `eq:finitesize`, nonnegativity and the field increments of
the free energy, and `h_a ≤ h_c` (with `h_a = log c`, `c = B - 1`).
(Existence of `F` and `F(h_c) = 0` are `freeEnergy_tendsto` and
`criticalPoint_isGreatest` in `DiamondPinning.Statements.Main`; the moment
bounds are `integrable_lawR`, `integrable_tiltedLogPower` there.)

Standing assumptions: `μ` is the law of `W` (a probability measure with
`W > 0` a.s. and `E W = 1`) and `B > 2`; `b_n = floorSeq B n`, `ρ = 2/B`,
`a = log B`.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology

/-- `lem:basic-bounds`, the floor (`critical.tex` line 16): at every field,
`R_n ≥ b_n` almost surely for every `n`; `b_n` is nondecreasing with limit `1`
and `1 - b_n ≤ ρ^n`. -/
theorem floor_bounds {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) :
    (∀ n : ℕ, ∀ᵐ x ∂(lawR μ B h n), floorSeq B n ≤ x) ∧ Monotone (floorSeq B) ∧
      Tendsto (floorSeq B) atTop (𝓝 1) ∧ ∀ n : ℕ, 1 - floorSeq B n ≤ (2 / B) ^ n := by
  exact floor_bounds_aux hpos hB h

/-- `eq:finitesize` (`critical.tex` lines 20–23): for `n ≥ 1`,
`2^{-n}(E log R_n - a) ≤ F(h) ≤ 2^{-n}(E log R_n - log b_n)`. -/
theorem finiteSize_bounds {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {n : ℕ} (hn : 1 ≤ n) :
    ((2 : ℝ) ^ n)⁻¹ * (logMean μ B h n - Real.log B) ≤ freeEnergy μ B h ∧
      freeEnergy μ B h ≤ ((2 : ℝ) ^ n)⁻¹ * (logMean μ B h n - Real.log (floorSeq B n)) := by
  exact finiteSize_bounds_aux hpos hmean hB h hn

/-- `lem:basic-bounds` (`critical.tex` line 20): the free energy is
nonnegative. -/
theorem freeEnergy_nonneg {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ) :
    0 ≤ freeEnergy μ B h := by
  exact freeEnergy_nonneg_aux hpos hmean hB h

/-- `lem:basic-bounds` (`critical.tex` line 24): `0 ≤ F(h+u) - F(h) ≤ u` for
`u ≥ 0`. -/
theorem freeEnergy_increment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ freeEnergy μ B (h + u) - freeEnergy μ B h ∧
      freeEnergy μ B (h + u) - freeEnergy μ B h ≤ u := by
  exact freeEnergy_increment_aux hpos hmean hB h hu

/-- `lem:basic-bounds` (`critical.tex` line 25): `h_a ≤ h_c`, with
`h_a = log c = log (B - 1)` (finiteness of `h_c` is that `criticalPoint` is a
real number with `F(h_c) = 0`, `criticalPoint_isGreatest`). -/
theorem logShift_le_criticalPoint {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    Real.log (B - 1) ≤ criticalPoint μ B := by
  exact logShift_le_criticalPoint_aux hpos hmean hB

end DiamondPinning
