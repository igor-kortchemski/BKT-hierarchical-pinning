module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Model.LogMean
public import DiamondPinning.Model.FreeEnergy
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Basic free-energy bounds

This module proves the deterministic-floor bounds, the finite-size sandwich
for the free energy, its nonnegativity and field-increment estimate, and the
comparison of the annealed and quenched critical fields. These are the parts
of `lem:basic-bounds` in `source/critical.tex` lines 15–26, using the proof at
lines 28–54.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology

/-- The partition functions dominate the deterministic floor, which increases
to one at the geometric rate `2 / B`. This proves the frozen `floor_bounds`. -/
theorem floor_bounds_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) :
    (∀ n : ℕ, ∀ᵐ x ∂(lawR μ B h n), floorSeq B n ≤ x) ∧ Monotone (floorSeq B) ∧
      Tendsto (floorSeq B) atTop (𝓝 1) ∧ ∀ n : ℕ, 1 - floorSeq B n ≤ (2 / B) ^ n := by
  exact ⟨ae_floorSeq_le_lawR hpos hB h, floorSeq_monotone hB,
    tendsto_floorSeq hB, one_sub_floorSeq_le hB⟩

/-- The normalized height-`n` logarithmic mean, shifted by `Real.log B` or by
the logarithm of the floor, bounds the free energy from below and above. This
proves the frozen `finiteSize_bounds`. -/
theorem finiteSize_bounds_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {n : ℕ} (hn : 1 ≤ n) :
    ((2 : ℝ) ^ n)⁻¹ * (logMean μ B h n - Real.log B) ≤ freeEnergy μ B h ∧
      freeEnergy μ B h ≤ ((2 : ℝ) ^ n)⁻¹ * (logMean μ B h n - Real.log (floorSeq B n)) := by
  have hu_mono : Monotone (logLowerSeq μ B h) :=
    monotone_nat_of_le_succ (logLowerSeq_step hpos hmean hB h)
  have hv_anti : Antitone (logUpperSeq μ B h) :=
    antitone_nat_of_succ_le (logUpperSeq_step hpos hmean hB h)
  have hS := freeEnergy_tendsto_aux hpos hmean hB h
  have hpow0 : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
    have hh := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (1 : ℝ) / 2) (by norm_num : (1 : ℝ) / 2 < 1)
    have heq : (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) = fun n => ((1 : ℝ) / 2) ^ n := by
      ext n
      simp
    rw [heq]
    exact hh
  have hlower' : Tendsto
      (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * logMoment μ B h n -
        ((2 : ℝ) ^ n)⁻¹ * Real.log B) atTop (𝓝 (freeEnergy μ B h)) := by
    simpa using hS.sub (hpow0.mul_const (Real.log B))
  have hEqLower : (fun n : ℕ => logLowerSeq μ B h n) =ᶠ[atTop]
      fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * logMoment μ B h n -
        ((2 : ℝ) ^ n)⁻¹ * Real.log B := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    simp only [logLowerSeq, max_eq_left hn]
    ring
  have hlower : Tendsto (logLowerSeq μ B h) atTop (𝓝 (freeEnergy μ B h)) :=
    hlower'.congr' hEqLower.symm
  have hupper' : Tendsto
      (fun n : ℕ => logLowerSeq μ B h n +
        (logUpperSeq μ B h n - logLowerSeq μ B h n)) atTop
      (𝓝 (freeEnergy μ B h)) := by
    simpa using hlower.add (logSeq_difference_tendsto (μ := μ) (B := B) (h := h) hB)
  have hEqUpper : (fun n : ℕ => logUpperSeq μ B h n) =ᶠ[atTop]
      fun n : ℕ => logLowerSeq μ B h n +
        (logUpperSeq μ B h n - logLowerSeq μ B h n) := by
    filter_upwards [] with n
    ring
  have hupper : Tendsto (logUpperSeq μ B h) atTop (𝓝 (freeEnergy μ B h)) :=
    hupper'.congr' hEqUpper.symm
  constructor
  · have hbound := hu_mono.ge_of_tendsto hlower n
    simpa only [logLowerSeq, logMean, logMoment, max_eq_left hn] using hbound
  · have hbound := hv_anti.le_of_tendsto hupper n
    simpa only [logUpperSeq, logMean, logMoment, max_eq_left hn] using hbound

/- Nonnegativity is proved by `freeEnergy_nonneg_aux` in `Model.FreeEnergy`. -/

/-- A nonnegative field increment changes the free energy by a nonnegative
amount at most equal to the increment, proving the frozen
`freeEnergy_increment`. -/
theorem freeEnergy_increment_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ freeEnergy μ B (h + u) - freeEnergy μ B h ∧
      freeEnergy μ B (h + u) - freeEnergy μ B h ≤ u := by
  constructor
  · exact sub_nonneg.mpr (freeEnergy_monotone_aux hpos hmean hB (by linarith : h ≤ h + u))
  · have hlip := (freeEnergy_lipschitz_aux hpos hmean hB).dist_le_mul (h + u) h
    rw [Real.dist_eq, Real.dist_eq] at hlip
    have hnonneg : 0 ≤ freeEnergy μ B (h + u) - freeEnergy μ B h :=
      sub_nonneg.mpr (freeEnergy_monotone_aux hpos hmean hB (by linarith : h ≤ h + u))
    rw [abs_of_nonneg hnonneg, abs_of_nonneg (by linarith : 0 ≤ (h + u) - h)] at hlip
    simpa using hlip

/-- The annealed critical field `Real.log (B - 1)` is at most the constructed
quenched critical point, proving the frozen `logShift_le_criticalPoint`. -/
theorem logShift_le_criticalPoint_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) :
    Real.log (B - 1) ≤ criticalPoint μ B := by
  exact (criticalPoint_isGreatest_aux hpos hmean hB).2
    (freeEnergy_logc_eq_zero_aux hpos hmean hB)

end DiamondPinning
