module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Model.FreeEnergy
public import DiamondPinning.Proofs.ProductAssembly
public import DiamondPinning.Proofs.ResponseAssembly
public import DiamondPinning.Proofs.FieldDerivProof
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Assembly of `th:bkt`, conditional on four asymptotic inputs

`bkt_of` proves the conclusion of `DiamondPinning.bkt`
(`DiamondPinning.Statements.Main`) from the proved `th:product`
(`criticalProduct_aux`), `th:response` (`response_transversality_aux`), the
differentiability of `H_n` (`hasDerivAt_tiltedLogMoment_aux`) and the basic
properties of `F` and `h_c`, with four further asymptotic results as
hypotheses, each quantified over the residues:
`exact_critical` and `gamma_eq_limit` (`Statements/Profile.lean`),
`freeEnergy_upper` and `escape_constant` (`Statements/Escape.lean`).
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Asymptotics

/-- `F(h_c + u) > 0` for `u > 0`: `F ≥ 0` and `h_c` is the greatest zero
of `F`. -/
theorem freeEnergy_pos_above_critical {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (u : ℝ) (hu : 0 < u) : 0 < freeEnergy μ B (criticalPoint μ B + u) := by
  rcases (freeEnergy_nonneg_aux hpos hmean hB (criticalPoint μ B + u)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hle := (criticalPoint_isGreatest_aux hpos hmean hB).2 (show
      criticalPoint μ B + u ∈ {h : ℝ | freeEnergy μ B h = 0} from h.symm)
    linarith

/-- The substitution `N = u^{-1/2}`: `N → ∞` as `u ↓ 0`. -/
theorem tendsto_sqrt_inv_nhdsGT_zero :
    Tendsto (fun u : ℝ => Real.sqrt u⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_inv_nhdsGT_zero

/-- Theorem `th:bkt`, conditional on `exact_critical`, `gamma_eq_limit`,
`freeEnergy_upper` and `escape_constant`, which enter as hypotheses
quantified over the residues. -/
theorem bkt_of {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B)
    (hExact : ∀ ℓ₃ : ℝ,
      Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
        tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃) →
      Tendsto (fun n : ℕ => (n : ℝ) * (tiltedMass μ B (criticalPoint μ B) n - 1))
          atTop (𝓝 2) ∧
        Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 2 n /
          (Real.log B ^ 2 * (n : ℝ))) atTop (𝓝 1) ∧
        Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
          (Real.log B ^ 3 * (n : ℝ) ^ 2)) atTop (𝓝 (3 / 2)) ∧
        Tendsto (fun n : ℕ => tiltedProduct μ B (criticalPoint μ B) n / (n : ℝ) ^ 2) atTop
          (𝓝 (3 * Real.log B ^ 3 / (2 * ℓ₃))))
    (hGamma : ∀ ℓ₃ κ γ : ℝ,
      Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
        tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃) →
      Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
        tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ) →
      γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃) →
      Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
        (Real.log B * (n : ℝ) ^ 2)) atTop (𝓝 γ))
    (hUpper : ∀ ℓ₃ κ γ : ℝ,
      Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
        tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃) →
      Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
        tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ) →
      γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃) →
      ∀ ε > 0, ∀ᶠ u in 𝓝[>] (0 : ℝ),
        Real.sqrt u * Real.log (freeEnergy μ B (criticalPoint μ B + u)) ≤
          -(Real.pi * Real.log 2) / Real.sqrt γ + ε)
    (hConst : ∀ ℓ₃ κ γ : ℝ,
      Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
        tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃) →
      Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
        tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ) →
      γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃) → ∀ lam : ℝ, 0 < lam →
      ∀ ε > 0, ∀ᶠ N : ℝ in atTop,
        0 < freeEnergy μ B (criticalPoint μ B + lam / N ^ 2) ∧
          -(Real.pi / Real.sqrt (γ * lam)) * Real.log 2 - ε ≤
            N⁻¹ * Real.log (freeEnergy μ B (criticalPoint μ B + lam / N ^ 2))) :
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
  obtain ⟨-, -, -, -, ⟨ℓ₃, hℓ₃pos, hℓ₃⟩, -⟩ := criticalProduct_aux hpos hmean hB hshift
  obtain ⟨κ, hκpos, hκ, -⟩ := response_transversality_aux hpos hmean hB hshift
  set γ : ℝ := 3 * Real.log B ^ 2 * κ / (2 * ℓ₃) with hγ
  have ha : 0 < Real.log B := Real.log_pos (by linarith)
  have hγpos : 0 < γ := by positivity
  refine ⟨ℓ₃, κ, γ, hℓ₃pos, hκpos, rfl, hℓ₃, fun n => ?_, hκ, ?_, hGamma ℓ₃ κ γ hℓ₃ hκ rfl,
    fun u hu => freeEnergy_pos_above_critical hpos hmean hB u hu, ?_⟩
  · exact (hasDerivAt_tiltedLogMoment_aux hpos hmean hB (criticalPoint μ B) 1 n).differentiableAt
  · -- `Π_n ∼ 3 a³ n² / (2 ℓ₃)` from `Π_n / n² → 3 a³ / (2 ℓ₃) > 0`.
    have hc : 0 < 3 * Real.log B ^ 3 / (2 * ℓ₃) := by positivity
    have hlim := ((hExact ℓ₃ hℓ₃).2.2.2).div_const (3 * Real.log B ^ 3 / (2 * ℓ₃))
    rw [div_self hc.ne'] at hlim
    refine isEquivalent_of_tendsto_one (hlim.congr fun n => ?_)
    change _ = tiltedProduct μ B (criticalPoint μ B) n /
      (3 * Real.log B ^ 3 * (n : ℝ) ^ 2 / (2 * ℓ₃))
    rw [div_div]
    congr 1
    ring
  · -- The BKT limit: upper bound from `freeEnergy_upper`, lower bound from
    -- `escape_constant` with `λ = 1` and `N = u^{-1/2}`.
    set L : ℝ := -(Real.pi * Real.log 2) / Real.sqrt γ with hL
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · have hε : 0 < (L - b) / 2 := by linarith
      have hN := (hConst ℓ₃ κ γ hℓ₃ hκ rfl 1 one_pos _ hε)
      have hev := tendsto_sqrt_inv_nhdsGT_zero.eventually hN
      filter_upwards [hev, self_mem_nhdsWithin] with u hu hu0
      have hu0' : (0 : ℝ) < u := hu0
      have h1 : (Real.sqrt u⁻¹)⁻¹ = Real.sqrt u := by rw [Real.sqrt_inv, inv_inv]
      have h2 : (1 : ℝ) / Real.sqrt u⁻¹ ^ 2 = u := by
        rw [Real.sq_sqrt (inv_nonneg.2 hu0'.le), one_div, inv_inv]
      rw [h1, h2, mul_one] at hu
      have h3 : -(Real.pi / Real.sqrt γ) * Real.log 2 = L := by rw [hL]; ring
      linarith [hu.2]
    · have hε : 0 < (b - L) / 2 := by linarith
      filter_upwards [hUpper ℓ₃ κ γ hℓ₃ hκ rfl _ hε] with u hu
      linarith

end DiamondPinning
