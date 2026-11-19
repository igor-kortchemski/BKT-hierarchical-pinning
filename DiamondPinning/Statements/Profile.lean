module

public import DiamondPinning.Model.Basic
public import DiamondPinning.Model.Scaling
public import DiamondPinning.Model.Profile
public import DiamondPinning.Proofs.Profile

/-! # Identification of the limiting profile

Section 6 of the paper (`source/profile.tex`): `th:profile-identification`
(lines 8–19) with `eq:exact-critical`, and the second expression of `γ` in
`eq:gamma` (`bkt_diamond_simplified.tex` lines 105–110), proved at
`profile.tex` lines 168–170. `lem:entire-bounds` is in
`DiamondPinning.Statements.EntireBounds`.

Standing assumptions as in `DiamondPinning.Statements.Scaling`: `μ` is the law
of `W` (a probability measure with `W > 0` a.s. and `E W = 1`), `B > 2`,
`a = log B`, `h_c > h_a`, and the residues `ℓ₃ = lim J_n/Π_n`,
`κ = lim ∂_h H_n(h_c)/Π_n` enter as real parameters with their defining limits
as hypotheses, with `γ = 3 a² κ/(2 ℓ₃)`. A subsequential limit of
`scaling:compactness` carries the entrance data
`EntranceData T λ (λ κ a²/ℓ₃) C`; its profile parameter is
`v = 3 α/2 = γ λ` with `α = λ κ a²/ℓ₃` (`profile.tex` line 154).
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology

/-- `th:profile-identification` (`profile.tex` lines 8–11). At `h_c > h_a`,
with the residues `ℓ₃, κ` and `γ = 3 a² κ/(2 ℓ₃)`: fix `λ ≥ 0`, `T > 0` and the
entrance constant `C > 0` of `scaling:compactness`. There is a common initial
interval `(0, T_*)`, `0 < T_* ≤ T`, chosen before the limit, such that every
subsequential limit of `scaling:compactness` with these constants (entrance
data `E : EntranceData T λ (λ κ a²/ℓ₃) C`) agrees on it with the profile:
`ν_t = f_v(t, x) dx` for almost every `t ∈ (0, T_*)`, `v = γ λ`. -/
theorem profile_identification {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ γ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hγ : γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃)) {lam T C : ℝ} (hlam : 0 ≤ lam)
    (hT : 0 < T) (hC : 0 < C) :
    ∃ Tstar : ℝ, 0 < Tstar ∧ Tstar ≤ T ∧
      ∀ E : EntranceData T lam (lam * κ * Real.log B ^ 2 / ℓ₃) C,
        ∀ᵐ t, t ∈ Set.Ioo 0 Tstar → E.ν t = profileMeasure (γ * lam) t := by
  exact profile_identification_aux hpos hmean hB hshift hℓ₃ hκ hγ hlam hT hC

/-- `th:profile-identification`, `eq:exact-critical` (`profile.tex`
lines 12–18): at `h_c > h_a`, with `ℓ₃ = lim J_n/Π_n`,
`n (A_n - 1) → 2`, `K_n/(a² n) → 1`, `J_n/(a³ n²) → 3/2` and
`Π_n/n² → 3 a³/(2 ℓ₃)`, all moments at `h_c`. -/
theorem exact_critical {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃)) :
    Tendsto (fun n : ℕ => (n : ℝ) * (tiltedMass μ B (criticalPoint μ B) n - 1))
        atTop (𝓝 2) ∧
      Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 2 n /
        (Real.log B ^ 2 * (n : ℝ))) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
        (Real.log B ^ 3 * (n : ℝ) ^ 2)) atTop (𝓝 (3 / 2)) ∧
      Tendsto (fun n : ℕ => tiltedProduct μ B (criticalPoint μ B) n / (n : ℝ) ^ 2) atTop
        (𝓝 (3 * Real.log B ^ 3 / (2 * ℓ₃))) := by
  exact exact_critical_aux hpos hmean hB hshift hℓ₃

/-- The second identity of `eq:gamma` (`bkt_diamond_simplified.tex`
lines 105–110), proved at `profile.tex` lines 168–170: at `h_c > h_a`, with the
residues `ℓ₃, κ` and `γ = 3 a² κ/(2 ℓ₃)`,
`∂_h H_n(h_c)/(a n²) → γ`. -/
theorem gamma_eq_limit {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ γ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hγ : γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃)) :
    Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      (Real.log B * (n : ℝ) ^ 2)) atTop (𝓝 γ) := by
  exact gamma_eq_limit_aux hpos hmean hB hshift hℓ₃ hκ hγ

end DiamondPinning
