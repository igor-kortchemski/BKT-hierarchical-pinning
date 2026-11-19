module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Proofs.ProfileProof
public import DiamondPinning.Proofs.ProductAssembly
public import DiamondPinning.Proofs.ResponseAssembly

/-!
# `th:profile-identification` at `h_c`

Assembles `DiamondPinning.profile_identification` (in
`DiamondPinning.Statements.Profile`) from the conditional theorem `profile_identification_of`
(`DiamondPinning.Proofs.ProfileProof`),
with `th:product` (`criticalProduct_aux`) and `th:response`
(`response_transversality_aux`).
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Asymptotics

/-- `th:profile-identification` at `h_c > h_a`. -/
theorem profile_identification_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
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
        ∀ᵐ t, t ∈ Set.Ioo 0 Tstar → E.ν t = profileMeasure (γ * lam) t :=
  profile_identification_of hpos hmean hB hshift hℓ₃ hκ
    (criticalProduct_aux hpos hmean hB hshift)
    (response_transversality_aux hpos hmean hB hshift) hγ hlam hT hC

end DiamondPinning
