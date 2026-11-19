module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Proofs.ProductAssembly
public import DiamondPinning.Proofs.SpineProof
public import DiamondPinning.Proofs.ResponseLinear
public import DiamondPinning.Proofs.TransversalityProof
public import DiamondPinning.Proofs.ContactMomentsProof
public import DiamondPinning.Proofs.WindowProof

/-!
# Section 4 results at `h_c` from their conditional proofs

Assembles the frozen statements `response_linear`, `response_transversality`
and `contactMoments` from the conditional theorems `response_linear_of`,
`response_transversality_of`, `contactMoments_of`, with `th:product`
(`criticalProduct_aux`) and the spine identities (`spine_identities_aux`).
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Asymptotics

/-- `response:linear` at `h_c > h_a`. -/
theorem response_linear_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) :
    ∃ C : ℝ, ∀ n : ℕ,
      deriv (fun h => tiltedMass μ B h n) (criticalPoint μ B) ≤ C * ((n : ℝ) + 1) :=
  response_linear_of hpos hmean hB hshift (criticalProduct_aux hpos hmean hB hshift)
    (fun n => spine_identities_aux hpos hmean hB (criticalPoint μ B) n)

/-- `th:response` at `h_c > h_a`. -/
theorem response_transversality_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
        tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ) ∧
      (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B)) =Θ[atTop]
        fun n : ℕ => (n : ℝ) ^ 2 :=
  response_transversality_of hpos hmean hB hshift (criticalProduct_aux hpos hmean hB hshift)
    (fun n => spine_identities_aux hpos hmean hB (criticalPoint μ B) n)
    (response_linear_aux hpos hmean hB hshift)

/-- `prop:contact-moments` at `h_c > h_a`. -/
theorem contactMoments_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) :
    ∃ M L : ℝ,
      (∀ k n : ℕ, 1 ≤ k →
        contactMoment μ B (criticalPoint μ B) k n ≤
          (k.factorial : ℝ) * M * L ^ (k - 1) * ((n : ℝ) + 1) ^ (2 * k - 1)) ∧
      ∀ (n : ℕ) (u : ℝ), 0 ≤ u → L * u * ((n : ℝ) + 1) ^ 2 < 1 →
        contactExpMoment μ B (criticalPoint μ B) u n ≤
            M * u * ((n : ℝ) + 1) / (1 - L * u * ((n : ℝ) + 1) ^ 2) ∧
          tiltedMass μ B (criticalPoint μ B + u) n - tiltedMass μ B (criticalPoint μ B) n ≤
            M * u * ((n : ℝ) + 1) / (1 - L * u * ((n : ℝ) + 1) ^ 2) :=
  contactMoments_of hpos hmean hB hshift (criticalProduct_aux hpos hmean hB hshift)
    (response_linear_aux hpos hmean hB hshift)

/-- `prop:window-moments`, derivative bounds, at `h_c > h_a`. -/
theorem window_derivBounds_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ v : ℝ, 0 ≤ v →
      v * ((n : ℝ) + 1) ^ 2 ≤ η →
      |deriv (fun h => tiltedMass μ B h n) (criticalPoint μ B + v)| ≤ C * ((n : ℝ) + 1) ∧
        |deriv (deriv fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B + v)| ≤
          C * ((n : ℝ) + 1) ^ 4 ∧
        |deriv (fun h => tiltedLogMoment μ B h 2 n) (criticalPoint μ B + v)| ≤
          C * ((n : ℝ) + 1) ^ 3 ∧
        |deriv (fun h => tiltedLogMoment μ B h 3 n) (criticalPoint μ B + v)| ≤
          C * ((n : ℝ) + 1) ^ 4 :=
  window_derivBounds_of hpos hmean hB hshift (criticalProduct_aux hpos hmean hB hshift)
    (contactMoments_aux hpos hmean hB hshift)

/-- `prop:window-moments` at `h_c > h_a`. -/
theorem windowMoments_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ u : ℝ, 0 ≤ u →
      u * ((n : ℝ) + 1) ^ 2 ≤ η →
      |tiltedMass μ B (criticalPoint μ B + u) n - tiltedMass μ B (criticalPoint μ B) n| ≤
          C * u * ((n : ℝ) + 1) ∧
        |tiltedLogMoment μ B (criticalPoint μ B + u) 1 n -
            tiltedLogMoment μ B (criticalPoint μ B) 1 n -
            u * deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B)| ≤
          C * u ^ 2 * ((n : ℝ) + 1) ^ 4 ∧
        |tiltedLogMoment μ B (criticalPoint μ B + u) 2 n -
            tiltedLogMoment μ B (criticalPoint μ B) 2 n| ≤ C * u * ((n : ℝ) + 1) ^ 3 ∧
        |tiltedLogMoment μ B (criticalPoint μ B + u) 3 n -
            tiltedLogMoment μ B (criticalPoint μ B) 3 n| ≤ C * u * ((n : ℝ) + 1) ^ 4 ∧
        absTiltedLogRpowMoment μ B (criticalPoint μ B + u) (7 / 2) n ≤
          C * ((n : ℝ) + 1) ^ ((5 : ℝ) / 2) ∧
        |tiltedProduct μ B (criticalPoint μ B + u) n /
            tiltedProduct μ B (criticalPoint μ B) n - 1| ≤ C * u * ((n : ℝ) + 1) ^ 2 :=
  windowMoments_of hpos hmean hB hshift (criticalProduct_aux hpos hmean hB hshift)
    (contactMoments_aux hpos hmean hB hshift)

end DiamondPinning
