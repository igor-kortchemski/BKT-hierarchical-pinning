module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Proofs.ProductAssembly
public import DiamondPinning.Proofs.ResponseAssembly
public import DiamondPinning.Proofs.ProfileAssembly
public import DiamondPinning.Proofs.CompactnessProof2
public import DiamondPinning.Proofs.ContinuationProof2
public import DiamondPinning.Proofs.ExactCriticalProof
public import DiamondPinning.Proofs.EnergyBounds
public import DiamondPinning.Proofs.BKTProof

/-!
# Final assembly: Sections 5–8 and `th:bkt`

Assembles the statements `scaling_compactness`, `continuation`,
`exact_critical`, `gamma_eq_limit`, `freeEnergy_upper`, `escape_constant` and
`bkt` from their conditional proofs, feeding each with the results it rests
on (`th:product`, `th:response`, `prop:window-moments`,
`th:profile-identification` and the results assembled here).
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Topology Asymptotics

/-- `scaling:compactness`. -/
theorem scaling_compactness_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ lam T : ℝ, 0 ≤ lam → 0 < T → lam * T ^ 2 ≤ η₀ →
      ∃ C : ℝ, 0 < C ∧ ∀ Nseq : ℕ → ℝ, Tendsto Nseq atTop atTop →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ E : EntranceData T lam (lam * κ * Real.log B ^ 2 / ℓ₃) C,
            (∀ r : ℝ, 0 < r → r < T →
              Tendsto (fun j => timeIntegral
                (fun t => |scaledMass μ B lam (Nseq (φ j)) t - E.S t|) r T) atTop (𝓝 0)) ∧
            (∀ r : ℝ, 0 < r →
              TendstoUniformlyOn (fun j t => scaledDrift μ B lam (Nseq (φ j)) t) E.d atTop
                (Set.Icc r T)) ∧
            (∀ r : ℝ, 0 < r →
              TendstoUniformlyOn (fun j t => scaledSecond μ B lam (Nseq (φ j)) t) E.K atTop
                (Set.Icc r T)) ∧
            (∀ r : ℝ, 0 < r →
              TendstoUniformlyOn (fun j t => scaledThird μ B lam (Nseq (φ j)) t) E.P atTop
                (Set.Icc r T)) ∧
            (∀ r M : ℝ, 0 < r →
              TendstoUniformlyOn
                (fun j (p : ℝ × ℝ) => scaledCompensated μ B lam (Nseq (φ j)) p.1 p.2)
                (fun p => E.H p.1 p.2) atTop (Set.Icc r T ×ˢ Set.Icc 0 M)) ∧
            (∀ᵐ t, t ∈ Set.Ioc 0 T →
              WeakConvergence (fun j => scalingMeasure μ B lam (Nseq (φ j)) t) atTop (E.ν t)) :=
  scaling_compactness_of hpos hmean hB hshift hℓ₃ hκ (criticalProduct_aux hpos hmean hB hshift)
    (response_transversality_aux hpos hmean hB hshift) (windowMoments_aux hpos hmean hB hshift)
    (window_derivBounds_aux hpos hmean hB hshift)

/-- `cont:continuation`. -/
theorem continuation_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ γ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hγ : γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃)) {lam : ℝ} (hlam : 0 < lam)
    {I : Set ℝ} (hI : IsCompact I) (hIpole : ∀ t ∈ I, IsPrePoleTime (γ * lam) t)
    {s : ℝ} (hs : 0 < s) (hadm : 0 < s + sInf (profileB (γ * lam) '' I)) :
    TendstoUniformlyOn (fun N t => scaledTransform μ B lam N t s)
        (fun t => profileTransform (γ * lam) t s) atTop I ∧
      ∀ t ∈ I, WeakConvergence (fun N => weightedMeasure (scalingMeasure μ B lam N t) s) atTop
        (weightedMeasure (profileMeasure (γ * lam) t) s) := by
  refine continuation_of hpos hmean hB hshift hℓ₃ hκ hγ hlam hI hIpole hs hadm
    (scaling_compactness_aux hpos hmean hB hshift hℓ₃ hκ) ?_
  intro lam' T C hlam' hT hC
  exact profile_identification_aux hpos hmean hB hshift hℓ₃ hκ hγ hlam' hT hC

/-- `eq:exact-critical`. -/
theorem exact_critical_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
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
  obtain ⟨κ, -, hκ, -⟩ := response_transversality_aux hpos hmean hB hshift
  refine exact_critical_of hpos hmean hB hshift hℓ₃ hκ
    (scaling_compactness_aux hpos hmean hB hshift hℓ₃ hκ) ?_
  intro γ hγ lam T C hlam hT hC
  exact profile_identification_aux hpos hmean hB hshift hℓ₃ hκ hγ hlam hT hC

/-- The second identity of `eq:gamma`. -/
theorem gamma_eq_limit_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ γ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hγ : γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃)) :
    Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      (Real.log B * (n : ℝ) ^ 2)) atTop (𝓝 γ) :=
  gamma_eq_limit_of hpos hmean hB hshift hℓ₃ hκ hγ (exact_critical_aux hpos hmean hB hshift hℓ₃)

/-- `cont:freeenergyupper`. -/
theorem freeEnergy_upper_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ γ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hγ : γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃)) :
    ∀ ε > 0, ∀ᶠ u in 𝓝[>] (0 : ℝ),
      Real.sqrt u * Real.log (freeEnergy μ B (criticalPoint μ B + u)) ≤
        -(Real.pi * Real.log 2) / Real.sqrt γ + ε := by
  refine freeEnergy_upper_of hpos hmean hB hshift hℓ₃ hκ hγ ?_
  intro lam hlam I hI hIpole s hs hadm
  exact continuation_aux hpos hmean hB hshift hℓ₃ hκ hγ hlam hI hIpole hs hadm

/-- `escape:constant`. -/
theorem escape_constant_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) {ℓ₃ κ γ : ℝ}
    (hℓ₃ : Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃))
    (hκ : Tendsto (fun n : ℕ => deriv (fun h => tiltedLogMoment μ B h 1 n) (criticalPoint μ B) /
      tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 κ))
    (hγ : γ = 3 * Real.log B ^ 2 * κ / (2 * ℓ₃)) {lam : ℝ} (hlam : 0 < lam) :
    ∀ ε > 0, ∀ᶠ N : ℝ in atTop,
      0 < freeEnergy μ B (criticalPoint μ B + lam / N ^ 2) ∧
        -(Real.pi / Real.sqrt (γ * lam)) * Real.log 2 - ε ≤
          N⁻¹ * Real.log (freeEnergy μ B (criticalPoint μ B + lam / N ^ 2)) := by
  refine escape_constant_of hpos hmean hB hshift hℓ₃ hκ hγ hlam ?_
  intro lam' hlam' I hI hIpole s hs hadm
  exact continuation_aux hpos hmean hB hshift hℓ₃ hκ hγ hlam' hI hIpole hs hadm

/-- `th:bkt`. -/
theorem bkt_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B) :
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
  refine bkt_of hpos hmean hB hshift ?_ ?_ ?_ ?_
  · intro ℓ₃ hℓ₃
    exact exact_critical_aux hpos hmean hB hshift hℓ₃
  · intro ℓ₃ κ γ hℓ₃ hκ hγ
    exact gamma_eq_limit_aux hpos hmean hB hshift hℓ₃ hκ hγ
  · intro ℓ₃ κ γ hℓ₃ hκ hγ
    exact freeEnergy_upper_aux hpos hmean hB hshift hℓ₃ hκ hγ
  · intro ℓ₃ κ γ hℓ₃ hκ hγ lam hlam
    exact escape_constant_aux hpos hmean hB hshift hℓ₃ hκ hγ hlam

end DiamondPinning
