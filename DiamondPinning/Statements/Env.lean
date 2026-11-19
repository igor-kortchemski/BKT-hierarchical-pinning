module

public import DiamondPinning.Model.Env
public import DiamondPinning.Proofs.Env

/-!
# The model-to-law bridge (key statement K3)

Positivity of the environments and the bridge
`map (evalR B h n) (envMeasure μ n) = lawR μ B h n`: at every field, the
partition function of an environment with independent leaf weights of law
`μ` has the law of the frozen recursion `lawR`.

Approved on 18 November 2026 (by the author's delegation to an Astra review)
with the definitions of `DiamondPinning.Model.Env`. The proofs are registered
holes of the freeze record, filled with proof text only, using the owned
helper module `DiamondPinning.Proofs.Env`, which this file imports.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory

/-- If the leaf weights are almost surely positive, almost every environment
has all its leaf weights positive: one null set for all fields. -/
theorem ae_envPos {μ : Measure ℝ} [IsProbabilityMeasure μ] (hpos : ∀ᵐ w ∂μ, 0 < w) (n : ℕ) :
    ∀ᵐ e ∂(envMeasure μ n), Env.Pos n e := by
  exact ae_envPos_aux hpos n

/-- On an environment with positive leaf weights, `R_n(h) > 0` at every field
`h`, for `B > 1`. -/
theorem evalR_pos {B : ℝ} (hB : 1 < B) (h : ℝ) {n : ℕ} {e : Env n} (he : Env.Pos n e) :
    0 < evalR B h n e := by
  exact evalR_pos_aux hB h n he

/-- The model-to-law bridge: at every field `h`, the partition function of an
environment with independent leaf weights of law `μ` has the law `lawR μ B h n`
of the recursion `eq:model`. -/
theorem map_evalR_envMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] (B h : ℝ) (n : ℕ) :
    (envMeasure μ n).map (evalR B h n) = lawR μ B h n := by
  exact map_evalR_envMeasure_aux μ B h n

end DiamondPinning
