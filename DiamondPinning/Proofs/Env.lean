module

public import DiamondPinning.Model.Env
public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Model.Basic

/-!
# Helpers for the frozen statements of `DiamondPinning.Statements.Env`

Owned helper module for the holes `ae_envPos`, `evalR_pos` and
`map_evalR_envMeasure` of `DiamondPinning.Statements.Env`, which imports it.
It must not import `DiamondPinning.Statements.Env`,
`DiamondPinning.Statements.Main` or the Challenge.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory

/-- The event that every leaf weight is positive is measurable. -/
theorem measurableSet_envPos : (n : ℕ) → MeasurableSet {e : Env n | Env.Pos n e}
  | 0 => by
      change MeasurableSet (Set.Ioi (0 : ℝ))
      exact measurableSet_Ioi
  | n + 1 => by
      change MeasurableSet
        (Prod.fst ⁻¹' {x : Env n | Env.Pos n x} ∩
          Prod.snd ⁻¹' {x : Env n | Env.Pos n x})
      exact ((measurableSet_envPos n).preimage measurable_fst).inter
        ((measurableSet_envPos n).preimage measurable_snd)

/-- Almost every environment has positive weights at every leaf. -/
theorem ae_envPos_aux {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) :
    ∀ n : ℕ, ∀ᵐ e ∂(envMeasure μ n), Env.Pos n e := by
  intro n
  induction n with
  | zero => simpa [Env.Pos, envMeasure] using hpos
  | succ n ih =>
      letI : IsProbabilityMeasure (envMeasure μ n) := envMeasure.instIsProbabilityMeasure μ n
      change ∀ᵐ e : Env n × Env n ∂((envMeasure μ n).prod (envMeasure μ n)),
        Env.Pos n e.1 ∧ Env.Pos n e.2
      have hp : MeasurableSet {e : Env n × Env n | Env.Pos n e.1 ∧ Env.Pos n e.2} := by
        exact ((measurableSet_envPos n).preimage measurable_fst).inter
          ((measurableSet_envPos n).preimage measurable_snd)
      rw [Measure.ae_prod_iff_ae_ae hp]
      filter_upwards [ih] with x hx
      filter_upwards [ih] with y hy
      exact ⟨hx, hy⟩

/-- Positivity of the leaves implies positivity of the recursive evaluator. -/
theorem evalR_pos_aux {B : ℝ} (hB : 1 < B) (h : ℝ) :
    ∀ n : ℕ, ∀ {e : Env n}, Env.Pos n e → 0 < evalR B h n e := by
  intro n
  induction n with
  | zero =>
      intro e he
      change 0 < (show ℝ from e) at he
      rw [evalR_zero]
      exact mul_pos (Real.exp_pos h) he
  | succ n ih =>
      intro e he
      change Env.Pos n e.1 ∧ Env.Pos n e.2 at he
      rw [evalR_succ]
      have h₁ : 0 < evalR B h n e.1 := ih he.1
      have h₂ : 0 < evalR B h n e.2 := ih he.2
      exact div_pos (by nlinarith [mul_pos h₁ h₂]) (by linarith : 0 < B)

/-- The law of the environment evaluator is the recursively defined law `lawR`. -/
theorem map_evalR_envMeasure_aux (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B h : ℝ) :
    ∀ n : ℕ, (envMeasure μ n).map (evalR B h n) = lawR μ B h n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      letI : IsProbabilityMeasure (envMeasure μ n) := envMeasure.instIsProbabilityMeasure μ n
      let f : Env n × Env n → ℝ × ℝ :=
        fun e => (evalR B h n e.1, evalR B h n e.2)
      let g : ℝ × ℝ → ℝ := fun p => (p.1 * p.2 + (B - 1)) / B
      have hf : Measurable f := by
        dsimp [f]
        exact ((measurable_evalR B h n).comp measurable_fst).prodMk
          ((measurable_evalR B h n).comp measurable_snd)
      have hg : Measurable g := by
        dsimp [g]
        fun_prop
      change ((envMeasure μ n).prod (envMeasure μ n)).map (g ∘ f) =
        ((lawR μ B h n).prod (lawR μ B h n)).map g
      calc
        ((envMeasure μ n).prod (envMeasure μ n)).map (g ∘ f) =
            (((envMeasure μ n).prod (envMeasure μ n)).map f).map g := by
              rw [← Measure.map_map hg hf]
        _ = (((envMeasure μ n).map (evalR B h n)).prod
              ((envMeasure μ n).map (evalR B h n))).map g := by
              congr 1
              rw [Measure.map_prod_map (envMeasure μ n) (envMeasure μ n)
                (measurable_evalR B h n) (measurable_evalR B h n)]
              rfl
        _ = ((lawR μ B h n).prod (lawR μ B h n)).map g := by rw [ih]

end DiamondPinning
