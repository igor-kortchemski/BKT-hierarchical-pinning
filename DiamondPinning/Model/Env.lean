module

public import DiamondPinning.Model.Defs

/-!
# Finite environments and the model-to-law bridge

The proofs couple all fields in one environment: the partition function
`R_n(h)` of the diamond lattice of height `n` is a function of the `2^n` leaf
weights, evaluated at every field `h` with the same weights
(`source/critical.tex` lines 45–48, `source/response.tex` lines 207–215). This
module defines

* `Env n`, the environments of height `n`: `Env 0 = ℝ` (one leaf weight) and
  `Env (n + 1) = Env n × Env n` (the two subtrees);
* `envMeasure μ n`, the law of an environment with independent leaf weights of
  law `μ` (the `n`-fold binary product of `μ`);
* `evalR B h n e`, the partition function `R_n(h)` of the environment `e`:
  `R_0(h) = e^h w` at a leaf of weight `w`, and
  `R_{n+1}(h) = (R_n(h, e₁) R_n(h, e₂) + (B - 1)) / B` for `e = (e₁, e₂)`;

with their defining equations, the probability instance of `envMeasure` and
the measurability of `evalR`, and the event `Env.Pos` that all leaf weights
are positive. The bridge to the law recursion `lawR` is stated in
`DiamondPinning.Statements.Env`. Statements about one field use `lawR`;
arguments that compare fields or follow individual leaves use `evalR` on
`envMeasure`.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory

/-- Environments of height `n`: `Env 0 = ℝ`, one leaf weight, and
`Env (n + 1) = Env n × Env n`, the environments of the two subtrees. -/
def Env : ℕ → Type
  | 0 => ℝ
  | n + 1 => Env n × Env n

/-- The product σ-algebra on environments. -/
instance Env.instMeasurableSpace : (n : ℕ) → MeasurableSpace (Env n)
  | 0 => (inferInstance : MeasurableSpace ℝ)
  | n + 1 => @Prod.instMeasurableSpace _ _ (Env.instMeasurableSpace n) (Env.instMeasurableSpace n)

/-- The law of an environment of height `n` whose `2^n` leaf weights are
independent with law `μ`: `μ` itself at height `0`, and the product of two
independent copies of the law at height `n` for height `n + 1`. -/
noncomputable def envMeasure (μ : Measure ℝ) : (n : ℕ) → Measure (Env n)
  | 0 => μ
  | n + 1 => (envMeasure μ n).prod (envMeasure μ n)

/-- The partition function `R_n(h)` of an environment of height `n`, at field
`h`: `e^h w` at a leaf of weight `w`, and `(R₁ R₂ + (B - 1)) / B` at a node
whose subtrees have partition functions `R₁, R₂`. -/
noncomputable def evalR (B h : ℝ) : (n : ℕ) → Env n → ℝ
  | 0, w => Real.exp h * (show ℝ from w)
  | n + 1, e => (evalR B h n e.1 * evalR B h n e.2 + (B - 1)) / B

@[simp] theorem env_zero : Env 0 = ℝ := rfl

@[simp] theorem env_succ (n : ℕ) : Env (n + 1) = (Env n × Env n) := rfl

theorem env_measurableSpace_succ (n : ℕ) :
    Env.instMeasurableSpace (n + 1) =
      @Prod.instMeasurableSpace _ _ (Env.instMeasurableSpace n) (Env.instMeasurableSpace n) :=
  rfl

@[simp] theorem envMeasure_zero (μ : Measure ℝ) : envMeasure μ 0 = μ := rfl

@[simp] theorem envMeasure_succ (μ : Measure ℝ) (n : ℕ) :
    envMeasure μ (n + 1) = (envMeasure μ n).prod (envMeasure μ n) := rfl

@[simp] theorem evalR_zero (B h : ℝ) (w : Env 0) :
    evalR B h 0 w = Real.exp h * (show ℝ from w) := rfl

@[simp] theorem evalR_succ (B h : ℝ) (n : ℕ) (e : Env (n + 1)) :
    evalR B h (n + 1) e = (evalR B h n e.1 * evalR B h n e.2 + (B - 1)) / B := rfl

/-- For a probability law `μ` of the leaf weights, the environment law is a
probability measure. -/
instance envMeasure.instIsProbabilityMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (n : ℕ) → IsProbabilityMeasure (envMeasure μ n)
  | 0 => inferInstanceAs (IsProbabilityMeasure μ)
  | n + 1 =>
    haveI := envMeasure.instIsProbabilityMeasure μ n
    inferInstanceAs (IsProbabilityMeasure ((envMeasure μ n).prod (envMeasure μ n)))

/-- The evaluator is measurable at every field and height. -/
theorem measurable_evalR (B h : ℝ) : (n : ℕ) → Measurable (evalR B h n)
  | 0 => (measurable_const.mul measurable_id : Measurable fun w : ℝ => Real.exp h * w)
  | n + 1 =>
    have ih := measurable_evalR B h n
    (((ih.comp measurable_fst).mul (ih.comp measurable_snd)).add_const (B - 1)).div_const B

/-- All leaf weights of the environment are positive. This event does not
depend on the field. -/
def Env.Pos : (n : ℕ) → Env n → Prop
  | 0, w => 0 < (show ℝ from w)
  | n + 1, e => Env.Pos n e.1 ∧ Env.Pos n e.2

end DiamondPinning
