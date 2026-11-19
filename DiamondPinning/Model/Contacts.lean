module

public import DiamondPinning.Model.Env
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Contacts: the contact polynomial and the Gibbs law of the contact count

Section 4.3 of the paper (`source/response.tex`, lines 205–215), following the
contact representation of Giacomin, Lacoin and Toninelli. At a fixed
environment, the Gibbs measure chooses the product term `S = R_n^{(1)} R_n^{(2)}`
with probability `S / (S + c)`, adding the contact counts of the two subtrees;
otherwise the count is zero; the initial count is `C_0 = 1`.

The Gibbs law is encoded by a finite polynomial:

* `contactPoly B h n e`, the contact polynomial `P_e ∈ ℝ[X]` of the
  environment `e` at field `h`: `C(e^h w) X` at a leaf of weight `w`, and
  `(P₁ P₂ + C c) / B` at a node, `c = B - 1`. Then `P_e(e^u) = R_n(h + u)(e)`
  for all `u`, and `P_e(1) = R_n(h)(e)`.
* `gibbsWeight B h n e k = P_e[k] / P_e(1)`, the Gibbs probability that the
  contact count `C_n` equals `k`;
* `gibbsMean B h n e f = ⟨f(C_n)⟩_n = ∑_{k ≤ 2^n} P_e[k] f(k) / P_e(1)`, the
  Gibbs expectation (`C_n ≤ 2^n` since `deg P_e ≤ 2^n`);
* `contactMoment μ B h k n = M_{k,n} = E[R_n(h)^θ ⟨C_n^k⟩_n]`
  (`contacts:all-moments`);
* `contactExpMoment μ B h u n = E[R_n(h)^θ ⟨e^{u C_n} - 1⟩_n]`
  (`contacts:exponential`);
* `tiltedLogMomentDeriv μ B h k n
  = E[R_n(h)^θ ⟨C_n⟩_n (θ Z_n^k + k Z_n^{k-1})]`, `Z_n = log R_n(h) - a`: the
  field derivative of `E[R_n(h)^θ Z_n^k]` (`response.tex` lines 87–89 and
  321–326, with `∂_h log R_n = ⟨C_n⟩_n`).

Off the null event where some leaf weight is not positive, `P_e(1)` may
vanish and the weights are meaningless; the statements only use them almost
surely or under `Env.Pos`.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory Polynomial

/-- The contact polynomial of an environment of height `n` at field `h`:
`C(e^h w) X` at a leaf of weight `w` (one contact), and
`(P₁ P₂ + C (B - 1)) / B` at a node whose subtrees have contact polynomials
`P₁, P₂` (the constant `c = B - 1` carries no contact). -/
noncomputable def contactPoly (B h : ℝ) : (n : ℕ) → Env n → ℝ[X]
  | 0, w => C (Real.exp h * (show ℝ from w)) * X
  | n + 1, e => C B⁻¹ * (contactPoly B h n e.1 * contactPoly B h n e.2 + C (B - 1))

/-- The Gibbs probability `P_e[k] / P_e(1)` that the contact count `C_n` of the
environment `e` at field `h` equals `k`. -/
noncomputable def gibbsWeight (B h : ℝ) (n : ℕ) (e : Env n) (k : ℕ) : ℝ :=
  (contactPoly B h n e).coeff k / (contactPoly B h n e).eval 1

/-- The Gibbs expectation `⟨f(C_n)⟩_n = ∑_{k ≤ 2^n} f(k) P_e[k] / P_e(1)` of a
function of the contact count, at field `h` and environment `e`. -/
noncomputable def gibbsMean (B h : ℝ) (n : ℕ) (e : Env n) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n + 1), gibbsWeight B h n e k * f k

/-- The contact moment `M_{k,n} = E[R_n(h)^θ ⟨C_n^k⟩_n]`
(`contacts:all-moments`, at `h = h_c` in the paper). -/
noncomputable def contactMoment (μ : Measure ℝ) (B h : ℝ) (k n : ℕ) : ℝ :=
  ∫ e, evalR B h n e ^ theta B * gibbsMean B h n e (fun j => (j : ℝ) ^ k) ∂(envMeasure μ n)

/-- The exponential contact moment `E[R_n(h)^θ ⟨e^{u C_n} - 1⟩_n]`
(`contacts:exponential`, at `h = h_c` in the paper). -/
noncomputable def contactExpMoment (μ : Measure ℝ) (B h u : ℝ) (n : ℕ) : ℝ :=
  ∫ e, evalR B h n e ^ theta B *
    gibbsMean B h n e (fun j => Real.exp (u * j) - 1) ∂(envMeasure μ n)

/-- The field derivative of the tilted logarithmic moment
`E[R_n(h)^θ (log R_n(h) - a)^k]`, `a = log B`, written with
`∂_h log R_n(h) = ⟨C_n⟩_n`:
`E[R_n(h)^θ ⟨C_n⟩_n (θ Z_n^k + k Z_n^{k-1})]`, `Z_n = log R_n(h) - a`. For
`k = 0` the second term vanishes. -/
noncomputable def tiltedLogMomentDeriv (μ : Measure ℝ) (B h : ℝ) (k n : ℕ) : ℝ :=
  ∫ e, evalR B h n e ^ theta B * gibbsMean B h n e (fun j => (j : ℝ)) *
    (theta B * (Real.log (evalR B h n e) - Real.log B) ^ k +
      k * (Real.log (evalR B h n e) - Real.log B) ^ (k - 1)) ∂(envMeasure μ n)

end DiamondPinning
