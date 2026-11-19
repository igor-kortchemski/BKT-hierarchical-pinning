module

public import DiamondPinning.Model.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The spine (Section 4.1)

Definitions for `response:spine-identities` (`source/response.tex`, lines
62–77). At a field `h`, with `μ_j` the law of `R_j(h)` and `A_j = E R_j(h)^θ`:

* `tiltedLaw μ B h j` is the size-biased law `r^θ μ_j(dr) / A_j`;
* `spineMeasure μ B h n` is the law of `(R_0^*, U_0, …, U_{n-1})`, independent
  with laws `r^θ μ_0(dr)/A_0` and `r^θ μ_j(dr)/A_j`, on `ℝ × (Fin n → ℝ)`;
  the identities involve only the coordinates up to time `n`, so a finite
  horizon replaces the source's infinite sequence;
* `spineWalk B u k = S_k = ∑_{j<k} (log U_j - a)`, `a = log B`;
* `spineW B n r u = w_n = (1 + c/(B R_0^*) ∑_{k=1}^n e^{-S_k})^{-p}`,
  `p = 1 - θ`, `c = B - 1`;
* `spineT B n r u = T_n = R_0^* e^{S_n} w_n^{-1/p}` (the spine's `T_n`, named
  `spineT` to avoid the collision with the product's `T_n`);
* `spineMeanW μ B h n = Ê w_n` and
  `spineMeanWLog μ B h n = Ê[w_n (log T_n + d_0)]`, `d_0 = 1/θ - a`.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory

/-- The size-biased law `r^θ μ_j(dr) / A_j` of `R_j(h)`, with
`A_j = E R_j(h)^θ`. -/
noncomputable def tiltedLaw (μ : Measure ℝ) (B h : ℝ) (j : ℕ) : Measure ℝ :=
  (lawR μ B h j).withDensity fun r => ENNReal.ofReal (r ^ theta B / tiltedMass μ B h j)

/-- The law of the spine variables `(R_0^*, U_0, …, U_{n-1})` at field `h`:
`R_0^*` with law `r^θ μ_0(dr)/A_0`, independent of the independent `U_j` with
laws `r^θ μ_j(dr)/A_j`, `j < n`. -/
noncomputable def spineMeasure (μ : Measure ℝ) (B h : ℝ) (n : ℕ) :
    Measure (ℝ × (Fin n → ℝ)) :=
  (tiltedLaw μ B h 0).prod (Measure.pi fun j : Fin n => tiltedLaw μ B h j)

/-- The spine walk `S_k = ∑_{j<k} (log U_j - a)`, `a = log B`, for `k ≤ n`. -/
noncomputable def spineWalk (B : ℝ) {n : ℕ} (u : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ j : Fin n, if (j : ℕ) < k then Real.log (u j) - Real.log B else 0

/-- The spine weight
`w_n = (1 + c / (B R_0^*) ∑_{k=1}^n e^{-S_k})^{-p}`, `p = 1 - θ`, `c = B - 1`,
at `R_0^* = r` and `U = u`. -/
noncomputable def spineW (B : ℝ) (n : ℕ) (r : ℝ) (u : Fin n → ℝ) : ℝ :=
  (1 + (B - 1) / (B * r) * ∑ k ∈ Finset.Icc 1 n, Real.exp (-spineWalk B u k)) ^
    (-(1 - theta B))

/-- The spine mass `T_n = R_0^* e^{S_n} w_n^{-1/p}`, `p = 1 - θ`, at
`R_0^* = r` and `U = u`. -/
noncomputable def spineT (B : ℝ) (n : ℕ) (r : ℝ) (u : Fin n → ℝ) : ℝ :=
  r * Real.exp (spineWalk B u n) * spineW B n r u ^ (-(1 / (1 - theta B)))

/-- The spine expectation `Ê w_n` (`response:spine`). -/
noncomputable def spineMeanW (μ : Measure ℝ) (B h : ℝ) (n : ℕ) : ℝ :=
  ∫ x, spineW B n x.1 x.2 ∂(spineMeasure μ B h n)

/-- The mixed spine expectation `Ê[w_n (log T_n + d_0)]`, `d_0 = 1/θ - a`
(`response:mixed-spine`). -/
noncomputable def spineMeanWLog (μ : Measure ℝ) (B h : ℝ) (n : ℕ) : ℝ :=
  ∫ x, spineW B n x.1 x.2 *
    (Real.log (spineT B n x.1 x.2) + (1 / theta B - Real.log B)) ∂(spineMeasure μ B h n)

end DiamondPinning
