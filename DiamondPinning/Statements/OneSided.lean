module

public import DiamondPinning.Proofs.OneSided
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Statement N14: one-sided compactness

The statement of `lem:one-sided` from `source/scaling.tex`, lines 195–209.
-/

@[expose] public section

namespace DiamondPinning

open Filter MeasureTheory Topology

/-- **One-sided compactness** (`lem:one-sided`, `source/scaling.tex:195–209`).
Let `A < B'`, let the functions `f j` be uniformly bounded on `[A, B']`, and
suppose `ε j → 0` and
`f j t - f j r ≤ C * (t - r) + ε j` whenever `A ≤ r ≤ t ≤ B'`.
If `g` is continuous on `[A, B']` and the `L¹` norms of `f j - g` on that
interval tend to zero, then `f j → g` uniformly on every compact subset of
`(A, B')`.

The source's implicit measurability is expressed by a.e. strong measurability
for Lebesgue measure restricted to `[A, B']`; nothing is assumed about the
representatives outside that interval. No separate integrability hypotheses
are needed: they follow from this measurability, uniform boundedness of the
`f j`, and continuity of `g` on the compact interval. As in the source, the
slope constant `C` is an arbitrary real number. -/
theorem one_sided_compactness (A B' C : ℝ) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (ε : ℕ → ℝ) (hAB : A < B')
    (hbound : ∃ M : ℝ, ∀ j x, x ∈ Set.Icc A B' → |f j x| ≤ M)
    (hmeas : ∀ j, AEStronglyMeasurable (f j) (volume.restrict (Set.Icc A B')))
    (hone : ∀ j r t, r ∈ Set.Icc A B' → t ∈ Set.Icc A B' → r ≤ t →
      f j t - f j r ≤ C * (t - r) + ε j)
    (hε : Tendsto ε atTop (𝓝 0))
    (hg : ContinuousOn g (Set.Icc A B'))
    (hL1 : Tendsto (fun j => ∫ x in A..B', |f j x - g x|) atTop (𝓝 0)) :
    ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioo A B' → TendstoUniformlyOn f g atTop K := by
  exact one_sided_compactness_aux A B' C f g ε hAB hbound hmeas hone hε hg hL1

end DiamondPinning
