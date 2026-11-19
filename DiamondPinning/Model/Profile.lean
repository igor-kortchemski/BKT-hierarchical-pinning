module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The explicit limiting profile (Section 5)

Definitions of `source/scaling.tex`, lines 24–41, for a parameter `v ≥ 0`
(in the paper `v = γ λ`):

* `IsPrePoleTime v t`: `0 < t < T_v`, where `T_v = π / √v` for `v > 0` and
  `T_0 = ∞` (line 25). The infinite pole time is encoded by this predicate,
  never by a real number.
* `profileU v t = u_v(t)`: `sin(√v t)/√v` for `v > 0`, `t` for `v = 0`
  (line 30).
* `profileA v t = a_v(t) = 4 / u_v(t)²`, `profileB v t = b_v(t) = 2 u_v'(t)/u_v(t)`
  and `profileDensity v t x = f_v(t, x) = a_v(t) e^{-b_v(t) x}` (`eq:profile`,
  lines 33–37), meaningful for `0 < t < T_v`.
* `profileTransform v t s = F_v(t, s) = a_v(t) / (s + b_v(t))`
  (`cont:laplaceprofile`, lines 39–41), meaningful for `s + b_v(t) > 0`.
* `profileMeasure v t`, the positive measure `f_v(t, x) dx` on `[0, ∞)`. It
  is kept as a `Measure`: its total mass is infinite when `b_v(t) ≤ 0`
  (`continuation.tex` line 11).

The source uses only `v ≥ 0`. For `v < 0` the definitions fall back on the
`v = 0` branch; no statement uses that range.
-/

@[expose] public section

namespace DiamondPinning

open MeasureTheory

/-- Pre-pole times (`scaling.tex` lines 24–25, 32): `0 < t < T_v`, with
`T_v = π / √v` for `v > 0` and `T_0 = ∞`. -/
def IsPrePoleTime (v t : ℝ) : Prop :=
  0 < t ∧ (0 < v → t < Real.pi / Real.sqrt v)

/-- `u_v(t) = sin(√v t)/√v` for `v > 0` and `u_0(t) = t` (`scaling.tex`
line 30). -/
noncomputable def profileU (v t : ℝ) : ℝ :=
  if 0 < v then Real.sin (Real.sqrt v * t) / Real.sqrt v else t

/-- `a_v(t) = 4 / u_v(t)²` (`eq:profile`, `scaling.tex` line 34). -/
noncomputable def profileA (v t : ℝ) : ℝ :=
  4 / profileU v t ^ 2

/-- `b_v(t) = 2 u_v'(t) / u_v(t)` (`eq:profile`, `scaling.tex` line 35), with
`u_v'` the derivative of `u_v` in time. -/
noncomputable def profileB (v t : ℝ) : ℝ :=
  2 * deriv (profileU v) t / profileU v t

/-- The profile density `f_v(t, x) = a_v(t) e^{-b_v(t) x}` (`eq:profile`,
`scaling.tex` line 36). -/
noncomputable def profileDensity (v t x : ℝ) : ℝ :=
  profileA v t * Real.exp (-(profileB v t * x))

/-- `F_v(t, s) = a_v(t) / (s + b_v(t))` (`cont:laplaceprofile`, `scaling.tex`
line 40), the Laplace transform of `f_v(t, ·)` when `s + b_v(t) > 0`. -/
noncomputable def profileTransform (v t s : ℝ) : ℝ :=
  profileA v t / (s + profileB v t)

/-- The profile measure `f_v(t, x) dx` on `[0, ∞)` (`scaling.tex` lines 52–53,
`profile.tex` line 11): Lebesgue measure on `[0, ∞)` with density `f_v(t, ·)`.
It is not normalized, and its mass is infinite when `b_v(t) ≤ 0`. -/
noncomputable def profileMeasure (v t : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ici 0)).withDensity fun x => ENNReal.ofReal (profileDensity v t x)

end DiamondPinning
