module

public import DiamondPinning.Proofs.EntireBounds
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Statements for `lem:entire-bounds`

Growth of matrix solutions of the Volterra integral equation, and the
Phragmén–Lindelöf principle in the closed right and left half-planes.
-/

@[expose] public section

open scoped Matrix.Norms.Elementwise

namespace DiamondPinning

/-- **The fundamental matrix exists and is unique** (presupposed by
`lem:entire-bounds`, `profile.tex:28–31`, "the fundamental matrix"). For
measurable `w` with `0 < m ≤ w ≤ M` on `(0, T)` and every `z : ℂ`, the
Volterra equation `Y t = 1 + ∫_0^t (-z) A_w(s) Y s ds` has a solution that is
continuous on `[0, T]`, and any two such solutions agree on `[0, T]`. -/
theorem matrix_integral_solution_exists_unique
    (T m M : ℝ) (hT : 0 < T) (w : ℝ → ℝ) (hw : Measurable w)
    (hm : 0 < m) (hw_lower : ∀ t ∈ Set.Ioo (0 : ℝ) T, m ≤ w t)
    (hw_upper : ∀ t ∈ Set.Ioo (0 : ℝ) T, w t ≤ M) (z : ℂ) :
    (∃ Y : ℝ → Matrix (Fin 2) (Fin 2) ℂ, ContinuousOn Y (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        Y t = 1 + ∫ s in (0 : ℝ)..t, (-z) •
          ((!![0, (w s : ℂ)⁻¹; (w s : ℂ), 0] : Matrix (Fin 2) (Fin 2) ℂ) * Y s)) ∧
    ∀ Y Y' : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      ContinuousOn Y (Set.Icc 0 T) → ContinuousOn Y' (Set.Icc 0 T) →
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        Y t = 1 + ∫ s in (0 : ℝ)..t, (-z) •
          ((!![0, (w s : ℂ)⁻¹; (w s : ℂ), 0] : Matrix (Fin 2) (Fin 2) ℂ) * Y s)) →
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        Y' t = 1 + ∫ s in (0 : ℝ)..t, (-z) •
          ((!![0, (w s : ℂ)⁻¹; (w s : ℂ), 0] : Matrix (Fin 2) (Fin 2) ℂ) * Y' s)) →
      ∀ t ∈ Set.Icc (0 : ℝ) T, Y t = Y' t := by
  exact matrix_integral_solution_exists_unique_aux T m M hT w hw hm hw_lower hw_upper z

/-- **Growth bound** (source `lem:entire-bounds`, `profile.tex:26–35`).
For fixed bounded measurable coefficients, every continuous matrix solution
of the Volterra equation has the stated exponential growth at time `T`.

The norm is Mathlib's elementwise supremum norm on
`Matrix (Fin 2) (Fin 2) ℂ`. The coefficient bounds are imposed at every point
of `(0, T)`, the stated all-points alternative to the a.e. formulation. -/
theorem matrix_integral_growth_bound
    (T m M : ℝ) (hT : 0 < T) (w : ℝ → ℝ) (hw : Measurable w)
    (hm : 0 < m) (hw_lower : ∀ t ∈ Set.Ioo (0 : ℝ) T, m ≤ w t)
    (hw_upper : ∀ t ∈ Set.Ioo (0 : ℝ) T, w t ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (z : ℂ) (Y : ℝ → Matrix (Fin 2) (Fin 2) ℂ),
      ContinuousOn Y (Set.Icc 0 T) →
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        Y t = 1 + ∫ s in (0 : ℝ)..t, (-z) •
          ((!![0, (w s : ℂ)⁻¹; (w s : ℂ), 0] :
            Matrix (Fin 2) (Fin 2) ℂ) * Y s)) →
      ‖Y T‖ ≤ C * Real.exp (T * |z.re| + ε * ‖z‖) := by
  exact matrix_integral_growth_bound_aux T m M hT w hw hm hw_lower hw_upper ε hε

/-- **Half-plane Phragmén–Lindelöf principle** (source `lem:entire-bounds`,
`profile.tex:36–38`, with the right-half-plane proof at lines 50–59).
A minimal-exponential-type function which is holomorphic on the open right
half-plane, continuous on its closure, and bounded by one on the imaginary
axis is bounded by one on the whole closed half-plane. -/
theorem rightHalfPlane_bounded_of_minimal_exponential_type
    (f : ℂ → ℂ)
    (hf_holo : DifferentiableOn ℂ f {z : ℂ | 0 < z.re})
    (hf_cont : ContinuousOn f {z : ℂ | 0 ≤ z.re})
    (hf_boundary : ∀ z : ℂ, z.re = 0 → ‖f z‖ ≤ 1)
    (hf_growth : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re →
      ‖f z‖ ≤ C * Real.exp (ε * ‖z‖)) :
    ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ 1 := by
  exact rightHalfPlane_bounded_of_minimal_exponential_type_aux f hf_holo hf_cont hf_boundary
    hf_growth

/-- **Half-plane Phragmén–Lindelöf principle, left half-plane** (source
`lem:entire-bounds`, `profile.tex:36–38`; the source states the principle for
every half-plane, obtained from the right one by reflection, and applies it in
the left half-plane at `profile.tex:116–123`). A minimal-exponential-type
function which is holomorphic on the open left half-plane, continuous on its
closure, and bounded by one on the imaginary axis is bounded by one on the
whole closed half-plane. -/
theorem leftHalfPlane_bounded_of_minimal_exponential_type
    (f : ℂ → ℂ)
    (hf_holo : DifferentiableOn ℂ f {z : ℂ | z.re < 0})
    (hf_cont : ContinuousOn f {z : ℂ | z.re ≤ 0})
    (hf_boundary : ∀ z : ℂ, z.re = 0 → ‖f z‖ ≤ 1)
    (hf_growth : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z : ℂ, z.re ≤ 0 →
      ‖f z‖ ≤ C * Real.exp (ε * ‖z‖)) :
    ∀ z : ℂ, z.re ≤ 0 → ‖f z‖ ≤ 1 := by
  exact leftHalfPlane_bounded_of_minimal_exponential_type_aux f hf_holo hf_cont hf_boundary
    hf_growth

end DiamondPinning
