module

public import DiamondPinning.Model.InstancePins
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Phragmén–Lindelöf bounds in half-planes

This module proves that a holomorphic function of minimal exponential type,
continuous up to the imaginary axis and bounded by one there, is bounded by
one in the closed right or left half-plane. The right-half-plane argument
covers `source/profile.tex` lines 36–38 and 50–59 of `lem:entire-bounds`;
reflection gives the left-half-plane version.
-/

@[expose] public section

open Set Filter Asymptotics Complex Bornology
open scoped Topology

namespace DiamondPinning

/-- A minimal-exponential-type function bounded by one on the imaginary axis
is bounded by one throughout the closed right half-plane. This proves
`DiamondPinning.rightHalfPlane_bounded_of_minimal_exponential_type` (in
`DiamondPinning.Statements.EntireBounds`). -/
theorem rightHalfPlane_bounded_of_minimal_exponential_type_aux
    (f : ℂ → ℂ)
    (hf_holo : DifferentiableOn ℂ f {z : ℂ | 0 < z.re})
    (hf_cont : ContinuousOn f {z : ℂ | 0 ≤ z.re})
    (hf_boundary : ∀ z : ℂ, z.re = 0 → ‖f z‖ ≤ 1)
    (hf_growth : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re →
      ‖f z‖ ≤ C * Real.exp (ε * ‖z‖)) :
    ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ 1 := by
  have hδ : ∀ δ : ℝ, 0 < δ → ∀ z : ℂ, 0 ≤ z.re →
      ‖f z‖ * Real.exp (-δ * z.re) ≤ 1 := by
    intro δ hδ
    let g : ℂ → ℂ := fun z => f z * Complex.exp (-(δ : ℂ) * z)
    have hg_diff : DifferentiableOn ℂ g {z : ℂ | 0 < z.re} := by
      intro z hz
      exact (hf_holo z hz).mul
        (((hasDerivAt_const z (-(δ : ℂ))).mul
          (hasDerivAt_id z)).cexp.differentiableAt).differentiableWithinAt
    have hg_cont : ContinuousOn g (closure {z : ℂ | 0 < z.re}) := by
      rw [Complex.closure_setOfPred_lt_re]
      exact hf_cont.mul ((continuous_const.mul continuous_id).cexp.continuousOn)
    have hg_exp : ∃ c < (2 : ℝ), ∃ B,
        g =O[cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 < z.re}]
          fun z => Real.exp (B * ‖z‖ ^ c) := by
      obtain ⟨C, hC⟩ := hf_growth δ hδ
      refine ⟨1, by norm_num, δ, Asymptotics.IsBigO.of_bound (max 1 C) ?_⟩
      have hmem : ∀ᶠ z in cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 < z.re}, 0 < z.re :=
        (eventually_mem_principal {z : ℂ | 0 < z.re}).filter_mono inf_le_right
      filter_upwards [hmem] with z hz
      have hCe : 0 ≤ C * Real.exp (δ * ‖z‖) :=
        (norm_nonneg (f z)).trans (hC z hz.le)
      have h_exp : Real.exp (-δ * z.re) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith
      calc
        ‖g z‖ = ‖f z‖ * Real.exp (-δ * z.re) := by
          simp [g, Complex.norm_exp]
        _ ≤ (C * Real.exp (δ * ‖z‖)) * 1 := by
          exact mul_le_mul (hC z hz.le) h_exp (Real.exp_pos _).le hCe
        _ ≤ max 1 C * ‖Real.exp (δ * ‖z‖ ^ (1 : ℝ))‖ := by
          rw [Real.norm_eq_abs, Real.abs_exp, Real.rpow_one]
          nlinarith [le_max_right (1 : ℝ) C, Real.exp_pos (δ * ‖z‖)]
    have hg_real : Tendsto (fun x : ℝ => g x) atTop (𝓝 0) := by
      obtain ⟨C, hC⟩ := hf_growth (δ / 2) (half_pos hδ)
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hconst : Tendsto (fun _ : ℝ => -(δ / 2)) atTop (𝓝 (-(δ / 2))) :=
        tendsto_const_nhds
      have hlin : Tendsto (fun x : ℝ => -(δ / 2) * x) atTop atBot :=
        hconst.neg_mul_atTop (by linarith) tendsto_id
      have hupper : Tendsto (fun x : ℝ => C * Real.exp (-(δ / 2) * x)) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp hlin) :
          Tendsto (fun x : ℝ => C * Real.exp (-(δ / 2) * x)) atTop (𝓝 (C * 0)))
      apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hupper
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      have hCx : 0 ≤ C := by
        have h := (norm_nonneg (f (0 : ℂ))).trans (hC 0 le_rfl)
        simpa using h
      calc
        ‖g (x : ℂ)‖ = ‖f (x : ℂ)‖ * Real.exp (-δ * x) := by
          simp [g, Complex.norm_exp]
        _ ≤ (C * Real.exp ((δ / 2) * ‖(x : ℂ)‖)) * Real.exp (-δ * x) := by
          gcongr
          exact hC (x : ℂ) (by simpa using hx)
        _ = C * Real.exp (-(δ / 2) * x) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx, mul_assoc, ← Real.exp_add]
          congr 2
          ring
    have hg_imag : ∀ x : ℝ, ‖g (x * Complex.I)‖ ≤ 1 := by
      intro x
      simpa [g, norm_mul, Complex.norm_exp] using hf_boundary (x * Complex.I) (by simp)
    intro z hz
    have h := PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real
      ⟨hg_diff, hg_cont⟩ hg_exp hg_real hg_imag hz
    simpa [g, norm_mul, Complex.norm_exp] using h
  intro z hz
  have htend : Tendsto
      (fun n : ℕ => ‖f z‖ * Real.exp (-(1 / (n + 1 : ℝ)) * z.re)) atTop
      (𝓝 ‖f z‖) := by
    have hzero : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Continuous (fun δ : ℝ => ‖f z‖ * Real.exp (-δ * z.re)) :=
      continuous_const.mul (Real.continuous_exp.comp (continuous_id.neg.mul continuous_const))
    have ht := (hc.tendsto (0 : ℝ)).comp hzero
    simpa [Function.comp_def] using ht
  apply le_of_tendsto htend
  exact Eventually.of_forall fun n => hδ _ (by positivity) z hz

/-- Reflection transfers the minimal-exponential-type bound from the right
half-plane to the left, proving `DiamondPinning.leftHalfPlane_bounded_of_minimal_exponential_type`
(in `DiamondPinning.Statements.EntireBounds`). -/
theorem leftHalfPlane_bounded_of_minimal_exponential_type_aux
    (f : ℂ → ℂ)
    (hf_holo : DifferentiableOn ℂ f {z : ℂ | z.re < 0})
    (hf_cont : ContinuousOn f {z : ℂ | z.re ≤ 0})
    (hf_boundary : ∀ z : ℂ, z.re = 0 → ‖f z‖ ≤ 1)
    (hf_growth : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z : ℂ, z.re ≤ 0 →
      ‖f z‖ ≤ C * Real.exp (ε * ‖z‖)) :
    ∀ z : ℂ, z.re ≤ 0 → ‖f z‖ ≤ 1 := by
  let F : ℂ → ℂ := fun z => f (-z)
  have hF_holo : DifferentiableOn ℂ F {z : ℂ | 0 < z.re} := by
    intro z hz
    change 0 < z.re at hz
    have hout := hf_holo (-z) (by change (-z).re < 0; rw [neg_re]; linarith)
    have hin : DifferentiableWithinAt ℂ (fun w : ℂ => -w) {z : ℂ | 0 < z.re} z :=
      differentiableWithinAt_id.neg
    have hmaps : MapsTo (fun w : ℂ => -w) {z : ℂ | 0 < z.re} {z : ℂ | z.re < 0} := by
      intro w hw
      change 0 < w.re at hw
      change (-w).re < 0
      rw [neg_re]
      linarith
    exact hout.comp z hin hmaps
  have hF_cont : ContinuousOn F {z : ℂ | 0 ≤ z.re} := by
    apply hf_cont.comp continuousOn_neg
    intro z hz
    change 0 ≤ z.re at hz
    change (-z).re ≤ 0
    rw [neg_re]
    linarith
  have hF_boundary : ∀ z : ℂ, z.re = 0 → ‖F z‖ ≤ 1 := by
    intro z hz
    apply hf_boundary (-z)
    simp [hz]
  have hF_growth : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re →
      ‖F z‖ ≤ C * Real.exp (ε * ‖z‖) := by
    intro ε hε
    obtain ⟨C, hC⟩ := hf_growth ε hε
    refine ⟨C, fun z hz => ?_⟩
    simpa [F] using hC (-z) (by rw [neg_re]; linarith)
  intro z hz
  have h := rightHalfPlane_bounded_of_minimal_exponential_type_aux
    F hF_holo hF_cont hF_boundary hF_growth (-z) (by simp only [neg_re]; linarith)
  simpa [F] using h

end DiamondPinning
