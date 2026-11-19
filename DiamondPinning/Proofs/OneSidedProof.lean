module

public import DiamondPinning.Model.InstancePins
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# One-sided compactness

This module proves that uniformly bounded functions with asymptotically
one-sided increments converge uniformly on interior compact sets whenever
they converge in `L¹` to a continuous limit. Persistent one-sided excursions
would otherwise force a fixed `L¹` discrepancy. This is `lem:one-sided`,
`source/scaling.tex` lines 195–209.
-/

@[expose] public section

namespace DiamondPinning

open Filter MeasureTheory Topology

/-- One-sided increment control and `L¹` convergence to a continuous function
imply uniform convergence on interior compact sets, proving `DiamondPinning.one_sided_compactness`
(in `DiamondPinning.Statements.OneSided`). -/
theorem one_sided_compactness_aux (A B' C : ℝ) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (ε : ℕ → ℝ) (hAB : A < B')
    (hbound : ∃ M : ℝ, ∀ j x, x ∈ Set.Icc A B' → |f j x| ≤ M)
    (hmeas : ∀ j, AEStronglyMeasurable (f j) (volume.restrict (Set.Icc A B')))
    (hone : ∀ j r t, r ∈ Set.Icc A B' → t ∈ Set.Icc A B' → r ≤ t →
      f j t - f j r ≤ C * (t - r) + ε j)
    (hε : Tendsto ε atTop (𝓝 0))
    (hg : ContinuousOn g (Set.Icc A B'))
    (hL1 : Tendsto (fun j => ∫ x in A..B', |f j x - g x|) atTop (𝓝 0)) :
    ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioo A B' → TendstoUniformlyOn f g atTop K := by
  obtain ⟨M, hM⟩ := hbound
  have hM0 : 0 ≤ M := by
    exact (abs_nonneg (f 0 A)).trans (hM 0 A ⟨le_rfl, hAB.le⟩)
  have hfint (j : ℕ) : IntervalIntegrable (f j) volume A B' := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hAB.le]
    refine (integrable_const M).mono (hmeas j) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hM0] using hM j x hx
  have hgint : IntervalIntegrable g volume A B' := hg.intervalIntegrable_of_Icc hAB.le
  have hφint (j : ℕ) : IntervalIntegrable (fun x => |f j x - g x|) volume A B' :=
    ((hfint j).sub hgint).abs
  intro K hK hKsub
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  by_cases hKne : K.Nonempty
  · let L := sInf K
    let U := sSup K
    have hLmem : L ∈ K := hK.sInf_mem hKne
    have hUmem : U ∈ K := hK.sSup_mem hKne
    have hAL : A < L := (hKsub hLmem).1
    have hUB : U < B' := (hKsub hUmem).2
    have hLlower : ∀ x ∈ K, L ≤ x := fun _ hx => (hK.isLeast_sInf hKne).2 hx
    have hUupper : ∀ x ∈ K, x ≤ U := fun _ hx => (hK.isGreatest_sSup hKne).2 hx
    obtain ⟨δ, hδ, hgδ⟩ := (Metric.uniformContinuousOn_iff.1
      ((isCompact_Icc : IsCompact (Set.Icc A B')).uniformContinuousOn_of_continuous hg))
      (η / 4) (by linarith)
    let h := min ((L - A) / 2) (min ((B' - U) / 2) (min (δ / 2) (η / (4 * (|C| + 1)))))
    have hCden : 0 < 4 * (|C| + 1) := by positivity
    have hh : 0 < h := by
      dsimp [h]
      positivity
    have hhLA : h ≤ (L - A) / 2 := by exact min_le_left _ _
    have hhUB : h ≤ (B' - U) / 2 := by
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hhδ : h ≤ δ / 2 := by
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hhC : h ≤ η / (4 * (|C| + 1)) := by
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hhL : h < L - A := by linarith
    have hhU : h < B' - U := by linarith
    have hhδ' : h < δ := by linarith
    have hCh : |C| * h ≤ η / 4 := by
      calc
        |C| * h ≤ |C| * (η / (4 * (|C| + 1))) :=
          mul_le_mul_of_nonneg_left hhC (abs_nonneg C)
        _ ≤ (|C| + 1) * (η / (4 * (|C| + 1))) := by
          gcongr
          linarith
        _ = η / 4 := by field_simp
    have hCsmall (d : ℝ) (hd0 : 0 ≤ d) (hdh : d ≤ h) : C * d ≤ η / 4 := by
      calc
        C * d ≤ |C| * d := mul_le_mul_of_nonneg_right (le_abs_self C) hd0
        _ ≤ |C| * h := mul_le_mul_of_nonneg_left hdh (abs_nonneg C)
        _ ≤ η / 4 := hCh
    have hεevent : ∀ᶠ j in atTop, |ε j| < η / 4 := by
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hε (η / 4) (by linarith)
      exact eventually_atTop.2 ⟨N, fun j hj => by simpa only [Real.dist_eq, sub_zero] using hN j hj⟩
    have hLevent : ∀ᶠ j in atTop,
        (∫ x in A..B', |f j x - g x|) < h * (η / 4) :=
      (tendsto_order.1 hL1).2 _ (mul_pos hh (by linarith))
    filter_upwards [hLevent, hεevent] with j hj hεj
    have integral_lower (a b : ℝ) (hAa : A ≤ a) (hab : a ≤ b) (hbB : b ≤ B')
        (hpoint : ∀ r ∈ Set.Icc a b, η / 4 ≤ |f j r - g r|) :
        (b - a) * (η / 4) ≤ ∫ x in A..B', |f j x - g x| := by
      have hsub : Set.uIoc a b ⊆ Set.uIoc A B' := by
        rw [Set.uIoc_of_le hab, Set.uIoc_of_le hAB.le]
        exact Set.Ioc_subset_Ioc hAa hbB
      calc
        (b - a) * (η / 4) = ∫ _r in a..b, (η / 4) := by
          simp only [intervalIntegral.integral_const, smul_eq_mul]
        _ ≤ ∫ r in a..b, |f j r - g r| :=
          intervalIntegral.integral_mono_on hab intervalIntegrable_const
            ((hφint j).mono_set' hsub) hpoint
        _ ≤ ∫ r in A..B', |f j r - g r| :=
          intervalIntegral.integral_mono_interval hAa hab hbB
            (Filter.Eventually.of_forall (fun r => abs_nonneg (f j r - g r))) (hφint j)
    intro x hx
    have hxgt : A < x := (hKsub hx).1
    have hxlt : x < B' := (hKsub hx).2
    have hxIcc : x ∈ Set.Icc A B' := ⟨hxgt.le, hxlt.le⟩
    by_contra hconv
    have hlarge : η ≤ |f j x - g x| := by
      apply le_of_not_gt
      simpa only [Real.dist_eq, abs_sub_comm] using hconv
    rcases le_total (g x) (f j x) with hxcase | hxcase
    · have hup : η ≤ f j x - g x := by
        rwa [abs_of_nonneg (sub_nonneg.mpr hxcase)] at hlarge
      have hxleft : A ≤ x - h := by
        have := hLlower x hx
        linarith
      have hleftpoint : ∀ r ∈ Set.Icc (x - h) x, η / 4 ≤ |f j r - g r| := by
        intro r hr
        have hrx : r ≤ x := hr.2
        have hrIcc : r ∈ Set.Icc A B' := ⟨hxleft.trans hr.1, hrx.trans hxlt.le⟩
        have hstep := hone j r x hrIcc hxIcc hrx
        have hdr : dist r x < δ := by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hrx)]
          have hrh : x - r ≤ h := by linarith [hr.1]
          simpa only [neg_sub] using hrh.trans_lt hhδ'
        have hgstep : |g r - g x| < η / 4 := by
          simpa only [Real.dist_eq] using hgδ r hrIcc x hxIcc hdr
        have hεhigh : ε j < η / 4 := (abs_lt.1 hεj).2
        have hghigh : g r - g x < η / 4 := (abs_lt.1 hgstep).2
        have hCxr : C * (x - r) ≤ η / 4 :=
          hCsmall (x - r) (sub_nonneg.mpr hrx) (by linarith [hr.1])
        have hvariation : f j x - f j r < η / 2 := calc
          f j x - f j r ≤ C * (x - r) + ε j := hstep
          _ < η / 4 + η / 4 := add_lt_add_of_le_of_lt hCxr hεhigh
          _ = η / 2 := by ring
        have hdiff : η / 4 < f j r - g r := by linarith
        rw [abs_of_nonneg (by linarith : 0 ≤ f j r - g r)]
        exact hdiff.le
      have hlow := integral_lower (x - h) x hxleft (by linarith) hxlt.le hleftpoint
      rw [show x - (x - h) = h by ring] at hlow
      linarith
    · have hdown : η ≤ g x - f j x := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxcase)] at hlarge
        linarith
      have hxright : x + h ≤ B' := by
        have := hUupper x hx
        linarith
      have hrightpoint : ∀ r ∈ Set.Icc x (x + h), η / 4 ≤ |f j r - g r| := by
        intro r hr
        have hxr : x ≤ r := hr.1
        have hrIcc : r ∈ Set.Icc A B' := ⟨hxgt.le.trans hxr, hr.2.trans hxright⟩
        have hstep := hone j x r hxIcc hrIcc hxr
        have hdr : dist x r < δ := by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxr)]
          have hrh : r - x ≤ h := by linarith [hr.2]
          simpa only [neg_sub] using hrh.trans_lt hhδ'
        have hgstep : |g x - g r| < η / 4 := by
          simpa only [Real.dist_eq] using hgδ x hxIcc r hrIcc hdr
        have hεhigh : ε j < η / 4 := (abs_lt.1 hεj).2
        have hghigh : g x - g r < η / 4 := (abs_lt.1 hgstep).2
        have hCxr : C * (r - x) ≤ η / 4 :=
          hCsmall (r - x) (sub_nonneg.mpr hxr) (by linarith [hr.2])
        have hvariation : f j r - f j x < η / 2 := calc
          f j r - f j x ≤ C * (r - x) + ε j := hstep
          _ < η / 4 + η / 4 := add_lt_add_of_le_of_lt hCxr hεhigh
          _ = η / 2 := by ring
        have hdiff : η / 4 < g r - f j r := by linarith
        rw [abs_of_nonpos (by linarith : f j r - g r ≤ 0)]
        simpa only [neg_sub] using hdiff.le
      have hlow := integral_lower x (x + h) hxgt.le (by linarith) hxright hrightpoint
      rw [show x + h - x = h by ring] at hlow
      linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hKne
    subst K
    exact Filter.Eventually.of_forall (fun _ => by simp)

end DiamondPinning
