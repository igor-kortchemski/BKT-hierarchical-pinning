module

public import DiamondPinning.Model.InstancePins
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Real

/-!
# The passage estimate

This file proves `response:ballot` (`source/response.tex`, lines 28–60).  It
first establishes the finite-product Harris inequality used at lines 48–57,
then combines independence with the stopped-sum and overshoot estimates to
obtain the uniform passage bound.
-/

@[expose] public section

namespace DiamondPinning

universe u

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

private lemma integrable_of_mem_Icc_zero_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    Integrable f μ := by
  exact .of_bound hf.aestronglyMeasurable 1 <| .of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    exact hf1 x

private lemma integral_le_one_of_mem_Icc_zero_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    ∫ x, f x ∂μ ≤ 1 := by
  have hint : Integrable f μ := integrable_of_mem_Icc_zero_one hf hf0 hf1
  calc
    ∫ x, f x ∂μ ≤ ∫ _x : Ω, (1 : ℝ) ∂μ := integral_mono hint (integrable_const 1) hf1
    _ = 1 := by simp

/-- The one-coordinate form of Harris's inequality, proved by integrating the
nonnegative product of increments over two independent copies. -/
private lemma harris_one {μ : Measure ℝ} [IsProbabilityMeasure μ] {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfm : Monotone f) (hgm : Monotone g)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ := by
  have hfi : Integrable f μ := integrable_of_mem_Icc_zero_one hf hf0 hf1
  have hgi : Integrable g μ := integrable_of_mem_Icc_zero_one hg hg0 hg1
  let H : ℝ × ℝ → ℝ := fun p => (f p.1 - f p.2) * (g p.1 - g p.2)
  have hH0 : ∀ p, 0 ≤ H p := by
    rintro ⟨x, y⟩
    rcases le_total x y with hxy | hyx
    · have h := mul_nonneg (sub_nonneg.mpr (hfm hxy)) (sub_nonneg.mpr (hgm hxy))
      dsimp [H]
      nlinarith
    · exact mul_nonneg (sub_nonneg.mpr (hfm hyx)) (sub_nonneg.mpr (hgm hyx))
  have hHmeas : Measurable H := by fun_prop
  have hHint : Integrable H ((μ.prod μ)) := by
    apply Integrable.of_bound hHmeas.aestronglyMeasurable 1
    apply Eventually.of_forall
    rintro ⟨x, y⟩
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · dsimp [H]
      by_cases hxy : x ≤ y
      · have hfx := hfm hxy
        have hgx := hgm hxy
        nlinarith [hf0 x, hf0 y, hf1 x, hf1 y, hg0 x, hg0 y, hg1 x, hg1 y]
      · have hyx : y ≤ x := le_of_not_ge hxy
        have hfx := hfm hyx
        have hgx := hgm hyx
        nlinarith [hf0 x, hf0 y, hf1 x, hf1 y, hg0 x, hg0 y, hg1 x, hg1 y]
    · dsimp [H]
      rcases le_total x y with hxy | hyx
      · have hfx := hfm hxy
        have hgx := hgm hxy
        nlinarith [hf0 x, hf0 y, hf1 x, hf1 y, hg0 x, hg0 y, hg1 x, hg1 y]
      · have hfx := hfm hyx
        have hgx := hgm hyx
        nlinarith [hf0 x, hf0 y, hf1 x, hf1 y, hg0 x, hg0 y, hg1 x, hg1 y]
  have hfg : Integrable (fun x => f x * g x) μ :=
    integrable_of_mem_Icc_zero_one (hf.mul hg) (fun x => mul_nonneg (hf0 x) (hg0 x))
      (fun x => by nlinarith [hf0 x, hg0 x, hf1 x, hg1 x])
  have hq1 : Integrable (fun p : ℝ × ℝ => f p.1 * g p.1) (μ.prod μ) :=
    hfg.comp_fst μ
  have hq2 : Integrable (fun p : ℝ × ℝ => f p.2 * g p.2) (μ.prod μ) :=
    hfg.comp_snd μ
  have hq3 : Integrable (fun p : ℝ × ℝ => f p.1 * g p.2) (μ.prod μ) :=
    hfi.mul_prod hgi
  have hq4 : Integrable (fun p : ℝ × ℝ => f p.2 * g p.1) (μ.prod μ) := by
    simpa [mul_comm] using hgi.mul_prod hfi
  have hH_eq : ∫ p, H p ∂(μ.prod μ) =
      2 * ((∫ x, f x * g x ∂μ) - (∫ x, f x ∂μ) * (∫ x, g x ∂μ)) := by
    have hpoint : H = fun p : ℝ × ℝ =>
        (f p.1 * g p.1 + f p.2 * g p.2) - (f p.1 * g p.2 + f p.2 * g p.1) := by
      funext p
      dsimp [H]
      ring
    rw [hpoint]
    change (∫ p : ℝ × ℝ,
      (f p.1 * g p.1 + f p.2 * g p.2) - (f p.1 * g p.2 + f p.2 * g p.1) ∂(μ.prod μ)) = _
    rw [MeasureTheory.integral_sub
      (f := fun p : ℝ × ℝ => f p.1 * g p.1 + f p.2 * g p.2)
      (g := fun p : ℝ × ℝ => f p.1 * g p.2 + f p.2 * g p.1)
      (hq1.add hq2) (hq3.add hq4),
      MeasureTheory.integral_add
        (f := fun p : ℝ × ℝ => f p.1 * g p.1)
        (g := fun p : ℝ × ℝ => f p.2 * g p.2) hq1 hq2,
      MeasureTheory.integral_add
        (f := fun p : ℝ × ℝ => f p.1 * g p.2)
        (g := fun p : ℝ × ℝ => f p.2 * g p.1) hq3 hq4]
    have hq1int : (∫ p : ℝ × ℝ, f p.1 * g p.1 ∂(μ.prod μ)) = ∫ x, f x * g x ∂μ := by
      simpa using integral_fun_fst (μ := μ) (ν := μ) (fun x => f x * g x)
    have hq2int : (∫ p : ℝ × ℝ, f p.2 * g p.2 ∂(μ.prod μ)) = ∫ x, f x * g x ∂μ := by
      simpa using integral_fun_snd (μ := μ) (ν := μ) (fun x => f x * g x)
    have hq4int : (∫ p : ℝ × ℝ, f p.2 * g p.1 ∂(μ.prod μ)) =
        (∫ x, g x ∂μ) * (∫ x, f x ∂μ) := by
      simpa [mul_comm] using integral_prod_mul (μ := μ) (ν := μ) g f
    rw [hq1int, hq2int, integral_prod_mul f g, hq4int]
    ring
  have hnonneg : 0 ≤ ∫ p, H p ∂(μ.prod μ) := integral_nonneg hH0
  rw [hH_eq] at hnonneg
  linarith


/-- Harris's inequality for bounded Borel functions on a finite product of
real probability measures. -/
lemma harris_pi (n : ℕ) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {f g : (∀ _i : Fin n, ℝ) → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfm : Monotone f) (hgm : Monotone g)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    (∫ x, f x ∂Measure.pi μ) * (∫ x, g x ∂Measure.pi μ) ≤
      ∫ x, f x * g x ∂Measure.pi μ := by
  induction n with
  | zero =>
      let x0 : (Fin 0 → ℝ) := fun i => Fin.elim0 i
      have hf_eq : f = fun _ => f x0 := by
        funext x
        congr
        funext i
        exact Fin.elim0 i
      have hg_eq : g = fun _ => g x0 := by
        funext x
        congr
        funext i
        exact Fin.elim0 i
      rw [hf_eq, hg_eq]
      simp
  | succ n ih =>
      let ν : Fin n → Measure ℝ := fun j => μ j.succ
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      let f0 : ℝ × (∀ j : Fin n, ℝ) → ℝ := fun p => f (e.symm p)
      let g0 : ℝ × (∀ j : Fin n, ℝ) → ℝ := fun p => g (e.symm p)
      have hf0meas : Measurable f0 := hf.comp e.symm.measurable
      have hg0meas : Measurable g0 := hg.comp e.symm.measurable
      have hf0bound0 : ∀ p, 0 ≤ f0 p := fun p => hf0 _
      have hf0bound1 : ∀ p, f0 p ≤ 1 := fun p => hf1 _
      have hg0bound0 : ∀ p, 0 ≤ g0 p := fun p => hg0 _
      have hg0bound1 : ∀ p, g0 p ≤ 1 := fun p => hg1 _
      have hf0int : Integrable f0 ((μ 0).prod (Measure.pi ν)) :=
        integrable_of_mem_Icc_zero_one hf0meas hf0bound0 hf0bound1
      have hg0int : Integrable g0 ((μ 0).prod (Measure.pi ν)) :=
        integrable_of_mem_Icc_zero_one hg0meas hg0bound0 hg0bound1
      have hmp : MeasurePreserving e (Measure.pi μ)
          ((μ 0).prod (Measure.pi ν)) := by
        simpa [e, ν, Fin.succAbove_zero] using measurePreserving_piFinSuccAbove μ 0
      have hf_fubini : (∫ x, f x ∂Measure.pi μ) =
          ∫ r, ∫ y, f0 (r, y) ∂Measure.pi ν ∂μ 0 := by
        calc
          (∫ x, f x ∂Measure.pi μ) = ∫ p, f0 p ∂((μ 0).prod (Measure.pi ν)) := by
            simpa [f0] using hmp.integral_comp' f0
          _ = ∫ r, ∫ y, f0 (r, y) ∂Measure.pi ν ∂μ 0 := integral_prod f0 hf0int
      have hg_fubini : (∫ x, g x ∂Measure.pi μ) =
          ∫ r, ∫ y, g0 (r, y) ∂Measure.pi ν ∂μ 0 := by
        calc
          (∫ x, g x ∂Measure.pi μ) = ∫ p, g0 p ∂((μ 0).prod (Measure.pi ν)) := by
            simpa [g0] using hmp.integral_comp' g0
          _ = ∫ r, ∫ y, g0 (r, y) ∂Measure.pi ν ∂μ 0 := integral_prod g0 hg0int
      let F : ℝ → ℝ := fun r => ∫ y, f0 (r, y) ∂Measure.pi ν
      let G : ℝ → ℝ := fun r => ∫ y, g0 (r, y) ∂Measure.pi ν
      have hsection_mono (r s : ℝ) (hrs : r ≤ s) (h : (∀ i : Fin (n + 1), ℝ) → ℝ)
          (hm : Monotone h) (y : Fin n → ℝ) :
          h (e.symm (r, y)) ≤ h (e.symm (s, y)) := by
        apply hm
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using hrs
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      have hFmeas : Measurable F := by
        exact (hf0meas.stronglyMeasurable.integral_prod_right'
          (ν := Measure.pi ν)).measurable
      have hGmeas : Measurable G := by
        exact (hg0meas.stronglyMeasurable.integral_prod_right'
          (ν := Measure.pi ν)).measurable
      have hFmono : Monotone F := by
        intro r s hrs
        apply integral_mono
        · exact integrable_of_mem_Icc_zero_one
            (hf0meas.comp (measurable_const.prodMk measurable_id))
            (fun y => hf0bound0 _) (fun y => hf0bound1 _)
        · exact integrable_of_mem_Icc_zero_one
            (hf0meas.comp (measurable_const.prodMk measurable_id))
            (fun y => hf0bound0 _) (fun y => hf0bound1 _)
        · exact fun y => hsection_mono r s hrs f hfm y
      have hGmono : Monotone G := by
        intro r s hrs
        apply integral_mono
        · exact integrable_of_mem_Icc_zero_one
            (hg0meas.comp (measurable_const.prodMk measurable_id))
            (fun y => hg0bound0 _) (fun y => hg0bound1 _)
        · exact integrable_of_mem_Icc_zero_one
            (hg0meas.comp (measurable_const.prodMk measurable_id))
            (fun y => hg0bound0 _) (fun y => hg0bound1 _)
        · exact fun y => hsection_mono r s hrs g hgm y
      have hF0 : ∀ r, 0 ≤ F r := fun r => integral_nonneg (fun y => hf0bound0 _)
      have hG0 : ∀ r, 0 ≤ G r := fun r => integral_nonneg (fun y => hg0bound0 _)
      have hF1 : ∀ r, F r ≤ 1 := by
        intro r
        exact integral_le_one_of_mem_Icc_zero_one
          (hf0meas.comp (measurable_const.prodMk measurable_id))
          (fun y => hf0bound0 _) (fun y => hf0bound1 _)
      have hG1 : ∀ r, G r ≤ 1 := by
        intro r
        exact integral_le_one_of_mem_Icc_zero_one
          (hg0meas.comp (measurable_const.prodMk measurable_id))
          (fun y => hg0bound0 _) (fun y => hg0bound1 _)
      have hFG : (∫ r, F r ∂μ 0) * (∫ r, G r ∂μ 0) ≤ ∫ r, F r * G r ∂μ 0 :=
        harris_one hFmeas hGmeas hFmono hGmono hF0 hF1 hG0 hG1
      have hpoint : ∀ r, F r * G r ≤ ∫ y, f0 (r, y) * g0 (r, y) ∂Measure.pi ν := by
        intro r
        apply ih ν
        · exact hf0meas.comp (measurable_const.prodMk measurable_id)
        · exact hg0meas.comp (measurable_const.prodMk measurable_id)
        · intro y z hyz
          apply hfm
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
          · simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using hyz j
        · intro y z hyz
          apply hgm
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
          · simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using hyz j
        · exact fun y => hf0bound0 _
        · exact fun y => hf0bound1 _
        · exact fun y => hg0bound0 _
        · exact fun y => hg0bound1 _
      have hFGint : Integrable (fun r => F r * G r) (μ 0) :=
        integrable_of_mem_Icc_zero_one (hFmeas.mul hGmeas)
          (fun r => mul_nonneg (hF0 r) (hG0 r))
          (fun r => by nlinarith [hF0 r, hG0 r, hF1 r, hG1 r])
      have hHmeas : Measurable (fun r => ∫ y, f0 (r, y) * g0 (r, y) ∂Measure.pi ν) := by
        exact ((hf0meas.mul hg0meas).stronglyMeasurable.integral_prod_right'
          (ν := Measure.pi ν)).measurable
      have hHint : Integrable (fun r => ∫ y, f0 (r, y) * g0 (r, y) ∂Measure.pi ν) (μ 0) := by
        apply integrable_of_mem_Icc_zero_one hHmeas
        · intro r
          exact integral_nonneg (fun y => mul_nonneg (hf0bound0 _) (hg0bound0 _))
        · intro r
          exact integral_le_one_of_mem_Icc_zero_one ((hf0meas.mul hg0meas).comp
            (measurable_const.prodMk measurable_id))
            (fun y => mul_nonneg (hf0bound0 _) (hg0bound0 _))
            (fun y => calc
              f0 (r, y) * g0 (r, y) ≤ 1 * 1 := mul_le_mul (hf0bound1 _)
                (hg0bound1 _) (hg0bound0 _) zero_le_one
              _ = 1 := one_mul 1)
      have hfg0int : Integrable (fun p => f0 p * g0 p) ((μ 0).prod (Measure.pi ν)) :=
        integrable_of_mem_Icc_zero_one (hf0meas.mul hg0meas)
          (fun p => mul_nonneg (hf0bound0 p) (hg0bound0 p))
          (fun p => by nlinarith [hf0bound0 p, hg0bound0 p, hf0bound1 p, hg0bound1 p])
      have hfg_fubini : (∫ x, f x * g x ∂Measure.pi μ) =
          ∫ r, ∫ y, f0 (r, y) * g0 (r, y) ∂Measure.pi ν ∂μ 0 := by
        calc
          (∫ x, f x * g x ∂Measure.pi μ) =
              ∫ p, f0 p * g0 p ∂((μ 0).prod (Measure.pi ν)) := by
            simpa [f0, g0] using hmp.integral_comp' (fun p => f0 p * g0 p)
          _ = ∫ r, ∫ y, f0 (r, y) * g0 (r, y) ∂Measure.pi ν ∂μ 0 :=
            integral_prod _ hfg0int
      rw [hf_fubini, hg_fubini, hfg_fubini]
      exact hFG.trans (integral_mono hFGint hHint hpoint)


private lemma indicator_monotone_of_upper {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, x ≤ y → y ∈ A) :
    Monotone (A.indicator (1 : (Fin n → ℝ) → ℝ)) := by
  intro x y hxy
  by_cases hx : x ∈ A
  · have hy : y ∈ A := hA hx hxy
    simp [Set.indicator_of_mem, hx, hy]
  · by_cases hy : y ∈ A <;> simp [hx, hy]

/-- Independent finite families satisfy Harris's inequality for measurable
upper events: the product of the two probabilities bounds the probability of
their intersection. -/
lemma harris_upper_iIndepFun {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Fin n → Ω → ℝ)
    (hYindep : iIndepFun Y μ) (hYmeas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (A D : Set (Fin n → ℝ)) (hA : MeasurableSet A) (hD : MeasurableSet D)
    (hAupper : ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, x ≤ y → y ∈ A)
    (hDupper : ∀ ⦃x⦄, x ∈ D → ∀ ⦃y⦄, x ≤ y → y ∈ D) :
    μ.real ((fun ω i => Y i ω) ⁻¹' A) * μ.real ((fun ω i => Y i ω) ⁻¹' D) ≤
      μ.real ((fun ω i => Y i ω) ⁻¹' (A ∩ D)) := by
  have htuple : AEMeasurable (fun ω i => Y i ω) μ := .of_eval fun i => (hYmeas i).aemeasurable
  have hmap : μ.map (fun ω i => Y i ω) = Measure.pi (fun i => μ.map (Y i)) :=
    hYindep.map_fun_eq_pi_map (fun i => (hYmeas i).aemeasurable)
  have hfmeas : Measurable (A.indicator (1 : (Fin n → ℝ) → ℝ)) :=
    measurable_one.indicator hA
  have hgmeas : Measurable (D.indicator (1 : (Fin n → ℝ) → ℝ)) :=
    measurable_one.indicator hD
  have hf0 : ∀ x, 0 ≤ A.indicator (1 : (Fin n → ℝ) → ℝ) x := by
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have hg0 : ∀ x, 0 ≤ D.indicator (1 : (Fin n → ℝ) → ℝ) x := by
    intro x
    by_cases hx : x ∈ D <;> simp [hx]
  have hf1 : ∀ x, A.indicator (1 : (Fin n → ℝ) → ℝ) x ≤ 1 := by
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have hg1 : ∀ x, D.indicator (1 : (Fin n → ℝ) → ℝ) x ≤ 1 := by
    intro x
    by_cases hx : x ∈ D <;> simp [hx]
  have h := harris_pi n (fun i => μ.map (Y i)) hfmeas hgmeas
    (indicator_monotone_of_upper hAupper) (indicator_monotone_of_upper hDupper)
    hf0 hf1 hg0 hg1
  have hind : (fun x => A.indicator (1 : (Fin n → ℝ) → ℝ) x *
      D.indicator (1 : (Fin n → ℝ) → ℝ) x) = (A ∩ D).indicator 1 := by
    funext x
    by_cases hxA : x ∈ A <;> by_cases hxD : x ∈ D <;>
      simp [hxA, hxD]
  rw [← hmap, integral_indicator_one hA, integral_indicator_one hD, hind,
    integral_indicator_one (hA.inter hD),
    map_measureReal_apply_of_aemeasurable htuple hA,
    map_measureReal_apply_of_aemeasurable htuple hD,
    map_measureReal_apply_of_aemeasurable htuple (hA.inter hD)] at h
  exact h


private def ballotSum {Ω : Type*} (Y : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω => ∑ j ∈ Finset.range k, Y j ω

private def ballotSurvival {Ω : Type*} (Y : ℕ → Ω → ℝ) (z : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ k ≤ n, -z ≤ ballotSum Y k ω}

private noncomputable def ballotStopped {Ω : Type*} (Y : ℕ → Ω → ℝ) (z : ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ j ∈ Finset.range n, (ballotSurvival Y z j).indicator 1 ω * Y j ω

private lemma measurable_ballotSum {Ω : Type*} [MeasurableSpace Ω]
    {Y : ℕ → Ω → ℝ} (hY : ∀ j, Measurable (Y j)) (k : ℕ) :
    Measurable (ballotSum Y k) := by
  exact Finset.measurable_sum _ (fun j _ => hY j)

private lemma measurable_ballotSurvival {Ω : Type*} [MeasurableSpace Ω]
    {Y : ℕ → Ω → ℝ} (hY : ∀ j, Measurable (Y j)) (z : ℝ) (n : ℕ) :
    MeasurableSet (ballotSurvival Y z n) := by
  have hset : ballotSurvival Y z n =
      ⋂ k : Fin (n + 1), {ω | -z ≤ ballotSum Y k ω} := by
    ext ω
    simp only [ballotSurvival, Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h i
      exact h i (Nat.lt_succ_iff.mp i.isLt)
    · intro h k hk
      exact h ⟨k, Nat.lt_succ_iff.mpr hk⟩
  rw [hset]
  exact MeasurableSet.iInter fun k => measurableSet_le measurable_const
    (measurable_ballotSum hY k)

private lemma ballotSurvival_anti {Ω : Type*} {Y : ℕ → Ω → ℝ} {z : ℝ}
    {m n : ℕ} (hmn : m ≤ n) : ballotSurvival Y z n ⊆ ballotSurvival Y z m := by
  intro ω hω k hk
  exact hω k (hk.trans hmn)

private lemma ballotStopped_eq_on_survival {Ω : Type*} {Y : ℕ → Ω → ℝ}
    {z : ℝ} {n : ℕ} {ω : Ω} (hω : ω ∈ ballotSurvival Y z n) :
    ballotStopped Y z n ω = ballotSum Y n ω := by
  unfold ballotStopped ballotSum
  apply Finset.sum_congr rfl
  intro j hj
  rw [Set.indicator_of_mem (ballotSurvival_anti (Nat.le_of_lt
    (Finset.mem_range.mp hj)) hω), Pi.one_apply, one_mul]

private lemma ballotStopped_succ {Ω : Type*} (Y : ℕ → Ω → ℝ) (z : ℝ) (n : ℕ) :
    ballotStopped Y z (n + 1) = fun ω => ballotStopped Y z n ω +
      (ballotSurvival Y z n).indicator 1 ω * Y n ω := by
  funext ω
  simp [ballotStopped, Finset.sum_range_succ]

private lemma neg_negPart_le' (x : ℝ) : -x⁻ ≤ x := by
  have h := posPart_sub_negPart x
  have hp := posPart_nonneg x
  linarith

private lemma ballotStopped_lower {Ω : Type*} [MeasurableSpace Ω] (Y : ℕ → Ω → ℝ)
    (μ : Measure Ω) {b z : ℝ} (hb : 0 ≤ b) (hz : 0 ≤ z)
    (hYlower : ∀ j, 1 ≤ j → ∀ᵐ ω ∂μ, -b ≤ Y j ω) (n : ℕ) :
    ∀ᵐ ω ∂μ, -z - b - (Y 0 ω)⁻ ≤ ballotStopped Y z n ω := by
  have hlow : ∀ᵐ ω ∂μ, ∀ j, -b ≤ Y (j + 1) ω :=
    ae_all_iff.mpr fun j => hYlower (j + 1) (Nat.succ_pos _)
  filter_upwards [hlow] with ω hω
  induction n with
  | zero =>
      simp only [ballotStopped, Finset.range_zero, Finset.sum_empty]
      have h0 := negPart_nonneg (Y 0 ω)
      linarith
  | succ n ih =>
      rw [ballotStopped_succ]
      dsimp only
      by_cases hA : ω ∈ ballotSurvival Y z n
      · rw [Set.indicator_of_mem hA, Pi.one_apply, one_mul, ballotStopped_eq_on_survival hA]
        have hS : -z ≤ ballotSum Y n ω := hA n le_rfl
        cases n with
        | zero =>
            simp only [ballotSum, Finset.range_zero, Finset.sum_empty, zero_add]
            have h0 := neg_negPart_le' (Y 0 ω)
            linarith
        | succ n =>
            have hY := hω n
            have h0 := negPart_nonneg (Y 0 ω)
            linarith
      · rw [Set.indicator_of_notMem hA, zero_mul, add_zero]
        exact ih


private def ballotPrefixSurvival (z : ℝ) (n : ℕ) :
    Set (({x // x ∈ Finset.range n}) → ℝ) :=
  {x | ∀ k ≤ n, -z ≤ ∑ j ∈ Finset.range k,
    if hj : j < n then x ⟨j, Finset.mem_range.mpr hj⟩ else 0}

private lemma measurable_ballotPrefixSurvival (z : ℝ) (n : ℕ) :
    MeasurableSet (ballotPrefixSurvival z n) := by
  have hset : ballotPrefixSurvival z n = ⋂ k : Fin (n + 1),
      {x | -z ≤ ∑ j ∈ Finset.range k,
        if hj : j < n then x ⟨j, Finset.mem_range.mpr hj⟩ else 0} := by
    ext x
    simp only [ballotPrefixSurvival, Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h i
      exact h i (Nat.lt_succ_iff.mp i.isLt)
    · intro h k hk
      exact h ⟨k, Nat.lt_succ_iff.mpr hk⟩
  rw [hset]
  apply MeasurableSet.iInter
  intro k
  apply measurableSet_le measurable_const
  apply Finset.measurable_sum
  intro j hj
  by_cases hjn : j < n
  · simp only [hjn, dite_eq_left]
    exact measurable_pi_apply _
  · simp [hjn]

private lemma ballotPrefixSurvival_preimage {Ω : Type*} (Y : ℕ → Ω → ℝ)
    (z : ℝ) (n : ℕ) :
    (fun ω (j : {x // x ∈ Finset.range n}) => Y j ω) ⁻¹' ballotPrefixSurvival z n =
      ballotSurvival Y z n := by
  ext ω
  simp only [Set.mem_preimage, ballotPrefixSurvival, ballotSurvival, Set.mem_ofPred_eq]
  constructor <;> intro h k hk
  · have h' := h k hk
    have hsum : (∑ j ∈ Finset.range k,
        if hj : j < n then Y j ω else 0) = ballotSum Y k ω := by
      unfold ballotSum
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < n := (Finset.mem_range.mp hj).trans_le hk
      simp [hjn]
    rw [← hsum]
    exact h'
  · have h' := h k hk
    have hsum : (∑ j ∈ Finset.range k,
        if hj : j < n then Y j ω else 0) = ballotSum Y k ω := by
      unfold ballotSum
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < n := (Finset.mem_range.mp hj).trans_le hk
      simp [hjn]
    rw [hsum]
    exact h'

private lemma indep_ballotSurvival {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (hYindep : iIndepFun Y μ)
    (hYmeas : ∀ j, Measurable (Y j)) (z : ℝ) (n : ℕ) :
    IndepFun ((ballotSurvival Y z n).indicator (1 : Ω → ℝ)) (Y n) μ := by
  have hdisj : Disjoint (Finset.range n) ({n} : Finset ℕ) :=
    by simp
  have hblock := hYindep.indepFun_finset (Finset.range n) {n} hdisj hYmeas
  have hcomp := hblock.comp
    (φ := (ballotPrefixSurvival z n).indicator
      (1 : (({x // x ∈ Finset.range n}) → ℝ) → ℝ))
    (ψ := fun x : ({x // x ∈ ({n} : Finset ℕ)}) → ℝ =>
      x ⟨n, Finset.mem_singleton_self n⟩)
    (measurable_one.indicator (measurable_ballotPrefixSurvival z n))
    (show Measurable (fun x : ({x // x ∈ ({n} : Finset ℕ)}) → ℝ =>
      x ⟨n, Finset.mem_singleton_self n⟩) from measurable_pi_apply _)

  have hleft : (ballotPrefixSurvival z n).indicator
      (1 : (({x // x ∈ Finset.range n}) → ℝ) → ℝ) ∘
      (fun ω (j : {x // x ∈ Finset.range n}) => Y j ω) =
      (ballotSurvival Y z n).indicator (1 : Ω → ℝ) := by
    funext ω
    rw [Function.comp_apply, ← ballotPrefixSurvival_preimage Y z n]
    by_cases hω : (fun ω (j : {x // x ∈ Finset.range n}) => Y j ω) ω ∈
        ballotPrefixSurvival z n <;> simp [hω]
  rw [hleft] at hcomp
  simpa only [id_eq, Function.comp_def] using hcomp


private lemma integrable_ballot_term {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (hYmeas : ∀ j, Measurable (Y j))
    (hYint : ∀ j, Integrable (Y j) μ) (z : ℝ) (j : ℕ) :
    Integrable (fun ω => (ballotSurvival Y z j).indicator 1 ω * Y j ω) μ := by
  have hA : MeasurableSet (ballotSurvival Y z j) := measurable_ballotSurvival hYmeas z j
  apply (hYint j).bdd_mul (c := 1)
    (measurable_one.indicator hA).aestronglyMeasurable
  apply Eventually.of_forall
  intro ω
  by_cases hω : ω ∈ ballotSurvival Y z j <;>
    simp [hω]

private lemma integrable_ballotStopped {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (hYmeas : ∀ j, Measurable (Y j))
    (hYint : ∀ j, Integrable (Y j) μ) (z : ℝ) (n : ℕ) :
    Integrable (ballotStopped Y z n) μ := by
  apply integrable_finsetSum
  intro j hj
  exact integrable_ballot_term μ Y hYmeas hYint z j

private lemma integral_ballotStopped_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hYindep : iIndepFun Y μ) (hYmeas : ∀ j, Measurable (Y j))
    (hYint : ∀ j, Integrable (Y j) μ) {mPos : ℝ}
    (hmean : Summable (fun j => (∫ ω, Y j ω ∂μ)⁺))
    (hmPos : ∑' j, (∫ ω, Y j ω ∂μ)⁺ ≤ mPos) (z : ℝ) (n : ℕ) :
    ∫ ω, ballotStopped Y z n ω ∂μ ≤ mPos := by
  have hterm_int : ∀ j, Integrable
      (fun ω => (ballotSurvival Y z j).indicator 1 ω * Y j ω) μ :=
    integrable_ballot_term μ Y hYmeas hYint z
  have hterm (j : ℕ) : (∫ ω, (ballotSurvival Y z j).indicator 1 ω * Y j ω ∂μ) =
      μ.real (ballotSurvival Y z j) * (∫ ω, Y j ω ∂μ) := by
    have hi := (indep_ballotSurvival μ Y hYindep hYmeas z j).integral_mul_eq_mul_integral
      ((measurable_one.indicator (measurable_ballotSurvival hYmeas z j)).aestronglyMeasurable)
      (hYmeas j).aestronglyMeasurable
    simpa only [Pi.mul_apply,
      integral_indicator_one (measurable_ballotSurvival hYmeas z j)] using hi
  calc
    (∫ ω, ballotStopped Y z n ω ∂μ) =
        ∑ j ∈ Finset.range n, ∫ ω, (ballotSurvival Y z j).indicator 1 ω * Y j ω ∂μ :=
      integral_finsetSum _ (fun j _ => hterm_int j)
    _ = ∑ j ∈ Finset.range n, μ.real (ballotSurvival Y z j) * (∫ ω, Y j ω ∂μ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm j
    _ ≤ ∑ j ∈ Finset.range n, (∫ ω, Y j ω ∂μ)⁺ := by
      apply Finset.sum_le_sum
      intro j hj
      have hp0 : 0 ≤ μ.real (ballotSurvival Y z j) := measureReal_nonneg
      have hp1 : μ.real (ballotSurvival Y z j) ≤ 1 := measureReal_le_one
      by_cases hm : 0 ≤ ∫ ω, Y j ω ∂μ
      · calc
          μ.real (ballotSurvival Y z j) * (∫ ω, Y j ω ∂μ) ≤ 1 * (∫ ω, Y j ω ∂μ) :=
            mul_le_mul_of_nonneg_right hp1 hm
          _ = (∫ ω, Y j ω ∂μ)⁺ := by rw [one_mul, posPart_eq_self.mpr hm]
      · have hm' : (∫ ω, Y j ω ∂μ) ≤ 0 := le_of_not_ge hm
        exact (mul_nonpos_of_nonneg_of_nonpos hp0 hm').trans (posPart_nonneg _)
    _ ≤ ∑' j, (∫ ω, Y j ω ∂μ)⁺ :=
      hmean.sum_le_tsum _ (fun j _ => posPart_nonneg _)
    _ ≤ mPos := hmPos

private lemma ballot_setIntegral_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hYindep : iIndepFun Y μ) (hYmeas : ∀ j, Measurable (Y j))
    (hYint : ∀ j, Integrable (Y j) μ) {b mNeg mPos z : ℝ}
    (hb : 0 ≤ b) (hz : 0 ≤ z)
    (hYlower : ∀ j, 1 ≤ j → ∀ᵐ ω ∂μ, -b ≤ Y j ω)
    (hY0neg : Integrable (fun ω => (Y 0 ω)⁻) μ)
    (hmNeg : ∫ ω, (Y 0 ω)⁻ ∂μ ≤ mNeg)
    (hmean : Summable (fun j => (∫ ω, Y j ω ∂μ)⁺))
    (hmPos : ∑' j, (∫ ω, Y j ω ∂μ)⁺ ≤ mPos) (n : ℕ) :
    ∫ ω in ballotSurvival Y z n, (ballotSum Y n ω + z + b) ∂μ ≤ mPos + z + b + mNeg := by
  have hA : MeasurableSet (ballotSurvival Y z n) := measurable_ballotSurvival hYmeas z n
  have hSint : Integrable (ballotSum Y n) μ := by
    apply integrable_finsetSum
    intro j hj
    exact hYint j
  have hLint : Integrable (fun ω => ballotSum Y n ω + z + b) μ :=
    (hSint.add (integrable_const z)).add (integrable_const b)
  have hTint : Integrable (ballotStopped Y z n) μ :=
    integrable_ballotStopped μ Y hYmeas hYint z n
  have hRint : Integrable (fun ω => ballotStopped Y z n ω + (z + b) + (Y 0 ω)⁻) μ :=
    (hTint.add (integrable_const (z + b))).add hY0neg
  rw [← integral_indicator hA]
  calc
    (∫ ω, (ballotSurvival Y z n).indicator (fun ω => ballotSum Y n ω + z + b) ω ∂μ) ≤
        ∫ ω, (ballotStopped Y z n ω + (z + b) + (Y 0 ω)⁻) ∂μ := by
      apply integral_mono_ae (hLint.indicator hA) hRint
      filter_upwards [ballotStopped_lower Y μ hb hz hYlower n] with ω hω
      by_cases hAω : ω ∈ ballotSurvival Y z n
      · rw [Set.indicator_of_mem hAω, ballotStopped_eq_on_survival hAω]
        have h0 := negPart_nonneg (Y 0 ω)
        linarith
      · rw [Set.indicator_of_notMem hAω]
        linarith
    _ = (∫ ω, ballotStopped Y z n ω ∂μ) + (z + b) + ∫ ω, (Y 0 ω)⁻ ∂μ := by
      rw [MeasureTheory.integral_add
        (f := fun ω => ballotStopped Y z n ω + (z + b))
        (g := fun ω => (Y 0 ω)⁻) (hTint.add (integrable_const (z + b))) hY0neg,
        MeasureTheory.integral_add
          (f := ballotStopped Y z n) (g := fun _ => z + b)
          hTint (integrable_const (z + b)), integral_const]
      simp
    _ ≤ mPos + z + b + mNeg := by
      have hT := integral_ballotStopped_le μ Y hYindep hYmeas hYint hmean hmPos z n
      linarith


private def ballotProductSurvival (z : ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ k ≤ n, -z ≤ ∑ j ∈ Finset.range k,
    if hj : j < n then x ⟨j, hj⟩ else 0}

private def ballotProductTail (η : ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  {x | η * n ≤ ∑ j : Fin n, x j}

private lemma measurable_ballotProductSurvival (z : ℝ) (n : ℕ) :
    MeasurableSet (ballotProductSurvival z n) := by
  have hset : ballotProductSurvival z n = ⋂ k : Fin (n + 1),
      {x | -z ≤ ∑ j ∈ Finset.range k, if hj : j < n then x ⟨j, hj⟩ else 0} := by
    ext x
    simp only [ballotProductSurvival, Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h i
      exact h i (Nat.lt_succ_iff.mp i.isLt)
    · intro h k hk
      exact h ⟨k, Nat.lt_succ_iff.mpr hk⟩
  rw [hset]
  apply MeasurableSet.iInter
  intro k
  apply measurableSet_le measurable_const
  apply Finset.measurable_sum
  intro j hj
  by_cases hjn : j < n
  · simp only [hjn, dite_eq_left]
    exact measurable_pi_apply _
  · simp [hjn]

private lemma upper_ballotProductSurvival {z : ℝ} {n : ℕ} :
    ∀ ⦃x⦄, x ∈ ballotProductSurvival z n → ∀ ⦃y⦄, x ≤ y →
      y ∈ ballotProductSurvival z n := by
  intro x hx y hxy k hk
  apply (hx k hk).trans
  apply Finset.sum_le_sum
  intro j hj
  by_cases hjn : j < n
  · simp only [hjn, dite_eq_left]
    exact hxy _
  · simp [hjn]

private lemma measurable_ballotProductTail (η : ℝ) (n : ℕ) :
    MeasurableSet (ballotProductTail η n) := by
  exact measurableSet_le measurable_const
    (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))

private lemma upper_ballotProductTail {η : ℝ} {n : ℕ} :
    ∀ ⦃x⦄, x ∈ ballotProductTail η n → ∀ ⦃y⦄, x ≤ y → y ∈ ballotProductTail η n := by
  intro x hx y hxy
  exact hx.trans (Finset.sum_le_sum fun j _ => hxy j)

private lemma ballotProductSurvival_preimage {Ω : Type*} (Y : ℕ → Ω → ℝ)
    (z : ℝ) (n : ℕ) :
    (fun ω (j : Fin n) => Y j ω) ⁻¹' ballotProductSurvival z n = ballotSurvival Y z n := by
  ext ω
  simp only [Set.mem_preimage, ballotProductSurvival, ballotSurvival, Set.mem_ofPred_eq]
  constructor <;> intro h k hk
  · have h' := h k hk
    have hsum : (∑ j ∈ Finset.range k, if hj : j < n then Y j ω else 0) =
        ballotSum Y k ω := by
      unfold ballotSum
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < n := (Finset.mem_range.mp hj).trans_le hk
      simp [hjn]
    rw [← hsum]
    exact h'
  · have h' := h k hk
    have hsum : (∑ j ∈ Finset.range k, if hj : j < n then Y j ω else 0) =
        ballotSum Y k ω := by
      unfold ballotSum
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < n := (Finset.mem_range.mp hj).trans_le hk
      simp [hjn]
    rw [hsum]
    exact h'

private lemma ballotProductTail_preimage {Ω : Type*} (Y : ℕ → Ω → ℝ)
    (η : ℝ) (n : ℕ) :
    (fun ω (j : Fin n) => Y j ω) ⁻¹' ballotProductTail η n =
      {ω | η * n ≤ ballotSum Y n ω} := by
  ext ω
  simp only [Set.mem_preimage, ballotProductTail, Set.mem_ofPred_eq]
  exact iff_of_eq (congrArg (fun t => η * (n : ℝ) ≤ t)
    (Fin.sum_univ_eq_sum_range (fun j => Y j ω) n))

private lemma ballot_main_inequality {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hYindep : iIndepFun Y μ) (hYmeas : ∀ j, Measurable (Y j))
    (hYint : ∀ j, Integrable (Y j) μ) {b η δ mNeg mPos z : ℝ}
    (hb : 0 ≤ b) (hη : 0 < η) (hz : 0 ≤ z)
    (hYlower : ∀ j, 1 ≤ j → ∀ᵐ ω ∂μ, -b ≤ Y j ω)
    (hY0neg : Integrable (fun ω => (Y 0 ω)⁻) μ)
    (hmNeg : ∫ ω, (Y 0 ω)⁻ ∂μ ≤ mNeg)
    (hmean : Summable (fun j => (∫ ω, Y j ω ∂μ)⁺))
    (hmPos : ∑' j, (∫ ω, Y j ω ∂μ)⁺ ≤ mPos) (n : ℕ)
    (htail : δ ≤ μ.real {ω | η * n ≤ ballotSum Y n ω}) :
    η * n * (δ * μ.real (ballotSurvival Y z n)) ≤ mPos + z + b + mNeg := by
  have hYfin : iIndepFun (fun j : Fin n => Y j) μ :=
    hYindep.precomp (g := fun j : Fin n => (j : ℕ)) Fin.val_injective
  have hh := harris_upper_iIndepFun μ (fun j : Fin n => Y j) hYfin
    (fun j => (hYmeas j).aestronglyMeasurable)
    (ballotProductSurvival z n) (ballotProductTail η n)
    (measurable_ballotProductSurvival z n) (measurable_ballotProductTail η n)
    upper_ballotProductSurvival upper_ballotProductTail
  simp only [ballotProductSurvival_preimage, ballotProductTail_preimage, Set.preimage_inter] at hh
  have hprob : δ * μ.real (ballotSurvival Y z n) ≤
      μ.real (ballotSurvival Y z n ∩ {ω | η * n ≤ ballotSum Y n ω}) := by
    calc
      δ * μ.real (ballotSurvival Y z n) ≤
          μ.real {ω | η * n ≤ ballotSum Y n ω} * μ.real (ballotSurvival Y z n) :=
        mul_le_mul_of_nonneg_right htail measureReal_nonneg
      _ = μ.real (ballotSurvival Y z n) * μ.real {ω | η * n ≤ ballotSum Y n ω} := mul_comm _ _
      _ ≤ _ := hh
  have hA : MeasurableSet (ballotSurvival Y z n) := measurable_ballotSurvival hYmeas z n
  have hD : MeasurableSet {ω | η * n ≤ ballotSum Y n ω} :=
    measurableSet_le measurable_const (measurable_ballotSum hYmeas n)
  have hSint : Integrable (ballotSum Y n) μ := by
    apply integrable_finsetSum
    intro j hj
    exact hYint j
  have hLint : Integrable (fun ω => ballotSum Y n ω + z + b) μ :=
    (hSint.add (integrable_const z)).add (integrable_const b)
  have hlow : η * n * (δ * μ.real (ballotSurvival Y z n)) ≤
      ∫ ω in ballotSurvival Y z n, (ballotSum Y n ω + z + b) ∂μ := by
    calc
      η * n * (δ * μ.real (ballotSurvival Y z n)) ≤
          η * n * μ.real (ballotSurvival Y z n ∩ {ω | η * n ≤ ballotSum Y n ω}) := by
        apply mul_le_mul_of_nonneg_left hprob
        positivity
      _ = ∫ ω in ballotSurvival Y z n ∩ {ω | η * n ≤ ballotSum Y n ω}, (η * n : ℝ) ∂μ := by
        rw [setIntegral_const (μ := μ)]
        simp only [smul_eq_mul]
        ring
      _ = ∫ ω, (ballotSurvival Y z n ∩ {ω | η * n ≤ ballotSum Y n ω}).indicator
          (fun _ => η * n) ω ∂μ := (integral_indicator (μ := μ) (hA.inter hD)).symm
      _ ≤ ∫ ω, (ballotSurvival Y z n).indicator
          (fun ω => ballotSum Y n ω + z + b) ω ∂μ := by
        apply integral_mono ((integrable_const (η * n)).indicator (hA.inter hD))
          (hLint.indicator hA)
        intro ω
        by_cases hAω : ω ∈ ballotSurvival Y z n
        · have hS := hAω n le_rfl
          by_cases hDω : η * (n : ℝ) ≤ ballotSum Y n ω
          · have hAD : ω ∈ ballotSurvival Y z n ∩
                {ω | η * (n : ℝ) ≤ ballotSum Y n ω} := ⟨hAω, hDω⟩
            rw [Set.indicator_of_mem hAD, Set.indicator_of_mem hAω]
            linarith
          · have hAD : ω ∉ ballotSurvival Y z n ∩
                {ω | η * (n : ℝ) ≤ ballotSum Y n ω} := fun h => hDω h.2
            rw [Set.indicator_of_notMem hAD, Set.indicator_of_mem hAω]
            linarith
        · have hAD : ω ∉ ballotSurvival Y z n ∩
              {ω | η * (n : ℝ) ≤ ballotSum Y n ω} := fun h => hAω h.1
          rw [Set.indicator_of_notMem hAD, Set.indicator_of_notMem hAω]
      _ = ∫ ω in ballotSurvival Y z n, (ballotSum Y n ω + z + b) ∂μ :=
        integral_indicator hA
  exact hlow.trans (ballot_setIntegral_upper μ Y hYindep hYmeas hYint hb hz hYlower
    hY0neg hmNeg hmean hmPos n)


private lemma ballot_measurable_explicit_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (N₀ : ℕ) {b η δ mNeg mPos z : ℝ} (n : ℕ)
    (hYindep : iIndepFun Y μ) (hYmeas : ∀ j, Measurable (Y j))
    (hYint : ∀ j, Integrable (Y j) μ) (hb : 0 ≤ b) (hη : 0 < η) (hδ : 0 < δ)
    (hYlower : ∀ j, 1 ≤ j → ∀ᵐ ω ∂μ, -b ≤ Y j ω)
    (hY0neg : Integrable (fun ω => (Y 0 ω)⁻) μ)
    (hmNeg : ∫ ω, (Y 0 ω)⁻ ∂μ ≤ mNeg)
    (hmean : Summable (fun j => (∫ ω, Y j ω ∂μ)⁺))
    (hmPos : ∑' j, (∫ ω, Y j ω ∂μ)⁺ ≤ mPos)
    (htail : ∀ n : ℕ, N₀ ≤ n → δ ≤ μ.real {ω | η * n ≤ ballotSum Y n ω})
    (hz : 0 ≤ z) :
    μ.real (ballotSurvival Y z n) ≤
      (2 * (b + mNeg + mPos + 1) / (η * δ) + (N₀ + 1 : ℝ)) *
        (z + 1) / (n + 1) := by
  let K : ℝ := b + mNeg + mPos + 1
  let C : ℝ := 2 * K / (η * δ) + (N₀ + 1 : ℝ)
  have hmNeg0 : 0 ≤ mNeg := (integral_nonneg fun ω => negPart_nonneg _).trans hmNeg
  have hmPos0 : 0 ≤ mPos := (tsum_nonneg fun j => posPart_nonneg _).trans hmPos
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hcoef0 : 0 ≤ 2 * K / (η * δ) := by positivity
  have hCcoef : 2 * K / (η * δ) ≤ C := by dsimp [C]; linarith
  have hCN : (N₀ + 1 : ℝ) ≤ C := by dsimp [C]; linarith
  change μ.real (ballotSurvival Y z n) ≤ C * (z + 1) / (n + 1)
  by_cases hlarge : N₀ ≤ n ∧ 0 < n
  · rcases hlarge with ⟨hnN, hn⟩
    have hmain := ballot_main_inequality μ Y hYindep hYmeas hYint hb hη hz
      hYlower hY0neg hmNeg hmean hmPos n (htail n hnN)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hden : 0 < η * n * δ := by positivity
    have hP : μ.real (ballotSurvival Y z n) ≤ (mPos + z + b + mNeg) / (η * n * δ) := by
      apply (le_div_iff₀ hden).2
      calc
        μ.real (ballotSurvival Y z n) * (η * n * δ) = η * n *
            (δ * μ.real (ballotSurvival Y z n)) := by ring
        _ ≤ mPos + z + b + mNeg := hmain
    have hR : mPos + z + b + mNeg ≤ K * (z + 1) := by
      have hKz : 0 ≤ K * z := mul_nonneg hK0 hz
      dsimp [K] at hKz ⊢
      nlinarith
    have hrecip : (1 : ℝ) / n ≤ 2 / (n + 1) := by
      apply (div_le_div_iff₀ hn0 (by positivity)).2
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    let Q : ℝ := K / (η * δ) * (z + 1)
    have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
    have hne : η * (n : ℝ) * δ ≠ 0 := ne_of_gt hden
    calc
      μ.real (ballotSurvival Y z n) ≤ (mPos + z + b + mNeg) / (η * n * δ) := hP
      _ ≤ K * (z + 1) / (η * n * δ) := by gcongr
      _ = Q / n := by
        dsimp [Q]
        field_simp
      _ = Q * (1 / n) := by rw [div_eq_mul_inv, one_div]
      _ ≤ Q * (2 / (n + 1)) := mul_le_mul_of_nonneg_left hrecip hQ0
      _ = (2 * K / (η * δ)) * (z + 1) / (n + 1) := by
        dsimp [Q]
        ring
      _ ≤ C * (z + 1) / (n + 1) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hCcoef (by linarith)
  · have hnle : n + 1 ≤ N₀ + 1 := by
      by_cases hn0 : n = 0
      · subst n
        simp
      · have hn : n < N₀ := by omega
        omega
    have hnleR : (n + 1 : ℝ) ≤ N₀ + 1 := by exact_mod_cast hnle
    calc
      μ.real (ballotSurvival Y z n) ≤ 1 := measureReal_le_one
      _ = (n + 1 : ℝ) / (n + 1) := by field_simp
      _ ≤ C * (z + 1) / (n + 1) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        calc
          (n + 1 : ℝ) ≤ N₀ + 1 := hnleR
          _ ≤ C := hCN
          _ = C * 1 := by ring
          _ ≤ C * (z + 1) := mul_le_mul_of_nonneg_left (by linarith) hC0

/-- Lemma `response:ballot`, with the constant made explicit in its data (as
in the source's proof, `response.tex` lines 40–60): `C` depends only on `b`,
`η`, `δ`, a threshold `N₀` from which the tail bound holds, a bound `mNeg` on
`E Y_0^-` and a bound `mPos` on `Σ_j (E Y_j)^+`, and works for every probability
space and every sequence of independent integrable increments satisfying the
hypotheses with these data.  This proves the frozen `response_ballot_uniform`. -/
theorem response_ballot_uniform_aux {b η δ mNeg mPos : ℝ} (N₀ : ℕ) (hb : 0 ≤ b) (hη : 0 < η)
    (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Y : ℕ → Ω → ℝ), iIndepFun Y μ → (∀ j, Integrable (Y j) μ) →
      (∀ j, 1 ≤ j → ∀ᵐ ω ∂μ, -b ≤ Y j ω) →
      ∫ ω, (Y 0 ω)⁻ ∂μ ≤ mNeg →
      Summable (fun j => (∫ ω, Y j ω ∂μ)⁺) →
      ∑' j, (∫ ω, Y j ω ∂μ)⁺ ≤ mPos →
      (∀ n : ℕ, N₀ ≤ n → δ ≤ μ.real {ω | η * n ≤ ∑ j ∈ Finset.range n, Y j ω}) →
      ∀ (n : ℕ) (z : ℝ), 0 ≤ z →
        μ.real {ω | ∀ k ≤ n, -z ≤ ∑ j ∈ Finset.range k, Y j ω} ≤
          C * (z + 1) / (n + 1) := by
  refine ⟨2 * (b + mNeg + mPos + 1) / (η * δ) + (N₀ + 1 : ℝ), ?_⟩
  intro Ω _ μ _ Y hYindep hYint hYlower hmNeg hmean hmPos htail n z hz
  let X : ℕ → Ω → ℝ := fun j => (hYint j).aestronglyMeasurable.mk (Y j)
  have hXY (j : ℕ) : X j =ᵐ[μ] Y j := (hYint j).aestronglyMeasurable.ae_eq_mk.symm
  have hYX (j : ℕ) : Y j =ᵐ[μ] X j := (hXY j).symm
  have hXmeas (j : ℕ) : Measurable (X j) :=
    (hYint j).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hXint (j : ℕ) : Integrable (X j) μ := (hYint j).congr (hYX j)
  have hXindep : iIndepFun X μ := hYindep.congr hYX
  have hmean_eq (j : ℕ) : (∫ ω, X j ω ∂μ) = ∫ ω, Y j ω ∂μ := integral_congr_ae (hXY j)
  have hXlower : ∀ j, 1 ≤ j → ∀ᵐ ω ∂μ, -b ≤ X j ω := by
    intro j hj
    filter_upwards [hYlower j hj, hXY j] with ω hω hX
    simpa [hX] using hω
  have hX0neg : Integrable (fun ω => (X 0 ω)⁻) μ :=
    hYint 0 |>.neg_part.congr ((hYX 0).fun_comp fun x => x⁻)
  have hXmNeg : ∫ ω, (X 0 ω)⁻ ∂μ ≤ mNeg := by
    calc
      (∫ ω, (X 0 ω)⁻ ∂μ) = ∫ ω, (Y 0 ω)⁻ ∂μ := by
        apply integral_congr_ae
        filter_upwards [hXY 0] with ω hω
        rw [hω]
      _ ≤ mNeg := hmNeg
  have hXmean : Summable (fun j => (∫ ω, X j ω ∂μ)⁺) := by
    simpa only [hmean_eq] using hmean
  have hXmPos : ∑' j, (∫ ω, X j ω ∂μ)⁺ ≤ mPos := by
    simpa only [hmean_eq] using hmPos
  have hAll : ∀ᵐ ω ∂μ, ∀ j, X j ω = Y j ω := ae_all_iff.mpr hXY
  have htailX : ∀ n : ℕ, N₀ ≤ n → δ ≤ μ.real {ω | η * n ≤ ballotSum X n ω} := by
    intro N hN
    have heq : {ω | η * N ≤ ballotSum X N ω} =ᵐ[μ]
        {ω | η * N ≤ ∑ j ∈ Finset.range N, Y j ω} := by
      filter_upwards [hAll] with ω hω
      simp only [ballotSum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact hω j
    rw [measureReal_congr heq]
    exact htail N hN
  have hbound := ballot_measurable_explicit_bound μ X N₀ n hXindep hXmeas hXint
    hb hη hδ hXlower hX0neg hXmNeg hXmean hXmPos htailX hz
  have hsurv : ballotSurvival X z n =ᵐ[μ]
      {ω | ∀ k ≤ n, -z ≤ ∑ j ∈ Finset.range k, Y j ω} := by
    filter_upwards [hAll] with ω hω
    simp only [ballotSurvival, ballotSum, Set.mem_ofPred_eq]
    apply propext
    constructor <;> intro h k hk
    · have hsum : (∑ j ∈ Finset.range k, X j ω) = ∑ j ∈ Finset.range k, Y j ω := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hω j
      rw [← hsum]
      exact h k hk
    · have hsum : (∑ j ∈ Finset.range k, X j ω) = ∑ j ∈ Finset.range k, Y j ω := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hω j
      rw [hsum]
      exact h k hk
  rw [← measureReal_congr hsurv]
  exact hbound

/-- Lemma `response:ballot` (`source/response.tex`, lines 28–39; proof at
lines 40–60). Let `Y j` be independent integrable real random variables and
put `S k = ∑ j < k, Y j`. For `b ≥ 0` and `η, δ > 0`, suppose that
`Y j ≥ -b` almost surely for `j ≥ 1`, `Y 0` has integrable negative part,
the positive parts of the expectations are summable, and
`P (S n ≥ η n) ≥ δ` eventually. Then there is a constant `C`, chosen after
all these hypotheses, such that for every `n` and every `z ≥ 0`,
`P (∀ k ≤ n, -z ≤ S k) ≤ C (z + 1) / (n + 1)`.

The separate integrability of the negative part of `Y 0` is implied by
integrability of `Y 0`; it is retained because the source states it explicitly.
The sums are written out rather than introducing a new definition of `S`.
This proves the frozen `response_ballot`. -/
theorem response_ballot_aux {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hYindep : iIndepFun Y μ)
    (hYint : ∀ j, Integrable (Y j) μ) {b η δ : ℝ} (hb : 0 ≤ b) (hη : 0 < η)
    (hδ : 0 < δ) (hYlower : ∀ j, 1 ≤ j → ∀ᵐ ω ∂μ, -b ≤ Y j ω)
    (hY0neg : Integrable (fun ω => (Y 0 ω)⁻) μ)
    (hmean : Summable (fun j => (∫ ω, Y j ω ∂μ)⁺))
    (htail : ∀ᶠ n : ℕ in atTop,
      δ ≤ μ.real {ω | η * n ≤ ∑ j ∈ Finset.range n, Y j ω}) :
    ∃ C : ℝ, ∀ (n : ℕ) (z : ℝ), 0 ≤ z →
      μ.real {ω | ∀ k ≤ n, -z ≤ ∑ j ∈ Finset.range k, Y j ω} ≤
        C * (z + 1) / (n + 1) := by
  -- The frozen statement retains this source hypothesis, though `hYint 0` implies it.
  have _ := hY0neg
  rcases eventually_atTop.mp htail with ⟨N₀, hN₀⟩
  rcases response_ballot_uniform_aux (mNeg := ∫ ω, (Y 0 ω)⁻ ∂μ)
      (mPos := ∑' j, (∫ ω, Y j ω ∂μ)⁺) N₀ hb hη hδ with ⟨C, hC⟩
  exact ⟨C, fun n z hz => hC μ Y hYindep hYint hYlower le_rfl hmean le_rfl
    (fun N hN => hN₀ N hN) n z hz⟩

end DiamondPinning
