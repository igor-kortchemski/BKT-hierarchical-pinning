module

public import DiamondPinning.Model.InstancePins
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.ProjIcc

/-!
# Fundamental-matrix existence, uniqueness, and growth

This module solves the matrix Volterra equation for a measurable bounded
weight and proves its exponential growth estimate. Picard iteration gives
existence and uniqueness; polynomial approximation and a column-energy
estimate give the growth bound. These results supply the fundamental-matrix
part of `lem:entire-bounds`, `source/profile.tex` lines 26–35 and 40–48.
-/

@[expose] public section

open scoped Matrix.Norms.Elementwise NNReal ComplexConjugate
open Set MeasureTheory Filter intervalIntegral Function

namespace DiamondPinning

local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "Coords" => (Fin 2 → Fin 2 → ℂ)

noncomputable section
-- The elementwise matrix norm is the iterated finite product norm.
local instance : ContinuousENorm Mat :=
  inferInstanceAs (ContinuousENorm (Fin 2 → Fin 2 → ℂ))

local instance : ENormedAddMonoid Mat :=
  inferInstanceAs (ENormedAddMonoid (Fin 2 → Fin 2 → ℂ))

local instance : TopologicalSpace.PseudoMetrizableSpace Mat :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace Coords)

local instance : SecondCountableTopology Mat :=
  inferInstanceAs (SecondCountableTopology Coords)

private noncomputable def weightMatrix (b : ℝ) : Mat := !![0, (b : ℂ)⁻¹; (b : ℂ), 0]

private theorem measurable_weightMatrix : Measurable weightMatrix := by
  apply Measurable.of_eval_matrix
  intro i j
  fin_cases i <;> fin_cases j
  · exact measurable_const
  · exact Complex.measurable_ofReal.inv
  · exact Complex.measurable_ofReal
  · exact measurable_const

private theorem weightMatrix_mul_zero (b : ℝ) (X : Mat) (j : Fin 2) :
    (weightMatrix b * X) 0 j = (b : ℂ)⁻¹ * X 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  change 0 * X 0 j + (b : ℂ)⁻¹ * X 1 j = _
  rw [zero_mul, zero_add]

private theorem weightMatrix_mul_one (b : ℝ) (X : Mat) (j : Fin 2) :
    (weightMatrix b * X) 1 j = (b : ℂ) * X 0 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  change (b : ℂ) * X 0 j + 0 * X 1 j = _
  rw [zero_mul, add_zero]

private theorem norm_weightMatrix_mul {m M b : ℝ} (hm : 0 < m) (hl : m ≤ b)
    (hu : b ≤ M) (X : Mat) :
    ‖weightMatrix b * X‖ ≤ max M m⁻¹ * ‖X‖ := by
  have hb : 0 < b := hm.trans_le hl
  have hM : 0 ≤ max M m⁻¹ := (hb.le.trans hu).trans (le_max_left _ _)
  have h₁ : ‖(b : ℂ)⁻¹‖ ≤ max M m⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
    exact (inv_anti₀ hm hl).trans (le_max_right _ _)
  have h₂ : ‖(b : ℂ)‖ ≤ max M m⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
    exact hu.trans (le_max_left _ _)
  apply (Matrix.norm_le_iff (mul_nonneg hM (norm_nonneg _))).2
  intro i j
  fin_cases i
  · change ‖(weightMatrix b * X) 0 j‖ ≤ _
    rw [weightMatrix_mul_zero, norm_mul]
    exact mul_le_mul h₁ (Matrix.norm_entry_le_entrywise_sup_norm X) (norm_nonneg _) hM
  · change ‖(weightMatrix b * X) 1 j‖ ≤ _
    rw [weightMatrix_mul_one, norm_mul]
    exact mul_le_mul h₂ (Matrix.norm_entry_le_entrywise_sup_norm X) (norm_nonneg _) hM

private theorem ae_Ioc_of_Ioo {a b : ℝ} {p : ℝ → Prop}
    (h : ∀ s ∈ Ioo a b, p s) : ∀ᵐ s : ℝ ∂volume, s ∈ Ioc a b → p s := by
  rw [← ae_restrict_iff' measurableSet_Ioc, ← restrict_Ioo_eq_restrict_Ioc]
  exact ae_restrict_of_forall_mem measurableSet_Ioo h

private noncomputable def volterraIntegrand (w : ℝ → ℝ) (z : ℂ) (Y : ℝ → Mat) (s : ℝ) : Mat :=
  (-z) • (weightMatrix (w s) * Y s)

private theorem norm_volterraIntegrand {m M : ℝ} {w : ℝ → ℝ} {z : ℂ} {Y : ℝ → Mat}
    {s : ℝ} (hm : 0 < m) (hl : m ≤ w s) (hu : w s ≤ M) :
    ‖volterraIntegrand w z Y s‖ ≤ (‖z‖ * max M m⁻¹) * ‖Y s‖ := by
  rw [volterraIntegrand, norm_smul, norm_neg, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_weightMatrix_mul hm hl hu _) (norm_nonneg _)

private theorem integrableOn_volterraIntegrand
    {a b m M : ℝ} {w : ℝ → ℝ} (hw : Measurable w) (hm : 0 < m)
    (hl : ∀ s ∈ Ioo a b, m ≤ w s) (hu : ∀ s ∈ Ioo a b, w s ≤ M)
    (z : ℂ) {Y : ℝ → Mat} (hY : ContinuousOn Y (Icc a b)) :
    IntegrableOn (volterraIntegrand w z Y) (Icc a b) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hY
  change Integrable _ (volume.restrict (Icc a b))
  rw [← restrict_Ioo_eq_restrict_Icc]
  have hc : 0 ≤ ‖z‖ * max M m⁻¹ :=
    mul_nonneg (norm_nonneg _) ((inv_nonneg.mpr hm.le).trans (le_max_right _ _))
  refine (integrable_const (‖z‖ * max M m⁻¹ * B)).mono' ?_ ?_
  · have hmultiply : Continuous (fun XY : Mat × Mat => XY.1 * XY.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact (hmultiply.comp_aestronglyMeasurable
      ((measurable_weightMatrix.comp hw).aestronglyMeasurable.prodMk
        ((hY.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo))).const_smul (-z)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (norm_volterraIntegrand hm (hl s hs) (hu s hs)).trans
      (mul_le_mul_of_nonneg_left (hB s (Ioo_subset_Icc_self hs)) hc)

private theorem integral_volterra_sub
    {a b t m M : ℝ} {w : ℝ → ℝ} (hw : Measurable w) (hm : 0 < m)
    (hl : ∀ s ∈ Ioo a b, m ≤ w s) (hu : ∀ s ∈ Ioo a b, w s ≤ M) (z : ℂ)
    {Y Z : ℝ → Mat} (hY : ContinuousOn Y (Icc a b)) (hZ : ContinuousOn Z (Icc a b))
    (ht : t ∈ Icc a b) :
    (∫ s in a..t, volterraIntegrand w z Y s) -
      (∫ s in a..t, volterraIntegrand w z Z s) =
      ∫ s in a..t, volterraIntegrand w z (fun s => Y s - Z s) s := by
  have hint {F : ℝ → Mat} (hF : ContinuousOn F (Icc a b)) :
      IntervalIntegrable (volterraIntegrand w z F) volume a t :=
    ⟨(integrableOn_volterraIntegrand hw hm hl hu z hF).mono_set
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2)), by
      rw [Ioc_eq_empty_of_le ht.1]
      exact integrableOn_empty⟩
  rw [← intervalIntegral.integral_sub (hint hY) (hint hZ)]
  simp only [volterraIntegrand, mul_sub, smul_sub]

private theorem integral_volterra_congr {a t : ℝ} {w : ℝ → ℝ} {z : ℂ}
    {Y Z : ℝ → Mat} (ht : a ≤ t) (h : EqOn Y Z (Icc a t)) :
    (∫ s in a..t, volterraIntegrand w z Y s) = ∫ s in a..t, volterraIntegrand w z Z s := by
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le ht]
  intro s hs
  simp only [volterraIntegrand, h hs]

private theorem volterra_fixedPoint
    (T m M : ℝ) (hT : 0 ≤ T) (w : ℝ → ℝ) (hw : Measurable w) (hm : 0 < m)
    (hl : ∀ s ∈ Ioo 0 T, m ≤ w s) (hu : ∀ s ∈ Ioo 0 T, w s ≤ M) (z : ℂ) :
    ∃! F : C(Icc (0 : ℝ) T, Coords),
      ∀ t : Icc (0 : ℝ) T,
        F t = (1 : Mat) + ∫ s in (0 : ℝ)..t, volterraIntegrand w z (F ∘ projIcc 0 T hT) s := by
  let S := Icc (0 : ℝ) T
  let _ : CompactSpace S := isCompact_iff_compactSpace.mp isCompact_Icc
  let _ : Nonempty S := ⟨⟨0, le_rfl, hT⟩⟩
  let p : ℝ → S := projIcc 0 T hT
  have hp : Continuous p := continuous_projIcc
  let L := ‖z‖ * max M m⁻¹
  have hL : 0 ≤ L :=
    mul_nonneg (norm_nonneg _) ((inv_nonneg.mpr hm.le).trans (le_max_right _ _))
  let P (F : C(S, Coords)) : C(S, Coords) := by
    have hint : IntegrableOn (volterraIntegrand w z (F ∘ p)) (uIcc 0 T) := by
      rw [uIcc_of_le hT]
      exact integrableOn_volterraIntegrand hw hm hl hu z (F.continuous.comp hp).continuousOn
    have hc := intervalIntegral.continuousOn_primitive_interval hint
    rw [uIcc_of_le hT] at hc
    have hc' : Continuous (fun t : S =>
        (1 : Mat) + ∫ s in (0 : ℝ)..t, volterraIntegrand w z (F ∘ p) s) :=
      continuous_const.add hc.domRestrict
    exact ⟨_, hc'⟩
  have hiter (n : ℕ) (F G : C(S, Coords)) (t : S) :
      dist ((P^[n]) F t) ((P^[n]) G t) ≤
        dist F G * (L ^ n / (n.factorial : ℝ)) * (t : ℝ) ^ n := by
    induction n generalizing t with
    | zero =>
        simpa using ContinuousMap.dist_apply_le_dist (f := F) (g := G) t
    | succ n ih =>
        let U := (P^[n]) F
        let V := (P^[n]) G
        let u (s : ℝ) : Mat := U (p s)
        let v (s : ℝ) : Mat := V (p s)
        have hU : ContinuousOn u (Icc 0 T) := (U.continuous.comp hp).continuousOn
        have hV : ContinuousOn v (Icc 0 T) := (V.continuous.comp hp).continuousOn
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dist_eq_norm]
        change ‖((1 : Mat) + ∫ s in (0 : ℝ)..t, volterraIntegrand w z u s) -
          ((1 : Mat) + ∫ s in (0 : ℝ)..t, volterraIntegrand w z v s)‖ ≤ _
        rw [add_sub_add_left_eq_sub]
        let c := L * (dist F G * (L ^ n / (n.factorial : ℝ)))
        calc
          _ = ‖∫ s in (0 : ℝ)..t, volterraIntegrand w z (fun s => u s - v s) s‖ :=
            congrArg (fun A : Mat => ‖A‖) (integral_volterra_sub hw hm hl hu z hU hV t.property)
          _ ≤ ∫ s in (0 : ℝ)..t, c * s ^ n := by
            apply intervalIntegral.norm_integral_le_of_norm_le t.property.1
            · apply ae_Ioc_of_Ioo
              intro s hs
              have hsT : s ∈ Ioo 0 T := ⟨hs.1, hs.2.trans_le t.property.2⟩
              have hpval : ((p s : S) : ℝ) = s := by
                change (projIcc 0 T hT s : ℝ) = s
                rw [projIcc_of_mem hT (Ioo_subset_Icc_self hsT)]
              refine (norm_volterraIntegrand hm (hl s hsT) (hu s hsT)).trans ?_
              have hh := ih (p s)
              rw [hpval, dist_eq_norm] at hh
              change ‖u s - v s‖ ≤ _ at hh
              change L * ‖u s - v s‖ ≤ c * s ^ n
              simpa only [c, mul_assoc] using mul_le_mul_of_nonneg_left hh hL
            · exact (continuous_const.mul (continuous_id.pow n)).intervalIntegrable _ _
          _ = _ := by
            rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero n),
              sub_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
            dsimp [c]
            field_simp
            ring
  have hsmall : ∃ n : ℕ, (L * T) ^ n / (n.factorial : ℝ) < 1 := by
    have he := (Real.summable_pow_div_factorial (L * T)).tendsto_atTop_zero.eventually
      (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    exact he.exists
  obtain ⟨n, hn⟩ := hsmall
  let K : ℝ≥0 := ⟨(L * T) ^ n / (n.factorial : ℝ), by positivity⟩
  have hP : ContractingWith K (P^[n]) := by
    refine ⟨hn, LipschitzWith.of_dist_le_mul fun F G => (ContinuousMap.dist_le
      (mul_nonneg K.coe_nonneg dist_nonneg)).2 fun t => ?_⟩
    calc
      _ ≤ dist F G * (L ^ n / (n.factorial : ℝ)) * (t : ℝ) ^ n := hiter n F G t
      _ ≤ dist F G * (L ^ n / (n.factorial : ℝ)) * T ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ t.property.1 t.property.2 _) (by positivity)
      _ = _ := by
        change _ = (L * T) ^ n / (n.factorial : ℝ) * dist F G
        rw [mul_pow]
        ring
  refine ⟨hP.fixedPoint (P^[n]), ?_, ?_⟩
  · intro t
    exact (congrArg (fun F : C(S, Coords) => F t) hP.isFixedPt_fixedPoint_iterate).symm
  · intro F hF
    exact hP.fixedPoint_unique ((show Function.IsFixedPt P F from
      ContinuousMap.ext fun t => (hF t).symm).iterate n)

/-- A positive polynomial weight can approximate the measurable weight in (L^1). -/
private theorem exists_polynomial_weight {T m M δ : ℝ} (hT : 0 < T) (hm : 0 < m)
    {w : ℝ → ℝ} (hw : Measurable w) (hl : ∀ t ∈ Ioo 0 T, m ≤ w t)
    (hu : ∀ t ∈ Ioo 0 T, w t ≤ M) (hδ : 0 < δ) :
    ∃ p : Polynomial ℝ, (∀ t ∈ Icc 0 T, m / 2 ≤ p.eval t) ∧
      IntervalIntegrable (fun t => |w t - p.eval t|) volume 0 T ∧
      (∫ t in (0 : ℝ)..T, |w t - p.eval t|) ≤ δ := by
  let S := Icc (0 : ℝ) T
  let _ : CompactSpace S := isCompact_iff_compactSpace.mp isCompact_Icc
  let μ := (volume : Measure ℝ).restrict S
  have hmM : m ≤ M := by
    have ht : T / 2 ∈ Ioo 0 T := ⟨by linarith, by linarith⟩
    exact (hl _ ht).trans (hu _ ht)
  have hioo : ∀ᵐ t ∂μ, t ∈ Ioo 0 T := by
    dsimp [μ, S]
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hwi : Integrable w μ := by
    refine (integrable_const M).mono' hw.aestronglyMeasurable ?_
    filter_upwards [hioo] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hm.le.trans (hl t ht))]
    exact hu t ht
  obtain ⟨g, hg, hgi⟩ := hwi.exists_boundedContinuous_integral_sub_le (half_pos hδ)
  let f (t : ℝ) := max m (min M (g t))
  have hf : Continuous f := continuous_const.max (continuous_const.min g.continuous)
  have hfm (t : ℝ) : m ≤ f t := le_max_left _ _
  have herror : ∀ᵐ t ∂μ, |w t - f t| ≤ ‖w t - g t‖ := by
    filter_upwards [hioo] with t ht
    have h₁ := hl t ht
    have h₂ := hu t ht
    rw [Real.norm_eq_abs]
    by_cases hg₁ : g t ≤ m
    · have hfval : f t = m := max_eq_left ((min_le_right _ _).trans hg₁)
      rw [hfval, abs_of_nonneg (sub_nonneg.mpr h₁),
        abs_of_nonneg (sub_nonneg.mpr (hg₁.trans h₁))]
      linarith
    · by_cases hg₂ : M ≤ g t
      · have hfval : f t = M := by dsimp [f]; rw [min_eq_left hg₂, max_eq_right hmM]
        rw [hfval, abs_of_nonpos (sub_nonpos.mpr h₂),
          abs_of_nonpos (sub_nonpos.mpr (h₂.trans hg₂))]
        linarith
      · have hfval : f t = g t := by
          dsimp [f]
          rw [min_eq_right (le_of_not_ge hg₂), max_eq_right (le_of_not_ge hg₁)]
        rw [hfval]
  let F : C(S, ℝ) := ⟨fun t => f t, hf.comp continuous_subtype_val⟩
  let d := min (m / 2) (δ / (2 * T))
  have hd : 0 < d := lt_min (half_pos hm) (div_pos hδ (by positivity))
  have hcl : F ∈ closure (polynomialFunctions S : Set C(S, ℝ)) := by
    change F ∈ (polynomialFunctions S).topologicalClosure
    rw [polynomialFunctions.topologicalClosure]
    exact Set.mem_univ F
  obtain ⟨P, hP, hdist⟩ := Metric.mem_closure_iff.mp hcl d hd
  change P ∈ (polynomialFunctions S : Set C(S, ℝ)) at hP
  rw [polynomialFunctions_coe] at hP
  obtain ⟨p, rfl⟩ := hP
  have hp (t : ℝ) (ht : t ∈ S) : |p.eval t - f t| ≤ d :=
    (by
      rw [← Real.dist_eq, dist_comm]
      exact (ContinuousMap.dist_apply_le_dist (⟨t, ht⟩ : S)).trans hdist.le)
  have hclose : ∀ᵐ t ∂μ, |w t - p.eval t| ≤ ‖w t - g t‖ + d := by
    filter_upwards [herror, ae_restrict_mem (measurableSet_Icc : MeasurableSet S)] with t he ht
    calc
      |w t - p.eval t| ≤ |w t - f t| + |p.eval t - f t| := by
        rw [abs_sub_comm (p.eval t) (f t)]
        exact abs_sub_le _ _ _
      _ ≤ _ := add_le_add he (hp t ht)
  have hpi : Integrable p.eval μ := p.continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hwi' : IntegrableOn (fun t => |w t - p.eval t|) (Icc 0 T) volume := by
    change Integrable (fun t => |w t - p.eval t|) μ
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hwi.sub hpi).norm
  refine ⟨p, fun t ht => ?_, (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).2 hwi', ?_⟩
  · have := (le_abs_self (f t - p.eval t)).trans
      (by simpa only [abs_sub_comm (f t)] using (hp t ht).trans (min_le_left _ _))
    linarith [hfm t]
  · rw [integral_of_le hT.le, ← integral_Icc_eq_integral_Ioc]
    change (∫ t, |w t - p.eval t| ∂μ) ≤ δ
    calc
      _ ≤ ∫ t, (‖w t - g t‖ + d) ∂μ :=
        MeasureTheory.integral_mono_ae
          (by simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hwi.sub hpi).norm)
          ((hwi.sub hgi).norm.add (integrable_const _)) hclose
      _ = (∫ t, ‖w t - g t‖ ∂μ) + d * T := by
        have hnorm : Integrable (fun t => ‖w t - g t‖) μ := (hwi.sub hgi).norm
        rw [MeasureTheory.integral_add hnorm (integrable_const _), MeasureTheory.integral_const]
        simp [μ, S, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal hT.le, mul_comm]
      _ ≤ δ / 2 + (δ / (2 * T)) * T :=
        add_le_add hg (mul_le_mul_of_nonneg_right (min_le_right _ _) hT.le)
      _ = δ := by field_simp; ring

/-- Grönwall's estimate for a real absolutely continuous function. -/
private theorem ac_le_exp_integral {a b : ℝ} (hab : a ≤ b) {E k : ℝ → ℝ}
    (hE : AbsolutelyContinuousOnInterval E a b) (hk : IntervalIntegrable k volume a b)
    (hle : ∀ᵐ t : ℝ ∂volume, t ∈ Icc a b → deriv E t ≤ k t * E t) :
    E b ≤ E a * Real.exp (∫ t in a..b, k t) := by
  let K (t : ℝ) := ∫ s in a..t, k s
  have hK : AbsolutelyContinuousOnInterval K a b :=
    hk.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  obtain ⟨R, hR⟩ := hK.neg.exists_bound
  have hKrange : MapsTo (fun t => -K t) (uIcc a b) (Icc (-R) R) := by
    intro t ht
    change -R ≤ -K t ∧ -K t ≤ R
    apply abs_le.mp
    simpa only [Real.norm_eq_abs, Pi.neg_apply] using hR t ht
  have hexpsmooth : ContDiffOn ℝ 1 Real.exp (Icc (-R) R) := Real.contDiff_exp.contDiffOn
  obtain ⟨L, hL⟩ := hexpsmooth.exists_lipschitzOnWith (by decide)
    (convex_Icc _ _) isCompact_Icc
  have hG : AbsolutelyContinuousOnInterval (fun t => Real.exp (-K t) * E t) a b :=
    (hL.comp_absolutelyContinuousOnInterval hKrange hK.neg).mul hE
  have hderiv : ∀ᵐ t : ℝ ∂volume, t ∈ Icc a b →
      deriv (fun t => Real.exp (-K t) * E t) t ≤ 0 := by
    filter_upwards [hle, hk.ae_hasDerivAt_integral, hE.ae_differentiableAt] with t ht₁ ht₂ ht₃ ht
    have htu : t ∈ uIcc a b := by rwa [uIcc_of_le hab]
    have hKt : HasDerivAt K (k t) t := ht₂ htu a (by simp)
    have hExp := (Real.hasDerivAt_exp (-K t)).comp t hKt.neg
    have hProd : HasDerivAt (fun u => Real.exp (-K u) * E u)
        (Real.exp (-K t) * -k t * E t + Real.exp (-K t) * deriv E t) t :=
      hExp.mul (ht₃ htu).hasDerivAt
    rw [hProd.deriv]
    have he := mul_le_mul_of_nonneg_left (ht₁ ht) (Real.exp_pos (-K t)).le
    dsimp only [Function.comp_apply, Pi.neg_apply] at *
    linarith
  have hint := intervalIntegral.integral_mono_ae_restrict hab
    hG.intervalIntegrable_deriv (intervalIntegrable_const (c := (0 : ℝ)) (μ := volume))
    (ae_restrict_iff' measurableSet_Icc |>.2 hderiv)
  rw [hG.integral_deriv_eq_sub] at hint
  simp only [intervalIntegral.integral_zero, K, integral_same, neg_zero, Real.exp_zero, one_mul,
    sub_nonpos] at hint
  calc
    E b ≤ E a / Real.exp (-(∫ t in a..b, k t)) :=
      (le_div_iff₀ (Real.exp_pos _)).2 (by simpa only [mul_comm] using hint)
    _ = _ := by rw [Real.exp_neg, div_inv_eq_mul]

private noncomputable def columnEnergy (b : ℝ) (x y : ℂ) : ℝ :=
  b * Complex.normSq x + b⁻¹ * Complex.normSq y

private theorem hasDerivAt_complexNormSq {f : ℝ → ℂ} {f' : ℂ} {t : ℝ}
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => Complex.normSq (f s)) (2 * (f' * conj (f t)).re) t := by
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
  convert (hre.mul hre).add (him.mul him) using 1
  · funext s
    exact Complex.normSq_apply _
  · simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
      Complex.mul_re, Complex.conj_re,
      Complex.conj_im]
    ring

private theorem abs_re_mul_le (x y : ℂ) : |(x * y).re| ≤ ‖x‖ * ‖y‖ := by
  rw [← norm_mul]
  exact Complex.abs_re_le_norm _

private theorem energy_derivative_bound {b w d m : ℝ} (hm : 0 < m) (hb : m / 2 ≤ b)
    (hw : m ≤ w) (x y z : ℂ) :
    (d / b) * (b * Complex.normSq x - b⁻¹ * Complex.normSq y) +
      2 * ((-z) * ((↑(b / w) : ℂ) * (y * conj x) +
        (↑(w / b) : ℂ) * (x * conj y))).re ≤
      (|d / b| + 2 * |z.re| + (4 / m) * ‖z‖ * |w - b|) * columnEnergy b x y := by
  have hbpos : 0 < b := (half_pos hm).trans_le hb
  have hwpos : 0 < w := hm.trans_le hw
  let E := columnEnergy b x y
  have hu : 0 ≤ b * Complex.normSq x := mul_nonneg hbpos.le (Complex.normSq_nonneg _)
  have hv : 0 ≤ b⁻¹ * Complex.normSq y :=
    mul_nonneg (inv_nonneg.mpr hbpos.le) (Complex.normSq_nonneg _)
  have hE : 0 ≤ E := add_nonneg hu hv
  have hcross : 2 * (‖x‖ * ‖y‖) ≤ E := by
    have h := mul_nonneg (inv_nonneg.mpr hbpos.le) (sq_nonneg (b * ‖x‖ - ‖y‖))
    have heq : b⁻¹ * (b * ‖x‖ - ‖y‖)^2 = E - 2 * (‖x‖ * ‖y‖) := by
      dsimp [E, columnEnergy]
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      field_simp
      ring
    linarith [heq]
  have hdiag :
      (d / b) * (b * Complex.normSq x - b⁻¹ * Complex.normSq y) ≤ |d / b| * E := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact abs_le.mpr ⟨by dsimp [E, columnEnergy]; linarith, by dsimp [E, columnEnergy]; linarith⟩
  let q := y * conj x
  let r := x * conj y
  have hq : ‖q‖ = ‖x‖ * ‖y‖ := by simp [q, mul_comm]
  have hr : ‖r‖ = ‖x‖ * ‖y‖ := by simp [r]
  have hbase : ((-z) * (q + r)).re ≤ |z.re| * E := by
    have him : (q + r).im = 0 := by
      simp only [q, r, Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re]
    calc
      _ ≤ |z.re| * |(q + r).re| := by
        simpa [abs_mul] using (le_abs_self (-z.re * (q + r).re))
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
        rw [hq, hr]
        linarith
  let e₁ := b / w - 1
  let e₂ := w / b - 1
  let D := (2 / m) * |w - b|
  have herr (s t : ℝ) (hs : 0 < s) (hl : m / 2 ≤ s) (ht : |t - s| = |w - b|) :
      |t / s - 1| ≤ D := by
    calc
      _ = |w - b| / s := by
        rw [show t / s - 1 = (t - s) / s by rw [sub_div, div_self hs.ne'],
          abs_div, abs_of_pos hs, ht]
      _ ≤ _ := by
        dsimp [D]
        rw [show (2 : ℝ) / m = (m / 2)⁻¹ by field_simp]
        rw [div_eq_mul_inv, mul_comm ((m / 2)⁻¹)]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (half_pos hm) hl) (abs_nonneg _)
  have he₁ : |e₁| ≤ D := herr w b hwpos (by linarith) (abs_sub_comm _ _)
  have he₂ : |e₂| ≤ D := herr b w hbpos hb rfl
  have hrest : ((-z) * ((e₁ : ℂ) * q + (e₂ : ℂ) * r)).re ≤ ‖z‖ * (D * E) := by
    refine (le_abs_self _).trans ((abs_re_mul_le _ _).trans ?_)
    rw [norm_neg]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (norm_nonneg _)
    rw [norm_mul (e₁ : ℂ) q, norm_mul (e₂ : ℂ) r, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, hq, hr]
    calc
      _ ≤ D * (‖x‖ * ‖y‖) + D * (‖x‖ * ‖y‖) :=
        add_le_add (mul_le_mul_of_nonneg_right he₁ (by positivity))
          (mul_le_mul_of_nonneg_right he₂ (by positivity))
      _ = D * (2 * (‖x‖ * ‖y‖)) := by ring
      _ ≤ D * E := mul_le_mul_of_nonneg_left hcross (by dsimp [D]; positivity)
  have hsplit :
      ((↑(b / w) : ℂ) * q + (↑(w / b) : ℂ) * r) =
        (q + r) + ((e₁ : ℂ) * q + (e₂ : ℂ) * r) := by
    dsimp [e₁, e₂]
    push_cast
    ring
  change _ + 2 * ((-z) * ((↑(b / w) : ℂ) * q + (↑(w / b) : ℂ) * r)).re ≤ _ * E
  rw [hsplit, mul_add, Complex.add_re]
  dsimp [D] at hrest
  linarith [hdiag, hbase, hrest,
    show (4 / m) * ‖z‖ * |w - b| * E = 2 * (‖z‖ * (2 / m * |w - b| * E)) by ring]

private noncomputable def entryCLM (i j : Fin 2) : Mat →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj j : (Fin 2 → ℂ) →L[ℝ] ℂ).comp
    (ContinuousLinearMap.proj i : Coords →L[ℝ] (Fin 2 → ℂ))

private theorem ac_volterra_coordinate {T : ℝ} (hT : 0 ≤ T) {Y G : ℝ → Mat}
    (hint : IntervalIntegrable G volume 0 T)
    (heq : ∀ t ∈ Icc (0 : ℝ) T, Y t = 1 + ∫ s in (0 : ℝ)..t, G s)
    (l : Mat →L[ℝ] ℝ) :
    AbsolutelyContinuousOnInterval (fun t => l (Y t)) 0 T := by
  have hlint : IntervalIntegrable (fun s => l (G s)) volume 0 T :=
    ⟨l.integrable_comp hint.1, l.integrable_comp hint.2⟩
  have hlac := hlint.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => l 1) 0 T :=
    (contDiff_const.contDiffOn (n := 1)).absolutelyContinuousOnInterval
  apply (hconst.add hlac).congr
  intro t ht
  rw [uIcc_of_le hT] at ht
  change l 1 + (∫ s in (0 : ℝ)..t, l (G s)) = l (Y t)
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 T := by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]
    exact Icc_subset_Icc_right ht.2
  rw [heq t ht, l.map_add]
  congr 1
  exact l.intervalIntegral_comp_comm (hint.mono_set hsub)

private theorem ac_volterra_energy {T : ℝ} (hT : 0 ≤ T) {b : ℝ → ℝ} {Y G : ℝ → Mat}
    (hint : IntervalIntegrable G volume 0 T)
    (heq : ∀ t ∈ Icc (0 : ℝ) T, Y t = 1 + ∫ s in (0 : ℝ)..t, G s)
    (hb : ContDiffOn ℝ 1 b (uIcc 0 T)) (hbn : ∀ t ∈ uIcc 0 T, b t ≠ 0) (j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun t => columnEnergy (b t) (Y t 0 j) (Y t 1 j)) 0 T := by
  have hinv : ContDiffOn ℝ 1 (fun t => (b t)⁻¹) (uIcc 0 T) :=
    hb.inv hbn
  have hs (i : Fin 2) :
      AbsolutelyContinuousOnInterval (fun t => Complex.normSq (Y t i j)) 0 T := by
    have hr : AbsolutelyContinuousOnInterval (fun t => (Y t i j).re) 0 T :=
      ac_volterra_coordinate hT hint heq (Complex.reCLM.comp (entryCLM i j))
    have hi : AbsolutelyContinuousOnInterval (fun t => (Y t i j).im) 0 T :=
      ac_volterra_coordinate hT hint heq (Complex.imCLM.comp (entryCLM i j))
    simp only [Complex.normSq_apply]
    exact (hr.mul hr).add (hi.mul hi)
  exact (hb.absolutelyContinuousOnInterval.mul (hs 0)).add
    (hinv.absolutelyContinuousOnInterval.mul (hs 1))

private theorem deriv_volterra_energy {t b d w : ℝ} (hb : b ≠ 0) {z : ℂ}
    {f : ℝ → ℝ} {x y : ℝ → ℂ} (hf : HasDerivAt f d t) (hft : f t = b)
    (hx : HasDerivAt x ((-z) * ((w : ℂ)⁻¹ * y t)) t)
    (hy : HasDerivAt y ((-z) * ((w : ℂ) * x t)) t) :
    deriv (fun s => columnEnergy (f s) (x s) (y s)) t =
      (d / b) * (b * Complex.normSq (x t) - b⁻¹ * Complex.normSq (y t)) +
        2 * ((-z) * ((↑(b / w) : ℂ) * (y t * conj (x t)) +
          (↑(w / b) : ℂ) * (x t * conj (y t)))).re := by
  have hh := ((hf.mul (hasDerivAt_complexNormSq hx)).add
    ((hf.inv (hft ▸ hb)).mul (hasDerivAt_complexNormSq hy))).deriv
  change deriv (fun s => columnEnergy (f s) (x s) (y s)) t = _ at hh
  rw [hh, Pi.inv_apply, hft]
  have hmain :
      b * (2 * (((-z) * ((w : ℂ)⁻¹ * y t)) * conj (x t)).re) +
        b⁻¹ * (2 * (((-z) * ((w : ℂ) * x t)) * conj (y t)).re) =
        2 * ((-z) * ((↑(b / w) : ℂ) * (y t * conj (x t)) +
          (↑(w / b) : ℂ) * (x t * conj (y t)))).re := by
    rw [← Complex.ofReal_inv, div_eq_mul_inv b w, div_eq_mul_inv w b,
      Complex.ofReal_mul, Complex.ofReal_mul]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, add_zero, sub_zero]
    ring
  rw [show d / b * (b * Complex.normSq (x t) - b⁻¹ * Complex.normSq (y t)) =
      d * Complex.normSq (x t) - d / b ^ 2 * Complex.normSq (y t) by field_simp]
  linear_combination hmain

private theorem volterra_growth
    (T m M : ℝ) (hT : 0 < T) (w : ℝ → ℝ) (hw : Measurable w)
    (hm : 0 < m) (hl : ∀ t ∈ Ioo 0 T, m ≤ w t) (hu : ∀ t ∈ Ioo 0 T, w t ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (z : ℂ) (Y : ℝ → Mat), ContinuousOn Y (Icc 0 T) →
      (∀ t ∈ Icc (0 : ℝ) T, Y t = 1 + ∫ s in (0 : ℝ)..t, volterraIntegrand w z Y s) →
      ‖Y T‖ ≤ C * Real.exp (T * |z.re| + ε * ‖z‖) := by
  let δ := m * ε / 2
  obtain ⟨p, hp, hei, he⟩ := exists_polynomial_weight hT hm hw hl hu (show 0 < δ by
    dsimp [δ]; positivity)
  let b := p.eval
  have hbp (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < b t := (half_pos hm).trans_le (hp t ht)
  have hbp₀ := hbp 0 ⟨le_rfl, hT.le⟩
  have hbpT := hbp T ⟨hT.le, le_rfl⟩
  have hbsmooth : ContDiffOn ℝ 1 b (uIcc 0 T) := by
    have hs : ContDiff ℝ 1 b := by simpa [b] using p.contDiff_aeval (𝕜 := ℝ) 1
    exact hs.contDiffOn
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (p.derivative.continuous.continuousOn (s := Icc (0 : ℝ) T))
  let D := max R 0 / (m / 2)
  have hderiv (t : ℝ) (ht : t ∈ Icc 0 T) : |p.derivative.eval t / b t| ≤ D := by
    rw [abs_div, abs_of_pos (hbp t ht)]
    exact div_le_div_of_nonneg_right ((by simpa only [Real.norm_eq_abs] using hR t ht :
      |p.derivative.eval t| ≤ R).trans (le_max_left _ _)) (hbp t ht).le |>.trans
        (div_le_div_of_nonneg_left (le_max_right _ _) (half_pos hm) (hp t ht))
  let H := max (b T) (b T)⁻¹
  let B := b 0 + (b 0)⁻¹
  have hH : 0 ≤ H := hbpT.le.trans (le_max_left _ _)
  have hB : 0 ≤ B := add_nonneg hbp₀.le (inv_nonneg.mpr hbp₀.le)
  refine ⟨Real.sqrt (H * B) * Real.exp (D * T / 2), ?_⟩
  intro z Y hY heq
  let G := volterraIntegrand w z Y
  have hint : IntervalIntegrable G volume 0 T :=
    ⟨(integrableOn_volterraIntegrand hw hm hl hu z hY).mono_set Ioc_subset_Icc_self, by
      rw [Ioc_eq_empty_of_le hT.le]
      exact integrableOn_empty⟩
  have hy₀ : Y 0 = 1 := by simpa using heq 0 ⟨le_rfl, hT.le⟩
  have hae : ∀ᵐ t : ℝ ∂volume, t ∈ Icc 0 T → t ∈ Ioo 0 T := by
    have h₀ : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by simp [ae_iff]
    have h₁ : ∀ᵐ t : ℝ ∂volume, t ≠ T := by simp [ae_iff]
    filter_upwards [h₀, h₁] with t ht₀ ht₁ ht
    exact ⟨lt_of_le_of_ne ht.1 (Ne.symm ht₀), lt_of_le_of_ne ht.2 ht₁⟩
  have hYd : ∀ᵐ t : ℝ ∂volume, t ∈ Icc 0 T → HasDerivAt Y (G t) t := by
    filter_upwards [hae, hint.ae_hasDerivAt_integral] with t ht₁ ht₂ ht
    have htu : t ∈ uIcc 0 T := by rwa [uIcc_of_le hT.le]
    have h : HasDerivAt (fun u => 1 + ∫ s in (0 : ℝ)..u, G s) (G t) t :=
      (ht₂ htu 0 (by simp)).const_add (1 : Mat)
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (ht₁ ht).1 (ht₁ ht).2] with u hu
    exact heq u (Ioo_subset_Icc_self hu)
  let k (t : ℝ) := D + 2 * |z.re| + ((4 / m) * ‖z‖) * |w t - b t|
  have hk : IntervalIntegrable k volume 0 T :=
    intervalIntegrable_const.add (hei.const_mul _)
  have hK : (∫ t in (0 : ℝ)..T, k t) ≤ D * T + 2 * (T * |z.re| + ε * ‖z‖) := by
    change (∫ t in (0 : ℝ)..T, (D + 2 * |z.re|) + ((4 / m) * ‖z‖) * |w t - b t|) ≤ _
    rw [intervalIntegral.integral_add intervalIntegrable_const (hei.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    have h := mul_le_mul_of_nonneg_left he (show 0 ≤ (4 / m) * ‖z‖ by positivity)
    have hc : (4 / m) * ‖z‖ * δ = 2 * (ε * ‖z‖) := by
      dsimp [δ]
      field_simp
      ring
    rw [hc] at h
    linarith
  have henergy (j : Fin 2) :
      columnEnergy (b T) (Y T 0 j) (Y T 1 j) ≤
        B * Real.exp (D * T + 2 * (T * |z.re| + ε * ‖z‖)) := by
    let E (t : ℝ) := columnEnergy (b t) (Y t 0 j) (Y t 1 j)
    have hEac : AbsolutelyContinuousOnInterval E 0 T :=
      ac_volterra_energy hT.le hint heq hbsmooth
        (fun t ht => (hbp t (by rwa [uIcc_of_le hT.le] at ht)).ne') j
    have hEd : ∀ᵐ t : ℝ ∂volume, t ∈ Icc 0 T → deriv E t ≤ k t * E t := by
      filter_upwards [hae, hYd] with t hti hyt ht
      have hzero := (entryCLM 0 j).hasFDerivAt.comp_hasDerivAt t (hyt ht)
      have hone := (entryCLM 1 j).hasFDerivAt.comp_hasDerivAt t (hyt ht)
      change HasDerivAt (fun s => Y s 0 j) (G t 0 j) t at hzero
      change HasDerivAt (fun s => Y s 1 j) (G t 1 j) t at hone
      simp only [G, volterraIntegrand, Matrix.smul_apply, smul_eq_mul,
        weightMatrix_mul_zero, weightMatrix_mul_one] at hzero hone
      rw [deriv_volterra_energy (hbp t ht).ne' (p.hasDerivAt t) rfl hzero hone]
      refine (energy_derivative_bound hm (hp t ht) (hl t (hti ht)) _ _ _).trans ?_
      have hEt : 0 ≤ E t := add_nonneg
        (mul_nonneg (hbp t ht).le (Complex.normSq_nonneg _))
        (mul_nonneg (inv_nonneg.mpr (hbp t ht).le) (Complex.normSq_nonneg _))
      apply mul_le_mul_of_nonneg_right _ hEt
      exact add_le_add (add_le_add (hderiv t ht) le_rfl) le_rfl
    have hE0 : E 0 ≤ B := by
      dsimp [E, B, columnEnergy]
      rw [hy₀]
      have h₁ (i : Fin 2) : Complex.normSq ((1 : Mat) i j) ≤ 1 := by
        simp only [Matrix.one_apply]
        split <;> simp
      simpa using add_le_add (mul_le_mul_of_nonneg_left (h₁ 0) hbp₀.le)
        (mul_le_mul_of_nonneg_left (h₁ 1) (inv_nonneg.mpr hbp₀.le))
    exact (ac_le_exp_integral hT.le hEac hk hEd).trans
      (mul_le_mul hE0 (Real.exp_le_exp.mpr hK) (Real.exp_pos _).le hB)
  have hC : 0 ≤ Real.sqrt (H * B) * Real.exp (D * T / 2) *
      Real.exp (T * |z.re| + ε * ‖z‖) := by positivity
  apply (Matrix.norm_le_iff hC).2
  intro i j
  apply le_of_sq_le_sq _ hC
  rw [Complex.sq_norm]
  have hh : Complex.normSq (Y T i j) ≤ H * columnEnergy (b T) (Y T 0 j) (Y T 1 j) := by
    have h₀ : 0 ≤ b T * Complex.normSq (Y T 0 j) :=
      mul_nonneg hbpT.le (Complex.normSq_nonneg _)
    have h₁ : 0 ≤ (b T)⁻¹ * Complex.normSq (Y T 1 j) :=
      mul_nonneg (inv_nonneg.mpr hbpT.le) (Complex.normSq_nonneg _)
    fin_cases i
    · change Complex.normSq (Y T 0 j) ≤ _
      calc
        _ = (b T)⁻¹ * (b T * Complex.normSq (Y T 0 j)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hbpT.ne', one_mul]
        _ ≤ _ := mul_le_mul (le_max_right _ _) (le_add_of_nonneg_right h₁) h₀ hH
    · change Complex.normSq (Y T 1 j) ≤ _
      calc
        _ = b T * ((b T)⁻¹ * Complex.normSq (Y T 1 j)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hbpT.ne', one_mul]
        _ ≤ _ := mul_le_mul (le_max_left _ _) (le_add_of_nonneg_left h₀) h₁ hH
  calc
    _ ≤ H * (B * Real.exp (D * T + 2 * (T * |z.re| + ε * ‖z‖))) :=
      hh.trans (mul_le_mul_of_nonneg_left (henergy j) hH)
    _ = _ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hH hB), ← Real.exp_nat_mul,
        ← Real.exp_nat_mul]
      push_cast
      rw [← mul_assoc, mul_assoc (H * B), ← Real.exp_add]
      congr 2
      ring

end

/-- The matrix Volterra equation has a continuous solution on `[0, T]`, and
any two continuous solutions agree there. This proves
`DiamondPinning.matrix_integral_solution_exists_unique` (in
`DiamondPinning.Statements.EntireBounds`). -/
theorem matrix_integral_solution_exists_unique_aux
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
  obtain ⟨F, hF, huniq⟩ := volterra_fixedPoint T m M hT.le w hw hm hw_lower hw_upper z
  let p := projIcc 0 T hT.le
  refine ⟨⟨F ∘ p, (F.continuous.comp continuous_projIcc).continuousOn, ?_⟩, ?_⟩
  · intro t ht
    change F (p t) = _
    simpa only [p, projIcc_of_mem hT.le ht, volterraIntegrand, weightMatrix] using hF ⟨t, ht⟩
  · intro Y Y' hY hY' eY eY' t ht
    have lift (Z : ℝ → Mat) (hZ : ContinuousOn Z (Icc 0 T))
        (eZ : ∀ s ∈ Icc (0 : ℝ) T,
          Z s = 1 + ∫ u in (0 : ℝ)..s, volterraIntegrand w z Z u) :
        (⟨fun s : Icc (0 : ℝ) T => Z s,
          continuousOn_iff_continuous_domRestrict.mp hZ⟩ : C(Icc (0 : ℝ) T, Coords)) = F := by
      apply huniq
      intro s
      change Z s = 1 + ∫ u in (0 : ℝ)..s, volterraIntegrand w z (Z ∘ fun x => (p x : ℝ)) u
      rw [eZ s s.property]
      congr 1
      apply integral_volterra_congr s.property.1
      intro u hu
      have huT : u ∈ Icc 0 T := ⟨hu.1, hu.2.trans s.property.2⟩
      simp only [Function.comp_apply, p, projIcc_of_mem hT.le huT]
    have h₁ := congrArg (fun G : C(Icc (0 : ℝ) T, Coords) => G ⟨t, ht⟩) (lift Y hY eY)
    have h₂ := congrArg (fun G : C(Icc (0 : ℝ) T, Coords) => G ⟨t, ht⟩) (lift Y' hY' eY')
    exact h₁.trans h₂.symm

/-- Every continuous solution of the matrix Volterra equation satisfies the
minimal-exponential-type growth bound at time `T`, proving
`DiamondPinning.matrix_integral_growth_bound` (in `DiamondPinning.Statements.EntireBounds`). -/
theorem matrix_integral_growth_bound_aux
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
  exact volterra_growth T m M hT w hw hm hw_lower hw_upper ε hε

end DiamondPinning
