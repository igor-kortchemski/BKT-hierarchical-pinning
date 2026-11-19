module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Model.Profile
public import DiamondPinning.Proofs.ScalingCalculus4
public import DiamondPinning.Proofs.OneSidedProof
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

namespace DiamondPinning

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction ENNReal

/-- If each sequence approaching a countably generated filter has a further
subsequence on which the images approach the same filter, the images converge. -/
theorem tendsto_of_further_subsequences {α β : Type*} {u : α → β}
    {l : Filter α} {k : Filter β} [l.IsCountablyGenerated]
    (h : ∀ x : ℕ → α, Tendsto x atTop l →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun j => u (x (φ j))) atTop k) :
    Tendsto u l k :=
  Filter.tendsto_of_subseq_tendsto fun x hx =>
    let ⟨φ, _, hφ⟩ := h x hx
    ⟨φ, hφ⟩

theorem profileU_pos_of_prePole {v t : ℝ} (ht : IsPrePoleTime v t) :
    0 < profileU v t := by
  by_cases hv : 0 < v
  · have hroot := Real.sqrt_pos.2 hv
    have hangle : Real.sqrt v * t < Real.pi := by
      rw [mul_comm]
      exact (lt_div_iff₀ hroot).1 (ht.2 hv)
    rw [profileU, ite_eq_left hv]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi (mul_pos hroot ht.1) hangle) hroot
  · simpa only [profileU, ite_eq_right hv] using ht.1

theorem hasDerivAt_profileU (v t : ℝ) :
    HasDerivAt (profileU v)
      (if 0 < v then Real.cos (Real.sqrt v * t) else 1) t := by
  by_cases hv : 0 < v
  · have h := (((hasDerivAt_id t).const_mul (Real.sqrt v)).sin).div_const (Real.sqrt v)
    have hf : profileU v = fun x => Real.sin (Real.sqrt v * x) / Real.sqrt v := by
      funext x
      rw [profileU, ite_eq_left hv]
    rw [hf]
    simpa [hv, Real.sqrt_ne_zero'.2 hv] using h
  · have hf : profileU v = id := by
      funext x
      rw [profileU, ite_eq_right hv]
      rfl
    rw [hf, ite_eq_right hv]
    exact hasDerivAt_id t

theorem hasDerivAt_profileB {v t : ℝ} (ht : IsPrePoleTime v t) :
    HasDerivAt (profileB v) (-(profileA v t / 2)) t := by
  have hu := (profileU_pos_of_prePole ht).ne'
  by_cases hv : 0 < v
  · have hx := Real.sqrt_pos.2 hv
    have hder : profileB v = fun x =>
        2 * Real.cos (Real.sqrt v * x) / profileU v x := by
      funext x
      simp [profileB, (hasDerivAt_profileU v x).deriv, hv]
    rw [hder]
    have hc := (((hasDerivAt_id t).const_mul (Real.sqrt v)).cos).const_mul 2
    have h := hc.div (hasDerivAt_profileU v t) hu
    simp only [ite_eq_left hv] at h
    refine h.congr_deriv ?_
    simp only [id_eq, mul_one, profileA]
    have hc' : Real.sin (Real.sqrt v * t) * Real.sqrt v * profileU v t =
        Real.sin (Real.sqrt v * t) ^ 2 := by
      rw [profileU, ite_eq_left hv]
      field_simp [hx.ne']
    have hnum := Real.sin_sq_add_cos_sq (Real.sqrt v * t)
    field_simp [hu]
    linarith only [hnum, hc']
  · have hder : profileB v = fun x => 2 / x := by
      funext x
      simp [profileB, (hasDerivAt_profileU v x).deriv, profileU, hv]
    rw [hder]
    have h := (hasDerivAt_const t (2 : ℝ)).div (hasDerivAt_id t) ht.1.ne'
    refine h.congr_deriv ?_
    simp [profileA, profileU, hv]
    ring

theorem hasDerivAt_profileA {v t : ℝ} (ht : IsPrePoleTime v t) :
    HasDerivAt (profileA v) (-(profileB v t * profileA v t)) t := by
  have hu := (profileU_pos_of_prePole ht).ne'
  have hd := hasDerivAt_profileU v t
  have h := (hasDerivAt_const t (4 : ℝ)).div (hd.pow 2) (pow_ne_zero _ hu)
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_mul, zero_sub, Pi.pow_apply]
  rw [profileA, profileB, hd.deriv]
  field_simp [hu]

theorem profileB_antitoneOn (v : ℝ) :
    AntitoneOn (profileB v) {t | IsPrePoleTime v t} := by
  intro x hx y hy hxy
  have hsub : Set.Icc x y ⊆ {t | IsPrePoleTime v t} := fun t ht =>
    ⟨hx.1.trans_le ht.1, fun hv => ht.2.trans_lt (hy.2 hv)⟩
  have hder : ∀ t ∈ Set.Icc x y, HasDerivAt (profileB v) (-(profileA v t / 2)) t :=
    fun t ht => hasDerivAt_profileB (hsub ht)
  apply antitoneOn_of_deriv_nonpos (convex_Icc x y)
    (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
  · exact fun t ht => (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hder t (interior_subset ht)).deriv]
    exact neg_nonpos.2 (div_nonneg (by unfold profileA; positivity) (by norm_num))
  · exact ⟨le_rfl, hxy⟩
  · exact ⟨hxy, le_rfl⟩
  · exact hxy

theorem profileTransform_hasDerivAt {v t s : ℝ} (ht : IsPrePoleTime v t)
    (hs : 0 < s + profileB v t) :
    HasDerivAt (fun τ => profileTransform v τ s)
      (psiS s (profileTransform v t s) - profileA v t) t := by
  have h := (hasDerivAt_profileA ht).div ((hasDerivAt_profileB ht).const_add s) hs.ne'
  refine h.congr_deriv ?_
  unfold profileTransform psiS
  field_simp [hs.ne']
  ring

/-- The explicitly weighted density, including the range where the unweighted
profile has infinite mass. -/
theorem weightedMeasure_profileMeasure (v t s : ℝ) :
    weightedMeasure (profileMeasure v t) s =
      (volume.restrict (Set.Ici 0)).withDensity
        (fun x => ENNReal.ofReal (profileA v t * Real.exp (-(s + profileB v t) * x))) := by
  unfold weightedMeasure profileMeasure
  rw [← withDensity_mul _ (by unfold profileDensity; fun_prop) (by fun_prop)]
  congr 1
  funext x
  have ha : 0 ≤ profileA v t := by unfold profileA; positivity
  simp only [Pi.mul_apply, profileDensity, ← ENNReal.ofReal_mul (mul_nonneg ha (Real.exp_pos _).le)]
  have heq : -(profileB v t * x) + -(s * x) = -(s + profileB v t) * x := by ring
  rw [mul_assoc, ← Real.exp_add, heq]

theorem weightedMeasure_profileMeasure_mass {v t s : ℝ} (hs : 0 < s + profileB v t) :
    weightedMeasure (profileMeasure v t) s Set.univ =
      ENNReal.ofReal (profileTransform v t s) := by
  have hi := (integrableOn_exp_mul_Ioi (neg_lt_zero.2 hs) 0).const_mul (profileA v t)
  rw [restrict_Ioi_eq_restrict_Ici] at hi
  rw [weightedMeasure_profileMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi]
  · congr 1
    rw [integral_const_mul, integral_Ici_eq_integral_Ioi,
      integral_exp_mul_Ioi (neg_lt_zero.2 hs), mul_zero, Real.exp_zero, neg_div_neg_eq]
    simp only [profileTransform, div_eq_mul_inv, one_mul]
  · exact ae_of_all _ fun x => mul_nonneg (by unfold profileA; positivity) (Real.exp_pos _).le

theorem weightedMeasure_profileMeasure_finite {v t s : ℝ} (hs : 0 < s + profileB v t) :
    IsFiniteMeasure (weightedMeasure (profileMeasure v t) s) :=
  ⟨by rw [weightedMeasure_profileMeasure_mass hs]; exact ENNReal.ofReal_lt_top⟩

/-- A bound at a smaller weight controls the right tail at any larger weight. -/
theorem weightedMeasure_tail_le (ν : Measure ℝ) {s₀ s R : ℝ} (hs : s₀ ≤ s) :
    weightedMeasure ν s (Set.Ioi R) ≤
      ENNReal.ofReal (Real.exp (-(s - s₀) * R)) * weightedMeasure ν s₀ Set.univ := by
  have hm (a : ℝ) : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-(a * x)))) := by
    fun_prop
  have heq : weightedMeasure ν s =
      (weightedMeasure ν s₀).withDensity (fun x => ENNReal.ofReal (Real.exp (-((s - s₀) * x)))) := by
    unfold weightedMeasure
    rw [← withDensity_mul _ (hm s₀) (hm (s - s₀))]
    congr 1
    funext x
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  rw [heq, withDensity_apply _ measurableSet_Ioi]
  calc
    _ ≤ ∫⁻ _ in Set.Ioi R, ENNReal.ofReal (Real.exp (-(s - s₀) * R))
        ∂(weightedMeasure ν s₀) := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      rw [Real.exp_le_exp]
      have h := mul_le_mul_of_nonneg_left (le_of_lt hx) (sub_nonneg.2 hs)
      linarith
    _ = ENNReal.ofReal (Real.exp (-(s - s₀) * R)) * weightedMeasure ν s₀ (Set.Ioi R) := by
      rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ _ := by
      exact mul_right_mono (measure_mono (μ := weightedMeasure ν s₀) (Set.subset_univ _))

private noncomputable def boundedExponential (s : ℝ) (hs : 0 ≤ s) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => Real.exp (-(s * max x 0)), by fun_prop⟩ 1
    (fun x y => by
      have h (z : ℝ) : Real.exp (-(s * max z 0)) ≤ 1 :=
        Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hs (le_max_right _ _)))
      rw [Real.dist_eq, abs_le]
      change -1 ≤ Real.exp (-(s * max x 0)) - Real.exp (-(s * max y 0)) ∧
        Real.exp (-(s * max x 0)) - Real.exp (-(s * max y 0)) ≤ 1
      exact ⟨by linarith [h y, Real.exp_pos (-(s * max x 0))],
        by linarith [h x, Real.exp_pos (-(s * max y 0))]⟩)

private theorem ae_nonneg_of_measure_Iio_zero {ν : Measure ℝ} (hν : ν (Set.Iio 0) = 0) :
    ∀ᵐ x ∂ν, 0 ≤ x := by
  rw [ae_iff]
  rw [show {x : ℝ | ¬0 ≤ x} = Set.Iio 0 by ext x; exact not_le]
  exact hν

theorem weightedMeasure_le_of_nonneg {ν : Measure ℝ} (hν : ν (Set.Iio 0) = 0)
    {s : ℝ} (hs : 0 ≤ s) :
    weightedMeasure ν s ≤ ν := by
  unfold weightedMeasure
  calc
    _ ≤ ν.withDensity 1 := by
      apply withDensity_mono
      filter_upwards [ae_nonneg_of_measure_Iio_zero hν] with x hx
      exact ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hs hx)))
    _ = _ := withDensity_one

/-- Multiplication by a nonnegative exponential weight preserves weak
convergence for measures supported on the nonnegative half-line. -/
theorem weakConvergence_weighted_of_supported {ι : Type*} {ν : ι → Measure ℝ}
    {l : Filter ι} {ν' : Measure ℝ} (h : WeakConvergence ν l ν')
    (hν : ∀ᶠ i in l, ν i (Set.Iio 0) = 0) (hν' : ν' (Set.Iio 0) = 0)
    {s : ℝ} (hs : 0 ≤ s) :
    WeakConvergence (fun i => weightedMeasure (ν i) s) l (weightedMeasure ν' s) := by
  have hfin (ψ : Measure ℝ) (hm : ψ (Set.Iio 0) = 0) (hf : IsFiniteMeasure ψ) :
      IsFiniteMeasure (weightedMeasure ψ s) :=
    ⟨(weightedMeasure_le_of_nonneg hm hs Set.univ).trans_lt hf.measure_univ_lt_top⟩
  refine ⟨hfin ν' hν' h.1, ?_, ?_⟩
  · filter_upwards [hν, h.2.1] with i hi hfi using hfin (ν i) hi hfi
  intro g
  have heq (ψ : Measure ℝ) (hm : ψ (Set.Iio 0) = 0) :
      (∫ x, g x ∂weightedMeasure ψ s) = ∫ x, (boundedExponential s hs * g) x ∂ψ := by
    unfold weightedMeasure
    rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp) _]
    apply integral_congr_ae
    filter_upwards [ae_nonneg_of_measure_Iio_zero hm] with x hx
    change (ENNReal.ofReal (Real.exp (-(s * x)))).toReal • g x =
      Real.exp (-(s * max x 0)) * g x
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, max_eq_left hx, smul_eq_mul]
  rw [heq ν' hν']
  apply (h.2.2 (boundedExponential s hs * g)).congr'
  filter_upwards [hν] with i hi using (heq (ν i) hi).symm

/-- A compact time set admits a slightly smaller base weight throughout the
interval from any earlier positive time to its last point. -/
theorem exists_continuation_base_weight {v s : ℝ} {I : Set ℝ}
    (hI : IsCompact I) (hIn : I.Nonempty) (hIpole : ∀ t ∈ I, IsPrePoleTime v t)
    (hs : 0 < s) (hadm : 0 < s + sInf (profileB v '' I)) :
    ∃ s₀ ∈ Set.Ioo 0 s, ∀ t, 0 < t → t ≤ sSup I → 0 < s₀ + profileB v t := by
  have htmax := hIpole _ (hI.sSup_mem hIn)
  have hmin : sInf (profileB v '' I) = profileB v (sSup I) := by
    apply IsLeast.csInf_eq
    refine ⟨⟨sSup I, hI.sSup_mem hIn, rfl⟩, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact profileB_antitoneOn v (hIpole t ht) htmax (le_csSup hI.bddAbove ht)
  rw [hmin] at hadm
  let s₀ := s - min s (s + profileB v (sSup I)) / 2
  have hminpos : 0 < min s (s + profileB v (sSup I)) := lt_min hs hadm
  refine ⟨s₀, ⟨?_, ?_⟩, ?_⟩
  · dsimp [s₀]
    linarith [min_le_left s (s + profileB v (sSup I))]
  · dsimp [s₀]
    linarith
  · intro t ht ht'
    have htp : IsPrePoleTime v t := ⟨ht, fun hv => ht'.trans_lt (htmax.2 hv)⟩
    have hb := profileB_antitoneOn v htp htmax ht'
    dsimp [s₀]
    linarith [min_le_right s (s + profileB v (sSup I))]

theorem profileTransform_sub_integral {v s s₀ r t : ℝ}
    (hpole : ∀ u ∈ Set.Icc r t, IsPrePoleTime v u)
    (hs : ∀ u ∈ Set.Icc r t, 0 < s + profileB v u)
    (hs₀ : ∀ u ∈ Set.Icc r t, 0 < s₀ + profileB v u) (hrt : r ≤ t) :
    (profileTransform v t s - profileTransform v t s₀) -
        (profileTransform v r s - profileTransform v r s₀) =
      timeIntegral (fun u => psiS s (profileTransform v u s) -
        psiS s₀ (profileTransform v u s₀)) r t := by
  have hder : ∀ u ∈ Set.uIcc r t, HasDerivAt
      (fun x => profileTransform v x s - profileTransform v x s₀)
      (psiS s (profileTransform v u s) - psiS s₀ (profileTransform v u s₀)) u := by
    intro u hu
    rw [Set.uIcc_of_le hrt] at hu
    refine ((profileTransform_hasDerivAt (hpole u hu) (hs u hu)).sub
      (profileTransform_hasDerivAt (hpole u hu) (hs₀ u hu))).congr_deriv ?_
    ring
  have hcon (w : ℝ) (hw : ∀ u ∈ Set.Icc r t, 0 < w + profileB v u) :
      ContinuousOn (fun u => psiS w (profileTransform v u w)) (Set.Icc r t) := by
    have h := fun u hu => (profileTransform_hasDerivAt (hpole u hu) (hw u hu)).continuousAt
    have hc : ContinuousOn (fun u => profileTransform v u w) (Set.Icc r t) :=
      fun u hu => (h u hu).continuousWithinAt
    unfold psiS
    exact (continuousOn_const.mul hc).add ((hc.pow 2).div_const 2)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (((hcon s hs).sub (hcon s₀ hs₀)).intervalIntegrable_of_Icc hrt)).symm

/-- A bounded solution of a homogeneous integral equation vanishes on a short
interval. The coefficient bound is only needed almost everywhere. -/
theorem eq_zero_of_bounded_volterra {e a : ℝ → ℝ} {r t K M : ℝ}
    (hrt : r ≤ t) (hK : 0 ≤ K) (hsmall : K * (t - r) < 1)
    (he : ∀ u ∈ Set.Icc r t, |e u| ≤ M)
    (ha : ∀ᵐ u : ℝ, u ∈ Set.Icc r t → |a u| ≤ K)
    (h : ∀ u ∈ Set.Icc r t, e u = timeIntegral (fun x => a x * e x) r u) :
    ∀ u ∈ Set.Icc r t, e u = 0 := by
  let vals := (fun u => |e u|) '' Set.Icc r t
  let m := sSup vals
  have hne : vals.Nonempty := ⟨|e r|, ⟨r, ⟨le_rfl, hrt⟩, rfl⟩⟩
  have hbdd : BddAbove vals := ⟨M, by rintro _ ⟨u, hu, rfl⟩; exact he u hu⟩
  have hle (u : ℝ) (hu : u ∈ Set.Icc r t) : |e u| ≤ m := le_csSup hbdd ⟨u, hu, rfl⟩
  have hm : 0 ≤ m := (abs_nonneg (e r)).trans (hle r ⟨le_rfl, hrt⟩)
  have hbound (u : ℝ) (hu : u ∈ Set.Icc r t) : |e u| ≤ (K * (t - r)) * m := by
    rw [h u hu, timeIntegral, ← Real.norm_eq_abs]
    calc
      _ ≤ K * m * |u - r| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
        filter_upwards [ha] with x hx hxu
        rw [Set.uIoc_of_le hu.1] at hxu
        have hxt : x ∈ Set.Icc r t := ⟨hxu.1.le, hxu.2.trans hu.2⟩
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hx hxt) (hle x hxt) (abs_nonneg _) hK
      _ ≤ _ := by
        rw [abs_of_nonneg (sub_nonneg.2 hu.1), mul_right_comm K (t - r) m]
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right hu.2 r) (mul_nonneg hK hm)
  have hs : m ≤ (K * (t - r)) * m :=
    csSup_le hne (by rintro _ ⟨u, hu, rfl⟩; exact hbound u hu)
  have hm0 : m = 0 := by
    by_contra hne
    exact (not_lt_of_ge hs) (mul_lt_of_lt_one_left (lt_of_le_of_ne hm (Ne.symm hne)) hsmall)
  intro u hu
  exact abs_eq_zero.mp (le_antisymm (hm0 ▸ hle u hu) (abs_nonneg _))

private theorem integrable_rpow_of_integrable_id {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hpos : ∀ᵐ x ∂ν, 0 ≤ x) (hi : Integrable id ν) {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1) :
    Integrable (fun x : ℝ => x ^ q) ν := by
  refine ((integrable_const (1 : ℝ)).add hi).mono'
    (Real.continuous_rpow_const hq).measurable.aestronglyMeasurable ?_
  filter_upwards [hpos] with x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx q)]
  change x ^ q ≤ 1 + x
  rcases le_total x 1 with hx' | hx'
  · exact (Real.rpow_le_one hx hx' hq).trans (le_add_of_nonneg_right hx)
  · exact (by simpa using Real.rpow_le_rpow_of_exponent_le hx' hq' : x ^ q ≤ x).trans
      (le_add_of_nonneg_left zero_le_one)

/-- Express the weighted mass of the model measure as an integral with respect to
the original law. -/
theorem rescaledMeasure_weighted_mass_real (μ : Measure ℝ) {B h N s : ℝ}
    (hB : 2 < B) (hN : 0 ≤ N) (n : ℕ) :
    (weightedMeasure (rescaledMeasure μ B h N n) s).real Set.univ =
      ∫ x in Set.Ici (1 : ℝ),
        N * (x ^ theta B - 1) * Real.exp (-(s * (Real.log x / (Real.log B * N))))
          ∂(lawR μ B h n) := by
  calc
    _ = ∫ _ : ℝ, (1 : ℝ) ∂weightedMeasure (rescaledMeasure μ B h N n) s := by
      rw [integral_const, smul_eq_mul, mul_one]
    _ = _ := by
      unfold weightedMeasure
      rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp) _]
      simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_one]
      unfold rescaledMeasure
      rw [integral_map (by fun_prop) (by fun_prop)]
      rw [integral_withDensity_eq_integral_toReal_smul
        (by
          have hm := (Real.continuous_rpow_const (theta_pos hB).le).measurable
          exact (hm.sub_const 1 |>.const_mul N).ennreal_ofReal)
        (by simp) _]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      rw [smul_eq_mul, ENNReal.toReal_ofReal]
      exact mul_nonneg hN (sub_nonneg.2 (Real.one_le_rpow hx (theta_pos hB).le))


/-- The positive weighted mass differs from the Mellin transform by the
negative-floor contribution and the weight applied to the subtracted unit. -/
theorem rescaledMeasure_weighted_mass_sub_bounds {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {N s : ℝ} (hN : 0 < N) (hs : 0 ≤ s)
    (hq : 0 < weightExponent B N s) (n : ℕ) :
    let L := transformAt μ B h N n s
    let ρ := (2 / B) ^ n
    let m := (weightedMeasure (rescaledMeasure μ B h N n) s).real Set.univ
    0 ≤ m - L ∧ m - L ≤ s / (Real.log B * N * weightExponent B N s) *
      (L + N * ρ) + N * ρ := by
  let ν := lawR μ B h n
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  let d := s / (Real.log B * N)
  let q := weightExponent B N s
  let ρ := (2 / B) ^ n
  let F : ℝ → ℝ := fun x => x ^ q - 1
  let W : ℝ → ℝ := Set.indicator (Set.Ici 1) (fun x => x ^ q - Real.exp (-(d * Real.log x)))
  have hden : 0 < Real.log B * N := mul_pos (Real.log_pos (by linarith)) hN
  have hd : 0 ≤ d := div_nonneg hs hden.le
  have hq' : q ≤ 1 := by
    change theta B - d ≤ 1
    linarith [theta_lt_one hB]
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hxq : Integrable (fun x => x ^ q) ν :=
    integrable_rpow_of_integrable_id ((ae_pos_lawR hpos hB h n).mono fun x hx => hx.le)
      (integrable_lawR_of hpos hmean hB h n) hq.le hq'
  have hF : Integrable F ν := hxq.sub (integrable_const 1)
  have hW : Integrable W ν := by
    unfold W
    apply IntegrableOn.integrable_indicator _ measurableSet_Ici
    refine hxq.restrict.sub ((integrable_const 1).mono' (by fun_prop) ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hd (Real.log_nonneg hx)))
  have hW_integral : (weightedMeasure (rescaledMeasure μ B h N n) s).real Set.univ =
      N * ∫ x, W x ∂ν := by
    dsimp only [W]
    rw [rescaledMeasure_weighted_mass_real μ hB hN.le, integral_indicator measurableSet_Ici,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    have hxpos : 0 < x := zero_lt_one.trans_le hx
    have he : -(s * (Real.log x / (Real.log B * N))) = -(d * Real.log x) := by
      dsimp [d]
      ring
    have hr : x ^ theta B * Real.exp (-(d * Real.log x)) = x ^ q := by
      rw [Real.rpow_def_of_pos hxpos, Real.rpow_def_of_pos hxpos, ← Real.exp_add]
      congr 1
      change Real.log x * theta B + -(d * Real.log x) = Real.log x * (theta B - d)
      ring
    rw [he, mul_assoc, sub_mul, one_mul, hr]
  have hF_integral : transformAt μ B h N n s = N * ∫ x, F x ∂ν := by
    simp only [F, integral_sub hxq (integrable_const 1), integral_const, probReal_univ,
      smul_eq_mul, one_mul, transformAt, realMoment]
    rfl
  have hpoint : ∀ᵐ x ∂ν, 0 ≤ W x - F x ∧ W x - F x ≤ (d / q) * (F x + ρ) + ρ := by
    filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx
    have hq_floor : -ρ ≤ F x := by
      have hb := floorSeq_nonneg hB n
      have hrs : floorSeq B n ≤ x ^ q :=
        (Real.self_le_rpow_of_le_one hb (floorSeq_le_one hB n) hq').trans
          (Real.rpow_le_rpow hb hx hq.le)
      have hf := one_sub_floorSeq_le hB n
      dsimp [F, ρ] at *
      linarith
    by_cases hx1 : 1 ≤ x
    · have hlog := Real.log_nonneg hx1
      have hlow : Real.exp (-(d * Real.log x)) ≤ 1 :=
        Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hd hlog))
      have hu : 1 - Real.exp (-(d * Real.log x)) ≤ d * Real.log x := by
        linarith [Real.add_one_le_exp (-(d * Real.log x))]
      have hlog' : Real.log x ≤ (F x + ρ) / q := by
        apply (le_div_iff₀ hq).2
        have he := Real.add_one_le_exp (Real.log x * q)
        rw [← Real.rpow_def_of_pos (zero_lt_one.trans_le hx1)] at he
        dsimp [F]
        linarith
      have hupper := mul_le_mul_of_nonneg_left hlog' hd
      simp only [W, Set.indicator_of_mem (show x ∈ Set.Ici 1 from hx1)]
      constructor
      · dsimp [F]; linarith
      · calc
          _ = 1 - Real.exp (-(d * Real.log x)) := by dsimp [F]; ring
          _ ≤ d * Real.log x := hu
          _ ≤ (d / q) * (F x + ρ) + ρ := by
            calc
              _ ≤ d * ((F x + ρ) / q) := hupper
              _ = (d / q) * (F x + ρ) := by ring
              _ ≤ _ := le_add_of_nonneg_right hρ
    · have hF_neg : F x ≤ 0 := sub_nonpos.2
        (Real.rpow_le_one ((floorSeq_nonneg hB n).trans hx) (le_of_not_ge hx1) hq.le)
      rw [show W x = 0 from Set.indicator_of_notMem hx1 _]
      have hnon : 0 ≤ (d / q) * (F x + ρ) :=
        mul_nonneg (div_nonneg hd hq.le) (by linarith)
      exact ⟨by linarith, by linarith⟩
  have hFρ : Integrable (fun x => F x + ρ) ν := hF.add (integrable_const ρ)
  have hD : Integrable (fun x => d / q * (F x + ρ)) ν := hFρ.const_mul (d / q)
  have hU : Integrable (fun x => d / q * (F x + ρ) + ρ) ν := hD.add (integrable_const ρ)
  have hl := integral_nonneg_of_ae (hpoint.mono fun x hx => hx.1)
  have hu := integral_mono_ae (hW.sub hF) hU (hpoint.mono fun x hx => hx.2)
  change (∫ x, W x - F x ∂ν) ≤ _ at hu
  rw [integral_sub hW hF] at hl hu
  rw [integral_add hD (integrable_const ρ),
    integral_const_mul, integral_add hF (integrable_const ρ)] at hu
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hu
  dsimp only
  rw [hW_integral, hF_integral, ← mul_sub]
  refine ⟨mul_nonneg hN.le hl, (mul_le_mul_of_nonneg_left hu hN.le).trans_eq ?_⟩
  dsimp [d]
  change N * (s / (Real.log B * N) / q * ((∫ x, F x ∂ν) + ρ) + ρ) =
    s / (Real.log B * N * q) * (N * (∫ x, F x ∂ν) + N * ρ) + N * ρ
  rw [div_div]
  ring

/-- A uniformly bounded sequence of monotone real functions admits a
subsequence converging almost everywhere. Compactness is used only on
rational evaluations. -/
theorem exists_subseq_ae_tendsto_of_monotone {f : ℕ → ℝ → ℝ} {M : ℝ}
    (hmono : ∀ j, Monotone (f j)) (hM : ∀ j x, |f j x| ≤ M) :
    ∃ (φ : ℕ → ℕ) (g : ℝ → ℝ), StrictMono φ ∧ Monotone g ∧
      ∀ᵐ x : ℝ, Tendsto (fun j => f (φ j) x) atTop (𝓝 (g x)) := by
  let F (j : ℕ) (q : ℚ) : Set.Icc (-M) M := ⟨f j q, abs_le.mp (hM j q)⟩
  obtain ⟨a, φ, hφ, hconv⟩ := CompactSpace.tendsto_subseq F
  let A (q : ℚ) := (a q : ℝ)
  have hlim (q : ℚ) : Tendsto (fun j => f (φ j) q) atTop (𝓝 (A q)) := by
    exact continuous_subtype_val.continuousAt.tendsto.comp ((tendsto_pi_nhds.1 hconv) q)
  have hmA : Monotone A := fun q p hqp =>
    le_of_tendsto_of_tendsto' (hlim q) (hlim p) fun j =>
      hmono (φ j) (Rat.cast_le.2 hqp)
  let S (x : ℝ) := A '' {q : ℚ | (q : ℝ) < x}
  have hnon (x : ℝ) : (S x).Nonempty := by
    obtain ⟨q, hq⟩ := exists_rat_lt x
    exact ⟨A q, q, hq, rfl⟩
  have hbdd (x : ℝ) : BddAbove (S x) :=
    ⟨M, by rintro _ ⟨q, _, rfl⟩; exact (a q).2.2⟩
  let g (x : ℝ) := sSup (S x)
  have hmg : Monotone g := by
    intro x y hxy
    exact csSup_le_csSup (hbdd y) (hnon x)
      (Set.image_mono fun q (hq : (q : ℝ) < x) => hq.trans_le hxy)
  have hl (x : ℝ) (q : ℚ) (hq : x ≤ q) : g x ≤ A q := by
    apply csSup_le (hnon x)
    rintro _ ⟨p, hp, rfl⟩
    exact hmA (Rat.cast_le.1 (hp.le.trans hq))
  have hu (x : ℝ) (q : ℚ) (hq : (q : ℝ) < x) : A q ≤ g x :=
    le_csSup (hbdd x) ⟨q, hq, rfl⟩
  have haec : ∀ᵐ x : ℝ, ContinuousAt g x := by
    rw [ae_iff]
    exact hmg.countable_not_continuousAt.measure_zero volume
  refine ⟨φ, g, hφ, hmg, ?_⟩
  filter_upwards [haec] with x hx
  rw [tendsto_order]
  constructor
  · intro y hy
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.1 hx (g x - y) (sub_pos.2 hy)
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show x - δ / 2 < x by linarith)
    have hdist : dist (x - δ / 2) x < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hx' := hclose hdist
    rw [Real.dist_eq, abs_lt] at hx'
    have hyq : y < A q := (show y < g (x - δ / 2) by linarith [hx'.1]).trans_le
      (hl _ q hq₁.le)
    filter_upwards [(tendsto_order.1 (hlim q)).1 y hyq] with j hj
    exact hj.trans_le (hmono (φ j) hq₂.le)
  · intro y hy
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.1 hx (y - g x) (sub_pos.2 hy)
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show x < x + δ / 2 by linarith)
    have hdist : dist (x + δ / 2) x < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hx' := hclose hdist
    rw [Real.dist_eq, abs_lt] at hx'
    have hyq : A q < y := (hu _ q hq₂).trans_lt (show g (x + δ / 2) < y by linarith [hx'.2])
    filter_upwards [(tendsto_order.1 (hlim q)).2 y hyq] with j hj
    exact (hmono (φ j) hq₁.le).trans_lt hj


theorem tendsto_weightExponent_atTop {B : ℝ} (hB : 2 < B) (s : ℝ) :
    Tendsto (fun N : ℝ => weightExponent B N s) atTop (𝓝 (theta B)) := by
  have hlog : 0 < Real.log B := Real.log_pos (by linarith)
  have hden : Tendsto (fun N : ℝ => Real.log B * N) atTop atTop :=
    tendsto_id.const_mul_atTop hlog
  have hdiv : Tendsto (fun N : ℝ => s / (Real.log B * N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  simpa [weightExponent] using
    (tendsto_const_nhds (x := theta B)).sub hdiv

theorem tendsto_pow_mul_geometric_floor {ρ t : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1)
    (ht : 0 < t) (k : ℕ) :
    Tendsto (fun N : ℝ => N ^ k * ρ ^ ⌊N * t⌋₊) atTop (𝓝 0) := by
  let c := -(t * Real.log ρ)
  have hc : 0 < c := neg_pos.2 (mul_neg_of_pos_of_neg ht (Real.log_neg hρ hρ'))
  have hlim : Tendsto (fun N : ℝ => ρ⁻¹ * (N ^ k * Real.exp (-c * N))) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) c hc).const_mul ρ⁻¹
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
    positivity
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
    have hr := Nat.lt_floor_add_one (N * t)
    have hpow : ρ ^ ⌊N * t⌋₊ ≤ Real.exp (-c * N) * ρ⁻¹ := by
      rw [← Real.rpow_natCast]
      calc
        ρ ^ (⌊N * t⌋₊ : ℝ) ≤ ρ ^ (N * t - 1) :=
          Real.rpow_le_rpow_of_exponent_ge hρ hρ'.le (by exact sub_le_iff_le_add.2 hr.le)
        _ = _ := by
          rw [Real.rpow_sub hρ, Real.rpow_one, Real.rpow_def_of_pos hρ, div_eq_mul_inv]
          congr 2
          dsimp [c]
          ring
    calc
      _ ≤ N ^ k * (Real.exp (-c * N) * ρ⁻¹) :=
        mul_le_mul_of_nonneg_left hpow (pow_nonneg hN _)
      _ = _ := by ring

/-- At a positive time, convergence of the weighted measures also determines
the Mellin transform. -/
theorem tendsto_scaledTransform_of_weak_weighted {ι : Type*} {l : Filter ι}
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1)
    {B : ℝ} (hB : 2 < B) {lam : ℝ} {t s v : ℝ} (ht : 0 < t) (hs : 0 ≤ s)
    (hadm : 0 < s + profileB v t) {ns : ι → ℝ} (hns : Tendsto ns l atTop)
    (hweak : WeakConvergence (fun j => weightedMeasure (scalingMeasure μ B lam (ns j) t) s) l
      (weightedMeasure (profileMeasure v t) s)) :
    Tendsto (fun j => scaledTransform μ B lam (ns j) t s) l (𝓝 (profileTransform v t s)) := by
  let m (j : ι) := (weightedMeasure (scalingMeasure μ B lam (ns j) t) s).real Set.univ
  let G (j : ι) := (ns j) * (2 / B) ^ ⌊ns j * t⌋₊
  let d (j : ι) := s / (Real.log B * ns j * weightExponent B (ns j) s)
  have hmass := hweak.2.2 (1 : ℝ →ᵇ ℝ)
  simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, integral_const, smul_eq_mul, mul_one] at hmass
  have hreal : (weightedMeasure (profileMeasure v t) s).real Set.univ = profileTransform v t s := by
    change (weightedMeasure (profileMeasure v t) s Set.univ).toReal = _
    rw [weightedMeasure_profileMeasure_mass hadm, ENNReal.toReal_ofReal]
    unfold profileTransform profileA
    positivity
  rw [hreal] at hmass
  have hm : Tendsto m l (𝓝 (profileTransform v t s)) := hmass
  have hG : Tendsto G l (𝓝 0) := by
    have hρ : 0 < 2 / B := by positivity
    have hρ' : 2 / B < 1 := (div_lt_one (by linarith)).2 hB
    have hg := (tendsto_pow_mul_geometric_floor hρ hρ' ht 1).comp hns
    change Tendsto (fun j => ns j ^ (1 : ℕ) * (2 / B) ^ ⌊ns j * t⌋₊) l (𝓝 0) at hg
    simpa only [pow_one, G] using hg
  have hq := (tendsto_weightExponent_atTop hB s).comp hns
  have hd : Tendsto d l (𝓝 0) := by
    have hlog : 0 < Real.log B := Real.log_pos (by linarith)
    have hden : Tendsto (fun j => Real.log B * ns j) l atTop := hns.const_mul_atTop hlog
    have hdiv : Tendsto (fun j => s / (Real.log B * ns j)) l (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    have h := hdiv.div hq (theta_pos hB).ne'
    change Tendsto (fun j => s / (Real.log B * ns j) / weightExponent B (ns j) s)
      l (𝓝 (0 / theta B)) at h
    simpa only [d, div_div, zero_div] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun j => m j - (d j * (m j + G j) + G j)) ?_ hm ?_ ?_
  · simpa only [zero_mul, zero_add, sub_zero] using hm.sub ((hd.mul (hm.add hG)).add hG)
  · filter_upwards [hns.eventually_gt_atTop 0, hq.eventually (Ioi_mem_nhds (theta_pos hB))]
      with j hj hqj
    have h := rescaledMeasure_weighted_mass_sub_bounds hpos hmean hB
      (scalingField μ B lam (ns j)) hj hs hqj ⌊ns j * t⌋₊
    have hnon : 0 ≤ d j := by
      dsimp [d]
      exact div_nonneg hs (mul_nonneg (mul_nonneg (Real.log_pos (by linarith)).le hj.le) hqj.le)
    have hle : scaledTransform μ B lam (ns j) t s ≤ m j := by
      exact sub_nonneg.mp h.1
    have hbound : m j - scaledTransform μ B lam (ns j) t s ≤
        d j * (scaledTransform μ B lam (ns j) t s + G j) + G j := h.2
    have hadd : scaledTransform μ B lam (ns j) t s + G j ≤ m j + G j :=
      add_le_add hle le_rfl
    linarith only [hbound, mul_le_mul_of_nonneg_left hadd hnon]
  · filter_upwards [hns.eventually_gt_atTop 0, hq.eventually (Ioi_mem_nhds (theta_pos hB))]
      with j hj hqj
    exact sub_nonneg.mp (rescaledMeasure_weighted_mass_sub_bounds hpos hmean hB
      (scalingField μ B lam (ns j)) hj hs hqj ⌊ns j * t⌋₊).1


private theorem abs_le_of_discrete_upper_growth {L : ℕ → ℝ} {n₀ : ℕ} {M δ : ℝ}
    (hM : 1 ≤ M) (hδ : 0 ≤ δ) (hinit : L n₀ ≤ M)
    (hlow : ∀ n, n₀ ≤ n → -1 ≤ L n)
    (hstep : ∀ n, n₀ ≤ n → |L n| ≤ M + 1 → L (n + 1) - L n ≤ δ) :
    ∀ k : ℕ, (k : ℝ) * δ ≤ 1 → |L (n₀ + k)| ≤ M + 1 := by
  have hupper : ∀ k : ℕ, (k : ℝ) * δ ≤ 1 → L (n₀ + k) ≤ M + (k : ℝ) * δ := by
    intro k
    induction k with
    | zero => simpa using hinit
    | succ k ih =>
      intro hk
      have hk' : (k : ℝ) * δ ≤ 1 := by
        rw [Nat.cast_succ, add_mul, one_mul] at hk
        linarith
      have h := ih hk'
      have hL : |L (n₀ + k)| ≤ M + 1 :=
        abs_le.mpr ⟨by linarith [hlow (n₀ + k) (by omega)], by linarith⟩
      have hs := hstep (n₀ + k) (by omega) hL
      rw [Nat.add_succ, Nat.cast_succ, add_mul, one_mul]
      linarith
  intro k hk
  exact abs_le.mpr ⟨by linarith [hlow (n₀ + k) (by omega)],
    by linarith [hupper k hk]⟩

/-- A bounded starting value gives an interval of bounded transforms. The
duration is independent of the field and of the starting time. -/
theorem transform_bounded_of_start {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {s M : ℝ} (hs : 0 ≤ s) (hM : 1 ≤ M) :
    ∃ δ > (0 : ℝ), ∀ r > (0 : ℝ), ∀ᶠ N : ℝ in atTop,
      ∀ h : ℝ, transformAt μ B h N ⌊N * r⌋₊ s ≤ M →
        ∀ t ∈ Set.Icc r (r + δ), |transformAt μ B h N ⌊N * t⌋₊ s| ≤ M + 1 := by
  let ρ := 2 / B
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ' : ρ < 1 := (div_lt_one (by linarith)).2 hB
  let q₁ := theta B / 2
  let q₂ := (1 + theta B) / 2
  have hq₁ : 0 < q₁ := by dsimp [q₁]; linarith [theta_pos hB]
  have hq₂ : q₂ < 1 := by dsimp [q₂]; linarith [theta_lt_one hB]
  obtain ⟨C, hdef⟩ := defectMean_lower_aux hpos hmean hB q₁ q₂ hq₁ hq₂
  obtain ⟨F, hfloor⟩ := transform_floor_aux hpos hmean hB
  let K := 2 * s * (M + 1) + 3 / 2 * (M + 1) ^ 2 + 3 / 2 * |C| + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let δ := 1 / (4 * K)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, fun r hr => ?_⟩
  have hq : ∀ᶠ N : ℝ in atTop, weightExponent B N s ∈ Set.Icc q₁ q₂ :=
    (tendsto_weightExponent_atTop hB s).eventually
      (Icc_mem_nhds (by dsimp [q₁]; linarith [theta_pos hB])
        (by dsimp [q₂]; linarith [theta_lt_one hB]))
  have hfloorN : Tendsto (fun N : ℝ => ⌊N * r⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.atTop_mul_const hr)
  have hG1 : ∀ᶠ N : ℝ in atTop, |F| * (N * ρ ^ ⌊N * r⌋₊) ≤ 1 := by
    have h : Tendsto (fun N : ℝ => |F| * (N ^ 1 * ρ ^ ⌊N * r⌋₊)) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_pow_mul_geometric_floor hρ hρ' hr 1).const_mul |F|
    simpa only [pow_one, mul_zero] using h.eventually (Iic_mem_nhds zero_lt_one)
  have hG2 : ∀ᶠ N : ℝ in atTop, N ^ 2 * ρ ^ ⌊N * r⌋₊ ≤ 1 :=
    (tendsto_pow_mul_geometric_floor hρ hρ' hr 2).eventually (Iic_mem_nhds zero_lt_one)
  filter_upwards [hq, hfloorN.eventually_ge_atTop 1, hG1, hG2,
    eventually_ge_atTop (max 1 (max s δ⁻¹))] with N hqN hstart hF hG hN
  intro h hinit t ht
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNs : s ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNδ : δ⁻¹ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hN0 : 0 < N := zero_lt_one.trans_le hN1
  let L (n : ℕ) := transformAt μ B h N n s
  let n₀ := ⌊N * r⌋₊
  have hρn (n : ℕ) (hn : n₀ ≤ n) : ρ ^ n ≤ ρ ^ n₀ :=
    pow_le_pow_of_le_one hρ.le hρ'.le hn
  have hlow (n : ℕ) (hn : n₀ ≤ n) : -1 ≤ L n := by
    have h := (hfloor h N n s s hN0 hs le_rfl (hq₁.le.trans hqN.1)).1
    have hh : F * N * ρ ^ n ≤ 1 := calc
      _ ≤ |F| * (N * ρ ^ n) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_abs_self F) (by positivity)
      _ ≤ _ := (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hρn n hn) hN0.le) (abs_nonneg F)).trans hF
    dsimp only [L, ρ] at *
    linarith
  have hstep (n : ℕ) (hn : n₀ ≤ n) (hL : |L n| ≤ M + 1) :
      L (n + 1) - L n ≤ K / N := by
    let e := Real.exp (s / N)
    have he0 : 0 < e := Real.exp_pos _
    have hx0 : 0 ≤ s / N := div_nonneg hs hN0.le
    have hx1 : s / N ≤ 1 := (div_le_one hN0).2 hNs
    have he1 : 1 ≤ e := Real.one_le_exp hx0
    have hexp : e - 1 ≤ 2 * (s / N) := by
      have h := Real.abs_exp_sub_one_le (abs_of_nonneg hx0 ▸ hx1)
      rwa [abs_of_nonneg (sub_nonneg.2 he1), abs_of_nonneg hx0] at h
    have he3 : e ≤ 3 := by linarith
    let D := defectMean μ B h n (weightExponent B N s)
    have hD : -D ≤ |C| * ρ ^ n := by
      have h := hdef h n (hstart.trans hn) _ hqN
      have hC := mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hρ.le n)
      change -(C * ρ ^ n) ≤ D at h
      linarith
    have hG' : N * ρ ^ n ≤ 1 / N := by
      apply (le_div_iff₀ hN0).2
      rw [show N * ρ ^ n * N = N ^ 2 * ρ ^ n by ring]
      exact (mul_le_mul_of_nonneg_left (hρn n hn) (sq_nonneg N)).trans hG
    have hrec : L (n + 1) = e * L n + e / (2 * N) * L n ^ 2 - N / 2 * e * D :=
      transform_recurrence_aux hpos hmean hB h hN0 (hstart.trans hn) hs
    have hterm₁ : (e - 1) * L n ≤ (2 * (s / N)) * (M + 1) := calc
      _ ≤ (e - 1) * (M + 1) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans hL) (sub_nonneg.2 he1)
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp (by positivity)
    have hterm₂ : e / (2 * N) * L n ^ 2 ≤ 3 / (2 * N) * (M + 1) ^ 2 := by
      have hsq : L n ^ 2 ≤ (M + 1) ^ 2 := by
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hL
      gcongr
    have hterm₃ : N / 2 * e * (-D) ≤ 3 / 2 * |C| / N := calc
      _ ≤ N / 2 * e * (|C| * ρ ^ n) := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = e / 2 * |C| * (N * ρ ^ n) := by ring
      _ ≤ 3 / 2 * |C| * (1 / N) := by gcongr
      _ = _ := by ring
    calc
      L (n + 1) - L n = (e - 1) * L n + e / (2 * N) * L n ^ 2 + N / 2 * e * (-D) := by
        rw [hrec]
        ring
      _ ≤ _ := by
        unfold K
        field_simp [hN0] at hterm₁ hterm₂ hterm₃ ⊢
        linarith
  have hm : n₀ ≤ ⌊N * t⌋₊ := Nat.floor_mono (mul_le_mul_of_nonneg_left ht.1 hN0.le)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
  have hb₁ := Nat.lt_floor_add_one (N * r)
  have hb₂ := Nat.floor_le (mul_nonneg hN0.le (hr.le.trans ht.1))
  have hk' : (k : ℝ) ≤ N * δ + 1 := by
    rw [hk, Nat.cast_add] at hb₂
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hN0.le]
  have hk'' : (k : ℝ) * (K / N) ≤ 1 := by
    have hδN : 1 ≤ N * δ := by
      simpa [one_div] using (div_le_iff₀ hδ).1 (show 1 / δ ≤ N by simpa [one_div] using hNδ)
    have hδK : δ * K = 1 / 4 := by
      dsimp [δ]
      field_simp [hK.ne']
    have hkk : (k : ℝ) * K ≤ N := calc
      _ ≤ (N * δ + 1) * K := mul_le_mul_of_nonneg_right hk' hK.le
      _ ≤ (N * δ + N * δ) * K := by gcongr
      _ = N / 2 := by linear_combination (2 * N) * hδK
      _ ≤ N := by linarith
    rw [← mul_div_assoc, div_le_one hN0]
    exact hkk
  rw [hk]
  exact abs_le_of_discrete_upper_growth hM (div_nonneg hK.le hN0.le) hinit hlow hstep k hk''


/-- Recover the base weight on a local interval after the transform at one
larger weight has been identified. -/
theorem eq_of_identified_larger_weight {L F U : ℝ → ℝ} {s₀ s r t M : ℝ}
    (hrt : r ≤ t) (hsmall : (|s₀| + M) * (t - r) < 1)
    (hL : ∀ u ∈ Set.Icc r t, |L u| ≤ M)
    (hF : ∀ u ∈ Set.Icc r t, |F u| ≤ M)
    (hinit : L r = F r)
    (hiL : IntervalIntegrable (fun u => psiS s (U u) - psiS s₀ (L u)) volume r t)
    (hiF : IntervalIntegrable (fun u => psiS s (U u) - psiS s₀ (F u)) volume r t)
    (hLdiff : ∀ u ∈ Set.Icc r t, (U u - L u) - (U r - L r) =
      timeIntegral (fun x => psiS s (U x) - psiS s₀ (L x)) r u)
    (hFdiff : ∀ u ∈ Set.Icc r t, (U u - F u) - (U r - F r) =
      timeIntegral (fun x => psiS s (U x) - psiS s₀ (F x)) r u) :
    ∀ u ∈ Set.Icc r t, L u = F u := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hL r ⟨le_rfl, hrt⟩)
  let e (u : ℝ) := L u - F u
  let a (u : ℝ) := s₀ + (L u + F u) / 2
  have hzero : ∀ u ∈ Set.Icc r t, e u = 0 := by
    apply eq_zero_of_bounded_volterra (a := a) (M := 2 * M) hrt
      (add_nonneg (abs_nonneg _) hM) hsmall
    · intro u hu
      dsimp [e]
      have h := norm_sub_le (L u) (F u)
      simp only [Real.norm_eq_abs] at h
      linarith [hL u hu, hF u hu]
    · exact ae_of_all _ fun u hu => by
        dsimp [a]
        have h := abs_add_le (L u) (F u)
        have h' := abs_add_le s₀ ((L u + F u) / 2)
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h'
        linarith [hL u hu, hF u hu]
    · intro u hu
      have hsub : Set.uIoc r u ⊆ Set.uIoc r t := by
        rw [Set.uIoc_of_le hu.1, Set.uIoc_of_le hrt]
        exact Set.Ioc_subset_Ioc_right hu.2
      have hli := hiL.mono_set' hsub
      have hfi := hiF.mono_set' hsub
      calc
        e u = ((U u - F u) - (U r - F r)) - ((U u - L u) - (U r - L r)) := by
          dsimp [e]
          rw [hinit]
          ring
        _ = timeIntegral (fun x => a x * e x) r u := by
          rw [hFdiff u hu, hLdiff u hu, timeIntegral, timeIntegral, timeIntegral,
            ← intervalIntegral.integral_sub hfi hli]
          congr 1
          funext x
          dsimp [a, e, psiS]
          ring
  exact fun u hu => sub_eq_zero.1 (hzero u hu)

theorem continuation_entrance_subsequence {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    {ℓ₃ κ γ lam : ℝ} (hlam : 0 < lam)
    (hCompact : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ lam T : ℝ, 0 ≤ lam → 0 < T → lam * T ^ 2 ≤ η₀ →
      ∃ C : ℝ, 0 < C ∧ ∀ Nseq : ℕ → ℝ, Tendsto Nseq atTop atTop →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ E : EntranceData T lam (lam * κ * Real.log B ^ 2 / ℓ₃) C,
            (∀ r : ℝ, 0 < r → r < T →
              Tendsto (fun j => timeIntegral
                (fun t => |scaledMass μ B lam (Nseq (φ j)) t - E.S t|) r T) atTop (𝓝 0)) ∧
            (∀ r : ℝ, 0 < r →
              TendstoUniformlyOn (fun j t => scaledDrift μ B lam (Nseq (φ j)) t) E.d atTop
                (Set.Icc r T)) ∧
            (∀ r : ℝ, 0 < r →
              TendstoUniformlyOn (fun j t => scaledSecond μ B lam (Nseq (φ j)) t) E.K atTop
                (Set.Icc r T)) ∧
            (∀ r : ℝ, 0 < r →
              TendstoUniformlyOn (fun j t => scaledThird μ B lam (Nseq (φ j)) t) E.P atTop
                (Set.Icc r T)) ∧
            (∀ r M : ℝ, 0 < r →
              TendstoUniformlyOn
                (fun j (p : ℝ × ℝ) => scaledCompensated μ B lam (Nseq (φ j)) p.1 p.2)
                (fun p => E.H p.1 p.2) atTop (Set.Icc r T ×ˢ Set.Icc 0 M)) ∧
            (∀ᵐ t, t ∈ Set.Ioc 0 T →
              WeakConvergence (fun j => scalingMeasure μ B lam (Nseq (φ j)) t) atTop (E.ν t)))
    (hProfile : ∀ lam T C : ℝ, 0 ≤ lam → 0 < T → 0 < C →
      ∃ Tstar : ℝ, 0 < Tstar ∧ Tstar ≤ T ∧
      ∀ E : EntranceData T lam (lam * κ * Real.log B ^ 2 / ℓ₃) C,
        ∀ᵐ t, t ∈ Set.Ioo 0 Tstar → E.ν t = profileMeasure (γ * lam) t) :
    ∃ Tstar > (0 : ℝ), ∀ Nseq : ℕ → ℝ, Tendsto Nseq atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ᵐ t : ℝ, t ∈ Set.Ioo 0 Tstar → ∀ s, 0 ≤ s → 0 < s + profileB (γ * lam) t →
          WeakConvergence
            (fun j => weightedMeasure (scalingMeasure μ B lam (Nseq (φ j)) t) s) atTop
            (weightedMeasure (profileMeasure (γ * lam) t) s) ∧
          Tendsto (fun j => scaledTransform μ B lam (Nseq (φ j)) t s) atTop
            (𝓝 (profileTransform (γ * lam) t s)) := by
  obtain ⟨η₀, hη₀, hc⟩ := hCompact
  let T := Real.sqrt (η₀ / lam)
  have hT : 0 < T := Real.sqrt_pos.2 (div_pos hη₀ hlam)
  have hsmall : lam * T ^ 2 ≤ η₀ := by
    dsimp only [T]
    rw [Real.sq_sqrt (div_nonneg hη₀.le hlam.le), mul_comm, div_mul_cancel₀ _ hlam.ne']
  obtain ⟨C, hC, hc⟩ := hc lam T hlam.le hT hsmall
  obtain ⟨Tstar, hTstar, hTstarT, hp⟩ := hProfile lam T C hlam.le hT hC
  refine ⟨Tstar, hTstar, fun Nseq hN => ?_⟩
  obtain ⟨φ, hφ, E, _, _, _, _, _, hw⟩ := hc Nseq hN
  have hN' : ∀ᶠ j in atTop, 0 < Nseq (φ j) :=
    (hN.comp hφ.tendsto_atTop).eventually_gt_atTop 0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hw, hp E, E.representation] with t ht hte hrep hmem s hs hadm
  have hmem' : t ∈ Set.Ioc 0 T := ⟨hmem.1, hmem.2.le.trans hTstarT⟩
  have hwt := ht hmem'
  have hν' := (hrep hmem').2.1
  rw [hte hmem] at hwt hν'
  have hν : ∀ᶠ j in atTop, scalingMeasure μ B lam (Nseq (φ j)) t (Set.Iio 0) = 0 := by
    filter_upwards [hN'] with j hj
    exact (rescaledMeasure_finite_aux hpos hmean hB _ hj _).2
  have hw' := weakConvergence_weighted_of_supported hwt hν hν' hs
  exact ⟨hw', tendsto_scaledTransform_of_weak_weighted hpos hmean hB hmem.1 hs hadm
    (hN.comp hφ.tendsto_atTop) hw'⟩



private theorem intervalIntegral_mul_primitive {c D H : ℝ → ℝ} {r t : ℝ}
    (hc : AbsolutelyContinuousOnInterval c r t)
    (hi : IntervalIntegrable H volume r t)
    (hD : ∀ x ∈ Set.uIcc r t, D x - D r = timeIntegral H r x) :
    let G := fun x => deriv c x * D x + c x * H x
    IntervalIntegrable G volume r t ∧ timeIntegral G r t = c t * D t - c r * D r := by
  let P (x : ℝ) := D r + timeIntegral H r x
  have hr : r ∈ Set.uIcc r t := Set.left_mem_uIcc
  have hp (x : ℝ) (hx : x ∈ Set.uIcc r t) : P x = D x := by
    dsimp [P]
    linarith [hD x hx]
  have hP : AbsolutelyContinuousOnInterval P r t := by
    have hconst : ContDiffOn ℝ 1 (fun _ : ℝ => D r) (Set.uIcc r t) := contDiffOn_const
    exact hconst.absolutelyContinuousOnInterval.fun_add
      (hi.absolutelyContinuousOnInterval_intervalIntegral hr)
  have hae : ∀ᵐ x, x ∈ Set.uIoc r t →
      deriv c x * P x + c x * deriv P x = deriv c x * D x + c x * H x := by
    filter_upwards [hi.ae_hasDerivAt_integral] with x hx hx'
    have hxm := Set.uIoc_subset_uIcc hx'
    rw [hp x hxm]
    have hd : HasDerivAt P (H x) x := (hx hxm r hr).const_add (D r)
    rw [hd.deriv]
  have hInt := (hc.intervalIntegrable_deriv.mul_continuousOn hP.continuousOn).add
    (hP.intervalIntegrable_deriv.continuousOn_mul hc.continuousOn)
  have heq := intervalIntegral.integral_congr_ae hae
  have hre := (ae_restrict_iff' measurableSet_uIoc).2 hae
  refine ⟨hInt.congr_ae hre, ?_⟩
  unfold timeIntegral
  rw [← heq, hc.integral_deriv_mul_eq_sub hP, hp r hr, hp t Set.right_mem_uIcc]

/-- Time-dependent finite combinations of transform differences satisfy
the integrated product rule. Each difference uses the same base weight,
so the coefficients of the associated spatial test sum to zero. -/
theorem timeIntegral_transform_test {ι : Type*} (weights : Finset ι)
    (c D H : ι → ℝ → ℝ) {r t : ℝ}
    (hc : ∀ i ∈ weights, AbsolutelyContinuousOnInterval (c i) r t)
    (hi : ∀ i ∈ weights, IntervalIntegrable (H i) volume r t)
    (hD : ∀ i ∈ weights, ∀ x ∈ Set.uIcc r t, D i x - D i r = timeIntegral (H i) r x) :
    let G := fun x => ∑ i ∈ weights, (deriv (c i) x * D i x + c i x * H i x)
    IntervalIntegrable G volume r t ∧
      (∑ i ∈ weights, c i t * D i t) - (∑ i ∈ weights, c i r * D i r) = timeIntegral G r t := by
  have h (i : ι) (hi' : i ∈ weights) :=
    intervalIntegral_mul_primitive (hc i hi') (hi i hi') (hD i hi')
  refine ⟨intervalIntegrable_iff.2 (integrable_finsetSum weights (fun i hi' => (h i hi').1.def')), ?_⟩
  unfold timeIntegral
  rw [intervalIntegral.integral_finsetSum (fun i hi' => (h i hi').1), ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i hi' => ((h i hi').2).symm


private theorem withDensity_map_eq_map_withDensity {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (ν : Measure α) {f : α → β}
    {w : β → ℝ≥0∞} (hf : Measurable f) (hw : Measurable w) :
    (ν.map f).withDensity w = (ν.withDensity (w ∘ f)).map f := by
  ext1 A hA
  rw [withDensity_apply _ hA, Measure.restrict_map hf hA,
    lintegral_map hw hf, Measure.map_apply hf hA, withDensity_apply _ (hf hA)]
  rfl

/-- Left translation with absorption of all mass at or below the travel distance. -/
noncomputable def absorbedTranslate (d : ℝ) (ν : Measure ℝ) : Measure ℝ :=
  (ν.restrict (Set.Ioi d)).map (fun x => x - d)

theorem weightedMeasure_absorbedTranslate (d s : ℝ) (ν : Measure ℝ) :
    weightedMeasure (absorbedTranslate d ν) s =
      ENNReal.ofReal (Real.exp (s * d)) • absorbedTranslate d (weightedMeasure ν s) := by
  unfold absorbedTranslate weightedMeasure
  have hshift : Measurable (fun x : ℝ => x - d) := by fun_prop
  have hw : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-(s * x))) := by fun_prop
  rw [withDensity_map_eq_map_withDensity _ hshift hw, restrict_withDensity measurableSet_Ioi,
    ← Measure.map_smul _ hshift.aemeasurable, ← withDensity_smul _ hw]
  congr 2
  funext x
  change ENNReal.ofReal (Real.exp (-(s * (x - d)))) =
    ENNReal.ofReal (Real.exp (s * d)) * ENNReal.ofReal (Real.exp (-(s * x)))
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

theorem weightedMeasure_absorbedTranslate_mass_le (d s : ℝ) (ν : Measure ℝ) :
    weightedMeasure (absorbedTranslate d ν) s Set.univ ≤
      ENNReal.ofReal (Real.exp (s * d)) * weightedMeasure ν s Set.univ := by
  rw [weightedMeasure_absorbedTranslate, Measure.smul_apply, smul_eq_mul, absorbedTranslate,
    Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ]
  exact mul_right_mono (measure_mono (μ := weightedMeasure ν s) (Set.subset_univ _))

theorem weightedMeasure_conv (s : ℝ) (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    weightedMeasure (μ ∗ ν) s = weightedMeasure μ s ∗ weightedMeasure ν s := by
  have h : Measurable (fun z : ℝ × ℝ => z.1 + z.2) := by fun_prop
  have hw : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-(s * x))) := by fun_prop
  unfold weightedMeasure Measure.conv
  rw [withDensity_map_eq_map_withDensity _ h hw, prod_withDensity hw hw]
  congr 2
  funext z
  change ENNReal.ofReal (Real.exp (-(s * (z.1 + z.2)))) =
    ENNReal.ofReal (Real.exp (-(s * z.1))) * ENNReal.ofReal (Real.exp (-(s * z.2)))
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring


private theorem polynomial_exists_primitive (q : Polynomial ℝ) :
    ∃ p : Polynomial ℝ, p.derivative = q := by
  classical
  refine ⟨q.sum (fun n a => Polynomial.monomial (n + 1) (a / (n + 1 : ℝ))), ?_⟩
  calc
    _ = q.sum (fun n a => Polynomial.monomial n a) := by
      unfold Polynomial.sum
      rw [Polynomial.derivative_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [Polynomial.derivative_monomial_succ]
      congr 1
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hn]
    _ = q := q.sum_monomial_eq

/-- Approximate a continuously differentiable function and its derivative
on a compact interval by a polynomial and its derivative. -/
theorem exists_polynomial_approx_deriv {g g' : ℝ → ℝ} {a b ε : ℝ} (hab : a ≤ b)
    (hder : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x) (hcont : ContinuousOn g' (Set.Icc a b))
    (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, p.eval a = g a ∧
      ∀ x ∈ Set.Icc a b, |p.eval x - g x| < ε ∧ |p.derivative.eval x - g' x| < ε := by
  let S := Set.Icc a b
  let G : C(S, ℝ) := ⟨fun x => g' x, continuousOn_iff_continuous_domRestrict.1 hcont⟩
  let η := ε / (b - a + 1)
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  have hden : 0 < b - a + 1 := by linarith
  have hη : 0 < η := div_pos hε hden
  have hηε : η ≤ ε := (div_le_iff₀ hden).2 (by nlinarith)
  have hG : G ∈ closure (polynomialFunctions S : Set C(S, ℝ)) := by
    change G ∈ (polynomialFunctions S).topologicalClosure
    rw [polynomialFunctions.topologicalClosure]
    trivial
  obtain ⟨Q, hQ, hdist⟩ := Metric.mem_closure_iff.1 hG η hη
  rw [polynomialFunctions_coe] at hQ
  obtain ⟨q, rfl⟩ := hQ
  have hq (x : ℝ) (hx : x ∈ S) : |q.eval x - g' x| < η := by
    have h := (Polynomial.toContinuousMapOnAlgHom S q - G).norm_coe_le_norm ⟨x, hx⟩
    rw [dist_comm, dist_eq_norm] at hdist
    exact (show |q.eval x - g' x| ≤ ‖Polynomial.toContinuousMapOnAlgHom S q - G‖ from h).trans_lt hdist
  obtain ⟨p₀, hp₀⟩ := polynomial_exists_primitive q
  let p := p₀ + Polynomial.C (g a - p₀.eval a)
  have hp : p.derivative = q := by simp [p, hp₀]
  have hpa : p.eval a = g a := by simp [p]
  refine ⟨p, hpa, fun x hx => ⟨?_, (hp ▸ hq x hx).trans_le hηε⟩⟩
  have hsub : Set.uIcc a x ⊆ S := by
    rw [Set.uIcc_of_le hx.1]
    intro u hu
    exact ⟨hu.1, hu.2.trans hx.2⟩
  have hD (u : ℝ) (hu : u ∈ Set.uIcc a x) :
      HasDerivAt (fun y => p.eval y - g y) (q.eval u - g' u) u := by
    rw [← hp]
    exact (p.hasDerivAt u).sub (hder u (hsub hu))
  have hi : IntervalIntegrable (fun u => q.eval u - g' u) volume a x := by
    have hc : ContinuousOn (fun u => q.eval u - g' u) (Set.uIcc a x) :=
      q.continuous.continuousOn.sub (hcont.mono hsub)
    rw [Set.uIcc_of_le hx.1] at hc
    exact hc.intervalIntegrable_of_Icc hx.1
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt hD hi
  simp only [hpa, sub_self, sub_zero] at hft
  rw [← hft, ← Real.norm_eq_abs]
  have hbnd : ‖∫ u in a..x, (q.eval u - g' u)‖ ≤ η * |x - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    exact (hq u (hsub (Set.uIoc_subset_uIcc hu))).le
  refine hbnd.trans_lt ?_
  rw [abs_of_nonneg (sub_nonneg.2 hx.1)]
  have hη_eq : η * (b - a + 1) = ε := div_mul_cancel₀ _ hden.ne'
  rw [← hη_eq]
  exact mul_lt_mul_of_pos_left (by linarith [hx.2]) hη


/-- The moving exponential tests cancel the transport terms, leaving only
the boundary correction and the convolution term. -/
theorem transformDifference_moving_dilation (p : Polynomial ℝ)
    (L : ℕ → ℝ → ℝ) {σ r t : ℝ}
    (hi : ∀ n ∈ p.support, IntervalIntegrable
      (fun x => psiS (σ + n) (L n x) - psiS σ (L 0 x)) volume r t)
    (hD : ∀ n ∈ p.support, ∀ u ∈ Set.uIcc r t,
      (L n u - L 0 u) - (L n r - L 0 r) =
        timeIntegral (fun x => psiS (σ + n) (L n x) - psiS σ (L 0 x)) r u) :
    let c := fun (n : ℕ) (u : ℝ) => p.coeff n * Real.exp ((σ + n) * (t - u))
    let F (x : ℝ) := ∑ n ∈ p.support,
        c n x * ((n : ℝ) * L 0 x + ((L n x) ^ 2 - (L 0 x) ^ 2) / 2)
    IntervalIntegrable F volume r t ∧
      (∑ n ∈ p.support, c n t * (L n t - L 0 t)) -
        (∑ n ∈ p.support, c n r * (L n r - L 0 r)) = timeIntegral F r t := by
  let c (n : ℕ) (u : ℝ) := p.coeff n * Real.exp ((σ + n) * (t - u))
  have hc (n : ℕ) : ContDiff ℝ 1 (c n) := by
    dsimp [c]
    fun_prop
  have heq := timeIntegral_transform_test p.support c
    (fun n x => L n x - L 0 x) (fun n x => psiS (σ + n) (L n x) - psiS σ (L 0 x))
    (fun n _ => (hc n).contDiffOn.absolutelyContinuousOnInterval) hi hD
  have hF : (fun x => ∑ n ∈ p.support, (deriv (c n) x * (L n x - L 0 x) +
      c n x * (psiS (σ + n) (L n x) - psiS σ (L 0 x)))) =
      fun x => ∑ n ∈ p.support, c n x * ((n : ℝ) * L 0 x + ((L n x) ^ 2 - (L 0 x) ^ 2) / 2) := by
    funext x
    apply Finset.sum_congr rfl
    intro n _
    have hd : HasDerivAt (c n) (-(σ + n) * c n x) x := by
      have h := ((((hasDerivAt_id x).const_sub t).const_mul (σ + n)).exp).const_mul (p.coeff n)
      refine h.congr_deriv ?_
      dsimp [c, id]
      ring
    rw [hd.deriv]
    unfold psiS
    ring
  rw [hF] at heq
  exact heq

theorem weightedMeasure_add (ν : Measure ℝ) (s w : ℝ) :
    weightedMeasure ν (s + w) = weightedMeasure (weightedMeasure ν s) w := by
  unfold weightedMeasure
  rw [← withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

/-- A Laplace transform on an arithmetic progression of weights is the
moment sequence of the image of the base-weighted measure under `exp(-x)`. -/
theorem measureMoment_weighted_exponential_map (ν : Measure ℝ) (σ : ℝ) (n : ℕ) :
    measureMoment ((weightedMeasure ν σ).map (fun x => Real.exp (-x))) n =
      (weightedMeasure ν (σ + n)).real Set.univ := by
  rw [measureMoment, integral_map (by fun_prop) (by fun_prop), weightedMeasure_add]
  let ξ := weightedMeasure ν σ
  change (∫ x, Real.exp (-x) ^ n ∂ξ) = (weightedMeasure ξ n).real Set.univ
  calc
    _ = ∫ x, Real.exp (-((n : ℝ) * x)) ∂ξ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← Real.exp_nat_mul, mul_neg]
    _ = ∫ _ : ℝ, (1 : ℝ) ∂weightedMeasure ξ n := by
      unfold weightedMeasure
      rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp) _]
      simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_one]
    _ = _ := by rw [integral_const, smul_eq_mul, mul_one]

theorem integral_polynomial_dilation (p : Polynomial ℝ) (E : ℝ)
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1) :
    ∫ y, p.eval (E * y) ∂ν =
      ∑ n ∈ p.support, p.coeff n * E ^ n * measureMoment ν n := by
  have hres := Measure.restrict_eq_self_of_ae_mem hν
  have hi (n : ℕ) : Integrable (fun y : ℝ => p.coeff n * E ^ n * y ^ n) ν := by
    rw [← hres]
    have hc : Continuous (fun y : ℝ => p.coeff n * E ^ n * y ^ n) := by fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  calc
    _ = ∫ y, ∑ n ∈ p.support, p.coeff n * E ^ n * y ^ n ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        change p.eval (E * y) = _
        rw [p.eval_eq_sum]
        unfold Polynomial.sum
        exact Finset.sum_congr rfl fun n _ => by
          change p.coeff n * (E * y) ^ n = _
          rw [mul_pow, mul_assoc]
    _ = _ := by
      rw [integral_finsetSum p.support (fun n _ => hi n)]
      simp only [integral_const_mul, measureMoment]

theorem measureMoment_zero_eq_mass (ν : Measure ℝ) :
    measureMoment ν 0 = ν.real Set.univ := by
  simp only [measureMoment, pow_zero, integral_const, smul_eq_mul, mul_one]

private theorem polynomial_centered_dilation (p : Polynomial ℝ) (σ d : ℝ)
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1) :
    (∑ n ∈ p.support, p.coeff n * Real.exp ((σ + n) * d) *
      (measureMoment ν n - measureMoment ν 0)) =
      Real.exp (σ * d) * (∫ y, p.eval (Real.exp d * y) - p.eval (Real.exp d) ∂ν) := by
  let E := Real.exp d
  have hi : Integrable (fun y => p.eval (E * y)) ν := by
    rw [← Measure.restrict_eq_self_of_ae_mem hν]
    have hc : Continuous (fun y : ℝ => p.eval (E * y)) := by fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  change _ = Real.exp (σ * d) * ∫ y, p.eval (E * y) - p.eval E ∂ν
  rw [integral_sub hi (integrable_const _), integral_polynomial_dilation p E hν,
    integral_const, smul_eq_mul, ← measureMoment_zero_eq_mass, mul_sub, p.eval_eq_sum]
  unfold Polynomial.sum
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [add_mul, Real.exp_add, Real.exp_nat_mul]
  dsimp [E]
  ring

theorem measureMoment_mconv_self (ν : Measure ℝ) [IsFiniteMeasure ν] (n : ℕ) :
    measureMoment (ν ∗ₘ ν) n = measureMoment ν n ^ 2 := by
  rw [measureMoment, Measure.mconv, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  have h := integral_prod_mul (μ := ν) (ν := ν) (fun y : ℝ => y ^ n) (fun y : ℝ => y ^ n)
  simpa only [measureMoment, pow_two] using h

theorem ae_Icc_mconv_self {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ y ∂(ν ∗ₘ ν), y ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Measure.mconv,
    ae_map_iff (f := fun z : ℝ × ℝ => z.1 * z.2) (by fun_prop)
      (p := fun y : ℝ => y ∈ Set.Icc (0 : ℝ) 1) measurableSet_Icc]
  apply (Measure.ae_prod_iff_ae_ae (show MeasurableSet
    {z : ℝ × ℝ | z.1 * z.2 ∈ Set.Icc (0 : ℝ) 1} from measurableSet_Icc.preimage (by fun_prop))).2
  filter_upwards [hν] with x hx
  filter_upwards [hν] with y hy
  exact ⟨mul_nonneg hx.1 hy.1, (mul_le_of_le_one_right hx.1 hy.2).trans hx.2⟩

/-- An upper bound on time increments up to a vanishing error yields
almost-everywhere subsequential compactness on the time interval. -/
theorem exists_subseq_ae_tendsto_of_one_sided {f : ℕ → ℝ → ℝ} {ε : ℕ → ℝ}
    {a b C M : ℝ} (hab : a ≤ b) (hε : Tendsto ε atTop (𝓝 0))
    (hM : ∀ j x, x ∈ Set.Icc a b → |f j x| ≤ M)
    (hone : ∀ j x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      f j y - f j x ≤ C * (y - x) + ε j) :
    ∃ (φ : ℕ → ℕ) (g : ℝ → ℝ), StrictMono φ ∧ Measurable g ∧
      ∀ᵐ x : ℝ, x ∈ Set.Icc a b → Tendsto (fun j => f (φ j) x) atTop (𝓝 (g x)) := by
  let clamp (x : ℝ) := max a (min x b)
  have hc (x : ℝ) : clamp x ∈ Set.Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hcid (x : ℝ) (hx : x ∈ Set.Icc a b) : clamp x = x := by
    dsimp [clamp]
    rw [min_eq_left hx.2, max_eq_right hx.1]
  have hclamp : Monotone clamp := fun _ _ h =>
    max_le_max le_rfl (min_le_min h le_rfl)
  let K := M + |C| * (|a| + |b|)
  let V (j : ℕ) (x : ℝ) := (fun u => f j u - C * u) '' Set.Icc (clamp x) b
  have hne (j : ℕ) (x : ℝ) : (V j x).Nonempty :=
    ⟨f j (clamp x) - C * clamp x, clamp x, ⟨le_rfl, (hc x).2⟩, rfl⟩
  have hval (j : ℕ) (x : ℝ) (u : ℝ) (hu : u ∈ V j x) : |u| ≤ K := by
    obtain ⟨v, hv, rfl⟩ := hu
    have hvm : v ∈ Set.Icc a b := ⟨(hc x).1.trans hv.1, hv.2⟩
    have hvb : |v| ≤ |a| + |b| := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b,
        hvm.1, hvm.2]
    calc
      |f j v - C * v| ≤ |f j v| + |C * v| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (f j v) (C * v)
      _ ≤ K := by
        rw [abs_mul]
        exact add_le_add (hM j v hvm) (mul_le_mul_of_nonneg_left hvb (abs_nonneg _))
  have hbd (j : ℕ) (x : ℝ) : BddAbove (V j x) :=
    ⟨K, fun u hu => (le_abs_self u).trans (hval j x u hu)⟩
  let F (j : ℕ) (x : ℝ) := -sSup (V j x)
  have hmon (j : ℕ) : Monotone (F j) := by
    intro x y hxy
    dsimp [F]
    apply neg_le_neg
    exact csSup_le_csSup (hbd j x) (hne j y)
      (Set.image_mono (Set.Icc_subset_Icc_left (hclamp hxy)))
  have hFb (j : ℕ) (x : ℝ) : |F j x| ≤ K := by
    rcases hne j x with ⟨u, hu⟩
    rw [abs_neg]
    exact abs_le.2 ⟨(neg_le_of_abs_le (hval j x u hu)).trans (le_csSup (hbd j x) hu),
      csSup_le ⟨u, hu⟩ fun v hv => (le_abs_self v).trans (hval j x v hv)⟩
  obtain ⟨φ, g, hφ, hg, ha⟩ := exists_subseq_ae_tendsto_of_monotone hmon hFb
  refine ⟨φ, fun x => C * x - g x, hφ, (measurable_const.mul measurable_id |>.sub hg.measurable), ?_⟩
  filter_upwards [ha] with x hx hxab
  have hbnd (j : ℕ) :
      C * x - F j x - ε j ≤ f j x ∧ f j x ≤ C * x - F j x := by
    have hleft : sSup (V j x) ≤ f j x - C * x + ε j := by
      apply csSup_le (hne j x)
      rintro _ ⟨u, hu, rfl⟩
      rw [hcid x hxab] at hu
      have hone' := hone j x u hxab ⟨hxab.1.trans hu.1, hu.2⟩ hu.1
      linarith
    have hright : f j x - C * x ≤ sSup (V j x) :=
      le_csSup (hbd j x) ⟨x, by rw [hcid x hxab]; exact ⟨le_rfl, hxab.2⟩, rfl⟩
    dsimp [F]
    constructor <;> linarith
  have hg₁ : Tendsto (fun j => C * x - F (φ j) x) atTop (𝓝 (C * x - g x)) :=
    tendsto_const_nhds.sub hx
  have hg₂ : Tendsto (fun j => C * x - F (φ j) x - ε (φ j)) atTop (𝓝 (C * x - g x)) := by
    have hε' : Tendsto (fun j => ε (φ j)) atTop (𝓝 0) := hε.comp hφ.tendsto_atTop
    simpa only [sub_zero] using hg₁.sub hε'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hg₂ hg₁
    (fun j => (hbnd (φ j)).1) (fun j => (hbnd (φ j)).2)


private theorem polynomial_boundary_dilation (p : Polynomial ℝ) (σ d m : ℝ) :
    (∑ n ∈ p.support, p.coeff n * Real.exp ((σ + n) * d) * ((n : ℝ) * m)) =
      Real.exp (σ * d) * Real.exp d * p.derivative.eval (Real.exp d) * m := by
  rw [Polynomial.derivative_eval, Polynomial.sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [add_mul, Real.exp_add, Real.exp_nat_mul]
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel, pow_succ]
    ring

/-- Polynomial tests of the lifted measure in the coordinate `y = exp(-x)`.
The derivative at the moving cutoff appears as a boundary term. -/
theorem projectedPolynomial_mild (p : Polynomial ℝ) (L : ℕ → ℝ → ℝ) (η : ℝ → Measure ℝ)
    {σ r t : ℝ} (hrt : r ≤ t)
    (hf : ∀ u, IsFiniteMeasure (η u))
    (hsupp : ∀ u, ∀ᵐ y ∂(η u), y ∈ Set.Icc (0 : ℝ) 1)
    (hr : ∀ n, L n r = measureMoment (η r) n)
    (ht : ∀ n, L n t = measureMoment (η t) n)
    (ha : ∀ᵐ u : ℝ, u ∈ Set.Icc r t → ∀ n, L n u = measureMoment (η u) n)
    (hi : ∀ n ∈ p.support, IntervalIntegrable
      (fun x => psiS (σ + n) (L n x) - psiS σ (L 0 x)) volume r t)
    (hD : ∀ n ∈ p.support, ∀ u ∈ Set.uIcc r t,
      (L n u - L 0 u) - (L n r - L 0 r) =
        timeIntegral (fun x => psiS (σ + n) (L n x) - psiS σ (L 0 x)) r u) :
    let W (d : ℝ) (ν : Measure ℝ) :=
      Real.exp (σ * d) * (∫ y, p.eval (Real.exp d * y) - p.eval (Real.exp d) ∂ν)
    let H (u : ℝ) := Real.exp (σ * (t - u)) * Real.exp (t - u) *
      p.derivative.eval (Real.exp (t - u)) * (η u).real Set.univ +
      W (t - u) (η u ∗ₘ η u) / 2
    IntervalIntegrable H volume r t ∧
      W (t - t) (η t) - W (t - r) (η r) = timeIntegral H r t := by
  let c (n : ℕ) (u : ℝ) := p.coeff n * Real.exp ((σ + n) * (t - u))
  let F (u : ℝ) := ∑ n ∈ p.support,
    (c n u * ((n : ℝ) * L 0 u + ((L n u) ^ 2 - (L 0 u) ^ 2) / 2))
  have h := transformDifference_moving_dilation p L hi hD
  change IntervalIntegrable F volume r t ∧
    (∑ n ∈ p.support, c n t * (L n t - L 0 t)) -
      (∑ n ∈ p.support, c n r * (L n r - L 0 r)) = timeIntegral F r t at h
  let W (d : ℝ) (ν : Measure ℝ) :=
    Real.exp (σ * d) * (∫ y, p.eval (Real.exp d * y) - p.eval (Real.exp d) ∂ν)
  let H (u : ℝ) := Real.exp (σ * (t - u)) * Real.exp (t - u) *
    p.derivative.eval (Real.exp (t - u)) * (η u).real Set.univ +
    W (t - u) (η u ∗ₘ η u) / 2
  have hh : ∀ᵐ u : ℝ, u ∈ Set.uIoc r t → F u = H u := by
    filter_upwards [ha] with u hu hmem
    rw [Set.uIoc_of_le hrt] at hmem
    have hl := hu ⟨hmem.1.le, hmem.2⟩
    letI := hf u
    have hfinconv : IsFiniteMeasure (η u ∗ₘ η u) := by
      unfold Measure.mconv
      infer_instance
    letI := hfinconv
    dsimp only [F, H]
    simp only [mul_add, ← mul_div_assoc, Finset.sum_add_distrib, ← Finset.sum_div, c]
    simp_rw [hl]
    rw [measureMoment_zero_eq_mass, polynomial_boundary_dilation]
    congr 1
    congr 1
    unfold W
    rw [← polynomial_centered_dilation p σ (t - u) (ae_Icc_mconv_self (hsupp u))]
    simp_rw [measureMoment_mconv_self, measureMoment_zero_eq_mass]
  have hcongr := intervalIntegral.integral_congr_ae hh
  have hcongr' := (ae_restrict_iff' measurableSet_uIoc).2 hh
  change IntervalIntegrable H volume r t ∧
    W (t - t) (η t) - W (t - r) (η r) = timeIntegral H r t
  refine ⟨h.1.congr_ae hcongr', ?_⟩
  letI := hf t
  letI := hf r
  have h₁ := polynomial_centered_dilation p σ (t - t) (hsupp t)
  have h₂ := polynomial_centered_dilation p σ (t - r) (hsupp r)
  change _ = W (t - t) (η t) at h₁
  change _ = W (t - r) (η r) at h₂
  have he := h.2
  dsimp only [c] at he
  simp_rw [hr, ht] at he
  rw [h₁, h₂, timeIntegral, hcongr] at he
  exact he

end DiamondPinning
