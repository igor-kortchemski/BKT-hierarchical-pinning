module

public import DiamondPinning.Model.InstancePins
public import DiamondPinning.Proofs.CriticalMoments
public import DiamondPinning.Proofs.Mellin
public import DiamondPinning.Proofs.IntegrabilityProof
public import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Summable

@[expose] public section

namespace DiamondPinning

open MeasureTheory Filter Set Asymptotics
open scoped Topology BigOperators

noncomputable def productLogKernel (B : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  s ^ theta B * (Real.log s - 2 * Real.log B) ^ k

/-- Half the mean of the soft correction kernel in the moment recurrence. -/
noncomputable def productLogCorrection (μ : Measure ℝ) (B h : ℝ) (k n : ℕ) : ℝ :=
  (∫ s, productLogKernel B k (s + (B - 1)) - productLogKernel B k s
    ∂productLaw μ B h n) / 2

private theorem product_B_rpow_theta {B : ℝ} (hB : 2 < B) : B ^ theta B = 2 := by
  have hb : 0 < B := by linarith
  have hl := Real.log_pos (show 1 < B by linarith)
  rw [Real.rpow_def_of_pos hb, theta, ← mul_div_assoc, mul_div_cancel_left₀ _ hl.ne',
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

private theorem product_signed_integrable {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {f : Ω → ℝ}
    (hf : AEMeasurable f ν) (hp : ∀ᵐ x ∂ν, 0 < f x) (hi : Integrable f ν)
    {B : ℝ} (hB : 2 < B) (a : ℝ) (k : ℕ) :
    Integrable (fun x => f x ^ theta B * (Real.log (f x) - a) ^ k) ν := by
  have hm : AEStronglyMeasurable
      (fun x => f x ^ theta B * (Real.log (f x) - a) ^ k) ν := by fun_prop
  rw [← integrable_norm_iff hm]
  apply (integrable_rpow_abs_log_sub_of ν hf hp hi (theta_pos hB) (theta_lt_one hB)
    (Nat.cast_nonneg k) (a := a)).congr
  filter_upwards [hp] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _),
    abs_pow, Real.rpow_natCast]

/-- Binomial form of the exact law-level recursion for all tilted log moments. -/
theorem tiltedLogMoment_succ_product {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (k n : ℕ) :
    tiltedLogMoment μ B h k (n + 1) =
      (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        (tiltedLogMoment μ B h i n * tiltedLogMoment μ B h (k - i) n)) / 2 +
      productLogCorrection μ B h k n := by
  let ν := lawR μ B h n
  let : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  let g (i : ℕ) (x : ℝ) := x ^ theta B * (Real.log x - Real.log B) ^ i
  let u (p : ℝ × ℝ) := p.1 * p.2
  have hb : 0 < B := by linarith
  have hc : 0 < B - 1 := by linarith
  have hm : Measurable u := measurable_fst.mul measurable_snd
  have hg (i : ℕ) : Measurable (g i) := by dsimp [g]; fun_prop
  have hk : Measurable (productLogKernel B k) := by unfold productLogKernel; fun_prop
  have hp := ae_pos_lawR hpos hB h n
  have hi := integrable_lawR_of hpos hmean hB h n
  have hpair : ∀ᵐ p ∂ν.prod ν, 0 < p.1 ∧ 0 < p.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hp,
      Measure.quasiMeasurePreserving_snd.ae hp] with p hp₁ hp₂
    exact ⟨hp₁, hp₂⟩
  have hu : ∀ᵐ p ∂ν.prod ν, 0 < u p := by
    filter_upwards [hpair] with p hp
    exact mul_pos hp.1 hp.2
  have hu' : ∀ᵐ p ∂ν.prod ν, 0 < u p + (B - 1) := by
    filter_upwards [hu] with p hp
    exact add_pos hp hc
  have hui : Integrable u (ν.prod ν) := hi.mul_prod hi
  have hs : Integrable (fun p => productLogKernel B k (u p + (B - 1))) (ν.prod ν) :=
    product_signed_integrable _ (hm.add_const _).aemeasurable hu'
      (hui.add (integrable_const _)) hB _ k
  have ht : Integrable (fun p => productLogKernel B k (u p)) (ν.prod ν) :=
    product_signed_integrable _ hm.aemeasurable hu hui hB _ k
  have hgi (i : ℕ) : Integrable (g i) ν :=
    product_signed_integrable _ measurable_id.aemeasurable hp hi hB _ i
  have hbin :
      (∫ p, productLogKernel B k (u p) ∂ν.prod ν) =
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          (tiltedLogMoment μ B h i n * tiltedLogMoment μ B h (k - i) n) := by
    calc
      _ = ∫ p : ℝ × ℝ, ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * (g i p.1 * g (k - i) p.2) ∂ν.prod ν := by
        apply integral_congr_ae
        filter_upwards [hpair] with p hp
        unfold productLogKernel u
        rw [Real.mul_rpow hp.1.le hp.2.le, Real.log_mul hp.1.ne' hp.2.ne',
          show Real.log p.1 + Real.log p.2 - 2 * Real.log B =
            (Real.log p.1 - Real.log B) + (Real.log p.2 - Real.log B) by ring,
          add_pow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [g]
        ring
      _ = _ := by
        rw [integral_finsetSum _ (fun i _ =>
          ((hgi i).mul_prod (hgi (k - i))).const_mul (k.choose i : ℝ))]
        simp only [integral_const_mul, integral_prod_mul]
        rfl
  have hrec : tiltedLogMoment μ B h k (n + 1) =
      (∫ p, productLogKernel B k (u p + (B - 1)) ∂ν.prod ν) / 2 := by
    unfold tiltedLogMoment
    rw [lawR_succ, integral_map (by fun_prop) (hg k).aestronglyMeasurable,
      ← integral_div]
    apply integral_congr_ae
    filter_upwards [hu'] with p hp
    change g k ((u p + (B - 1)) / B) = _
    dsimp [g, productLogKernel]
    rw [Real.div_rpow hp.le hb.le, product_B_rpow_theta hB,
      Real.log_div hp.ne' hb.ne']
    ring
  have hcorr : productLogCorrection μ B h k n =
      ((∫ p, productLogKernel B k (u p + (B - 1)) ∂ν.prod ν) -
        ∫ p, productLogKernel B k (u p) ∂ν.prod ν) / 2 := by
    unfold productLogCorrection productLaw
    have hdiff : Measurable (fun s => productLogKernel B k (s + (B - 1)) -
        productLogKernel B k s) := (hk.comp (measurable_id.add_const _)).sub hk
    rw [integral_map hm.aemeasurable hdiff.aestronglyMeasurable, integral_sub hs ht]
  rw [hrec, hcorr, hbin]
  ring

private theorem tiltedLogMoment_zero_product (μ : Measure ℝ) (B h : ℝ) (n : ℕ) :
    tiltedLogMoment μ B h 0 n = tiltedMass μ B h n := by
  simp [tiltedLogMoment, tiltedMass]

/-- The four signed moment recurrences of the critical product argument. -/
theorem productLogMoment_recursions {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) :
    let A := tiltedMass μ B h n
    let M := fun k => tiltedLogMoment μ B h k n
    let M' := fun k => tiltedLogMoment μ B h k (n + 1)
    let e := fun k => productLogCorrection μ B h k n
    M' 1 = A * M 1 + e 1 ∧
    M' 2 = A * M 2 + M 1 ^ 2 + e 2 ∧
    M' 3 = A * M 3 + 3 * M 1 * M 2 + e 3 ∧
    M' 4 = A * M 4 + 4 * M 1 * M 3 + 3 * M 2 ^ 2 + e 4 := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [tiltedLogMoment_succ_product hpos hmean hB] <;>
    norm_num [Finset.sum_range_succ, Nat.choose, tiltedLogMoment_zero_product] <;> ring

/-- The finite telescoping identity for the mass defect and its source.
The sum starts at height `n` and has `m` terms. -/
theorem product_defect_telescope {a P D : ℕ → ℝ}
    (hP : ∀ n, 0 < P n) (hprod : ∀ n, P (n + 1) = P n * (1 + a n))
    (ha : ∀ n, a (n + 1) = a n + (a n) ^ 2 / 2 - D n / 2) (n m : ℕ) :
    (∑ j ∈ Finset.range m, P n * D (n + j) / P (n + j + 1)) =
      2 * a n - (∑ j ∈ Finset.range m, P n * a (n + j) ^ 2 / P (n + j + 1)) -
        2 * P n * a (n + m) / P (n + m) := by
  induction m with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, Nat.add_zero]
    field_simp [(hP n).ne']
    ring
  | succ m ih =>
    simp only [Finset.sum_range_succ, ← Nat.add_assoc]
    rw [ih]
    have hstep : P n * D (n + m) / P (n + m + 1) +
          P n * a (n + m) ^ 2 / P (n + m + 1) +
          2 * P n * a (n + m + 1) / P (n + m + 1) =
        2 * P n * a (n + m) / P (n + m) := by
      rw [← add_div, ← add_div, div_eq_iff (hP _).ne', ha, hprod]
      have hm : 2 * P n * a (n + m) / P (n + m) * P (n + m) =
          2 * P n * a (n + m) := div_mul_cancel₀ _ (hP _).ne'
      rw [← mul_assoc, hm]
      ring
    linarith

/-- The square-root argument in the Nash estimate. Here `x` is the square
root of the increasing product, and `T` its accumulated inverse. -/
theorem product_nash_summable {x T : ℕ → ℝ} {c R : ℝ}
    (hx : ∀ n, 0 < x n) (hT : ∀ n, 0 < T n)
    (hc : 0 < c) (hR : 0 < R)
    (hxstep : ∀ n, c / Real.sqrt (T n) ≤ x (n + 1) - x n)
    (hxratio : ∀ n, x (n + 1) ≤ R * x n)
    (hTstep : ∀ n, T (n + 1) = T n + (x n ^ 2)⁻¹) :
    Summable (fun n => (x n ^ 2)⁻¹) ∧ ∃ d > 0, ∀ n : ℕ, d * ((n : ℝ) + 1) ≤ x n := by
  have hdecreasing : Antitone (fun n => (x n)⁻¹ + (c / R) * Real.sqrt (T n)) := by
    apply antitone_nat_of_succ_le
    intro n
    have hs := Real.sqrt_pos_of_pos (hT n)
    have hs' := Real.sqrt_pos_of_pos (hT (n + 1))
    have hsle : Real.sqrt (T n) ≤ Real.sqrt (T (n + 1)) :=
      Real.sqrt_le_sqrt (by rw [hTstep]; exact le_add_of_nonneg_right (by positivity))
    have hdiff : Real.sqrt (T (n + 1)) - Real.sqrt (T n) ≤
        (x n ^ 2)⁻¹ / Real.sqrt (T n) := by
      apply (le_div_iff₀ hs).2
      have heq := congrArg (fun y => y - T n) (hTstep n)
      have hsq := Real.sq_sqrt (hT n).le
      have hsq' := Real.sq_sqrt (hT (n + 1)).le
      have hn := mul_nonneg (sub_nonneg.mpr hsle) hs'.le
      nlinarith only [heq, hsq, hsq', hn]
    have hinv : ((c / R) * ((x n ^ 2)⁻¹ / Real.sqrt (T n))) ≤
        (x n)⁻¹ - (x (n + 1))⁻¹ := by
      calc
        _ = (c / Real.sqrt (T n)) / (x n * (R * x n)) := by
          field_simp [hR.ne', hs.ne', (hx n).ne']
        _ ≤ (c / Real.sqrt (T n)) / (x n * x (n + 1)) :=
          div_le_div_of_nonneg_left (div_nonneg hc.le hs.le) (mul_pos (hx n) (hx (n + 1)))
            (mul_le_mul_of_nonneg_left (hxratio n) (hx n).le)
        _ ≤ (x (n + 1) - x n) / (x n * x (n + 1)) :=
          div_le_div_of_nonneg_right (hxstep n) (mul_nonneg (hx n).le (hx (n + 1)).le)
        _ = _ := by field_simp [(hx n).ne', (hx (n + 1)).ne']
    have hh := (mul_le_mul_of_nonneg_left hdiff (div_nonneg hc.le hR.le)).trans hinv
    linarith
  let U := ((x 0)⁻¹ + (c / R) * Real.sqrt (T 0)) / (c / R)
  have hU : 0 < U := div_pos
    (add_pos_of_pos_of_nonneg (inv_pos.mpr (hx 0))
      (mul_nonneg (div_nonneg hc.le hR.le) (Real.sqrt_nonneg _))) (div_pos hc hR)
  have hbound (n : ℕ) : Real.sqrt (T n) ≤ U := by
    apply (le_div_iff₀ (div_pos hc hR)).2
    have h := hdecreasing (Nat.zero_le n)
    dsimp at h ⊢
    linarith [inv_pos.mpr (hx n)]
  constructor
  · apply summable_of_sum_range_le (c := U ^ 2) (fun n => by positivity)
    intro n
    have heq : (∑ j ∈ Finset.range n, (x j ^ 2)⁻¹) = T n - T 0 := by
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, ih, hTstep]; ring
    rw [heq]
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg (T n)) (hbound n) 2
    rw [Real.sq_sqrt (hT n).le] at hh
    linarith [hT 0]
  · let d := min (x 0) (c / U)
    have hd : 0 < d := lt_min (hx 0) (div_pos hc hU)
    refine ⟨d, hd, ?_⟩
    intro n
    induction n with
    | zero => simpa only [Nat.cast_zero, zero_add, mul_one] using (show d ≤ x 0 from min_le_left _ _)
    | succ n ih =>
      have hdstep := (min_le_right (x 0) (c / U)).trans
        (div_le_div_of_nonneg_left hc.le (Real.sqrt_pos_of_pos (hT n)) (hbound n))
      have hh := hdstep.trans (hxstep n)
      push_cast
      linarith

/-- The law concentrates at one as soon as its tilted mass converges to one.
The almost-sure lower floor removes the lower deviation tail. -/
theorem lawR_concentrates_of_tiltedMass_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    (hmass : Tendsto (tiltedMass μ B h) atTop (𝓝 1)) :
    ∀ ε > 0, Tendsto (fun n : ℕ => lawR μ B h n {x | ε < |x - 1|}) atTop (𝓝 0) := by
  intro ε hε
  have hθ := theta_pos hB
  let d : ℝ := (1 + ε) ^ theta B - 1
  have hd : 0 < d := sub_pos.mpr (by
    simpa only [Real.one_rpow] using
      Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 1 < 1 + ε) hθ)
  let defect (n : ℕ) := (tiltedMass μ B h n - floorSeq B n ^ theta B) / d
  have hfloor := tendsto_floorSeq hB
  have hpow := ((Real.continuous_rpow_const hθ.le).continuousAt (x := (1 : ℝ))).tendsto.comp hfloor
  have hlim : Tendsto defect atTop (𝓝 0) := by
    simpa [defect] using (hmass.sub hpow).div_const d
  have hu : Tendsto (fun n => ENNReal.ofReal (defect n)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hfloor.eventually (Ioi_mem_nhds (show 1 - ε < 1 by linarith))] with n hn
  have hn' : 1 - ε < floorSeq B n := hn
  let ν := lawR μ B h n
  let : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  let f (x : ℝ) := (x ^ theta B - floorSeq B n ^ theta B) / d
  have hi : Integrable (fun x : ℝ => x ^ theta B) ν := by
    simpa using product_signed_integrable ν measurable_id.aemeasurable (ae_pos_lawR hpos hB h n)
      (integrable_lawR_of hpos hmean hB h n) hB 0 0
  have hf : Integrable f ν := (hi.sub (integrable_const _)).div_const _
  have hnonneg : 0 ≤ᵐ[ν] f := by
    filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx
    exact div_nonneg (sub_nonneg.mpr
      (Real.rpow_le_rpow (floorSeq_nonneg hB n) hx hθ.le)) hd.le
  have htail : ν {x | 1 + ε < x} ≤ ENNReal.ofReal (defect n) := by
    have hle := hf.measure_le_integral hnonneg (s := {x | 1 + ε < x}) (fun x hx => by
      have hx' : 1 + ε < x := hx
      have h1 := Real.rpow_le_one (floorSeq_nonneg hB n) (floorSeq_le_one hB n) hθ.le
      have h2 := Real.rpow_le_rpow (show 0 ≤ 1 + ε by positivity) hx'.le hθ.le
      apply (le_div_iff₀ hd).2
      dsimp [d]
      linarith)
    have heq : (∫ x, f x ∂ν) = defect n := by
      simp [f, defect, integral_div, integral_sub hi (integrable_const _), tiltedMass, ν]
    rwa [heq] at hle
  change ν {x | ε < |x - 1|} ≤ _
  apply le_trans ?_ htail
  apply measure_mono_ae
  filter_upwards [ae_floorSeq_le_lawR hpos hB h n] with x hx hdev
  have hdev' : ε < |x - 1| := hdev
  change 1 + ε < x
  rcases lt_abs.mp hdev' with hneg | hpos'
  · linarith
  · linarith

/-- The cubic residue cannot vanish when the defect returns arbitrarily close
to zero. The Nash bound absorbs the constant source in the backward estimate,
so the exponent-halving step uses a single constant for all exponents. -/
theorem product_cubic_residue_ne_zero {P z K J : ℕ → ℝ} {ρ δ C : ℝ}
    (hP : ∀ n, 1 ≤ P n) (hz : ∀ n, 0 ≤ z n) (hK : ∀ n, 0 ≤ K n)
    (hstep : ∀ n, P (n + 1) = P n * (1 + z n))
    (hρ : 0 ≤ ρ) (hρ' : ρ < 1) (hδ : 0 < δ) (hC : 1 ≤ C)
    (hNash : ∀ n, δ ≤ z n * (K n + 1))
    (hCS : ∀ n, K n ^ 2 ≤ C * (J n + C))
    (hJ : ∀ n, J n / P n - J (n + 1) / P (n + 1) ≤
      C * ((z n + ρ ^ n) * K n + 1) / P (n + 1))
    (hinit : ∃ M : ℝ, ∀ n, K n ≤ M * Real.sqrt (P n))
    (hreturn : ∀ ε > 0, ∃ᶠ n in atTop, z n < ε) :
    ¬ Tendsto (fun n => J n / P n) atTop (𝓝 0) := by
  intro hlim
  have hPpos (n : ℕ) : 0 < P n := zero_lt_one.trans_le (hP n)
  have hPmono (n : ℕ) : P n ≤ P (n + 1) := by
    rw [hstep]
    nlinarith [mul_nonneg (hPpos n).le (hz n)]
  let D := C * (1 + 2 / δ)
  let E := 2 + (1 - ρ)⁻¹
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have halve (M γ : ℝ) (hM : 1 ≤ M) (hγ : 0 ≤ γ) (hγ' : γ ≤ 1 / 2)
      (hMK : ∀ n, K n ≤ M * P n ^ γ) :
      ∀ n, J n ≤ D * E * M * P n ^ γ := by
    let F (n : ℕ) := P n ^ (γ - 1)
    have hF (n : ℕ) : 0 < F n := Real.rpow_pos_of_pos (hPpos n) _
    have hFmono (n : ℕ) : F (n + 1) ≤ F n :=
      Real.rpow_le_rpow_of_nonpos (hPpos n) (hPmono n) (by linarith)
    have htel (n : ℕ) : z n * P n ^ γ / P (n + 1) ≤ 2 * (F n - F (n + 1)) := by
      let r := P n / P (n + 1)
      have hr0 : 0 < r := div_pos (hPpos _) (hPpos _)
      have hr1 : r ≤ 1 := (div_le_one (hPpos _)).2 (hPmono n)
      have hratio : F (n + 1) = F n * r ^ (1 - γ) := by
        dsimp [F, r]
        rw [Real.div_rpow (hPpos _).le (hPpos _).le,
          show γ - 1 = -(1 - γ) by ring, Real.rpow_neg (hPpos _).le,
          Real.rpow_neg (hPpos _).le]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos (hPpos n) (1 - γ))]
      have hsq := Real.sq_sqrt hr0.le
      have hroot : r ^ (1 - γ) ≤ Real.sqrt r := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
      have h := mul_le_mul_of_nonneg_left
        (show 1 - r ≤ 2 * (1 - r ^ (1 - γ)) by
          nlinarith only [hroot, hsq, sq_nonneg (Real.sqrt r - 1)]) (hF n).le
      have heq : F n * (1 - r) = z n * P n ^ γ / P (n + 1) := by
        dsimp [F, r]
        rw [Real.rpow_sub (hPpos n), Real.rpow_one]
        field_simp [(hPpos n).ne', (hPpos (n + 1)).ne']
        rw [hstep]
        ring
      rw [heq] at h
      rw [hratio]
      linarith
    have hgeo (n : ℕ) : ρ ^ n * P n ^ γ / P (n + 1) ≤
        (ρ ^ n * F n - ρ ^ (n + 1) * F (n + 1)) / (1 - ρ) := by
      calc
        _ ≤ ρ ^ n * F n := by
          dsimp [F]
          rw [Real.rpow_sub (hPpos n), Real.rpow_one, ← mul_div_assoc]
          exact div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg hρ n) (Real.rpow_nonneg (hPpos n).le γ)) (hPpos n) (hPmono n)
        _ ≤ _ := by
          apply (le_div_iff₀ (sub_pos.mpr hρ')).2
          rw [pow_succ]
          nlinarith only [mul_nonneg (pow_nonneg hρ n) (mul_nonneg hρ
            (sub_nonneg.mpr (hFmono n)))]
    have hanti : Antitone (fun n => D * M *
        (2 * F n + ρ ^ n * F n / (1 - ρ)) - J n / P n) := by
      apply antitone_nat_of_succ_le
      intro n
      have hpow : 1 ≤ P n ^ γ := Real.one_le_rpow (hP n) hγ
      have hN := hNash n
      have hK' := hMK n
      have hconst : 1 ≤ 2 / δ * (z n * (M * P n ^ γ)) := by
        have hh : δ ≤ 2 * (z n * (M * P n ^ γ)) := by
          calc
            δ ≤ z n * (K n + 1) := hN
            _ ≤ z n * (2 * (M * P n ^ γ)) := by
              apply mul_le_mul_of_nonneg_left _ (hz n)
              linarith only [hK', one_le_mul_of_one_le_of_one_le hM hpow]
            _ = _ := by ring
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
        simpa using hh
      have hsource : C * ((z n + ρ ^ n) * K n + 1) / P (n + 1) ≤
          D * M * (z n * P n ^ γ / P (n + 1) + ρ ^ n * P n ^ γ / P (n + 1)) := by
        have h1 := mul_le_mul_of_nonneg_left hK' (add_nonneg (hz n) (pow_nonneg hρ n))
        have h2 := mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ.le)
          (mul_nonneg (pow_nonneg hρ n) (mul_nonneg (zero_le_one.trans hM)
            (zero_le_one.trans hpow)))
        dsimp [D]
        rw [← add_div, ← mul_div_assoc]
        apply div_le_div_of_nonneg_right _ (hPpos _).le
        simp only [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
        linarith only [h1, h2, hconst]
      have hh := (hJ n).trans (hsource.trans (mul_le_mul_of_nonneg_left
        (add_le_add (htel n) (hgeo n)) (mul_nonneg hD (zero_le_one.trans hM))))
      rw [sub_div] at hh
      linarith
    intro n
    have hle : J n / P n ≤ D * M * (2 * F n + ρ ^ n * F n / (1 - ρ)) := by
      have hev : ∀ᶠ j in atTop,
          J n / P n - D * M * (2 * F n + ρ ^ n * F n / (1 - ρ)) ≤ J j / P j := by
        filter_upwards [eventually_ge_atTop n] with j hj
        have hh := hanti hj
        dsimp at hh
        have hterm : 0 ≤ D * M * (2 * F j + ρ ^ j * F j / (1 - ρ)) := by
          have hjF := (hF j).le
          have hρ1 := sub_nonneg.mpr hρ'.le
          have hMp : 0 ≤ M := zero_le_one.trans hM
          positivity
        linarith
      have hh := ge_of_tendsto hlim hev
      linarith
    have hρpow : ρ ^ n ≤ 1 := pow_le_one₀ hρ hρ'.le
    have hh : 2 * F n + ρ ^ n * F n / (1 - ρ) ≤ E * F n := by
      dsimp [E]
      have h := mul_le_mul_of_nonneg_right hρpow (hF n).le
      have h' := div_le_div_of_nonneg_right h (sub_nonneg.mpr hρ'.le)
      rw [one_mul] at h'
      rw [add_mul, inv_mul_eq_div]
      linarith
    have hupper := (div_le_iff₀ (hPpos n)).mp (hle.trans
      (mul_le_mul_of_nonneg_left hh (mul_nonneg hD (zero_le_one.trans hM))))
    dsimp [F] at hupper
    rw [Real.rpow_sub (hPpos n), Real.rpow_one] at hupper
    simp only [mul_assoc, div_mul_cancel₀ _ (hPpos n).ne'] at hupper
    nlinarith only [hupper]
  obtain ⟨M₀, hM₀⟩ := hinit
  let M := max 1 (max M₀ (C * (D * E + C)))
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : M₀ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hMC : C * (D * E + C) ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hboot (γ : ℝ) (hγ : 0 ≤ γ) (hγ' : γ ≤ 1 / 2)
      (hMK : ∀ n, K n ≤ M * P n ^ γ) (n : ℕ) :
      K n ≤ M * P n ^ (γ / 2) := by
    have hh := halve M γ hM hγ hγ' hMK n
    have hp := Real.one_le_rpow (hP n) hγ
    have hCp : C ≤ C * (M * P n ^ γ) := by
      apply le_mul_of_one_le_right (zero_le_one.trans hC)
      exact one_le_mul_of_one_le_of_one_le hM hp
    have hh' := (hCS n).trans (mul_le_mul_of_nonneg_left
      (add_le_add hh hCp) (zero_le_one.trans hC))
    have hcoef := mul_le_mul_of_nonneg_right hMC (mul_nonneg
      (zero_le_one.trans hM) (zero_le_one.trans hp))
    have hx : (M * P n ^ (γ / 2)) ^ 2 = M ^ 2 * P n ^ γ := by
      rw [mul_pow, ← Real.rpow_natCast (P n ^ (γ / 2)) 2, ← Real.rpow_mul (hPpos n).le]
      norm_num
    apply (sq_le_sq₀ (hK n) (mul_nonneg (zero_le_one.trans hM) (Real.rpow_nonneg (hPpos n).le _))).mp
    rw [hx]
    nlinarith only [hh', hcoef]
  let γ (i : ℕ) := (1 / 2 : ℝ) ^ (i + 1)
  have hγstep (i : ℕ) : γ (i + 1) = γ i / 2 := by
    dsimp [γ]
    rw [pow_succ]
    ring
  have hbound (i : ℕ) : ∀ n, K n ≤ M * P n ^ γ i := by
    induction i with
    | zero =>
      intro n
      have hh := (hM₀ n).trans (mul_le_mul_of_nonneg_right hM0 (Real.sqrt_nonneg _))
      simpa only [γ, Nat.zero_add, pow_one, ← Real.sqrt_eq_rpow] using hh
    | succ i ih =>
      rw [hγstep]
      apply hboot _ (by dsimp [γ]; positivity) _ ih
      dsimp [γ]
      rw [pow_succ]
      have hh := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 : ℝ) / 2 ≤ 1) (n := i)
      linarith
  have hbounded (n : ℕ) : K n ≤ M := by
    have hg : Tendsto γ atTop (𝓝 0) := by
      simpa only [γ, pow_succ, zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)).mul_const (1 / 2)
    have hr := (Real.continuousAt_const_rpow (a := P n) (b := 0) (hPpos n).ne').tendsto.comp hg
    have hr' : Tendsto (fun i => M * P n ^ γ i) atTop (𝓝 M) := by
      simpa using hr.const_mul M
    exact ge_of_tendsto' hr' (fun i => hbound i n)
  have heps : 0 < δ / (M + 1) := div_pos hδ (by linarith)
  obtain ⟨n, hn⟩ := (hreturn _ heps).exists
  have hcontra : δ ≤ z n * (M + 1) := (hNash n).trans
    (mul_le_mul_of_nonneg_left (add_le_add_left (hbounded n) 1) (hz n))
  have hn' := (lt_div_iff₀ (show 0 < M + 1 by linarith)).mp hn
  exact (not_lt_of_ge hcontra) hn'

private theorem product_integral_cauchy_schwarz {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [SFinite ν] {w f : Ω → ℝ}
    (hw : 0 ≤ᵐ[ν] w) (h₀ : Integrable w ν)
    (h₁ : Integrable (fun x => w x * f x) ν)
    (h₂ : Integrable (fun x => w x * f x ^ 2) ν) :
    (∫ x, w x * f x ∂ν) ^ 2 ≤ (∫ x, w x ∂ν) * (∫ x, w x * f x ^ 2 ∂ν) := by
  let w₁ (x : Ω) := w x * f x
  let w₂ (x : Ω) := w x * f x ^ 2
  have hprod₁ : Integrable (fun p : Ω × Ω => w₂ p.1 * w p.2) (ν.prod ν) :=
    h₂.mul_prod h₀
  have hprod₂ : Integrable (fun p : Ω × Ω => w p.1 * w₂ p.2) (ν.prod ν) :=
    h₀.mul_prod h₂
  have hprod₃ : Integrable (fun p : Ω × Ω => 2 * (w₁ p.1 * w₁ p.2)) (ν.prod ν) :=
    (h₁.mul_prod h₁).const_mul 2
  have hnonneg : 0 ≤ (∫ p : Ω × Ω, w₂ p.1 * w p.2 + w p.1 * w₂ p.2 -
      2 * (w₁ p.1 * w₁ p.2) ∂ν.prod ν) := by
    apply integral_nonneg_of_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hw,
      Measure.quasiMeasurePreserving_snd.ae hw] with p hpx hpy
    calc
      0 ≤ (w p.1 * w p.2) * (f p.1 - f p.2) ^ 2 :=
        mul_nonneg (mul_nonneg hpx hpy) (sq_nonneg _)
      _ = _ := by dsimp [w₁, w₂]; ring
  have hprod₁₂ : Integrable (fun p : Ω × Ω => w₂ p.1 * w p.2 + w p.1 * w₂ p.2)
      (ν.prod ν) := hprod₁.add hprod₂
  rw [integral_sub hprod₁₂ hprod₃, integral_add hprod₁ hprod₂,
    integral_const_mul, integral_prod_mul, integral_prod_mul, integral_prod_mul] at hnonneg
  dsimp [w₁, w₂] at hnonneg
  nlinarith only [hnonneg]

/-- The fourth and second moments control the square of the cubic moment. -/
theorem product_third_sq_le_second_mul_fourth {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) :
    tiltedLogMoment μ B h 3 n ^ 2 ≤
      tiltedLogMoment μ B h 2 n * tiltedLogMoment μ B h 4 n := by
  let ν := lawR μ B h n
  let : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  let Z (x : ℝ) := Real.log x - Real.log B
  let w (x : ℝ) := x ^ theta B * Z x ^ 2
  have hp := ae_pos_lawR hpos hB h n
  have hi (k : ℕ) : Integrable (fun x => x ^ theta B * Z x ^ k) ν :=
    product_signed_integrable _ measurable_id.aemeasurable hp
      (integrable_lawR_of hpos hmean hB h n) hB _ k
  have hw : 0 ≤ᵐ[ν] w := by
    filter_upwards [hp] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le _) (sq_nonneg _)
  have h₃ : (fun x => w x * Z x) = (fun x => x ^ theta B * Z x ^ 3) := by
    funext x
    dsimp [w]
    ring
  have h₄ : (fun x => w x * Z x ^ 2) = (fun x => x ^ theta B * Z x ^ 4) := by
    funext x
    dsimp [w]
    ring
  have hCS := product_integral_cauchy_schwarz hw (hi 2) (h₃ ▸ hi 3) (h₄ ▸ hi 4)
  rw [h₃, h₄] at hCS
  exact hCS

/-- Bounded positive increments with a summable majorant give convergence
when the sequence has a uniform lower bound. -/
theorem product_tendsto_of_summable_upper_increments {j s : ℕ → ℝ} {m : ℝ}
    (hlo : ∀ n, m ≤ j n) (hs : ∀ n, 0 ≤ s n) (hsum : Summable s)
    (hstep : ∀ n, j (n + 1) - j n ≤ s n) :
    ∃ l : ℝ, Tendsto j atTop (𝓝 l) := by
  let v (n : ℕ) := j n - ∑ i ∈ Finset.range n, s i
  have hva : Antitone v := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [v]
    rw [Finset.sum_range_succ]
    linarith only [hstep n]
  have hvb : BddBelow (Set.range v) := by
    refine ⟨m - ∑' n, s n, ?_⟩
    rintro _ ⟨n, rfl⟩
    apply sub_le_sub (hlo n)
    exact hsum.sum_le_tsum _ (fun i _ => hs i)
  have ht := (tendsto_atTop_ciInf hva hvb).add (hsum.hasSum.tendsto_sum_nat)
  refine ⟨_, ht.congr (fun n => ?_)⟩
  dsimp [v]
  ring

/-- From the Nash inequality and the first two normalized moment recurrences,
the increasing product has summable inverse and at least quadratic growth. -/
theorem product_preliminary_bounds {P z K J : ℕ → ℝ} {ρ δ C : ℝ}
    (hP : ∀ n, 1 ≤ P n) (hz : ∀ n, 0 ≤ z n) (hzmax : ∀ n, z n ≤ C)
    (hstep : ∀ n, P (n + 1) = P n * (1 + z n))
    (hρ : 0 ≤ ρ) (hρ' : ρ < 1) (hδ : 0 < δ) (hC : 1 ≤ C)
    (hK : ∀ n, 0 ≤ K n) (hNash : ∀ n, δ ≤ z n * (K n + 1))
    (hCS : ∀ n, K n ^ 2 ≤ C * (J n + C))
    (hKstep : ∀ n, K (n + 1) / P (n + 1) - K n / P n ≤ C / P (n + 1))
    (hJstep : ∀ n, J (n + 1) / P (n + 1) - J n / P n ≤
      C * ρ ^ n * K n / P (n + 1) + C / P (n + 1)) :
    Summable (fun n => (P n)⁻¹) ∧
      (∃ d > 0, ∀ n : ℕ, d * ((n : ℝ) + 1) ^ 2 ≤ P n) ∧
      (∃ D > 0, ∀ n, K n ^ 2 ≤ D * P n ∧ J n ≤ D * P n) := by
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hp (n : ℕ) : 0 < P n := zero_lt_one.trans_le (hP n)
  have hmono (n : ℕ) : P n ≤ P (n + 1) := by
    rw [hstep, mul_add, mul_one]
    exact le_add_of_nonneg_right (mul_nonneg (hp n).le (hz n))
  let T (n : ℕ) : ℝ := 1 + ∑ i ∈ Finset.range n, (P i)⁻¹
  have hT (n : ℕ) : 1 ≤ T n := le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => inv_nonneg.mpr (hp i).le)
  have hTp (n : ℕ) : 0 < T n := zero_lt_one.trans_le (hT n)
  have hTstep (n : ℕ) : T (n + 1) = T n + (P n)⁻¹ := by
    simp [T, Finset.sum_range_succ, add_assoc]
  have hTupper (n : ℕ) : T n ≤ (n : ℝ) + 1 := by
    dsimp [T]
    have hh : (∑ i ∈ Finset.range n, (P i)⁻¹) ≤ (n : ℝ) := by
      calc
        _ ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
          inv_le_one_of_one_le₀ (hP i)
        _ = _ := by simp
    linarith
  let D := C + |K 0 / P 0| + |J 0 / P 0|
  have hD : 0 < D := by dsimp [D]; positivity
  have hCD : C ≤ D := by dsimp [D]; linarith [abs_nonneg (K 0 / P 0), abs_nonneg (J 0 / P 0)]
  have hKbound (n : ℕ) : K n / P n ≤ D * T n := by
    induction n with
    | zero =>
      simp only [T, Finset.range_zero, Finset.sum_empty, add_zero, mul_one]
      dsimp [D]
      linarith [le_abs_self (K 0 / P 0), abs_nonneg (J 0 / P 0)]
    | succ n ih =>
      have hi := hKstep n
      have hb : C / P (n + 1) ≤ D * (P n)⁻¹ := by
        rw [← div_eq_mul_inv]
        exact (div_le_div_of_nonneg_right hCD (hp (n + 1)).le).trans
          (div_le_div_of_nonneg_left hD.le (hp n) (hmono n))
      rw [hTstep]
      linarith only [ih, hi, hb]
  let g (n : ℕ) : ℝ := C * D * (n + 1) * ρ ^ n
  have hg (n : ℕ) : 0 ≤ g n := by dsimp [g]; positivity
  have hgSum : Summable g := by
    have hnorm : ‖ρ‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hρ]
    have ha := summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
    have hb := summable_geometric_of_norm_lt_one hnorm
    convert (ha.add hb).mul_left (C * D) using 1
    ext n
    simp only [g, pow_one]
    ring
  have hJbound (n : ℕ) : J n / P n ≤ D * T n + ∑ i ∈ Finset.range n, g i := by
    induction n with
    | zero =>
      simp only [T, Finset.range_zero, Finset.sum_empty, add_zero, mul_one]
      dsimp [D]
      linarith [le_abs_self (J 0 / P 0), abs_nonneg (K 0 / P 0)]
    | succ n ih =>
      have hb : C / P (n + 1) ≤ D * (P n)⁻¹ := by
        rw [← div_eq_mul_inv]
        exact (div_le_div_of_nonneg_right hCD (hp (n + 1)).le).trans
          (div_le_div_of_nonneg_left hD.le (hp n) (hmono n))
      have hk : K n / P (n + 1) ≤ D * ((n : ℝ) + 1) :=
        (div_le_div_of_nonneg_left (hK n) (hp n) (hmono n)).trans
          ((hKbound n).trans (mul_le_mul_of_nonneg_left (hTupper n) hD.le))
      have hgeo : C * ρ ^ n * K n / P (n + 1) ≤ g n := by
        rw [mul_div_assoc]
        dsimp [g]
        have hh := mul_le_mul_of_nonneg_left hk (mul_nonneg hCp.le (pow_nonneg hρ n))
        convert hh using 1
        ring
      rw [hTstep, Finset.sum_range_succ]
      linarith only [ih, hJstep n, hb, hgeo]
  let G := ∑' n, g n
  have hG : 0 ≤ G := tsum_nonneg hg
  have hJtotal (n : ℕ) : J n / P n ≤ (D + G) * T n := by
    have hs := hgSum.sum_le_tsum (Finset.range n) (fun i _ => hg i)
    have hgt := le_mul_of_one_le_right hG (hT n)
    linarith only [hJbound n, hs, hgt]
  let M := Real.sqrt (C * (D + G + C))
  have hM : 0 < M := Real.sqrt_pos_of_pos (by positivity)
  let x (n : ℕ) := Real.sqrt (P n)
  have hx (n : ℕ) : 0 < x n := Real.sqrt_pos_of_pos (hp n)
  have hxsq (n : ℕ) : x n ^ 2 = P n := Real.sq_sqrt (hp n).le
  have hx1 (n : ℕ) : 1 ≤ x n := by
    simpa [x] using Real.sqrt_le_sqrt (hP n)
  have hts (n : ℕ) : 1 ≤ Real.sqrt (T n) := by simpa using Real.sqrt_le_sqrt (hT n)
  have hKsqrt (n : ℕ) : K n ≤ M * x n * Real.sqrt (T n) := by
    apply (sq_le_sq₀ (hK n) (mul_nonneg (mul_nonneg hM.le (hx n).le) (Real.sqrt_nonneg _))).mp
    rw [mul_pow, mul_pow, hxsq, Real.sq_sqrt (hTp n).le, show M ^ 2 =
      C * (D + G + C) from Real.sq_sqrt (by positivity)]
    have hJ := (div_le_iff₀ (hp n)).mp (hJtotal n)
    have hPT : 1 ≤ T n * P n := one_le_mul_of_one_le_of_one_le (hT n) (hP n)
    have hCPT := le_mul_of_one_le_right hCp.le hPT
    have hbound : J n + C ≤ (D + G + C) * P n * T n := by
      linarith only [hJ, hCPT]
    have hh := mul_le_mul_of_nonneg_left hbound hCp.le
    linarith only [hh, hCS n]
  let R := Real.sqrt (1 + C)
  have hR : 0 < R := Real.sqrt_pos_of_pos (by positivity)
  have hxratio (n : ℕ) : x (n + 1) ≤ R * x n := by
    dsimp [x, R]
    rw [← Real.sqrt_mul (show 0 ≤ 1 + C by positivity)]
    apply Real.sqrt_le_sqrt
    rw [hstep]
    have hh := mul_le_mul_of_nonneg_left (add_le_add_left (hzmax n) 1) (hp n).le
    linarith only [hh]
  let c := δ / ((M + 1) * (R + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hxstep (n : ℕ) : c / Real.sqrt (T n) ≤ x (n + 1) - x n := by
    have h1 := one_le_mul_of_one_le_of_one_le (hx1 n) (hts n)
    have hnash : δ ≤ z n * ((M + 1) * x n * Real.sqrt (T n)) :=
      (hNash n).trans (mul_le_mul_of_nonneg_left (by linarith only [hKsqrt n, h1]) (hz n))
    have hdiff : x (n + 1) - x n = z n * P n / (x (n + 1) + x n) := by
      apply (eq_div_iff (add_pos (hx (n + 1)) (hx n)).ne').2
      calc
        _ = x (n + 1) ^ 2 - x n ^ 2 := by ring
        _ = _ := by rw [hxsq, hxsq, hstep]; ring
    rw [hdiff]
    calc
      _ ≤ z n * x n / (R + 1) := by
        dsimp [c]
        apply (le_div_iff₀ (by positivity : 0 < R + 1)).2
        have hs : 0 < Real.sqrt (T n) := Real.sqrt_pos_of_pos (hTp n)
        field_simp [hs.ne', show M + 1 ≠ 0 by positivity, show R + 1 ≠ 0 by positivity]
        nlinarith only [hnash]
      _ = z n * P n / ((R + 1) * x n) := by
        rw [← hxsq]
        field_simp [(hx n).ne', show R + 1 ≠ 0 by positivity]
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (hz n) (hp n).le)
        (add_pos (hx (n + 1)) (hx n)) (by nlinarith only [hxratio n])
  have hTstep' (n : ℕ) : T (n + 1) = T n + (x n ^ 2)⁻¹ := by rw [hxsq, hTstep]
  obtain ⟨hsum, d, hd, hdx⟩ := product_nash_summable hx hTp hc hR hxstep hxratio hTstep'
  simp only [hxsq] at hsum
  refine ⟨hsum, ⟨d ^ 2, by positivity, fun n => ?_⟩, ?_⟩
  · have hh := pow_le_pow_left₀ (show 0 ≤ d * ((n : ℝ) + 1) by positivity) (hdx n) 2
    simpa only [mul_pow, hxsq] using hh
  · let U := 1 + ∑' n, (P n)⁻¹
    have hU : 0 < U := add_pos_of_pos_of_nonneg one_pos
      (tsum_nonneg fun n => inv_nonneg.mpr (hp n).le)
    have hTU (n : ℕ) : T n ≤ U :=
      add_le_add_right (hsum.sum_le_tsum _ (fun i _ => inv_nonneg.mpr (hp i).le)) 1
    let E := (M ^ 2 + D + G) * U
    have hE : 0 < E := by dsimp [E]; positivity
    refine ⟨E, hE, fun n => ⟨?_, ?_⟩⟩
    · have hh := pow_le_pow_left₀ (hK n) (hKsqrt n) 2
      rw [mul_pow, mul_pow, hxsq, Real.sq_sqrt (hTp n).le] at hh
      refine hh.trans ?_
      dsimp [E]
      have h := mul_le_mul_of_nonneg_left (hTU n) (mul_nonneg (sq_nonneg M) (hp n).le)
      have h' := mul_nonneg (add_nonneg hD.le hG) (mul_nonneg hU.le (hp n).le)
      linarith only [h, h']
    · have hh := (div_le_iff₀ (hp n)).mp (hJtotal n)
      dsimp [E]
      have h := mul_le_mul_of_nonneg_left (hTU n) (mul_nonneg (add_nonneg hD.le hG) (hp n).le)
      have h' := mul_nonneg (sq_nonneg M) (mul_nonneg hU.le (hp n).le)
      linarith only [hh, h, h']

/-- The positive cubic residue and the fourth-moment recurrence give the
upper bounds on the product and the fourth moment. -/
theorem product_upper_of_cubic_limit {P K J L : ℕ → ℝ} {ρ C D ell : ℝ}
    (hP : ∀ n, 1 ≤ P n) (hmono : Monotone P) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1)
    (hC : 0 < C) (hD : 0 < D)
    (hK : ∀ n, 0 ≤ K n) (hL : ∀ n, 0 ≤ L n) (hJlow : ∀ n, -C ≤ J n)
    (hbound : ∀ n, K n ^ 2 ≤ D * P n ∧ J n ≤ D * P n)
    (hCS : ∀ n, J n ^ 2 ≤ K n * L n)
    (hLstep : ∀ n, L (n + 1) / P (n + 1) - L n / P n ≤
      C * (ρ ^ n * |J n| + K n ^ 2 + 1) / P (n + 1))
    (hell : 0 < ell) (hlim : Tendsto (fun n => J n / P n) atTop (𝓝 ell)) :
    ∃ E > 0, ∀ᶠ n : ℕ in atTop,
      P n ≤ E * ((n : ℝ) + 1) ^ 2 ∧ L n ≤ E * ((n : ℝ) + 1) ^ 3 := by
  have hp (n : ℕ) : 0 < P n := zero_lt_one.trans_le (hP n)
  let e := L 0 / P 0 + C * (max C D + D + 1)
  have he : 0 < e :=
    add_pos_of_nonneg_of_pos (div_nonneg (hL 0) (hp 0).le)
      (mul_pos hC (by have := le_max_right C D; linarith))
  have hLnorm (n : ℕ) : L n / P n ≤ e * ((n : ℝ) + 1) := by
    induction n with
    | zero =>
      simp only [Nat.cast_zero, zero_add, mul_one]
      apply le_add_of_nonneg_right
      apply mul_nonneg hC.le
      have := le_max_right C D
      linarith
    | succ n ih =>
      have hJabs : |J n| ≤ max C D * P n := by
        apply abs_le.mpr
        constructor
        · have hl := le_mul_of_one_le_right (le_trans hC.le (le_max_left C D)) (hP n)
          linarith only [hl, le_max_left C D, hJlow n]
        · exact (hbound n).2.trans (mul_le_mul_of_nonneg_right (le_max_right C D) (hp n).le)
      have hsrc : ρ ^ n * |J n| + K n ^ 2 + 1 ≤ (max C D + D + 1) * P n := by
        have hh := mul_le_of_le_one_left (abs_nonneg (J n)) (pow_le_one₀ hρ hρ' (n := n))
        nlinarith only [hh, hJabs, (hbound n).1, hP n]
      have hs : C * (ρ ^ n * |J n| + K n ^ 2 + 1) / P (n + 1) ≤
          C * (max C D + D + 1) := by
        apply (div_le_iff₀ (hp _)).2
        have hq := mul_le_mul_of_nonneg_left (hmono (Nat.le_succ n))
          (mul_nonneg hC.le (show 0 ≤ max C D + D + 1 by have := le_max_right C D; linarith))
        have hh := mul_le_mul_of_nonneg_left hsrc hC.le
        linarith only [hq, hh]
      have hle := (hLstep n).trans hs
      have hep : C * (max C D + D + 1) ≤ e :=
        le_add_of_nonneg_left (div_nonneg (hL 0) (hp 0).le)
      push_cast
      linarith only [hle, ih, hep]
  let u := D * e ^ 2 / (ell / 2) ^ 4
  have hu : 0 < u := by dsimp [u]; positivity
  let E := max u (e * u)
  refine ⟨E, hu.trans_le (le_max_left _ _), ?_⟩
  have hJevent := hlim.eventually (Ioi_mem_nhds (show ell / 2 < ell by linarith))
  filter_upwards [hJevent] with n hn
  have hJ : ell / 2 * P n ≤ J n := (le_div_iff₀ (hp n)).mp (le_of_lt hn)
  have hJ2 := pow_le_pow_left₀ (show 0 ≤ ell / 2 * P n from
    mul_nonneg (by positivity) (hp n).le) hJ 2
  have hL' := (div_le_iff₀ (hp n)).mp (hLnorm n)
  have hKL : (ell / 2) ^ 2 * P n ≤ e * ((n : ℝ) + 1) * K n := by
    apply le_of_mul_le_mul_right _ (hp n)
    have hh := hJ2.trans ((hCS n).trans (mul_le_mul_of_nonneg_left hL' (hK n)))
    nlinarith only [hh]
  have hs := pow_le_pow_left₀ (show 0 ≤ (ell / 2) ^ 2 * P n from
    mul_nonneg (sq_nonneg _) (hp n).le) hKL 2
  have hsq := mul_le_mul_of_nonneg_left (hbound n).1
    (sq_nonneg (e * ((n : ℝ) + 1)))
  have hsq' : (ell / 2) ^ 4 * P n ≤ D * e ^ 2 * ((n : ℝ) + 1) ^ 2 := by
    apply le_of_mul_le_mul_right _ (hp n)
    nlinarith only [hs, hsq]
  have hU : P n ≤ u * ((n : ℝ) + 1) ^ 2 := by
    dsimp [u]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (show 0 < (ell / 2) ^ 4 by positivity)).2
    nlinarith only [hsq']
  constructor
  · exact hU.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  · have hh := mul_le_mul_of_nonneg_left hU
      (mul_nonneg he.le (by positivity : 0 ≤ (n : ℝ) + 1))
    have hh' := mul_le_mul_of_nonneg_right (le_max_right u (e * u))
      (pow_nonneg (by positivity : 0 ≤ (n : ℝ) + 1) 3)
    nlinarith only [hL', hh, hh']

/-- The defect at height `n` is bounded by the growth of the product over
the last half of the generations. -/
theorem product_defect_upper_of_quadratic {P z : ℕ → ℝ} {d D : ℝ}
    (hP : ∀ n, 0 < P n) (hmono : Monotone P) (hz : ∀ n, 0 ≤ z n)
    (hstep : ∀ n, P (n + 1) = P n * (1 + z n))
    (hzstep : ∀ n, z (n + 1) ≤ z n * (1 + z n))
    (hd : 0 < d) (hD : 0 < D)
    (hlower : ∀ n : ℕ, d * ((n : ℝ) + 1) ^ 2 ≤ P n)
    (hupper : ∀ᶠ n : ℕ in atTop, P n ≤ D * ((n : ℝ) + 1) ^ 2) :
    ∃ E > 0, ∀ᶠ n : ℕ in atTop, z n ≤ E * (n : ℝ)⁻¹ := by
  have hanti : Antitone (fun n => z n / P n) := by
    apply antitone_nat_of_succ_le
    intro n
    apply (div_le_iff₀ (hP (n + 1))).2
    rw [hstep, ← mul_assoc, div_mul_cancel₀ _ (hP n).ne']
    exact hzstep n
  let R := 4 * D / d
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨2 * R ^ 2, by positivity, ?_⟩
  filter_upwards [hupper, eventually_ge_atTop 1] with n hn hn1
  let m := n / 2
  have hmn : m ≤ n := Nat.div_le_self _ _
  have hhalf : (n : ℝ) + 1 ≤ 2 * ((m : ℝ) + 1) := by
    have hh : n + 1 ≤ 2 * (m + 1) := by dsimp [m]; omega
    exact_mod_cast hh
  have hhalf' : (n : ℝ) ≤ 2 * ((n - m : ℕ) : ℝ) := by
    have hh : n ≤ 2 * (n - m) := by dsimp [m]; omega
    exact_mod_cast hh
  have hRatio : P n ≤ R * P m := by
    have hsq := pow_le_pow_left₀ (show 0 ≤ (n : ℝ) + 1 by positivity) hhalf 2
    have hh := mul_le_mul_of_nonneg_left hsq hD.le
    have hh' := mul_le_mul_of_nonneg_left (hlower m) hR.le
    have hRd : R * d = 4 * D := div_mul_cancel₀ _ hd.ne'
    nlinarith only [hn, hh, hh', congrArg (fun x : ℝ => x * ((m : ℝ) + 1) ^ 2) hRd]
  let c := z n / P n * P m ^ 2
  have hc : 0 ≤ c := mul_nonneg (div_nonneg (hz n) (hP n).le) (sq_nonneg _)
  have hinc (j : ℕ) (hj₁ : m ≤ j) (hj₂ : j ≤ n) :
      c ≤ P (j + 1) - P j := by
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hP m).le (hmono hj₁) 2) (div_nonneg (hz n) (hP n).le)
    have hh' := mul_le_mul_of_nonneg_right (hanti hj₂) (sq_nonneg (P j))
    have hcancel : z j / P j * P j ^ 2 = z j * P j := by field_simp [(hP j).ne']
    unfold c at *
    rw [hcancel] at hh'
    rw [hstep]
    nlinarith only [hh, hh']
  have hfinite (k : ℕ) (hk : m + k ≤ n) : (k : ℝ) * c ≤ P (m + k) - P m := by
    induction k with
    | zero => simp
    | succ k ih =>
      have ha := ih (Nat.le_of_succ_le hk)
      have hb := hinc (m + k) (Nat.le_add_right _ _) (Nat.le_of_succ_le hk)
      rw [← Nat.add_assoc]
      push_cast
      nlinarith only [ha, hb]
  have hs := hfinite (n - m) (by omega)
  rw [Nat.add_sub_of_le hmn] at hs
  have hs' : (((n - m : ℕ) : ℝ) * z n) * P m ^ 2 ≤ P n ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hs (hP n).le
    have hcancel : c * P n = z n * P m ^ 2 := by
      dsimp [c]
      field_simp [(hP n).ne']
    calc
      _ = ((n - m : ℕ) : ℝ) * c * P n := by rw [mul_assoc, mul_assoc, hcancel]
      _ ≤ (P n - P m) * P n := h
      _ ≤ _ := by nlinarith only [mul_nonneg (hP m).le (hP n).le]
  have hs'' := hs'.trans (pow_le_pow_left₀ (hP n).le hRatio 2)
  rw [mul_pow] at hs''
  have hz' := le_of_mul_le_mul_right hs'' (sq_pos_of_pos (hP m))
  have hfinal := mul_le_mul_of_nonneg_right hhalf' (hz n)
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (show 0 < (n : ℝ) by exact_mod_cast hn1)).2
  nlinarith only [hz', hfinal]

private theorem product_tendsto_weighted_log_power {q a : ℝ} (hq : q < 1) (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ (q - 1) * (Real.log x - a) ^ k) atTop (𝓝 0) := by
  cases k with
  | zero =>
    simpa only [pow_zero, mul_one, neg_sub] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hq))
  | succ k =>
    let s := (1 - q) / ((k + 1 : ℕ) : ℝ)
    have hs : 0 < s := div_pos (sub_pos.mpr hq) (by positivity)
    have hconst : (fun _ : ℝ => a) =o[atTop] (fun x : ℝ => x ^ s) := by
      apply Asymptotics.isLittleO_const_left.mpr
      right
      have ht := tendsto_rpow_atTop hs
      apply ht.congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      exact (Real.norm_of_nonneg (Real.rpow_nonneg hx s)).symm
    have hlog := ((isLittleO_log_rpow_atTop hs).sub hconst).pow (Nat.succ_pos k)
    apply hlog.tendsto_div_nhds_zero.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_natCast (x ^ s), ← Real.rpow_mul hx.le,
      show s * ((k + 1 : ℕ) : ℝ) = 1 - q from div_mul_cancel₀ _ (by positivity),
      div_eq_mul_inv, ← Real.rpow_neg hx.le, neg_sub, mul_comm]

private theorem productLogKernel_hasDerivAt (B : ℝ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (productLogKernel B k)
      (theta B * (x ^ (theta B - 1) * (Real.log x - 2 * Real.log B) ^ k) +
        (k : ℝ) * (x ^ (theta B - 1) * (Real.log x - 2 * Real.log B) ^ (k - 1))) x := by
  unfold productLogKernel
  convert ((Real.hasDerivAt_rpow_const (p := theta B) (Or.inl hx.ne')).mul
    (((Real.hasDerivAt_log hx.ne').sub_const (2 * Real.log B)).pow k)) using 1
  rw [Real.rpow_sub hx, Real.rpow_one, div_eq_mul_inv]
  simp only [Pi.pow_apply]
  ring

/-- The correction kernels are bounded on each positive half-line uniformly
in the height. -/
theorem productLogCorrection_bounded {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) {B : ℝ} (hB : 2 < B) (h : ℝ) (k : ℕ) :
    ∃ C ≥ 0, ∀ n : ℕ, 1 ≤ n → |productLogCorrection μ B h k n| ≤ C := by
  let b := floorSeq B 1 ^ 2
  have hb : 0 < b := sq_pos_of_pos (floorSeq_one_pos hB)
  let c := B - 1
  have hc : 0 < c := by dsimp [c]; linarith
  let d (x : ℝ) := theta B * (x ^ (theta B - 1) * (Real.log x - 2 * Real.log B) ^ k) +
    (k : ℝ) * (x ^ (theta B - 1) * (Real.log x - 2 * Real.log B) ^ (k - 1))
  have hdlim : Tendsto d atTop (𝓝 0) := by
    have h₁ := Tendsto.const_mul (theta B)
      (product_tendsto_weighted_log_power (a := 2 * Real.log B) (theta_lt_one hB) k)
    have h₂ := Tendsto.const_mul (k : ℝ)
      (product_tendsto_weighted_log_power (a := 2 * Real.log B) (theta_lt_one hB) (k - 1))
    simpa only [mul_zero, add_zero] using h₁.add h₂
  have htail : ∀ᶠ x : ℝ in atTop, ‖d x‖ < 1 :=
    hdlim.norm.eventually (Iio_mem_nhds (by simp))
  obtain ⟨M, hM⟩ := eventually_atTop.mp htail
  have hdcont : ContinuousOn (fun x => ‖d x‖) (Icc b (max M b)) := by
    apply ContinuousOn.norm
    apply ContinuousOn.mono _ (show Icc b (max M b) ⊆ Ioi 0 from
      fun _ hx => hb.trans_le hx.1)
    dsimp [d]
    have hr : ContinuousOn (fun x : ℝ => x ^ (theta B - 1)) (Ioi 0) :=
      fun x hx => (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hx))).continuousWithinAt
    have hl : ContinuousOn (fun x : ℝ => Real.log x - 2 * Real.log B) (Ioi 0) :=
      (Real.continuousOn_log.mono (fun _ hx => ne_of_gt hx)).sub continuousOn_const
    exact ((hr.mul (hl.pow k)).const_mul _).add ((hr.mul (hl.pow (k - 1))).const_mul _)
  obtain ⟨U, hU⟩ := isCompact_Icc.bddAbove_image hdcont
  let V := max U 1
  have hV : 0 ≤ V := zero_le_one.trans (le_max_right _ _)
  have hdB (x : ℝ) (hx : b ≤ x) : ‖d x‖ ≤ V := by
    by_cases hMx : M ≤ x
    · exact (le_of_lt (hM x hMx)).trans (le_max_right _ _)
    · exact (hU (mem_image_of_mem _ ⟨hx, (le_of_not_ge hMx).trans (le_max_left _ _)⟩)).trans
        (le_max_left _ _)
  have hpoint (x : ℝ) (hx : b ≤ x) :
      ‖productLogKernel B k (x + c) - productLogKernel B k x‖ ≤ V * c := by
    have hDiff (t : ℝ) (ht : t ∈ Icc x (x + c)) : HasDerivWithinAt (productLogKernel B k)
        (d t) (Icc x (x + c)) t :=
      (productLogKernel_hasDerivAt B k (hb.trans_le (hx.trans ht.1))).hasDerivWithinAt
    have hBd : ∀ t ∈ Ico x (x + c), ‖d t‖ ≤ V := fun t ht => hdB t (hx.trans ht.1)
    have hh := norm_image_sub_le_of_norm_deriv_le_segment' hDiff hBd (x + c)
      (right_mem_Icc.2 (le_add_of_nonneg_right hc.le))
    simpa using hh
  refine ⟨V * c / 2, by positivity, ?_⟩
  intro n hn
  let ν := lawR μ B h n
  let : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  have hm : Measurable (fun p : ℝ × ℝ => p.1 * p.2) := measurable_fst.mul measurable_snd
  let : IsProbabilityMeasure (productLaw μ B h n) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2
      (inferInstanceAs (IsProbabilityMeasure (ν.prod ν)))
  have hFloor : ∀ᵐ x ∂productLaw μ B h n, b ≤ x := by
    rw [productLaw, ae_map_iff hm.aemeasurable measurableSet_Ici]
    have hh := ae_floorSeq_le_lawR hpos hB h n
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hh,
      Measure.quasiMeasurePreserving_snd.ae hh] with p hx hy
    have h₁ := (floorSeq_one_le hB hn).trans hx
    have h₂ := (floorSeq_one_le hB hn).trans hy
    exact (pow_two _).trans_le (mul_le_mul h₁ h₂ (floorSeq_nonneg hB 1)
      ((floorSeq_nonneg hB 1).trans h₁))
  have hBound : ∀ᵐ x ∂productLaw μ B h n,
      ‖productLogKernel B k (x + c) - productLogKernel B k x‖ ≤ V * c := by
    filter_upwards [hFloor] with x hx
    exact hpoint x hx
  unfold productLogCorrection
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right (by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hBound) (by norm_num)

private theorem product_mass_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : 0 < tiltedMass μ B h n := by
  let ν := lawR μ B h n
  let : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  have ha := ae_pos_lawR hpos hB h n
  have hi : Integrable (fun x : ℝ => x ^ theta B) ν := by
    simpa using product_signed_integrable ν measurable_id.aemeasurable ha
      (integrable_lawR_of hpos hmean hB h n) hB 0 0
  have hp : ∀ᵐ x ∂ν, 0 < x ^ theta B := ha.mono fun _ hx => Real.rpow_pos_of_pos hx _
  apply (integral_pos_iff_support_of_nonneg_ae (hp.mono fun _ hx => hx.le) hi).2
  apply pos_iff_ne_zero.mpr
  intro hz
  have hzero : (fun x : ℝ => x ^ theta B) =ᵐ[ν] 0 := ae_iff.mp hz
  obtain ⟨x, hx, hx0⟩ := (hp.and hzero).exists
  exact hx.ne' hx0

private theorem product_mass_floor {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) (n : ℕ) : floorSeq B n ^ theta B ≤ tiltedMass μ B h n := by
  let ν := lawR μ B h n
  let : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  have hi : Integrable (fun x : ℝ => x ^ theta B) ν := by
    simpa using product_signed_integrable ν measurable_id.aemeasurable (ae_pos_lawR hpos hB h n)
      (integrable_lawR_of hpos hmean hB h n) hB 0 0
  have h := integral_mono_ae (integrable_const (floorSeq B n ^ theta B)) hi
    ((ae_floorSeq_le_lawR hpos hB h n).mono fun _ hx =>
      Real.rpow_le_rpow (floorSeq_nonneg hB n) hx (theta_pos hB).le)
  simpa [tiltedMass, ν] using h

private theorem product_rpow_floor_le_one {B : ℝ} (hB : 2 < B) (n : ℕ) :
    floorSeq B n ^ theta B ≤ 1 :=
  Real.rpow_le_one (floorSeq_nonneg hB n) (floorSeq_le_one hB n) (theta_pos hB).le

private theorem product_floor_rpow_error {B : ℝ} (hB : 2 < B) {n : ℕ} (hn : 1 ≤ n) :
    1 - floorSeq B n ^ theta B ≤ (2 / B) ^ n := by
  have hp : 0 < floorSeq B n := (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)
  have hq := Real.rpow_le_rpow_of_exponent_ge hp (floorSeq_le_one hB n) (theta_lt_one hB).le
  rw [Real.rpow_one] at hq
  linarith only [hq, one_sub_floorSeq_le hB n]

/-- The tilted mass normalized by the deterministic floor satisfies the
one-step quadratic bound used in the rate argument. -/
theorem product_floor_defect_step {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    let z (i : ℕ) := tiltedMass μ B h i / floorSeq B i ^ theta B - 1
    z (n + 1) ≤ z n + z n ^ 2 / 2 := by
  let ν := lawR μ B h n
  let : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  let q := theta B
  let c := B - 1
  let b := floorSeq B n
  have hb : 0 < b := (floorSeq_one_pos hB).trans_le (floorSeq_one_le hB hn)
  have hc : 0 < c := by dsimp [c]; linarith
  have hB0 : 0 < B := by linarith
  have hq : 0 < q := theta_pos hB
  have hq1 : q < 1 := theta_lt_one hB
  have hd : AntitoneOn (fun s : ℝ => (s + c) ^ q - s ^ q) (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi _)
    · intro x hx
      have hp : 0 < x := hx
      exact (((Real.hasDerivAt_rpow_const (p := q) (Or.inl (add_pos hp hc).ne')).comp x
        ((hasDerivAt_id x).add_const c)).sub
        (Real.hasDerivAt_rpow_const (p := q) (Or.inl hp.ne'))).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      have hp : 0 < x := hx
      exact (((Real.hasDerivAt_rpow_const (p := q) (Or.inl (add_pos hp hc).ne')).comp x
        ((hasDerivAt_id x).add_const c)).sub
        (Real.hasDerivAt_rpow_const (p := q) (Or.inl hp.ne'))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      have hp : 0 < x := hx
      have heq : deriv (fun s : ℝ => (s + c) ^ q - s ^ q) x =
          q * (x + c) ^ (q - 1) - q * x ^ (q - 1) := by
        rw [← mul_one (q * (x + c) ^ (q - 1))]
        exact (((Real.hasDerivAt_rpow_const (p := q) (Or.inl (add_pos hp hc).ne')).comp x
          ((hasDerivAt_id x).add_const c)).sub
          (Real.hasDerivAt_rpow_const (p := q) (Or.inl hp.ne'))).deriv
      rw [heq]
      exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hp (le_add_of_nonneg_right hc.le) (by linarith)) hq.le)
  have hm : Measurable (fun p : ℝ × ℝ => p.1 * p.2) := measurable_fst.mul measurable_snd
  let f (p : ℝ × ℝ) := p.1 * p.2
  let g (p : ℝ × ℝ) := f p + c
  have hflo := ae_floorSeq_le_lawR hpos hB h n
  have hfp : ∀ᵐ p ∂ν.prod ν, b ^ 2 ≤ f p := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hflo,
      Measure.quasiMeasurePreserving_snd.ae hflo] with p hx hy
    exact (pow_two _).trans_le (mul_le_mul hx hy hb.le (hb.le.trans hx))
  have hfpos : ∀ᵐ p ∂ν.prod ν, 0 < f p := hfp.mono fun _ hx => (sq_pos_of_pos hb).trans_le hx
  have hgpos : ∀ᵐ p ∂ν.prod ν, 0 < g p := hfpos.mono fun _ hx => add_pos hx hc
  have hI := integrable_lawR_of hpos hmean hB h n
  have hiF : Integrable f (ν.prod ν) := hI.mul_prod hI
  have hiG : Integrable g (ν.prod ν) := hiF.add (integrable_const _)
  have hix : Integrable (fun p => f p ^ q) (ν.prod ν) := by
    simpa using product_signed_integrable _ hm.aemeasurable hfpos hiF hB 0 0
  have hiy : Integrable (fun p => g p ^ q) (ν.prod ν) := by
    simpa using product_signed_integrable _ (hm.add_const c).aemeasurable hgpos hiG hB 0 0
  have hcorr : productLogCorrection μ B h 0 n ≤ ((b ^ 2 + c) ^ q - (b ^ 2) ^ q) / 2 := by
    have hm' : Measurable (fun x : ℝ => (x + c) ^ q - x ^ q) := by fun_prop
    unfold productLogCorrection productLaw
    simp only [productLogKernel, pow_zero, mul_one]
    rw [integral_map hm.aemeasurable hm'.aestronglyMeasurable]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    have hi := integral_mono_ae (hiy.sub hix) (integrable_const ((b ^ 2 + c) ^ q - (b ^ 2) ^ q))
      (hfp.mono fun p hp => hd (sq_pos_of_pos hb) ((sq_pos_of_pos hb).trans_le hp) hp)
    simpa using hi
  have hrec := tiltedLogMoment_succ_product hpos hmean hB h 0 n
  norm_num [Finset.sum_range_succ, tiltedLogMoment_zero_product, Nat.choose] at hrec
  let A := tiltedMass μ B h n
  let b' := floorSeq B (n + 1) ^ q
  let u := b ^ q
  have hu : 0 < u := Real.rpow_pos_of_pos hb _
  have hb' : 0 < b' := Real.rpow_pos_of_pos
    ((floorSeq_one_pos hB).trans_le (floorSeq_one_le hB (by omega))) _
  have heq : (b ^ 2 + c) ^ q = 2 * b' := by
    change (b ^ 2 + c) ^ theta B = 2 * ((b ^ 2 + c) / B) ^ theta B
    rw [Real.div_rpow (add_nonneg (sq_nonneg _) hc.le) hB0.le, product_B_rpow_theta hB]
    ring
  have heq' : (b ^ 2) ^ q = u ^ 2 := by
    rw [pow_two, Real.mul_rpow hb.le hb.le]
    ring
  have hmass : tiltedMass μ B h (n + 1) - b' ≤ (A ^ 2 - u ^ 2) / 2 := by
    rw [heq, heq'] at hcorr
    dsimp [A]
    nlinarith only [hrec, hcorr]
  let z := A / u - 1
  have hz : 0 ≤ z := sub_nonneg.mpr ((le_div_iff₀ hu).2
    (by simpa [A, u, b, q] using product_mass_floor hpos hmean hB h n))
  have hfu : u ^ 2 ≤ b' := by
    have hu1 : u ≤ 1 := product_rpow_floor_le_one hB n
    have huu := Real.rpow_le_rpow hb.le (floorSeq_mono_step hB n) hq.le
    nlinarith only [huu, mul_nonneg hu.le (sub_nonneg.mpr hu1)]
  have hAz : A = u * (1 + z) := by dsimp [z]; field_simp [hu.ne']; ring
  change tiltedMass μ B h (n + 1) / b' - 1 ≤ z + z ^ 2 / 2
  rw [div_sub_one hb'.ne']
  apply (div_le_iff₀ hb').2
  rw [hAz] at hmass
  have hh := mul_le_mul_of_nonneg_left hfu (by positivity : 0 ≤ z + z ^ 2 / 2)
  nlinarith only [hmass, hh]

/-- The tilted second moment and the excess over the floor satisfy the Nash
bound once the first centered moment is small near return. -/
theorem product_floor_nash {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hA : ∀ n : ℕ, 1 ≤ n → tiltedMass μ B h n ≤ M)
    (hH : ∀ n : ℕ, 1 ≤ n → |tiltedLogMoment μ B h 1 n| ≤
      C * (max (tiltedMass μ B h n - 1) 0 + (2 / B) ^ n)) :
    ∃ δ > 0, ∀ᶠ n : ℕ in atTop, δ ≤
      (tiltedMass μ B h n / floorSeq B n ^ theta B - 1) * (tiltedLogMoment μ B h 2 n + 1) := by
  let a := Real.log B
  let q := theta B
  let b₀ := floorSeq B 1
  let u₀ := b₀ ^ q
  have ha : 0 < a := Real.log_pos (by linarith)
  have hq : 0 < q := theta_pos hB
  have hb₀ : 0 < b₀ := floorSeq_one_pos hB
  have hu₀ : 0 < u₀ := Real.rpow_pos_of_pos hb₀ q
  have hb₀1 : b₀ ≤ 1 := floorSeq_le_one hB 1
  let D := 2 * (1 + (a - Real.log b₀) ^ 2 * M) / u₀
  have hD : 0 < D := by dsimp [D]; positivity
  let E := C / u₀ + q⁻¹ + 1
  have hE : 0 < E := by dsimp [E]; positivity
  let η := a / (4 * E)
  have hη : 0 < η := by dsimp [η]; positivity
  let ρ : ℝ := 2 / B
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ' : ρ < 1 := (div_lt_one (by linarith : 0 < B)).2 hB
  have hr : ∀ᶠ n : ℕ in atTop, ρ ^ n < η :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ').eventually (Iio_mem_nhds hη)
  refine ⟨min η ((a / 2) ^ 2 / D), lt_min hη (by positivity), ?_⟩
  filter_upwards [hr, eventually_ge_atTop 1] with n hrn hn
  let ν := lawR μ B h n
  let : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  let b := floorSeq B n
  let u := b ^ q
  let A := tiltedMass μ B h n
  let H := tiltedLogMoment μ B h 1 n
  let K := tiltedLogMoment μ B h 2 n
  let z := A / u - 1
  let V (x : ℝ) := x ^ q / u
  let Y (x : ℝ) := Real.log x - Real.log b
  let w (x : ℝ) := V x - 1
  have hbb : b₀ ≤ b := floorSeq_one_le hB hn
  have hb := hb₀.trans_le hbb
  have hb1 : b ≤ 1 := floorSeq_le_one hB n
  have hu := Real.rpow_pos_of_pos hb q
  have huu : u₀ ≤ u := Real.rpow_le_rpow hb₀.le hbb hq.le
  have hu1 : u ≤ 1 := product_rpow_floor_le_one hB n
  have hf := ae_floorSeq_le_lawR hpos hB h n
  have hp : ∀ᵐ x ∂ν, 0 < x := hf.mono fun _ hx => hb.trans_le hx
  have hi := integrable_lawR_of hpos hmean hB h n
  have hZ (k : ℕ) : Integrable (fun x : ℝ => x ^ q * (Real.log x - a) ^ k) ν :=
    product_signed_integrable ν measurable_id.aemeasurable hp hi hB a k
  have hK : 0 ≤ K := integral_nonneg_of_ae (hp.mono fun _ hx =>
    mul_nonneg (Real.rpow_nonneg hx.le q) (sq_nonneg _))
  by_cases hzη : η ≤ z
  · change min η _ ≤ z * (K + 1)
    exact (min_le_left _ _).trans (hzη.trans
      (le_mul_of_one_le_right (hη.le.trans hzη) (by linarith)))
  have haz : u ≤ A := product_mass_floor hpos hmean hB h n
  have hz : 0 ≤ z := sub_nonneg.mpr ((le_div_iff₀ hu).2 (by simpa using haz))
  have hdef : max (A - 1) 0 ≤ z := by
    have hAu : A = u * (1 + z) := by
      change A = u * (1 + (A / u - 1))
      rw [show 1 + (A / u - 1) = A / u by ring, mul_div_cancel₀ _ hu.ne']
    apply max_le _ hz
    rw [hAu]
    nlinarith only [hu1, mul_nonneg (sub_nonneg.mpr hu1) hz]
  have hH' : |H| ≤ C * (z + ρ ^ n) := (hH n hn).trans
    (mul_le_mul_of_nonneg_left (add_le_add_left hdef _) hC)
  have hvi (k : ℕ) : Integrable (fun x => V x * Y x ^ k) ν := by
    have hw := product_signed_integrable ν measurable_id.aemeasurable hp hi hB (Real.log b) k
    apply (hw.div_const u).congr
    exact Eventually.of_forall (fun x => by dsimp [V, Y]; ring)
  have hV : Integrable V ν := by simpa only [pow_zero, mul_one] using hvi 0
  have hVY : Integrable (fun x => V x * Y x) ν := by simpa only [pow_one] using hvi 1
  have hY : Integrable Y ν :=
    (integrable_log_lawR_of hpos hmean hB h hn).sub (integrable_const _)
  have hw : 0 ≤ᵐ[ν] w := hf.mono fun _ hx => sub_nonneg.mpr
    ((le_div_iff₀ hu).2 (by simpa using Real.rpow_le_rpow hb.le hx hq.le))
  have hwi : Integrable w ν := hV.sub (integrable_const 1)
  have hwY : Integrable (fun x => w x * Y x) ν := by
    apply (hVY.sub hY).congr
    exact Eventually.of_forall (fun x => by dsimp [w]; ring)
  have hwY2 : Integrable (fun x => w x * Y x ^ 2) ν := by
    apply (hvi 2).mono' (by dsimp [w, V, Y]; fun_prop)
    filter_upwards [hw] with x hx
    rw [Real.norm_of_nonneg (mul_nonneg hx (sq_nonneg _))]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    dsimp [w]
    linarith
  have hwint : (∫ x, w x ∂ν) = z := by
    dsimp [w, V, z]
    rw [integral_sub hV (integrable_const 1), integral_div]
    simp [A, tiltedMass, ν, q]
  have hYint : (∫ x, Y x ∂ν) ≤ z / q := by
    rw [← hwint, ← integral_div]
    apply integral_mono_ae hY (hwi.div_const q)
    filter_upwards [hf] with x hx
    have hx' : 0 < x := hb.trans_le hx
    have he : Real.exp (q * Y x) = V x := by
      dsimp [Y, V, u]
      rw [mul_sub, Real.exp_sub, Real.rpow_def_of_pos hx', Real.rpow_def_of_pos hb]
      ring
    apply (le_div_iff₀ hq).2
    dsimp [w]
    linarith only [Real.add_one_le_exp (q * Y x), he]
  have hVYint : (∫ x, V x * Y x ∂ν) = (H + (a - Real.log b) * A) / u := by
    have he : (fun x => V x * Y x) =
        fun x => (x ^ q * (Real.log x - a) + (a - Real.log b) * x ^ q) / u := by
      funext x
      dsimp [V, Y]
      ring
    have hpow : Integrable (fun x : ℝ => x ^ q) ν := by
      simpa only [pow_zero, mul_one] using hZ 0
    have hZi : Integrable (fun x : ℝ => x ^ q * (Real.log x - a)) ν := by
      simpa only [pow_one] using hZ 1
    rw [he, integral_div, integral_add hZi (hpow.const_mul _), integral_const_mul]
    simp only [H, tiltedLogMoment, pow_one]
    rfl
  have hhV : a - C / u₀ * (z + ρ ^ n) ≤ (∫ x, V x * Y x ∂ν) := by
    rw [hVYint, add_div]
    have h₁ : a ≤ (a - Real.log b) * A / u := by
      have hl : Real.log b ≤ 0 := Real.log_nonpos hb.le hb1
      apply (le_div_iff₀ hu).2
      have h₂ := mul_le_mul_of_nonneg_left haz ha.le
      have h₃ := mul_nonpos_of_nonpos_of_nonneg hl (hu.le.trans haz)
      nlinarith only [h₂, h₃]
    have h₂ : -(C / u₀ * (z + ρ ^ n)) ≤ H / u := by
      have hnabs : - (C * (z + ρ ^ n)) ≤ H := by
        linarith only [neg_abs_le H, hH']
      have h := div_le_div_of_nonneg_right hnabs hu.le
      have h' := div_le_div_of_nonneg_left (mul_nonneg hC (add_nonneg hz (pow_nonneg hρ n))) hu₀ huu
      have he : -(C / u₀ * (z + ρ ^ n)) = -(C * (z + ρ ^ n) / u₀) := by ring
      rw [he]
      rw [neg_div] at h
      exact (neg_le_neg h').trans h
    linarith only [h₁, h₂]
  have hwYint : a / 2 ≤ (∫ x, w x * Y x ∂ν) := by
    have he : (fun x => w x * Y x) = fun x => V x * Y x - Y x := by
      funext x
      dsimp [w]
      ring
    rw [he, integral_sub hVY hY]
    have hzle := le_of_lt (lt_of_not_ge hzη)
    have hzz := mul_le_mul_of_nonneg_left (add_le_add hzle hrn.le) (div_nonneg hC hu₀.le)
    have hqq := div_le_div_of_nonneg_right hzle hq.le
    have hηmul : η * (4 * E) = a := div_mul_cancel₀ _ (by positivity)
    dsimp [E] at hηmul
    have h0 := mul_nonneg hη.le (inv_nonneg.mpr hq.le)
    have h1 := mul_nonneg hη.le (div_nonneg hC hu₀.le)
    rw [div_eq_mul_inv, div_eq_mul_inv] at hqq
    rw [div_eq_mul_inv] at hYint
    nlinarith only [hhV, hYint, hzz, hqq, hηmul, h0, h1, hη.le]
  have hwY2int : (∫ x, w x * Y x ^ 2 ∂ν) ≤ D * (K + 1) := by
    let v := a - Real.log b
    have hv0 : 0 ≤ v := sub_nonneg.mpr ((Real.log_nonpos hb.le hb1).trans ha.le)
    have hv : v ≤ a - Real.log b₀ := sub_le_sub_left (Real.log_le_log hb₀ hbb) a
    have hpow : Integrable (fun x : ℝ => x ^ q) ν := by
      simpa only [pow_zero, mul_one] using hZ 0
    have hi' : Integrable (fun x : ℝ =>
        (2 * (x ^ q * (Real.log x - a) ^ 2) + (2 * v ^ 2) * x ^ q) / u) ν :=
      (((hZ 2).const_mul 2).add (hpow.const_mul _)).div_const u
    have hh := integral_mono_ae hwY2 hi' (hp.mono fun x hx => by
      have hnon := Real.rpow_nonneg hx.le q
      have he := mul_nonneg hnon (sq_nonneg (Real.log x - a - v))
      apply (le_div_iff₀ hu).2
      change (x ^ q / u - 1) * (Real.log x - Real.log b) ^ 2 * u ≤ _
      have hYeq : Real.log x - Real.log b = Real.log x - a + v := by dsimp [v]; ring
      rw [hYeq, mul_right_comm, sub_mul, div_mul_cancel₀ _ hu.ne', one_mul, sub_mul]
      have hterm := mul_nonneg hu.le (sq_nonneg (Real.log x - a + v))
      nlinarith only [he, hterm])
    rw [integral_div, integral_add ((hZ 2).const_mul 2) (hpow.const_mul _),
      integral_const_mul, integral_const_mul] at hh
    change _ ≤ (2 * K + (2 * v ^ 2) * A) / u at hh
    refine hh.trans ?_
    have hv2 := pow_le_pow_left₀ hv0 hv 2
    have hA0 := hu.le.trans haz
    have hA' := hA n hn
    have hprod := (mul_le_mul_of_nonneg_right hv2 hA0).trans
      (mul_le_mul_of_nonneg_left hA' (sq_nonneg (a - Real.log b₀)))
    have hD' : D * u₀ = 2 * (1 + (a - Real.log b₀) ^ 2 * M) :=
      div_mul_cancel₀ _ hu₀.ne'
    apply (div_le_iff₀ hu).2
    have hDu := mul_le_mul_of_nonneg_left huu (mul_nonneg hD.le (add_nonneg hK zero_le_one))
    have hprod' := mul_nonneg (mul_nonneg (sq_nonneg (a - Real.log b₀)) hM) hK
    have hu' := congrArg (fun x : ℝ => x * (K + 1)) hD'
    nlinarith only [hprod, hDu, hprod', hu']
  have hCS := product_integral_cauchy_schwarz hw hwi hwY hwY2
  rw [hwint] at hCS
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ a / 2) hwYint 2
  have hfin := hs.trans (hCS.trans (mul_le_mul_of_nonneg_left hwY2int hz))
  change min η _ ≤ z * (K + 1)
  refine (min_le_right _ _).trans ((div_le_iff₀ hD).2 ?_)
  nlinarith only [hfin]

/-- Deterministic conclusions for the floor-normalized critical product and
moments. The hypotheses describe the errors in the normalized recurrences. -/
theorem product_sequence_bounds {P z K J L : ℕ → ℝ} {ρ δ C : ℝ}
    (hP : ∀ n, 1 ≤ P n) (hz : ∀ n, 0 ≤ z n) (hzmax : ∀ n, z n ≤ C)
    (hstep : ∀ n, P (n + 1) = P n * (1 + z n))
    (hzstep : ∀ n, z (n + 1) ≤ z n * (1 + z n))
    (hρ : 0 ≤ ρ) (hρ' : ρ < 1) (hδ : 0 < δ) (hC : 1 ≤ C)
    (hK : ∀ n, 0 ≤ K n) (hL : ∀ n, 0 ≤ L n) (hJlow : ∀ n, -C ≤ J n)
    (hNash : ∀ n, δ ≤ z n * (K n + 1))
    (hCS : ∀ n, K n ^ 2 ≤ C * (J n + C))
    (hCS' : ∀ n, J n ^ 2 ≤ K n * L n)
    (hKstep : ∀ n, K (n + 1) / P (n + 1) - K n / P n ≤ C / P (n + 1))
    (hJstep : ∀ n, J (n + 1) / P (n + 1) - J n / P n ≤
      C * ρ ^ n * K n / P (n + 1) + C / P (n + 1))
    (hJback : ∀ n, J n / P n - J (n + 1) / P (n + 1) ≤
      C * ((z n + ρ ^ n) * K n + 1) / P (n + 1))
    (hLstep : ∀ n, L (n + 1) / P (n + 1) - L n / P n ≤
      C * (ρ ^ n * |J n| + K n ^ 2 + 1) / P (n + 1))
    (hreturn : ∀ ε > 0, ∃ᶠ n in atTop, z n < ε) :
    Summable (fun n => (P n)⁻¹) ∧
    (∃ ell > 0, Tendsto (fun n => J n / P n) atTop (𝓝 ell)) ∧
    (∃ d D : ℝ, 0 < d ∧ 0 < D ∧
      (∀ n : ℕ, d * ((n : ℝ) + 1) ^ 2 ≤ P n ∧ K n ^ 2 ≤ D * P n) ∧
      ∀ᶠ n : ℕ in atTop,
        P n ≤ D * ((n : ℝ) + 1) ^ 2 ∧ L n ≤ D * ((n : ℝ) + 1) ^ 3 ∧
        d * (n : ℝ)⁻¹ ≤ z n ∧ z n ≤ D * (n : ℝ)⁻¹ ∧
        d * (n : ℝ) ≤ K n ∧ K n ≤ D * (n : ℝ)) := by
  have hp (n : ℕ) : 0 < P n := zero_lt_one.trans_le (hP n)
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hmono : Monotone P := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hstep, mul_add, mul_one]
    exact le_add_of_nonneg_right (mul_nonneg (hp n).le (hz n))
  obtain ⟨hsum, ⟨d, hd, hlow⟩, ⟨D, hD, hb⟩⟩ :=
    product_preliminary_bounds hP hz hzmax hstep hρ hρ' hδ hC hK hNash hCS hKstep hJstep
  have hKs (n : ℕ) : K n ≤ Real.sqrt D * Real.sqrt (P n) := by
    apply (sq_le_sq₀ (hK n) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hD.le, Real.sq_sqrt (hp n).le]
    exact (hb n).1
  let s (n : ℕ) : ℝ := C * Real.sqrt D * ρ ^ n + C / P (n + 1)
  have hsum' : Summable (fun n : ℕ => (P (n + 1))⁻¹) := (summable_nat_add_iff 1).2 hsum
  have hs : Summable s := by
    simpa only [s, div_eq_mul_inv] using ((summable_geometric_of_lt_one hρ hρ').mul_left
      (C * Real.sqrt D)).add (hsum'.mul_left C)
  have hsup (n : ℕ) : J (n + 1) / P (n + 1) - J n / P n ≤ s n := by
    have hk : K n / P (n + 1) ≤ Real.sqrt D := by
      apply (div_le_iff₀ (hp (n + 1))).2
      apply (hKs n).trans
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      have hn : 1 ≤ Real.sqrt (P n) := by simpa using Real.sqrt_le_sqrt (hP n)
      exact (show Real.sqrt (P n) ≤ P n by
        have hh := Real.sq_sqrt (hp n).le
        nlinarith only [hn, hh, mul_nonneg (Real.sqrt_nonneg (P n)) (sub_nonneg.mpr hn)]).trans
        (hmono (Nat.le_succ n))
    have hh := mul_le_mul_of_nonneg_left hk (mul_nonneg hCp.le (pow_nonneg hρ n))
    dsimp [s]
    have hj := hJstep n
    rw [mul_div_assoc] at hj
    linarith only [hj, hh]
  have hminor (n : ℕ) : -C / P n ≤ J n / P n :=
    div_le_div_of_nonneg_right (hJlow n) (hp n).le
  have hlo (n : ℕ) : -C ≤ J n / P n :=
    ((le_div_iff₀ (hp n)).2 (by
      have hh := mul_nonneg hCp.le (sub_nonneg.mpr (hP n))
      nlinarith only [hh])).trans (hminor n)
  obtain ⟨ell, hlim⟩ := product_tendsto_of_summable_upper_increments hlo
    (fun n => add_nonneg
      (mul_nonneg (mul_nonneg hCp.le (Real.sqrt_nonneg _)) (pow_nonneg hρ n))
      (div_nonneg hCp.le (hp (n + 1)).le)) hs hsup
  have hnonneg : 0 ≤ ell := by
    have hm : Tendsto (fun n => -C / P n) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using hsum.tendsto_atTop_zero.const_mul (-C)
    exact le_of_tendsto_of_tendsto' hm hlim hminor
  have hell : 0 < ell := by
    rcases hnonneg.eq_or_lt with he | he
    · exact False.elim (product_cubic_residue_ne_zero hP hz hK hstep hρ hρ' hδ hC hNash
        hCS hJback ⟨Real.sqrt D, hKs⟩ hreturn (he ▸ hlim))
    · exact he
  obtain ⟨E, hE, hevent⟩ := product_upper_of_cubic_limit hP hmono hρ hρ'.le hCp hD
    hK hL hJlow hb hCS' hLstep hell hlim
  obtain ⟨Z, hZ, hZevent⟩ := product_defect_upper_of_quadratic hp hmono hz hstep hzstep hd
    hE hlow (hevent.mono fun _ h => h.1)
  let V := 2 * Real.sqrt D * Real.sqrt E
  have hV : 0 < V := by dsimp [V]; positivity
  let c := min d (min (δ / (V + 1)) (δ / (2 * Z)))
  have hc : 0 < c := lt_min hd (lt_min (div_pos hδ (by positivity)) (div_pos hδ (by positivity)))
  let U := max D (max E (max Z V))
  have hDU : D ≤ U := le_max_left _ _
  have hEU : E ≤ U := (le_max_left _ _).trans (le_max_right _ _)
  have hZU : Z ≤ U := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hVU : V ≤ U := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨hsum, ⟨ell, hell, hlim⟩, ⟨c, U, hc, hD.trans_le hDU, fun n => ⟨?_, ?_⟩, ?_⟩⟩
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans (hlow n)
  · exact (hb n).1.trans (mul_le_mul_of_nonneg_right hDU (hp n).le)
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 * Z / δ ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hevent, hZevent, hlarge, eventually_ge_atTop 1] with n hE' hz' hn hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hnone : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hk : K n ≤ V * (n : ℝ) := by
    apply (hKs n).trans
    apply (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE'.1) (Real.sqrt_nonneg D)).trans
    rw [Real.sqrt_mul hE.le, Real.sqrt_sq (by positivity : 0 ≤ (n : ℝ) + 1)]
    have h1 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
    have hh := mul_le_mul_of_nonneg_left h1
      (mul_nonneg (Real.sqrt_nonneg D) (Real.sqrt_nonneg E))
    simpa only [V, mul_assoc, mul_left_comm (Real.sqrt D) 2, mul_left_comm (Real.sqrt E) 2]
      using hh
  have hzlow : δ / (V + 1) * (n : ℝ)⁻¹ ≤ z n := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hnpos).2
    apply (div_le_iff₀ (show 0 < V + 1 by positivity)).2
    have hle : K n + 1 ≤ (V + 1) * (n : ℝ) := by nlinarith only [hk, hnone]
    have hh := (hNash n).trans (mul_le_mul_of_nonneg_left hle (hz n))
    linarith only [hh]
  have hklow : δ / (2 * Z) * (n : ℝ) ≤ K n := by
    have hh := (hNash n).trans
      (mul_le_mul_of_nonneg_right hz' (add_nonneg (hK n) zero_le_one))
    rw [← div_eq_mul_inv, div_mul_eq_mul_div] at hh
    have hh' := (le_div_iff₀ hnpos).1 hh
    have hZle := (div_le_iff₀ hδ).1 hn
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 2 * Z by positivity)).2
    nlinarith only [hh', hZle]
  refine ⟨hE'.1.trans (mul_le_mul_of_nonneg_right hEU (sq_nonneg _)),
    hE'.2.trans (mul_le_mul_of_nonneg_right hEU (by positivity)),
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _))
      (inv_nonneg.mpr hnpos.le)).trans hzlow,
    hz'.trans (mul_le_mul_of_nonneg_right hZU (inv_nonneg.mpr hnpos.le)),
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hnpos.le).trans hklow,
    hk.trans (mul_le_mul_of_nonneg_right hVU hnpos.le)⟩

private theorem product_lower_moment_bounds {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B) (h : ℝ)
    {M : ℝ} (hM : ∀ n, absTiltedLogMoment μ B h 1 n ≤ M) :
    ∃ C ≥ 1, ∀ n : ℕ, 1 ≤ n →
      0 ≤ tiltedLogMoment μ B h 2 n ∧ 0 ≤ tiltedLogMoment μ B h 4 n ∧
      -C ≤ tiltedLogMoment μ B h 3 n ∧
      tiltedLogMoment μ B h 2 n ^ 2 ≤ C * (tiltedLogMoment μ B h 3 n + C) := by
  let b := floorSeq B 1
  let a := Real.log B
  let d := a - Real.log b
  have hd : 0 ≤ d := sub_nonneg.mpr ((Real.log_nonpos (floorSeq_nonneg hB 1)
    (floorSeq_le_one hB 1)).trans (Real.log_nonneg (by linarith)))
  let D := 4 * d ^ 3
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let C := max 1 (max M D)
  have hC : 1 ≤ C := le_max_left _ _
  have hDC : D ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hMC : M ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCp : 0 ≤ C := zero_le_one.trans hC
  refine ⟨C, hC, ?_⟩
  intro n hn
  let ν := lawR μ B h n
  let : IsProbabilityMeasure ν := isProbabilityMeasure_lawR B h n
  let Z (x : ℝ) := Real.log x - a
  let w (x : ℝ) := x ^ theta B * |Z x|
  have hi := integrable_lawR_of hpos hmean hB h n
  have hf := ae_floorSeq_le_lawR hpos hB h n
  have hp := ae_pos_lawR hpos hB h n
  have hZI (k : ℕ) : Integrable (fun x => x ^ theta B * Z x ^ k) ν :=
    product_signed_integrable ν measurable_id.aemeasurable hp hi hB a k
  have hAi (k : ℕ) : Integrable (fun x => x ^ theta B * |Z x| ^ k) ν := by
    simpa only [Real.rpow_natCast] using
      integrable_absTiltedLogRpow_aux hpos hmean hB h n (Nat.cast_nonneg k)
  have hK : 0 ≤ tiltedLogMoment μ B h 2 n := integral_nonneg_of_ae
    (hp.mono fun _ hx => mul_nonneg (Real.rpow_nonneg hx.le _) (sq_nonneg _))
  have hL : 0 ≤ tiltedLogMoment μ B h 4 n := integral_nonneg_of_ae
    (hp.mono fun _ hx => mul_nonneg (Real.rpow_nonneg hx.le _) (by positivity))
  have hwi : Integrable w ν := by simpa only [pow_one] using hAi 1
  have hnon : 0 ≤ᵐ[ν] w := hp.mono fun _ hx =>
    mul_nonneg (Real.rpow_nonneg hx.le _) (abs_nonneg _)
  have h₁ : (fun x => w x * |Z x|) = (fun x => x ^ theta B * Z x ^ 2) := by
    funext x
    dsimp [w]
    rw [mul_assoc, ← pow_two, sq_abs]
  have h₃ : (fun x => w x * |Z x| ^ 2) = (fun x => x ^ theta B * |Z x| ^ 3) := by
    funext x
    dsimp [w]
    ring
  have hCS := product_integral_cauchy_schwarz hnon hwi (h₁ ▸ hZI 2) (h₃ ▸ hAi 3)
  rw [h₁, h₃] at hCS
  let V := ∫ x, x ^ theta B * |Z x| ^ 3 ∂ν
  have hV : 0 ≤ V := integral_nonneg_of_ae (hp.mono fun _ hx =>
    mul_nonneg (Real.rpow_nonneg hx.le _) (pow_nonneg (abs_nonneg _) _))
  have hVJ : V ≤ tiltedLogMoment μ B h 3 n + D := by
    have hh := integral_mono_ae (hAi 3) ((hZI 3).add (integrable_const D))
      (show ∀ᵐ x ∂ν, x ^ theta B * |Z x| ^ 3 ≤ x ^ theta B * Z x ^ 3 + D from by
        filter_upwards [hp, hf] with x hxp hx
        by_cases hz : 0 ≤ Z x
        · rw [abs_of_nonneg hz]
          exact le_add_of_nonneg_right hD
        · have hzl : -Z x ≤ d := by
            have hlog := Real.log_le_log (floorSeq_one_pos hB) ((floorSeq_one_le hB hn).trans hx)
            dsimp [d, Z]
            linarith
          have hxB : x ≤ B := (Real.log_le_log_iff hxp (by linarith)).mp
            (by dsimp [Z, a] at hz; linarith)
          have hxq : x ^ theta B ≤ 2 := by
            rw [← product_B_rpow_theta hB]
            exact Real.rpow_le_rpow hxp.le hxB (theta_pos hB).le
          rw [abs_of_neg (lt_of_not_ge hz)]
          have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ -Z x) hzl 3
          have hmul := mul_le_mul hxq hpow (pow_nonneg (by linarith : 0 ≤ -Z x) 3)
            (by norm_num : (0 : ℝ) ≤ 2)
          dsimp [D]
          nlinarith only [hmul])
    simpa [V, tiltedLogMoment, ν, Z, a, integral_add (hZI 3) (integrable_const D)] using hh
  have hl : -C ≤ tiltedLogMoment μ B h 3 n := by linarith only [hVJ, hV, hDC]
  refine ⟨hK, hL, hl, ?_⟩
  have hwiEq : (∫ x, w x ∂ν) = absTiltedLogMoment μ B h 1 n := by
    simp only [w, absTiltedLogMoment, pow_one, Z, a, ν]
  rw [hwiEq] at hCS
  change tiltedLogMoment μ B h 2 n ^ 2 ≤ absTiltedLogMoment μ B h 1 n * V at hCS
  exact hCS.trans ((mul_le_mul_of_nonneg_right ((hM n).trans hMC) hV).trans
    (mul_le_mul_of_nonneg_left (hVJ.trans (add_le_add_right hDC _)) hCp))

private theorem product_floor_factor {B : ℝ} (hB : 2 < B) {N : ℕ} (hN : 1 ≤ N)
    {Q₀ : ℝ} (hQ₀ : 0 < Q₀) :
    ∃ fInf > 0, Tendsto
      (fun n => Q₀ * ∏ i ∈ Finset.range n, floorSeq B (i + N) ^ theta B)
      atTop (𝓝 fInf) := by
  let b (i : ℕ) := floorSeq B (i + N) ^ theta B
  have hb (i : ℕ) : 0 < b i := Real.rpow_pos_of_pos
    ((floorSeq_one_pos hB).trans_le (floorSeq_one_le hB (by omega))) _
  have hb1 (i : ℕ) : b i ≤ 1 := product_rpow_floor_le_one hB _
  let ρ : ℝ := 2 / B
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ' : ρ < 1 := (div_lt_one (by linarith : 0 < B)).2 hB
  have hsum : Summable (fun i => b i - 1) := by
    apply (summable_geometric_of_lt_one hρ hρ').of_norm_bounded
    intro i
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hb1 i)), neg_sub]
    have hh := product_floor_rpow_error hB (n := i + N) (by omega)
    exact hh.trans (pow_le_pow_of_le_one hρ hρ'.le (Nat.le_add_right i N))
  have hs : Summable (fun i => Real.log (b i)) := by
    simpa only [add_sub_cancel] using Real.summable_log_one_add_of_summable hsum
  let L := Real.exp (∑' i, Real.log (b i))
  refine ⟨Q₀ * L, mul_pos hQ₀ (Real.exp_pos _), ?_⟩
  exact ((Real.hasProd_of_hasSum_log hb hs.hasSum).tendsto_prod_nat).const_mul Q₀

private theorem product_scaled_step {a z f P m e : ℕ → ℝ}
    (hP : ∀ n, 0 < P n) (hf : ∀ n, 0 < f n)
    (hPstep : ∀ n, P (n + 1) = P n * (1 + z n))
    (hfactor : ∀ n, a n * f n = (1 + z n) * f (n + 1))
    (hm : ∀ n, m (n + 1) = a n * m n + e n) (n : ℕ) :
    m (n + 1) / f (n + 1) / P (n + 1) - m n / f n / P n =
      (e n / f (n + 1)) / P (n + 1) := by
  have hr : (f (n + 1) * P (n + 1)) = a n * (f n * P n) := by
    rw [hPstep]
    nlinarith only [congrArg (fun x : ℝ => x * P n) (hfactor n)]
  rw [hm, div_div, div_div, div_div, add_div, add_sub_assoc]
  have heq : a n * m n / (f (n + 1) * P (n + 1)) = m n / (f n * P n) := by
    apply (div_eq_div_iff (mul_pos (hf _) (hP _)).ne'
      (mul_pos (hf _) (hP _)).ne').2
    rw [hr]
    ring
  rw [heq]
  ring

private theorem product_eventually_unshift {p : ℕ → Prop} (N : ℕ)
    (h : ∀ᶠ n in atTop, p (n + N)) : ∀ᶠ n in atTop, p n := by
  obtain ⟨m, hm⟩ := eventually_atTop.mp h
  refine eventually_atTop.mpr ⟨m + N, fun n hn => ?_⟩
  have hh := hm (n - N) (by omega)
  simpa only [Nat.sub_add_cancel (show N ≤ n by omega)] using hh

private theorem product_global_upper {p w : ℕ → ℝ} {D : ℝ}
    (hw : ∀ n, 0 < w n) (hD : 0 < D)
    (h : ∀ᶠ n in atTop, p n ≤ D * w n) : ∃ E > 0, ∀ n, p n ≤ E * w n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  let S := ∑ i ∈ Finset.range N, |p i / w i|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨D + S, add_pos_of_pos_of_nonneg hD hS, fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hS) (hw n).le)
  · apply (div_le_iff₀ (hw n)).mp
    have hh : |p n / w n| ≤ S := Finset.single_le_sum (fun i _ => abs_nonneg (p i / w i))
      (Finset.mem_range.mpr (lt_of_not_ge hn))
    linarith only [le_abs_self (p n / w n), hh, hD]

private theorem product_geom_inv_eventual {ρ c : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ < 1) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ρ ^ n ≤ c * (n : ℝ)⁻¹ := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one 1
    (show ‖ρ‖ < 1 by simpa only [Real.norm_eq_abs, abs_of_nonneg hρ] using hρ')
  have ht : Tendsto (fun n : ℕ => (n : ℝ) * ρ ^ n) atTop (𝓝 0) := by
    simpa only [pow_one] using hs.tendsto_atTop_zero
  filter_upwards [ht.eventually (Iio_mem_nhds hc), (eventually_ge_atTop 1 :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n)] with n hn hn1
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (show 0 < (n : ℝ) by exact_mod_cast hn1)).2
  have hn' : (n : ℝ) * ρ ^ n < c := hn
  linarith only [hn']

set_option maxHeartbeats 400000 in
/-- The critical product theorem conditional on return and the small first moment. -/
theorem criticalProduct_of_return {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ w ∂μ, 0 < w) (hmean : ∫ w, w ∂μ = 1) {B : ℝ} (hB : 2 < B)
    (hshift : Real.log (B - 1) < criticalPoint μ B)
    (hReturn : (∀ ε > 0, ∃ᶠ n in atTop, tiltedMass μ B (criticalPoint μ B) n < 1 + ε) ∧
      (∀ ε > 0, ∀ᶠ n in atTop, 1 - ε < tiltedMass μ B (criticalPoint μ B) n))
    (hHsmall : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |tiltedLogMoment μ B (criticalPoint μ B) 1 n| ≤
        C * (max (tiltedMass μ B (criticalPoint μ B) n - 1) 0 + (2 / B) ^ n)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n : ℕ, 1 ≤ n →
        ((n : ℝ) + 1) ^ 2 / C ≤ tiltedProduct μ B (criticalPoint μ B) n ∧
        tiltedProduct μ B (criticalPoint μ B) n ≤ C * ((n : ℝ) + 1) ^ 2 ∧
        tiltedLogMoment μ B (criticalPoint μ B) 2 n ^ 2 ≤
          C * tiltedProduct μ B (criticalPoint μ B) n ∧
        tiltedLogMoment μ B (criticalPoint μ B) 4 n ≤ C * ((n : ℝ) + 1) ^ 3) ∧
      Summable (fun n : ℕ => (tiltedProduct μ B (criticalPoint μ B) n)⁻¹) ∧
      (∃ ℓ₃ : ℝ, 0 < ℓ₃ ∧
        Tendsto (fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 3 n /
          tiltedProduct μ B (criticalPoint μ B) n) atTop (𝓝 ℓ₃)) ∧
      (∀ᶠ n : ℕ in atTop, 1 < tiltedMass μ B (criticalPoint μ B) n) ∧
      ((fun n : ℕ => tiltedMass μ B (criticalPoint μ B) n - 1) =Θ[atTop]
        fun n : ℕ => ((n : ℝ))⁻¹) ∧
      ((fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 2 n) =Θ[atTop]
        fun n : ℕ => (n : ℝ)) ∧
      ((fun n : ℕ => tiltedLogMoment μ B (criticalPoint μ B) 1 n) =O[atTop]
        fun n : ℕ => ((n : ℝ))⁻¹) ∧
      ∀ ε > 0, Tendsto (fun n : ℕ => lawR μ B (criticalPoint μ B) n {x | ε < |x - 1|})
        atTop (𝓝 0) := by
  clear hshift
  let h := criticalPoint μ B
  let A₀ := tiltedMass μ B h
  let Q₀ := tiltedProduct μ B h
  let H₀ := tiltedLogMoment μ B h 1
  let K₀ := tiltedLogMoment μ B h 2
  let J₀ := tiltedLogMoment μ B h 3
  let L₀ := tiltedLogMoment μ B h 4
  let ρ : ℝ := 2 / B
  let Mₐ : ℝ := (B - 1) ^ theta B
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ' : ρ < 1 := (div_lt_one (by linarith : 0 < B)).2 hB
  have hfree : freeEnergy μ B h = 0 := (criticalPoint_isGreatest_aux hpos hmean hB).1
  obtain ⟨C₀, hc₀⟩ := criticalMoments_aux hB
  obtain ⟨hcrit, M₀, habs⟩ := hc₀ μ hpos hmean h hfree
  obtain ⟨C₁, hc₁⟩ := hHsmall
  let M := max 1 (max C₀ C₁)
  have hM : 1 ≤ M := le_max_left _ _
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hM₀ : C₀ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hM₁ : C₁ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hHsmall' (n : ℕ) (hn : 1 ≤ n) :
      |H₀ n| ≤ M * (max (A₀ n - 1) 0 + ρ ^ n) :=
    (hc₁ n hn).trans (mul_le_mul_of_nonneg_right hM₁
      (add_nonneg (le_max_right _ _) (pow_nonneg hρ n)))
  have hMₐ : 0 ≤ Mₐ := Real.rpow_nonneg (by linarith) _
  have hAM (n : ℕ) (hn : 1 ≤ n) : A₀ n ≤ Mₐ := (hcrit n hn).1
  obtain ⟨δ, hδ, hNash⟩ := product_floor_nash hpos hmean hB h hMp.le hMₐ hAM hHsmall'
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hNash
  let N := max 1 N₀
  have hN : 1 ≤ N := le_max_left _ _
  have hNn (n : ℕ) : 1 ≤ n + N := by omega
  let A (n : ℕ) := A₀ (n + N)
  let Q (n : ℕ) := Q₀ (n + N)
  let b (n : ℕ) := floorSeq B (n + N) ^ theta B
  let b₁ := floorSeq B 1 ^ theta B
  have hb₁ : 0 < b₁ := Real.rpow_pos_of_pos (floorSeq_one_pos hB) _
  have hbL (n : ℕ) : b₁ ≤ b n := Real.rpow_le_rpow (floorSeq_nonneg hB 1)
    (floorSeq_one_le hB (hNn n)) (theta_pos hB).le
  have hb (n : ℕ) : 0 < b n := hb₁.trans_le (hbL n)
  have hbU (n : ℕ) : b n ≤ 1 := product_rpow_floor_le_one hB _
  have hba (n : ℕ) : b n ≤ A n := product_mass_floor hpos hmean hB h _
  let z (n : ℕ) := A n / b n - 1
  have hz (n : ℕ) : 0 ≤ z n := sub_nonneg.mpr ((le_div_iff₀ (hb n)).2 (by simpa using hba n))
  have hAz (n : ℕ) : A n = b n * (1 + z n) := by
    dsimp only [z]
    rw [show 1 + (A n / b n - 1) = A n / b n by ring, mul_div_cancel₀ _ (hb n).ne']
  have hQ₀pos (n : ℕ) : 0 < Q₀ n := Finset.prod_pos fun i _ => product_mass_pos hpos hmean hB h i
  have hQ (n : ℕ) : 0 < Q n := hQ₀pos _
  have hQstep (n : ℕ) : Q (n + 1) = Q n * A n := by
    dsimp only [Q, Q₀, A]
    rw [show n + 1 + N = (n + N) + 1 by omega, tiltedProduct, Finset.prod_range_succ]
    rfl
  -- The shifted floor factor includes the original product up to height N.
  let f (n : ℕ) := Q 0 * ∏ i ∈ Finset.range n, b i
  have hf (n : ℕ) : 0 < f n := mul_pos (hQ 0) (Finset.prod_pos fun i _ => hb i)
  have hfstep (n : ℕ) : f (n + 1) = f n * b n := by
    simp only [f, Finset.prod_range_succ, mul_assoc]
  have hfm : Antitone f := antitone_nat_of_succ_le fun n => by
    rw [hfstep]
    exact mul_le_of_le_one_right (hf n).le (hbU n)
  obtain ⟨fInf, hfInf, hflim⟩ := product_floor_factor hB hN (hQ 0)
  have hflim' : Tendsto f atTop (𝓝 fInf) := hflim
  have hflo (n : ℕ) : fInf ≤ f n :=
    le_of_tendsto hflim' ((eventually_ge_atTop n).mono fun _ hj => hfm hj)
  let S := max 1 (max (f 0) fInf⁻¹)
  have hS1 : 1 ≤ S := le_max_left _ _
  have hS : 0 < S := zero_lt_one.trans_le hS1
  have hfhi (n : ℕ) : f n ≤ S :=
    (hfm (Nat.zero_le n)).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hfinv (n : ℕ) : (f n)⁻¹ ≤ S :=
    (inv_anti₀ hfInf (hflo n)).trans ((le_max_right _ _).trans (le_max_right _ _))
  let P (n : ℕ) := Q n / f n
  have hp (n : ℕ) : 0 < P n := div_pos (hQ n) (hf n)
  have hPstep (n : ℕ) : P (n + 1) = P n * (1 + z n) := by
    dsimp only [P]
    rw [hQstep, hfstep, hAz]
    field_simp [(hf n).ne', (hb n).ne']
  have hP (n : ℕ) : 1 ≤ P n := by
    induction n with
    | zero => simp [P, f, (hQ 0).ne']
    | succ n ih =>
      apply ih.trans
      rw [hPstep]
      exact le_mul_of_one_le_right (hp n).le (by linarith only [hz n])
  have hfactor (n : ℕ) : A n * f n = (1 + z n) * f (n + 1) := by
    rw [hfstep, hAz]
    ring
  -- With this rescaling, the normalized moment ratios keep their original values.
  let K (n : ℕ) := K₀ (n + N) / f n
  let J (n : ℕ) := J₀ (n + N) / f n
  let L (n : ℕ) := L₀ (n + N) / f n
  have hKr (n : ℕ) : K₀ (n + N) = f n * K n := by
    dsimp only [K]
    rw [mul_div_cancel₀ _ (hf n).ne']
  have hJr (n : ℕ) : J₀ (n + N) = f n * J n := by
    dsimp only [J]
    rw [mul_div_cancel₀ _ (hf n).ne']
  have hLr (n : ℕ) : L₀ (n + N) = f n * L n := by
    dsimp only [L]
    rw [mul_div_cancel₀ _ (hf n).ne']
  have hQr (n : ℕ) : Q n = f n * P n := by
    dsimp only [P]
    rw [mul_div_cancel₀ _ (hf n).ne']
  obtain ⟨G, hG, hKG⟩ := product_lower_moment_bounds hpos hmean hB h habs
  have hGp : 0 ≤ G := zero_le_one.trans hG
  have hK₀ (n : ℕ) : 0 ≤ K₀ (n + N) := (hKG _ (hNn n)).1
  have hL₀ (n : ℕ) : 0 ≤ L₀ (n + N) := (hKG _ (hNn n)).2.1
  have hJ₀ (n : ℕ) : -G ≤ J₀ (n + N) := (hKG _ (hNn n)).2.2.1
  have hK (n : ℕ) : 0 ≤ K n := div_nonneg (hK₀ n) (hf n).le
  have hL (n : ℕ) : 0 ≤ L n := div_nonneg (hL₀ n) (hf n).le
  have hJlow (n : ℕ) : -(G * S) ≤ J n := by
    have hh := div_le_div_of_nonneg_right (hJ₀ n) (hf n).le
    have hs := mul_le_mul_of_nonneg_left (hfinv n) hGp
    rw [div_eq_mul_inv, neg_mul] at hh
    linarith only [hh, hs]
  have hCS (n : ℕ) : K n ^ 2 ≤ (G * S) * (J n + G * S) := by
    have h1 : K n ^ 2 ≤ (G * (f n)⁻¹) * (J n + G * (f n)⁻¹) := by
      have hh := (hKG _ (hNn n)).2.2.2
      dsimp only [K, J]
      rw [div_pow]
      apply (div_le_iff₀ (sq_pos_of_pos (hf n))).2
      convert hh using 1
      field_simp [(hf n).ne']
      rfl
    have h2 := mul_le_mul_of_nonneg_left (hfinv n) hGp
    have h3 : 0 ≤ J n + G * (f n)⁻¹ := by
      have hh := div_le_div_of_nonneg_right (hJ₀ n) (hf n).le
      rw [div_eq_mul_inv, neg_mul] at hh
      linarith only [hh]
    exact h1.trans (mul_le_mul h2 (add_le_add_right h2 _) h3 (mul_nonneg hGp hS.le))
  have hCS' (n : ℕ) : J n ^ 2 ≤ K n * L n := by
    have hh : J₀ (n + N) ^ 2 ≤ K₀ (n + N) * L₀ (n + N) :=
      product_third_sq_le_second_mul_fourth hpos hmean hB h (n + N)
    rw [hJr, hKr, hLr] at hh
    apply le_of_mul_le_mul_left _ (sq_pos_of_pos (hf n))
    nlinarith only [hh]
  let Z := Mₐ / b₁
  have hZ : 0 ≤ Z := div_nonneg hMₐ hb₁.le
  have hzmax (n : ℕ) : z n ≤ Z := by
    have hh := (div_le_div_of_nonneg_right (hAM _ (hNn n)) (hb n).le).trans
      (div_le_div_of_nonneg_left hMₐ hb₁ (hbL n))
    dsimp only [z, Z]
    linarith only [hh]
  have hzstep (n : ℕ) : z (n + 1) ≤ z n * (1 + z n) := by
    have hh : z (n + 1) ≤ z n + z n ^ 2 / 2 := by
      simpa only [z, A, b, A₀, show n + 1 + N = n + N + 1 by omega] using
        product_floor_defect_step hpos hmean hB h (hNn n)
    nlinarith only [hh, sq_nonneg (z n)]
  have hNash' (n : ℕ) : δ / S ≤ z n * (K n + 1) := by
    have hh := hN₀ (n + N) (by dsimp [N]; omega)
    change δ ≤ z n * (K₀ (n + N) + 1) at hh
    rw [hKr] at hh
    apply (div_le_iff₀ hS).2
    have h1 := mul_le_mul_of_nonneg_right (hfhi n) (hK n)
    have h2 : f n * K n + 1 ≤ S * (K n + 1) := by nlinarith only [h1, hS1]
    have h3 := mul_le_mul_of_nonneg_left h2 (hz n)
    linarith only [hh, h3]
  have hρle (n : ℕ) : ρ ^ (n + N) ≤ ρ ^ n :=
    pow_le_pow_of_le_one hρ hρ'.le (Nat.le_add_right n N)
  let H (n : ℕ) := H₀ (n + N)
  have hH (n : ℕ) : H n ≤ M * ρ ^ n := by
    exact ((hcrit _ (hNn n)).2.trans (mul_le_mul_of_nonneg_right hM₀
      (pow_nonneg hρ _))).trans (mul_le_mul_of_nonneg_left (hρle n) hMp.le)
  have hHabs (n : ℕ) : |H n| ≤ M * (z n + ρ ^ n) := by
    have hd : max (A n - 1) 0 ≤ z n := by
      apply max_le _ (hz n)
      rw [hAz]
      nlinarith only [hbU n, mul_nonneg (sub_nonneg.mpr (hbU n)) (hz n)]
    exact (hHsmall' _ (hNn n)).trans
      (mul_le_mul_of_nonneg_left (add_le_add hd (hρle n)) hMp.le)
  let V := M * (Z + 1)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hHab (n : ℕ) : |H n| ≤ V := (hHabs n).trans
    (mul_le_mul_of_nonneg_left (add_le_add (hzmax n) (pow_le_one₀ hρ hρ'.le)) hMp.le)
  obtain ⟨E₂, hE₂, hE₂b⟩ := productLogCorrection_bounded hpos hB h 2
  obtain ⟨E₃, hE₃, hE₃b⟩ := productLogCorrection_bounded hpos hB h 3
  obtain ⟨E₄, hE₄, hE₄b⟩ := productLogCorrection_bounded hpos hB h 4
  let E := E₂ + E₃ + E₄
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let e (k n : ℕ) := productLogCorrection μ B h k (n + N)
  have he₂ (n : ℕ) : |e 2 n| ≤ E := (hE₂b _ (hNn n)).trans (by dsimp [E]; linarith)
  have he₃ (n : ℕ) : |e 3 n| ≤ E := (hE₃b _ (hNn n)).trans (by dsimp [E]; linarith)
  have he₄ (n : ℕ) : |e 4 n| ≤ E := (hE₄b _ (hNn n)).trans (by dsimp [E]; linarith)
  have hrec (n : ℕ) :
      K₀ (n + 1 + N) = A n * K₀ (n + N) + (H n ^ 2 + e 2 n) ∧
      J₀ (n + 1 + N) = A n * J₀ (n + N) + (3 * H n * K₀ (n + N) + e 3 n) ∧
      L₀ (n + 1 + N) = A n * L₀ (n + N) +
        (4 * H n * J₀ (n + N) + 3 * K₀ (n + N) ^ 2 + e 4 n) := by
    simpa only [show n + 1 + N = n + N + 1 by omega, K₀, L₀, J₀, H, H₀, A, A₀, e, add_assoc]
      using (productLogMoment_recursions hpos hmean hB h (n + N)).2
  let C := 1 + Z + G * S + S * (V ^ 2 + E) + 4 * M * S ^ 2 + 3 * S ^ 3 +
    S * (4 * V * G + E)
  have hCb : 1 ≤ C ∧ Z ≤ C ∧ G * S ≤ C ∧ S * (V ^ 2 + E) ≤ C ∧
      4 * M * S ^ 2 ≤ C ∧ 3 * S ^ 3 ≤ C ∧ S * (4 * V * G + E) ≤ C := by
    have ha : 0 ≤ G * S := by positivity
    have hb : 0 ≤ S * (V ^ 2 + E) := by positivity
    have hc : 0 ≤ 4 * M * S ^ 2 := by positivity
    have hd : 0 ≤ 3 * S ^ 3 := by positivity
    have he : 0 ≤ S * (4 * V * G + E) := by positivity
    dsimp only [C]
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨hC, hZC, hGSC, hCV, hCM, hCK, hCJ⟩ := hCb
  have hES : S * E ≤ C := (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left (sq_nonneg V)) hS.le).trans hCV
  have hCSb (n : ℕ) : K n ^ 2 ≤ C * (J n + C) := (hCS n).trans
    (mul_le_mul hGSC (add_le_add_right hGSC _) (by linarith only [hJlow n])
      (zero_le_one.trans hC))
  have hKdiff (n : ℕ) : K (n + 1) / P (n + 1) - K n / P n =
      (H n ^ 2 + e 2 n) / f (n + 1) / P (n + 1) :=
    product_scaled_step (m := fun i => K₀ (i + N)) (e := fun i => H i ^ 2 + e 2 i)
      hp hf hPstep hfactor (fun i => (hrec i).1) n
  have hJdiff (n : ℕ) : J (n + 1) / P (n + 1) - J n / P n =
      (3 * H n * K₀ (n + N) + e 3 n) / f (n + 1) / P (n + 1) :=
    product_scaled_step (m := fun i => J₀ (i + N))
      (e := fun i => 3 * H i * K₀ (i + N) + e 3 i)
      hp hf hPstep hfactor (fun i => (hrec i).2.1) n
  have hLdiff (n : ℕ) : L (n + 1) / P (n + 1) - L n / P n =
      (4 * H n * J₀ (n + N) + 3 * K₀ (n + N) ^ 2 + e 4 n) / f (n + 1) / P (n + 1) :=
    product_scaled_step (m := fun i => L₀ (i + N))
      (e := fun i => 4 * H i * J₀ (i + N) + 3 * K₀ (i + N) ^ 2 + e 4 i)
      hp hf hPstep hfactor (fun i => (hrec i).2.2) n
  have hKS (n : ℕ) : K (n + 1) / P (n + 1) - K n / P n ≤ C / P (n + 1) := by
    rw [hKdiff]
    apply div_le_div_of_nonneg_right _ (hp _).le
    have hsq : H n ^ 2 ≤ V ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hHab n) 2
    have hb : H n ^ 2 + e 2 n ≤ V ^ 2 + E :=
      add_le_add hsq ((le_abs_self _).trans (he₂ n))
    calc
      _ ≤ (V ^ 2 + E) / f (n + 1) := div_le_div_of_nonneg_right hb (hf _).le
      _ ≤ S * (V ^ 2 + E) := by
        rw [div_eq_mul_inv, mul_comm S]
        exact mul_le_mul_of_nonneg_left (hfinv _) (by positivity)
      _ ≤ C := hCV
  have hJS (n : ℕ) : J (n + 1) / P (n + 1) - J n / P n ≤
      C * ρ ^ n * K n / P (n + 1) + C / P (n + 1) := by
    rw [hJdiff, ← add_div]
    apply div_le_div_of_nonneg_right _ (hp _).le
    have hm : 3 * H n * K₀ (n + N) ≤ 3 * M * ρ ^ n * (S * K n) := by
      have h1 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hH n) (by norm_num : (0 : ℝ) ≤ 3))
        (hK₀ n)
      have h2 := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hfhi n) (hK n))
        (mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (3 : ℝ)) hMp.le) (pow_nonneg hρ n))
      rw [hKr] at h1 ⊢
      nlinarith only [h1, h2]
    let R := 3 * M * ρ ^ n * (S * K n) + E
    have hR : 0 ≤ R := by
      have hk := hK n
      dsimp [R]
      positivity
    have hbound : (3 * H n * K₀ (n + N) + e 3 n) / f (n + 1) ≤ R * S := by
      rw [div_eq_mul_inv]
      exact (mul_le_mul_of_nonneg_right (add_le_add hm ((le_abs_self _).trans (he₃ n)))
        (inv_nonneg.mpr (hf _).le)).trans (mul_le_mul_of_nonneg_left (hfinv _) hR)
    have hcol := mul_le_mul_of_nonneg_right hCM (mul_nonneg (pow_nonneg hρ n) (hK n))
    dsimp [R] at hbound
    nlinarith only [hbound, hcol, hES,
      mul_nonneg (mul_nonneg hMp.le (sq_nonneg S)) (mul_nonneg (pow_nonneg hρ n) (hK n))]
  have hJB (n : ℕ) : J n / P n - J (n + 1) / P (n + 1) ≤
      C * ((z n + ρ ^ n) * K n + 1) / P (n + 1) := by
    have hh := hJdiff n
    have hh' : J n / P n - J (n + 1) / P (n + 1) =
        (-(3 * H n * K₀ (n + N) + e 3 n) / f (n + 1)) / P (n + 1) := by
      rw [neg_div, neg_div]
      linarith only [hh]
    rw [hh']
    apply div_le_div_of_nonneg_right _ (hp _).le
    have hz0 := hz n
    have hk0 := hK n
    have hm : -(3 * H n * K₀ (n + N) + e 3 n) ≤
        3 * M * (z n + ρ ^ n) * (S * K n) + E := by
      have h1 : -H n ≤ M * (z n + ρ ^ n) := (neg_le_abs _).trans (hHabs n)
      have h2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3)) (hK₀ n)
      have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hfhi n) (hK n))
        (show 0 ≤ 3 * M * (z n + ρ ^ n) by positivity)
      rw [hKr] at h2 ⊢
      nlinarith only [h2, h3, (neg_le_abs (e 3 n)).trans (he₃ n)]
    have hbound : -(3 * H n * K₀ (n + N) + e 3 n) / f (n + 1) ≤
        (3 * M * (z n + ρ ^ n) * (S * K n) + E) * S := by
      rw [div_eq_mul_inv]
      exact (mul_le_mul_of_nonneg_right hm (inv_nonneg.mpr (hf _).le)).trans
        (mul_le_mul_of_nonneg_left (hfinv _) (by positivity))
    have hg : 0 ≤ (z n + ρ ^ n) * K n := by positivity
    have hcol := mul_le_mul_of_nonneg_right hCM hg
    nlinarith only [hbound, hcol, hES, mul_nonneg (mul_nonneg hMp.le (sq_nonneg S)) hg]
  have hLS (n : ℕ) : L (n + 1) / P (n + 1) - L n / P n ≤
      C * (ρ ^ n * |J n| + K n ^ 2 + 1) / P (n + 1) := by
    rw [hLdiff]
    apply div_le_div_of_nonneg_right _ (hp _).le
    have hHJ : H n * J₀ (n + N) ≤ M * ρ ^ n * (S * |J n|) + V * G := by
      by_cases hj : 0 ≤ J₀ (n + N)
      · have h1 := mul_le_mul_of_nonneg_right (hH n) hj
        have h2 : J₀ (n + N) ≤ S * |J n| := by
          rw [hJr]
          exact (mul_le_mul_of_nonneg_left (le_abs_self _) (hf n).le).trans
            (mul_le_mul_of_nonneg_right (hfhi n) (abs_nonneg _))
        have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hMp.le (pow_nonneg hρ n))
        linarith only [h1, h3, mul_nonneg hV hGp]
      · have h1 : |J₀ (n + N)| ≤ G := by
          rw [abs_of_neg (lt_of_not_ge hj)]
          linarith only [hJ₀ n]
        have h2 : H n * J₀ (n + N) ≤ V * G := calc
          _ ≤ |H n * J₀ (n + N)| := le_abs_self _
          _ = |H n| * |J₀ (n + N)| := abs_mul _ _
          _ ≤ _ := mul_le_mul (hHab n) h1 (abs_nonneg _) hV
        linarith only [h2, show 0 ≤ M * ρ ^ n * (S * |J n|) by positivity]
    have hs : K₀ (n + N) ^ 2 ≤ S ^ 2 * K n ^ 2 := by
      rw [hKr, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hf n).le (hfhi n) 2) (sq_nonneg _)
    let R := (4 * M * ρ ^ n * (S * |J n|) + 3 * S ^ 2 * K n ^ 2) + (4 * V * G + E)
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have hbound : (4 * H n * J₀ (n + N) + 3 * K₀ (n + N) ^ 2 + e 4 n) / f (n + 1) ≤
        R * S := by
      rw [div_eq_mul_inv]
      calc
        _ ≤ R * (f (n + 1))⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (hf (n + 1)).le)
          dsimp [R]
          linarith only [hHJ, hs, (le_abs_self (e 4 n)).trans (he₄ n)]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hfinv (n + 1)) hR
    have hcol := mul_le_mul_of_nonneg_right hCM
      (mul_nonneg (pow_nonneg hρ n) (abs_nonneg (J n)))
    have hsq := mul_le_mul_of_nonneg_right hCK (sq_nonneg (K n))
    dsimp [R] at hbound
    linarith only [hbound, hcol, hsq, hCJ]
  have hreturn (ε : ℝ) (hε : 0 < ε) : ∃ᶠ n in atTop, z n < ε := by
    have hlim : Tendsto b atTop (𝓝 1) := by
      have hh := (tendsto_floorSeq hB).comp (tendsto_add_atTop_nat N)
      simpa only [Real.one_rpow, Function.comp_def, b] using
        ((Real.continuous_rpow_const (theta_pos hB).le).continuousAt.tendsto.comp hh)
    have hevent : ∀ᶠ n in atTop, 1 + ε / 2 < b n * (1 + ε) := by
      have hh := hlim.mul_const (1 + ε)
      simp only [one_mul] at hh
      exact hh.eventually (Ioi_mem_nhds (by linarith))
    obtain ⟨k, hk⟩ := eventually_atTop.mp hevent
    apply frequently_atTop.mpr
    intro m
    obtain ⟨i, hi, ha⟩ := frequently_atTop.mp (hReturn.1 (ε / 2) (by positivity)) (max m k + N)
    let j := i - N
    have hji : j + N = i := Nat.sub_add_cancel (by omega)
    have hja : A j < 1 + ε / 2 := by
      simpa only [A, A₀, hji, h] using ha
    have hb' := hk j (by omega)
    refine ⟨j, by omega, ?_⟩
    dsimp only [z]
    apply (sub_lt_iff_lt_add).2
    apply (div_lt_iff₀ (hb j)).2
    nlinarith only [hja, hb']
  obtain ⟨hPs, ⟨ell, hell, hJlim⟩, d, D, hd, hD, hlow, hevent⟩ :=
    product_sequence_bounds hP hz (fun n => (hzmax n).trans hZC) hPstep hzstep hρ hρ'
      (div_pos hδ hS) hC hK hL (fun n => by linarith only [hGSC, hJlow n])
      hNash' hCSb hCS' hKS hJS hJB hLS hreturn
  have hsumShift : Summable (fun n => (Q n)⁻¹) := by
    apply (hPs.mul_left S).of_nonneg_of_le (fun n => inv_nonneg.mpr (hQ n).le)
    intro n
    rw [hQr]
    rw [show (f n * P n)⁻¹ = (f n)⁻¹ * (P n)⁻¹ by field_simp [(hf n).ne', (hp n).ne']]
    exact mul_le_mul_of_nonneg_right (hfinv n) (inv_nonneg.mpr (hp n).le)
  have hsum : Summable (fun n => (Q₀ n)⁻¹) := (summable_nat_add_iff N).1 hsumShift
  have hjlimShift : Tendsto (fun n => J₀ (n + N) / Q₀ (n + N)) atTop (𝓝 ell) := by
    apply hJlim.congr
    intro n
    change J n / P n = J₀ (n + N) / Q n
    rw [hJr, hQr, mul_div_mul_left _ _ (hf n).ne']
  have hjlim : Tendsto (fun n => J₀ n / Q₀ n) atTop (𝓝 ell) :=
    (tendsto_add_atTop_iff_nat N).1 hjlimShift
  have hlarge : ∀ᶠ n : ℕ in atTop, max N 1 ≤ n := eventually_ge_atTop _
  have hqB : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) ^ 2 / Q₀ n ≤ 4 / (fInf * d) ∧
      Q₀ n ≤ S * D * ((n : ℝ) + 1) ^ 2 ∧ K₀ n ^ 2 / Q₀ n ≤ S * D ∧
      L₀ n ≤ S * D * ((n : ℝ) + 1) ^ 3 := by
    apply product_eventually_unshift N
    filter_upwards [hevent, hlarge] with n hn hnN
    have hnN' : (N : ℝ) ≤ n := by exact_mod_cast (le_max_left N 1).trans hnN
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right N 1).trans hnN
    have hhalf : ((n + N : ℕ) : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) := by push_cast; linarith
    have hsmall : (n : ℝ) + 1 ≤ ((n + N : ℕ) : ℝ) + 1 := by
      have hh : (n : ℝ) ≤ ((n + N : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right n N
      linarith only [hh]
    have hlower : fInf * d * (((n + N : ℕ) : ℝ) + 1) ^ 2 ≤ 4 * Q n := by
      have h1 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (show 0 ≤ ((n + N : ℕ) : ℝ) + 1 by positivity) hhalf 2)
        (mul_nonneg hfInf.le hd.le)
      have h2 := mul_le_mul (hflo n) (hlow n).1
        (show 0 ≤ d * ((n : ℝ) + 1) ^ 2 by positivity) (hf n).le
      rw [hQr]
      nlinarith only [h1, h2]
    have hQupper : Q n ≤ S * D * (((n + N : ℕ) : ℝ) + 1) ^ 2 := by
      rw [hQr]
      have h1 := mul_le_mul (hfhi n) hn.1 (hp n).le hS.le
      have h2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (show 0 ≤ (n : ℝ) + 1 by positivity) hsmall 2)
        (mul_nonneg hS.le hD.le)
      nlinarith only [h1, h2]
    have hKupper : K₀ (n + N) ^ 2 ≤ S * D * Q n := by
      rw [hKr, hQr, mul_pow]
      have h1 := mul_le_mul_of_nonneg_left (hlow n).2 (sq_nonneg (f n))
      have h2 := mul_le_mul_of_nonneg_right (hfhi n)
        (mul_nonneg hD.le (mul_nonneg (hf n).le (hp n).le))
      nlinarith only [h1, h2]
    have hLupper : L₀ (n + N) ≤ S * D * (((n + N : ℕ) : ℝ) + 1) ^ 3 := by
      rw [hLr]
      have h1 := mul_le_mul (hfhi n) hn.2.1 (hL n) hS.le
      have h2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (show 0 ≤ (n : ℝ) + 1 by positivity) hsmall 3)
        (mul_nonneg hS.le hD.le)
      nlinarith only [h1, h2]
    refine ⟨?_, hQupper, (div_le_iff₀ (hQ n)).2 hKupper, hLupper⟩
    apply (div_le_iff₀ (hQ n)).2
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (mul_pos hfInf hd)).2
    linarith only [hlower]
  obtain ⟨Cq, hCq, hCqB⟩ := product_global_upper (p := fun n => ((n : ℝ) + 1) ^ 2 / Q₀ n) (D := 4 / (fInf * d))
    (w := fun _ => 1) (fun _ => one_pos) (by positivity)
    (by simpa only [mul_one] using hqB.mono fun _ h => h.1)
  obtain ⟨Cq', hCq', hCqB'⟩ := product_global_upper (p := Q₀) (D := S * D)
    (w := fun n => ((n : ℝ) + 1) ^ 2) (fun _ => by positivity) (by positivity)
    (hqB.mono fun _ h => h.2.1)
  obtain ⟨Ck, hCk, hCkB⟩ := product_global_upper (p := fun n => K₀ n ^ 2 / Q₀ n) (D := S * D)
    (w := fun _ => 1) (fun _ => one_pos) (by positivity)
    (by simpa only [mul_one] using hqB.mono fun _ h => h.2.2.1)
  obtain ⟨Cl, hCl, hClB⟩ := product_global_upper (p := L₀) (D := S * D)
    (w := fun n => ((n : ℝ) + 1) ^ 3) (fun _ => by positivity) (by positivity)
    (hqB.mono fun _ h => h.2.2.2)
  let Cfin := Cq + Cq' + Ck + Cl
  have hCfin : 0 < Cfin := by dsimp [Cfin]; positivity
  have hCfinB : ∀ n : ℕ,
      ((n : ℝ) + 1) ^ 2 / Cfin ≤ Q₀ n ∧ Q₀ n ≤ Cfin * ((n : ℝ) + 1) ^ 2 ∧
      K₀ n ^ 2 ≤ Cfin * Q₀ n ∧ L₀ n ≤ Cfin * ((n : ℝ) + 1) ^ 3 := by
    intro n
    have h1 : Cq ≤ Cfin := by dsimp [Cfin]; linarith
    have h2 : Cq' ≤ Cfin := by dsimp [Cfin]; linarith
    have h3 : Ck ≤ Cfin := by dsimp [Cfin]; linarith
    have h4 : Cl ≤ Cfin := by dsimp [Cfin]; linarith
    have hq := (div_le_iff₀ (hQ₀pos n)).1 ((by simpa only [mul_one] using hCqB n :
      ((n : ℝ) + 1) ^ 2 / Q₀ n ≤ Cq).trans h1)
    have hk := (div_le_iff₀ (hQ₀pos n)).1 ((by simpa only [mul_one] using hCkB n :
      K₀ n ^ 2 / Q₀ n ≤ Ck).trans h3)
    exact ⟨(div_le_iff₀ hCfin).2 (by simpa only [mul_comm Cfin] using hq),
      (hCqB' n).trans (mul_le_mul_of_nonneg_right h2 (sq_nonneg _)), hk,
      (hClB n).trans (mul_le_mul_of_nonneg_right h4 (by positivity))⟩
  let ca := b₁ * d / 2
  let ck := fInf * d / 2
  have hca : 0 < ca := by dsimp [ca]; positivity
  have hck : 0 < ck := by dsimp [ck]; positivity
  have hGeo : ∀ᶠ n : ℕ in atTop, ρ ^ (n + N) ≤ ca * ((n + N : ℕ) : ℝ)⁻¹ :=
    (tendsto_add_atTop_nat N).eventually (product_geom_inv_eventual hρ hρ' hca)
  have hRates : ∀ᶠ n : ℕ in atTop,
      ca * (n : ℝ)⁻¹ ≤ A₀ n - 1 ∧ A₀ n - 1 ≤ (2 * D) * (n : ℝ)⁻¹ ∧
      ck * (n : ℝ) ≤ K₀ n ∧ K₀ n ≤ (S * D) * (n : ℝ) ∧
      |H₀ n| ≤ M * (2 * D + ca) * (n : ℝ)⁻¹ := by
    apply product_eventually_unshift N
    filter_upwards [hevent, hlarge, hGeo] with n hn hnN hg
    have hnN' : (N : ℝ) ≤ n := by exact_mod_cast (le_max_left N 1).trans hnN
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right N 1).trans hnN
    have hnpos : (0 : ℝ) < n := by linarith
    have h0 : (n : ℝ) ≤ ((n + N : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right n N
    have h1 : ((n + N : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by push_cast; linarith
    have hnp : 0 < ((n + N : ℕ) : ℝ) := hnpos.trans_le h0
    have hi : (((n + N : ℕ) : ℝ))⁻¹ ≤ (n : ℝ)⁻¹ := inv_anti₀ hnpos h0
    have hi' : (n : ℝ)⁻¹ ≤ 2 * (((n + N : ℕ) : ℝ))⁻¹ := by
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ hnp).2
      rw [inv_mul_eq_div]
      apply (div_le_iff₀ hnpos).2
      linarith only [h1]
    have hferr : 1 - b n ≤ ca * (((n + N : ℕ) : ℝ))⁻¹ :=
      (product_floor_rpow_error hB (hNn n)).trans hg
    have h1a : ca * (((n + N : ℕ) : ℝ))⁻¹ ≤ A n - 1 := by
      have hh := mul_le_mul (hbL n)
        ((mul_le_mul_of_nonneg_left hi hd.le).trans hn.2.2.1)
        (mul_nonneg hd.le (inv_nonneg.mpr hnp.le)) (hb n).le
      rw [hAz]
      dsimp only [ca] at hferr ⊢
      nlinarith only [hh, hferr]
    have h2a : A n - 1 ≤ (2 * D) * (((n + N : ℕ) : ℝ))⁻¹ := by
      have h2 : A n - 1 ≤ z n := by
        rw [hAz]
        nlinarith only [hbU n, mul_nonneg (sub_nonneg.mpr (hbU n)) (hz n)]
      have h3 := mul_le_mul_of_nonneg_left hi' hD.le
      have h4 := h2.trans hn.2.2.2.1
      nlinarith only [h3, h4]
    have h1k : ck * (((n + N : ℕ) : ℝ)) ≤ K₀ (n + N) := by
      rw [hKr]
      have hh := mul_le_mul (hflo n) hn.2.2.2.2.1 (by positivity) (hf n).le
      have hck' := mul_le_mul_of_nonneg_left h1 (mul_nonneg hfInf.le hd.le)
      dsimp [ck]
      nlinarith only [hh, hck']
    have h2k : K₀ (n + N) ≤ (S * D) * (((n + N : ℕ) : ℝ)) := by
      rw [hKr]
      have hh := mul_le_mul (hfhi n) hn.2.2.2.2.2 (hK n) hS.le
      have hh' := mul_le_mul_of_nonneg_left h0 (mul_nonneg hS.le hD.le)
      nlinarith only [hh, hh']
    have hh := hHsmall' (n + N) (hNn n)
    have hmax : max (A n - 1) 0 = A n - 1 := max_eq_left
      ((mul_nonneg hca.le (inv_nonneg.mpr hnp.le)).trans h1a)
    change |H₀ (n + N)| ≤ M * (max (A n - 1) 0 + ρ ^ (n + N)) at hh
    rw [hmax] at hh
    refine ⟨h1a, h2a, h1k, h2k, ?_⟩
    have hh' := mul_le_mul_of_nonneg_left (add_le_add h2a hg) hMp.le
    nlinarith only [hh, hh']
  have hApos : ∀ᶠ n : ℕ in atTop, 1 < A₀ n := by
    filter_upwards [hRates, eventually_ge_atTop 1] with n hn hn1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
    exact sub_pos.mp ((mul_pos hca (inv_pos.mpr hnpos)).trans_le hn.1)
  have hATheta : (fun n => A₀ n - 1) =Θ[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
    constructor
    · refine isBigO_iff.2 ⟨2 * D, ?_⟩
      filter_upwards [hRates, hApos] with n hn ha
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha.le),
        abs_of_nonneg (show 0 ≤ (n : ℝ)⁻¹ from inv_nonneg.mpr (Nat.cast_nonneg n))] using hn.2.1
    · refine isBigO_iff.2 ⟨ca⁻¹, ?_⟩
      filter_upwards [hRates, hApos] with n hn ha
      simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha.le),
        abs_of_nonneg (show 0 ≤ (n : ℝ)⁻¹ from inv_nonneg.mpr (Nat.cast_nonneg n))]
      simpa only [div_eq_inv_mul] using (le_div_iff₀' hca).2 hn.1
  have hKTheta : K₀ =Θ[atTop] (fun n : ℕ => (n : ℝ)) := by
    constructor
    · refine isBigO_iff.2 ⟨S * D, ?_⟩
      filter_upwards [hRates] with n hn
      have hk : 0 ≤ K₀ n := (mul_nonneg hck.le (Nat.cast_nonneg n)).trans hn.2.2.1
      simpa only [Real.norm_eq_abs, abs_of_nonneg hk, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using hn.2.2.2.1
    · refine isBigO_iff.2 ⟨ck⁻¹, ?_⟩
      filter_upwards [hRates] with n hn
      have hk : 0 ≤ K₀ n := (mul_nonneg hck.le (Nat.cast_nonneg n)).trans hn.2.2.1
      simp only [Real.norm_eq_abs, abs_of_nonneg hk, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      simpa only [div_eq_inv_mul] using (le_div_iff₀' hck).2 hn.2.2.1
  have hHO : H₀ =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
    refine isBigO_iff.2 ⟨M * (2 * D + ca), ?_⟩
    filter_upwards [hRates] with n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (n : ℝ)⁻¹ from inv_nonneg.mpr (Nat.cast_nonneg n))]
      using hn.2.2.2.2
  have hAtend : Tendsto A₀ atTop (𝓝 1) := by
    have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_natCast_atTop_atTop.inv_tendsto_atTop
    have ht : Tendsto (fun n : ℕ => (2 * D) * (n : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using hi.const_mul (2 * D)
    have hz : Tendsto (fun n => A₀ n - 1) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
        (hApos.mono fun _ hh => sub_nonneg.mpr hh.le) (hRates.mono fun _ hh => hh.2.1)
    simpa only [sub_add_cancel, zero_add] using hz.add_const 1
  exact ⟨Cfin, hCfin, fun n _ => hCfinB n, hsum, ⟨ell, hell, hjlim⟩, hApos, hATheta,
    hKTheta, hHO, lawR_concentrates_of_tiltedMass_tendsto hpos hmean hB h hAtend⟩

end DiamondPinning
